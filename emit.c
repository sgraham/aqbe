#include "all.h"

enum {
	SecText,
	SecData,
	SecBss,
};

/**
 * Emits a symbol declaration with appropriate section and linkage attributes.
 * 
 * This function generates assembly code for symbol declarations, handling
 * different object file formats (ELF, Mach-O, PE) and various symbol types.
 * It supports:
 * - Function and data symbols
 * - Thread-local variables (with special handling for Apple platforms)
 * - Different sections (text, data, bss)
 * - Export declarations and alignment specifications
 * 
 * The function adapts its output based on the target platform, using
 * appropriate section names and syntax for each format. For thread-local
 * variables on Apple platforms, it generates the special TLV bootstrap
 * structure required by the runtime.
 * 
 * @param n The symbol name
 * @param l Linkage information (section, alignment, export status, thread-local)
 * @param s Section type (SecText, SecData, SecBss)
 * @param f Output file stream
 */
void
emitlnk(char *n, Lnk *l, int s, FILE *f)
{
	static char *sec[2][3] = {
		[0][SecText] = ".text",
		[0][SecData] = ".data",
		[0][SecBss] = ".bss",
		[1][SecText] = ".abort \"unreachable\"",
		[1][SecData] = ".section .tdata,\"awT\"",
		[1][SecBss] = ".section .tbss,\"awT\"",
	};
	char *pfx, *sfx;

	pfx = n[0] == '"' ? "" : T.assym;
	sfx = "";
	if (T.apple && l->thread) {
		l->sec = "__DATA";
		l->secf = "__thread_data,thread_local_regular";
		sfx = "$tlv$init";
		fputs(
			".section __DATA,__thread_vars,"
			"thread_local_variables\n",
			f
		);
		fprintf(f, "%s%s:\n", pfx, n);
		fprintf(f,
			"\t.quad __tlv_bootstrap\n"
			"\t.quad 0\n"
			"\t.quad %s%s%s\n\n",
			pfx, n, sfx
		);
	}
	if (l->sec) {
		fprintf(f, ".section %s", l->sec);
		if (l->secf)
			fprintf(f, ",%s", l->secf);
	} else
		fputs(sec[l->thread != 0][s], f);
	fputc('\n', f);
	if (l->align)
		fprintf(f, ".balign %d\n", l->align);
	if (l->export)
		fprintf(f, ".globl %s%s\n", pfx, n);
	fprintf(f, "%s%s%s:\n", pfx, n, sfx);
}

/**
 * Emits a function symbol declaration.
 * 
 * This is a convenience wrapper around emitlnk() that specifically
 * handles function symbols, which are always placed in the text section.
 * 
 * @param n The function name
 * @param l Linkage information
 * @param f Output file stream
 */
void
emitfnlnk(char *n, Lnk *l, FILE *f)
{
	emitlnk(n, l, SecText, f);
}

/**
 * Emits data declarations and initializations.
 * 
 * This function processes data section declarations and generates
 * appropriate assembly directives. It handles various data types:
 * - Byte, halfword, word, and quadword data
 * - String literals
 * - Symbol references with offsets
 * - Zero-initialized data (BSS)
 * - Common symbols
 * 
 * The function uses a state machine approach to accumulate zero
 * bytes and emit them efficiently using .fill directives. It also
 * handles special cases like common symbols and string literals.
 * 
 * @param d The data declaration to emit
 * @param f Output file stream
 */
void
emitdat(Dat *d, FILE *f)
{
	static char *dtoa[] = {
		[DB] = "\t.byte",
		[DH] = "\t.short",
		[DW] = "\t.int",
		[DL] = "\t.quad"
	};
	static int64_t zero;
	char *p;

	switch (d->type) {
	case DStart:
		zero = 0;
		break;
	case DEnd:
		if (d->lnk->common) {
			if (zero == -1)
				die("invalid common data definition");
			p = d->name[0] == '"' ? "" : T.assym;
			fprintf(f, ".comm %s%s,%"PRId64,
				p, d->name, zero);
			if (d->lnk->align)
				fprintf(f, ",%d", d->lnk->align);
			fputc('\n', f);
		}
		else if (zero != -1) {
			emitlnk(d->name, d->lnk, SecBss, f);
			fprintf(f, "\t.fill %"PRId64",1,0\n", zero);
		}
		break;
	case DZ:
		if (zero != -1)
			zero += d->u.num;
		else
			fprintf(f, "\t.fill %"PRId64",1,0\n", d->u.num);
		break;
	default:
		if (zero != -1) {
			emitlnk(d->name, d->lnk, SecData, f);
			if (zero > 0)
				fprintf(f, "\t.fill %"PRId64",1,0\n", zero);
			zero = -1;
		}
		if (d->isstr) {
			if (d->type != DB)
				err("strings only supported for 'b' currently");
			fprintf(f, "\t.ascii %s\n", d->u.str);
		}
		else if (d->isref) {
			p = d->u.ref.name[0] == '"' ? "" : T.assym;
			fprintf(f, "%s %s%s%+"PRId64"\n",
				dtoa[d->type], p, d->u.ref.name,
				d->u.ref.off);
		}
		else {
			fprintf(f, "%s %"PRId64"\n",
				dtoa[d->type], d->u.num);
		}
		break;
	}
}

typedef struct Asmbits Asmbits;

struct Asmbits {
	bits n;
	int size;
	Asmbits *link;
};

static Asmbits *stash;

/**
 * Stashes floating-point constants for later emission.
 * 
 * This function maintains a list of floating-point constants that need
 * to be emitted as data. It deduplicates constants by checking if a
 * constant of the same or larger size already exists. This optimization
 * reduces the size of the generated assembly by avoiding duplicate
 * constant definitions.
 * 
 * The function supports 32-bit (float), 64-bit (double), and 128-bit
 * (long double) constants. Constants are stored in a linked list and
 * indexed for later emission.
 * 
 * @param n The bit representation of the floating-point constant
 * @param size The size of the constant in bytes (4, 8, or 16)
 * @return The index of the constant in the stash list
 */
int
stashbits(bits n, int size)
{
	Asmbits **pb, *b;
	int i;

	assert(size == 4 || size == 8 || size == 16);
	for (pb=&stash, i=0; (b=*pb); pb=&b->link, i++)
		if (size <= b->size && b->n == n)
			return i;
	b = emalloc(sizeof *b);
	b->n = n;
	b->size = size;
	b->link = 0;
	*pb = b;
	return i;
}

/**
 * Emits all stashed floating-point constants.
 * 
 * This function generates assembly code for all floating-point constants
 * that were previously stashed by stashbits(). It organizes constants
 * by size and emits them in appropriate sections with proper alignment.
 * 
 * The function handles different constant sizes:
 * - 32-bit floats: emitted as .int with comment showing decimal value
 * - 64-bit doubles: emitted as .quad with comment showing decimal value
 * - 128-bit long doubles: emitted as two .quad directives
 * 
 * After emission, it cleans up the stash list to free memory.
 * 
 * @param f Output file stream
 * @param sec Array of section names for different constant sizes
 */
static void
emitfin(FILE *f, char *sec[3])
{
	Asmbits *b;
	int lg, i;
	union { int32_t i; float f; } u;

	if (!stash)
		return;
	fprintf(f, "/* floating point constants */\n");
	for (lg=4; lg>=2; lg--)
		for (b=stash, i=0; b; b=b->link, i++) {
			if (b->size == (1<<lg)) {
				fprintf(f,
					".section %s\n"
					".p2align %d\n"
					"%sfp%d:",
					sec[lg-2], lg, T.asloc, i
				);
				if (lg == 4)
					fprintf(f,
						"\n\t.quad %"PRId64
						"\n\t.quad 0\n\n",
						(int64_t)b->n);
				else if (lg == 3)
					fprintf(f,
						"\n\t.quad %"PRId64
						" /* %f */\n\n",
						(int64_t)b->n,
						*(double *)&b->n);
				else if (lg == 2) {
					u.i = b->n;
					fprintf(f,
						"\n\t.int %"PRId32
						" /* %f */\n\n",
						u.i, (double)u.f);
				}
			}
		}
	while ((b=stash)) {
		stash = b->link;
		free(b);
	}
}

/**
 * Emits ELF-specific finalization directives.
 * 
 * This function generates ELF-specific assembly directives at the end
 * of the file, including floating-point constants and the GNU stack
 * note section that marks the stack as non-executable.
 * 
 * @param f Output file stream
 */
void
elf_emitfin(FILE *f)
{
	static char *sec[3] = { ".rodata", ".rodata", ".rodata" };

	emitfin(f ,sec);
	fprintf(f, ".section .note.GNU-stack,\"\",@progbits\n");
}

/**
 * Emits ELF-specific function finalization directives.
 * 
 * This function generates ELF-specific directives that mark the end
 * of a function, including the function type declaration and size
 * information for debugging and linking.
 * 
 * @param fn The function name
 * @param f Output file stream
 */
void
elf_emitfnfin(char *fn, FILE *f)
{
	fprintf(f, ".type %s, @function\n", fn);
	fprintf(f, ".size %s, .-%s\n", fn, fn);
}

/**
 * Emits Mach-O-specific finalization directives.
 * 
 * This function generates Mach-O-specific assembly directives at the
 * end of the file, including floating-point constants in appropriate
 * Mach-O sections. It handles the special case of 128-bit constants
 * which are not supported in Mach-O.
 * 
 * @param f Output file stream
 */
void
macho_emitfin(FILE *f)
{
	static char *sec[3] = {
		"__TEXT,__literal4,4byte_literals",
		"__TEXT,__literal8,8byte_literals",
		".abort \"unreachable\"",
	};

	emitfin(f, sec);
}

/**
 * Emits PE-specific finalization directives.
 * 
 * This function generates PE-specific assembly directives at the end
 * of the file, including floating-point constants in read-only data
 * sections.
 * 
 * @param f Output file stream
 */
void
pe_emitfin(FILE *f)
{
	static char *sec[3] = { ".rodata", ".rodata", ".rodata" };

	emitfin(f ,sec);
}

static uint32_t *file;
static uint nfile;
static uint curfile;

/**
 * Emits debug file information.
 * 
 * This function manages debug file information for assembly output.
 * It maintains a list of source files and assigns them unique identifiers
 * for use in debug location directives. The function deduplicates files
 * to avoid emitting the same .file directive multiple times.
 * 
 * The function uses the intern() function to canonicalize filenames
 * and maintains a global state of file numbers for the current
 * compilation unit.
 * 
 * @param fn The source filename
 * @param f Output file stream
 */
void
emitdbgfile(char *fn, FILE *f)
{
	uint32_t id;
	uint n;

	id = intern(fn);
	for (n=0; n<nfile; n++)
		if (file[n] == id) {
			/* gas requires positive
			 * file numbers */
			curfile = n + 1;
			return;
		}
	if (!file)
		file = vnew(0, sizeof *file, PHeap);
	vgrow(&file, ++nfile);
	file[nfile-1] = id;
	curfile = nfile;
	fprintf(f, ".file %u %s\n", curfile, fn);
}

/**
 * Emits debug location information.
 * 
 * This function generates debug location directives that map assembly
 * instructions back to source code locations. It uses the current file
 * number (set by emitdbgfile()) and the provided line and column numbers
 * to create .loc directives for the assembler.
 * 
 * The function handles both line-only and line+column location information,
 * adapting the output format accordingly.
 * 
 * @param line The source line number
 * @param col The source column number (0 if not specified)
 * @param f Output file stream
 */
void
emitdbgloc(uint line, uint col, FILE *f)
{
	if (col != 0)
		fprintf(f, "\t.loc %u %u %u\n", curfile, line, col);
	else
		fprintf(f, "\t.loc %u %u\n", curfile, line);
}
