#include "all.h"
#include "config.h"
#include <ctype.h>
#include "getopt.h"

Target T;

char debug['Z'+1] = {
	['P'] = 0, /* parsing */
	['M'] = 0, /* memory optimization */
	['N'] = 0, /* ssa construction */
	['C'] = 0, /* copy elimination */
	['F'] = 0, /* constant folding */
	['A'] = 0, /* abi lowering */
	['I'] = 0, /* instruction selection */
	['L'] = 0, /* liveness */
	['S'] = 0, /* spilling */
	['R'] = 0, /* reg. allocation */
};

extern Target T_amd64_sysv;
extern Target T_amd64_apple;
extern Target T_amd64_win;
extern Target T_arm64;
extern Target T_arm64_apple;
extern Target T_rv64;

static Target *tlist[] = {
	&T_amd64_sysv,
	&T_amd64_apple,
	&T_amd64_win,
	&T_arm64,
	&T_arm64_apple,
	&T_rv64,
	0
};
static FILE *outf;
static int dbg;

/**
 * Processes data sections from the input file.
 * 
 * This function handles data declarations and emits them to the output file.
 * When debug mode is enabled, it skips data processing entirely.
 * When a data section ends (DEnd type), it adds a comment marker and frees
 * all allocated memory.
 * 
 * @param d Pointer to the data structure containing the data section information
 */
static void
data(Dat *d)
{
	if (dbg)
		return;
	emitdat(d, outf);
	if (d->type == DEnd) {
		fputs("/* end data */\n\n", outf);
		freeall();
	}
}

/**
 * Processes a single function through the complete compilation pipeline.
 * 
 * This is the main function processing routine that applies all optimization
 * and code generation passes in the correct order. The pipeline includes:
 * - ABI lowering (initial)
 * - Control flow graph construction
 * - Use/def analysis
 * - SSA construction and validation
 * - Alias analysis
 * - Load optimization
 * - Copy coalescing
 * - Dominance analysis
 * - Global value numbering
 * - Global code motion
 * - ABI lowering (final)
 * - Instruction simplification
 * - Instruction selection
 * - Liveness analysis
 * - Loop analysis
 * - Cost analysis
 * - Register spilling
 * - Register allocation
 * - Jump simplification
 * 
 * In debug mode, it prints intermediate representations after each pass.
 * Otherwise, it emits the final assembly code for the function.
 * 
 * @param fn Pointer to the function structure to be processed
 */
static void
func(Fn *fn)
{
	uint n;

	if (dbg)
		fprintf(stderr, "**** Function %s ****", fn->name);
	if (debug['P']) {
		fprintf(stderr, "\n> After parsing:\n");
		printfn(fn, stderr);
	}
	T.abi0(fn);
	fillcfg(fn);
	filluse(fn);
	promote(fn);
	filluse(fn);
	ssa(fn);
	filluse(fn);
	ssacheck(fn);
	fillalias(fn);
	loadopt(fn);
	filluse(fn);
	fillalias(fn);
	coalesce(fn);
	filluse(fn);
	filldom(fn);
	ssacheck(fn);
	gvn(fn);
	fillcfg(fn);
	filluse(fn);
	filldom(fn);
	gcm(fn);
	filluse(fn);
	ssacheck(fn);
	T.abi1(fn);
	simpl(fn);
	fillcfg(fn);
	filluse(fn);
	T.isel(fn);
	fillcfg(fn);
	filllive(fn);
	fillloop(fn);
	fillcost(fn);
	spill(fn);
	rega(fn);
	fillcfg(fn);
	simpljmp(fn);
	fillcfg(fn);
	assert(fn->rpo[0] == fn->start);
	for (n=0;; n++)
		if (n == fn->nblk-1) {
			fn->rpo[n]->link = 0;
			break;
		} else
			fn->rpo[n]->link = fn->rpo[n+1];
	if (!dbg) {
		T.emitfn(fn, outf);
		fprintf(outf, "/* end function %s */\n\n", fn->name);
	} else
		fprintf(stderr, "\n");
	freeall();
}

/**
 * Emits debug file information to the output.
 * 
 * This function is called during parsing to output debug information
 * about source files. It delegates to the target-specific debug file
 * emission function.
 * 
 * @param fn The filename to emit debug information for
 */
static void
dbgfile(char *fn)
{
	emitdbgfile(fn, outf);
}

/**
 * Main entry point for the qbe compiler backend.
 * 
 * This function parses command line arguments, sets up the target architecture,
 * and processes input files through the compilation pipeline. It supports:
 * - Multiple target architectures (amd64, arm64, rv64)
 * - Debug output with various flags
 * - Output file specification
 * - Multiple input files
 * 
 * The compilation process involves parsing SSA-form input, applying
 * optimizations, and generating target-specific assembly code.
 * 
 * @param ac Number of command line arguments
 * @param av Array of command line argument strings
 * @return 0 on successful completion, 1 on error
 */
int
main(int ac, char *av[])
{
	Target **t;
	FILE *inf, *hf;
	char *f, *sep;
	int c;

	T = Deftgt;
	outf = stdout;
	while ((c = getopt(ac, av, "hd:o:t:")) != -1)
		switch (c) {
		case 'd':
			for (; *optarg; optarg++)
				if (isalpha(*optarg)) {
					debug[toupper(*optarg)] = 1;
					dbg = 1;
				}
			break;
		case 'o':
			if (strcmp(optarg, "-") != 0) {
				outf = fopen(optarg, "w");
				if (!outf) {
					fprintf(stderr, "cannot open '%s'\n", optarg);
					exit(1);
				}
			}
			break;
		case 't':
			if (strcmp(optarg, "?") == 0) {
				puts(T.name);
				exit(0);
			}
			for (t=tlist;; t++) {
				if (!*t) {
					fprintf(stderr, "unknown target '%s'\n", optarg);
					exit(1);
				}
				if (strcmp(optarg, (*t)->name) == 0) {
					T = **t;
					break;
				}
			}
			break;
		case 'h':
		default:
			hf = c != 'h' ? stderr : stdout;
			fprintf(hf, "%s [OPTIONS] {file.ssa, -}\n", av[0]);
			fprintf(hf, "\t%-11s prints this help\n", "-h");
			fprintf(hf, "\t%-11s output to file\n", "-o file");
			fprintf(hf, "\t%-11s generate for a target among:\n", "-t <target>");
			fprintf(hf, "\t%-11s ", "");
			for (t=tlist, sep=""; *t; t++, sep=", ") {
				fprintf(hf, "%s%s", sep, (*t)->name);
				if (*t == &Deftgt)
					fputs(" (default)", hf);
			}
			fprintf(hf, "\n");
			fprintf(hf, "\t%-11s dump debug information\n", "-d <flags>");
			exit(c != 'h');
		}

	do {
		f = av[optind];
		if (!f || strcmp(f, "-") == 0) {
			inf = stdin;
			f = "-";
		} else {
			inf = fopen(f, "r");
			if (!inf) {
				fprintf(stderr, "cannot open '%s'\n", f);
				exit(1);
			}
		}
		parse(inf, f, dbgfile, data, func);
		fclose(inf);
	} while (++optind < ac);

	if (!dbg)
		T.emitfin(outf);

	exit(0);
}
