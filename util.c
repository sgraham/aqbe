#include "all.h"
#include <stdarg.h>

typedef struct Bitset Bitset;
typedef struct Vec Vec;
typedef struct Bucket Bucket;

struct Vec {
	ulong mag;
	Pool pool;
	size_t esz;
	ulong cap;
	union {
		long long ll;
		long double ld;
		void *ptr;
	} align[];
};

struct Bucket {
	uint nstr;
	char **str;
};

enum {
	VMin = 2,
	VMag = 0xcabba9e,
	NPtr = 256,
	IBits = 12,
	IMask = (1<<IBits) - 1,
};

Typ *typ;
Ins insb[NIns], *curi;

static void *ptr[NPtr];
static void **pool = ptr;
static int nptr = 1;

static Bucket itbl[IMask+1]; /* string interning table */

/**
 * Computes a simple hash value for a string.
 * Uses a basic rolling hash algorithm: h = char + 17*h for each character.
 * 
 * @param s The string to hash
 * @return 32-bit hash value
 */
uint32_t
hash(char *s)
{
	uint32_t h;

	for (h=0; *s; ++s)
		h = *s + 17*h;
	return h;
}

/**
 * Fatal error handler that prints an error message and aborts the program.
 * Used for unrecoverable errors during compilation.
 * 
 * @param file Source file name where error occurred
 * @param s Format string for error message
 * @param ... Variable arguments for format string
 */
void
die_(char *file, char *s, ...)
{
	va_list ap;

	fprintf(stderr, "%s: dying: ", file);
	va_start(ap, s);
	vfprintf(stderr, s, ap);
	va_end(ap);
	fputc('\n', stderr);
	abort();
}

/**
 * Allocates memory with error checking.
 * Calls calloc to zero-initialize the memory and aborts if allocation fails.
 * 
 * @param n Number of bytes to allocate
 * @return Pointer to allocated memory, never NULL
 */
void *
emalloc(size_t n)
{
	void *p;

	p = calloc(1, n);
	if (!p)
		die("emalloc, out of memory");
	return p;
}

/**
 * Allocates memory from the compiler's memory pool.
 * Uses a simple pool-based allocator for temporary allocations during compilation.
 * Memory is automatically freed when freeall() is called.
 * 
 * @param n Number of bytes to allocate
 * @return Pointer to allocated memory, or NULL if n is 0
 */
void *
alloc(size_t n)
{
	void **pp;

	if (n == 0)
		return 0;
	if (nptr >= NPtr) {
		pp = emalloc(NPtr * sizeof(void *));
		pp[0] = pool;
		pool = pp;
		nptr = 1;
	}
	return pool[nptr++] = emalloc(n);
}

/**
 * Frees all memory allocated through the pool allocator.
 * Traverses the pool chain and frees all allocated blocks.
 * Resets the pool state for reuse.
 */
void
freeall()
{
	void **pp;

	for (;;) {
		for (pp = &pool[1]; pp < &pool[nptr]; pp++)
			free(*pp);
		pp = pool[0];
		if (!pp)
			break;
		free(pool);
		pool = pp;
		nptr = NPtr;
	}
	nptr = 1;
}

/**
 * Creates a new dynamic vector with specified capacity.
 * Vectors can grow automatically and support different memory pools.
 * 
 * @param len Initial capacity (will be rounded up to power of 2)
 * @param esz Size of each element in bytes
 * @param pool Memory pool to use (PHeap for permanent, other for temporary)
 * @return Pointer to vector data (vector header is hidden)
 */
void *
vnew(ulong len, size_t esz, Pool pool)
{
	void *(*f)(size_t);
	ulong cap;
	Vec *v;

	for (cap=VMin; cap<len; cap*=2)
		;
	f = pool == PHeap ? emalloc : alloc;
	v = f(cap * esz + sizeof(Vec));
	v->mag = VMag;
	v->cap = cap;
	v->esz = esz;
	v->pool = pool;
	return v + 1;
}

/**
 * Frees a vector allocated with vnew().
 * Only frees vectors allocated from the heap pool.
 * 
 * @param p Pointer to vector data (returned by vnew)
 */
void
vfree(void *p)
{
	Vec *v;

	v = (Vec *)p - 1;
	assert(v->mag == VMag);
	if (v->pool == PHeap) {
		v->mag = 0;
		free(v);
	}
}

/**
 * Grows a vector to accommodate at least 'len' elements.
 * Reallocates and copies data if current capacity is insufficient.
 * 
 * @param vp Pointer to vector pointer (will be updated if reallocation occurs)
 * @param len Minimum number of elements needed
 */
void
vgrow(void *vp, ulong len)
{
	Vec *v;
	void *v1;

	v = *(Vec **)vp - 1;
	assert(v+1 && v->mag == VMag);
	if (v->cap >= len)
		return;
	v1 = vnew(len, v->esz, v->pool);
	memcpy(v1, v+1, v->cap * v->esz);
	vfree(v+1);
	*(Vec **)vp = v1;
}

/**
 * Adds an instruction to a dynamic instruction array.
 * Skips no-op instructions and grows the array if needed.
 * 
 * @param pvins Pointer to instruction array pointer
 * @param pnins Pointer to instruction count
 * @param i Instruction to add
 */
void
addins(Ins **pvins, uint *pnins, Ins *i)
{
	if (i->op == Onop)
		return;
	vgrow(pvins, ++(*pnins));
	(*pvins)[(*pnins)-1] = *i;
}

/**
 * Adds all instructions from a basic block to a dynamic instruction array.
 * 
 * @param b Basic block containing instructions to add
 * @param pvins Pointer to instruction array pointer
 * @param pnins Pointer to instruction count
 */
void
addbins(Blk *b, Ins **pvins, uint *pnins)
{
	Ins *i;

	for (i=b->ins; i<&b->ins[b->nins]; i++)
		addins(pvins, pnins, i);
}

/**
 * Formats a string into a fixed-size buffer.
 * Uses vsnprintf for safe string formatting.
 * 
 * @param str Destination buffer (must be NString bytes)
 * @param s Format string
 * @param ... Variable arguments for format string
 */
void
strf(char str[NString], char *s, ...)
{
	va_list ap;

	va_start(ap, s);
	vsnprintf(str, NString, s, ap);
	va_end(ap);
}

/**
 * Interns a string for efficient comparison and storage.
 * Returns a unique integer ID for the string. Identical strings
 * get the same ID, enabling fast string comparison.
 * 
 * @param s String to intern
 * @return Unique integer ID for the string
 */
uint32_t
intern(char *s)
{
	Bucket *b;
	uint32_t h;
	uint i, n;

	h = hash(s) & IMask;
	b = &itbl[h];
	n = b->nstr;

	for (i=0; i<n; i++)
		if (strcmp(s, b->str[i]) == 0)
			return h + (i<<IBits);

	if (n == 1<<(32-IBits))
		die("interning table overflow");
	if (n == 0)
		b->str = vnew(1, sizeof b->str[0], PHeap);
	else if ((n & (n-1)) == 0)
		vgrow(&b->str, n+n);

	b->str[n] = emalloc(strlen(s)+1);
	b->nstr = n + 1;
	strcpy(b->str[n], s);
	return h + (n<<IBits);
}

/**
 * Retrieves a string from its interned ID.
 * 
 * @param id Interned string ID returned by intern()
 * @return Pointer to the original string
 */
char *
str(uint32_t id)
{
	assert(id>>IBits < itbl[id&IMask].nstr);
	return itbl[id&IMask].str[id>>IBits];
}

/**
 * Checks if a reference is a register (hardware register).
 * 
 * @param r Reference to check
 * @return 1 if reference is a register, 0 otherwise
 */
int
isreg(Ref r)
{
	return rtype(r) == RTmp && r.val < Tmp0;
}

/**
 * Checks if an operation is a comparison operation.
 * Sets the comparison kind and condition code if it is.
 * 
 * @param op Operation code to check
 * @param pk Pointer to store comparison kind (Kw, Kl, Ks, Kd)
 * @param pc Pointer to store condition code
 * @return 1 if op is a comparison, 0 otherwise
 */
int
iscmp(int op, int *pk, int *pc)
{
	if (Ocmpw <= op && op <= Ocmpw1) {
		*pc = op - Ocmpw;
		*pk = Kw;
	}
	else if (Ocmpl <= op && op <= Ocmpl1) {
		*pc = op - Ocmpl;
		*pk = Kl;
	}
	else if (Ocmps <= op && op <= Ocmps1) {
		*pc = NCmpI + op - Ocmps;
		*pk = Ks;
	}
	else if (Ocmpd <= op && op <= Ocmpd1) {
		*pc = NCmpI + op - Ocmpd;
		*pk = Kd;
	}
	else
		return 0;
	return 1;
}

/**
 * Groups related instructions together.
 * Identifies instruction groups like blit pairs, parameter passing,
 * and function calls, returning the start and end of each group.
 * 
 * @param b Basic block containing the instruction
 * @param i Instruction to group
 * @param i0 Pointer to store start of instruction group
 * @param i1 Pointer to store end of instruction group
 */
void
igroup(Blk *b, Ins *i, Ins **i0, Ins **i1)
{
	Ins *ib, *ie;

	ib = b->ins;
	ie = ib + b->nins;
	switch (i->op) {
	case Oblit0:
		*i0 = i;
		*i1 = i + 2;
		return;
	case Oblit1:
		*i0 = i - 1;
		*i1 = i + 1;
		return;
	case_Opar:
		for (; i>ib && ispar((i-1)->op); i--)
			;
		*i0 = i;
		for (; i<ie && ispar(i->op); i++)
			;
		*i1 = i;
		return;
	case Ocall:
	case_Oarg:
		for (; i>ib && isarg((i-1)->op); i--)
			;
		*i0 = i;
		for (; i<ie && i->op != Ocall; i++)
			;
		assert(i < ie);
		*i1 = i + 1;
		return;
	default:
		if (ispar(i->op))
			goto case_Opar;
		if (isarg(i->op))
			goto case_Oarg;
		*i0 = i;
		*i1 = i + 1;
		return;
	}
}

/**
 * Gets the argument class for an instruction's nth argument.
 * 
 * @param i Instruction to examine
 * @param n Argument index (0 or 1)
 * @return Argument class (Kx, Kw, Kl, etc.)
 */
int
argcls(Ins *i, int n)
{
	return optab[i->op].argcls[n][i->cls];
}

/**
 * Emits an instruction to the current instruction buffer.
 * Instructions are emitted in reverse order (curi decrements).
 * 
 * @param op Operation code
 * @param k Class of the instruction
 * @param to Destination reference
 * @param arg0 First argument
 * @param arg1 Second argument
 */
void
emit(int op, int k, Ref to, Ref arg0, Ref arg1)
{
	if (curi == insb)
		die("emit, too many instructions");
	*--curi = (Ins){
		.op = op, .cls = k,
		.to = to, .arg = {arg0, arg1}
	};
}

/**
 * Emits a complete instruction structure.
 * 
 * @param i Instruction to emit
 */
void
emiti(Ins i)
{
	emit(i.op, i.cls, i.to, i.arg[0], i.arg[1]);
}

/**
 * Duplicates instructions into a basic block.
 * Replaces the block's instructions with the provided ones.
 * 
 * @param b Basic block to update
 * @param s Source instructions
 * @param n Number of instructions to copy
 */
void
idup(Blk *b, Ins *s, ulong n)
{
	vgrow(&b->ins, n);
	icpy(b->ins, s, n);
	b->nins = n;
}

/**
 * Copies instructions from source to destination.
 * 
 * @param d Destination instruction array
 * @param s Source instruction array
 * @param n Number of instructions to copy
 * @return Pointer past the last copied instruction
 */
Ins *
icpy(Ins *d, Ins *s, ulong n)
{
	if (n)
		memmove(d, s, n * sizeof(Ins));
	return d + n;
}

static int cmptab[][2] ={
	             /* negation    swap */
	[Ciule]      = {Ciugt,      Ciuge},
	[Ciult]      = {Ciuge,      Ciugt},
	[Ciugt]      = {Ciule,      Ciult},
	[Ciuge]      = {Ciult,      Ciule},
	[Cisle]      = {Cisgt,      Cisge},
	[Cislt]      = {Cisge,      Cisgt},
	[Cisgt]      = {Cisle,      Cislt},
	[Cisge]      = {Cislt,      Cisle},
	[Cieq]       = {Cine,       Cieq},
	[Cine]       = {Cieq,       Cine},
	[NCmpI+Cfle] = {NCmpI+Cfgt, NCmpI+Cfge},
	[NCmpI+Cflt] = {NCmpI+Cfge, NCmpI+Cfgt},
	[NCmpI+Cfgt] = {NCmpI+Cfle, NCmpI+Cflt},
	[NCmpI+Cfge] = {NCmpI+Cflt, NCmpI+Cfle},
	[NCmpI+Cfeq] = {NCmpI+Cfne, NCmpI+Cfeq},
	[NCmpI+Cfne] = {NCmpI+Cfeq, NCmpI+Cfne},
	[NCmpI+Cfo]  = {NCmpI+Cfuo, NCmpI+Cfo},
	[NCmpI+Cfuo] = {NCmpI+Cfo,  NCmpI+Cfuo},
};

/**
 * Negates a comparison condition.
 * Returns the opposite condition (e.g., < becomes >=).
 * 
 * @param c Comparison condition to negate
 * @return Negated comparison condition
 */
int
cmpneg(int c)
{
	assert(0 <= c && c < NCmp);
	return cmptab[c][0];
}

/**
 * Swaps a comparison condition.
 * Returns the swapped condition (e.g., < becomes >).
 * 
 * @param c Comparison condition to swap
 * @return Swapped comparison condition
 */
int
cmpop(int c)
{
	assert(0 <= c && c < NCmp);
	return cmptab[c][1];
}

/**
 * Negates a word/long comparison operation.
 * Converts the operation code to its negated form.
 * 
 * @param op Comparison operation to negate
 * @return Negated comparison operation
 */
int
cmpwlneg(int op)
{
	if (INRANGE(op, Ocmpw, Ocmpw1))
		return cmpneg(op - Ocmpw) + Ocmpw;
	if (INRANGE(op, Ocmpl, Ocmpl1))
		return cmpneg(op - Ocmpl) + Ocmpl;
	die("not a wl comparison");
}

/**
 * Merges two register classes.
 * Attempts to find a common class that can represent both inputs.
 * Returns 1 if classes are incompatible, 0 if merge succeeds.
 * 
 * @param pk Pointer to first class (will be updated with merged class)
 * @param k Second class to merge
 * @return 1 if classes are incompatible, 0 if merge succeeds
 */
int
clsmerge(short *pk, short k)
{
	short k1;

	k1 = *pk;
	if (k1 == Kx) {
		*pk = k;
		return 0;
	}
	if ((k1 == Kw && k == Kl) || (k1 == Kl && k == Kw)) {
		*pk = Kw;
		return 0;
	}
	return k1 != k;
}

// |t| is the index of the temporary
// |tmp| is the vector of all temporaries
//
// TODO: I think this is following phi instructions back through a chain of
// temporaries and returning the outermost that's still a phi. It also has the
// side-effect of collapsing the ones that it walks through.

/**
 * Follows phi instruction chains to find the root temporary.
 * Collapses phi chains by updating phi pointers during traversal.
 * Used for register allocation to find the ultimate source of a value.
 * 
 * @param t Temporary index to trace
 * @param tmp Array of all temporaries
 * @return Index of the root temporary (no longer a phi)
 */
int phicls(int t, Tmp* tmp) {
  int t1 = tmp[t].phi;
  if (!t1) {
    return t;
  }
  int t2 = phicls(t1, tmp);
  tmp[t].phi = t2;
  return t2;
}

/**
 * Finds the argument index for a phi instruction from a specific block.
 * 
 * @param p Phi instruction to examine
 * @param b Block to find argument for
 * @return Argument index, or -1 if block not found
 */
uint
phiargn(Phi *p, Blk *b)
{
	uint n;

	if (p)
		for (n=0; n<p->narg; n++)
			if (p->blk[n] == b)
				return n;
	return -1;
}

/**
 * Gets the argument value for a phi instruction from a specific block.
 * 
 * @param p Phi instruction to examine
 * @param b Block to get argument for
 * @return Reference to the argument value
 */
Ref
phiarg(Phi *p, Blk *b)
{
	uint n;

	n = phiargn(p, b);
	assert(n != -1u && "block not found");
	return p->arg[n];
}

/**
 * Creates a new temporary variable.
 * Allocates a temporary with the specified class and optional prefix.
 * 
 * @param prfx Optional prefix for temporary name (can be NULL)
 * @param k Register class for the temporary
 * @param fn Function to add temporary to
 * @return Reference to the new temporary
 */
Ref
newtmp(char *prfx, int k,  Fn *fn)
{
	static int n;
	int t;

	t = fn->ntmp++;
	vgrow(&fn->tmp, fn->ntmp);
	memset(&fn->tmp[t], 0, sizeof(Tmp));
	if (prfx)
		strf(fn->tmp[t].name, "%s.%d", prfx, ++n);
	fn->tmp[t].cls = k;
	fn->tmp[t].slot = -1;
	fn->tmp[t].nuse = +1;
	fn->tmp[t].ndef = +1;
	return TMP(t);
}

/**
 * Changes the use count of a reference.
 * Updates the use count of a temporary if the reference is to a temporary.
 * 
 * @param r Reference to update use count for
 * @param du Delta to add to use count
 * @param fn Function containing the temporary
 */
void
chuse(Ref r, int du, Fn *fn)
{
	if (rtype(r) == RTmp)
		fn->tmp[r.val].nuse += du;
}

/**
 * Compares two symbols for equality.
 * 
 * @param s0 First symbol
 * @param s1 Second symbol
 * @return 1 if symbols are equal, 0 otherwise
 */
int
symeq(Sym s0, Sym s1)
{
	return s0.type == s1.type && s0.id == s1.id;
}

/**
 * Creates a new constant or finds an existing identical one.
 * Deduplicates constants to save memory and enable constant folding.
 * 
 * @param c0 Constant to add
 * @param fn Function to add constant to
 * @return Reference to the constant (new or existing)
 */
Ref
newcon(Con *c0, Fn *fn)
{
	Con *c1;
	int i;

	for (i=1; i<fn->ncon; i++) {
		c1 = &fn->con[i];
		if (c0->type == c1->type
		&& symeq(c0->sym, c1->sym)
		&& c0->bits.i == c1->bits.i)
			return CON(i);
	}
	vgrow(&fn->con, ++fn->ncon);
	fn->con[i] = *c0;
	return CON(i);
}

/**
 * Gets or creates a constant with the specified integer value.
 * 
 * @param val Integer value for the constant
 * @param fn Function to add constant to
 * @return Reference to the constant
 */
Ref
getcon(int64_t val, Fn *fn)
{
	int c;

	for (c=1; c<fn->ncon; c++)
		if (fn->con[c].type == CBits
		&& fn->con[c].bits.i == val)
			return CON(c);
	vgrow(&fn->con, ++fn->ncon);
	fn->con[c] = (Con){.type = CBits, .bits.i = val};
	return CON(c);
}

/**
 * Adds two constants together.
 * Performs constant folding for address arithmetic and integer addition.
 * 
 * @param c0 First constant (will be updated with result)
 * @param c1 Second constant to add
 * @param m Multiplier for second constant
 * @return 1 if addition succeeded, 0 if it failed
 */
int
addcon(Con *c0, Con *c1, int m)
{
	if (m != 1 && c1->type == CAddr)
		return 0;
	if (c0->type == CUndef) {
		*c0 = *c1;
		c0->bits.i *= m;
	} else {
		if (c1->type == CAddr) {
			if (c0->type == CAddr)
				return 0;
			c0->type = CAddr;
			c0->sym = c1->sym;
		}
		c0->bits.i += c1->bits.i * m;
	}
	return 1;
}

/**
 * Checks if a reference is a constant with an integer value.
 * Extracts the value if it is.
 * 
 * @param fn Function containing the reference
 * @param r Reference to check
 * @param v Pointer to store the integer value
 * @return 1 if reference is a constant integer, 0 otherwise
 */
int
isconbits(Fn *fn, Ref r, int64_t *v)
{
	Con *c;

	if (rtype(r) == RCon) {
		c = &fn->con[r.val];
		if (c->type == CBits) {
			*v = c->bits.i;
			return 1;
		}
	}
	return 0;
}

/**
 * Generates stack allocation instructions.
 * Ensures stack alignment and handles both constant and variable sizes.
 * 
 * @param rt Temporary to store allocated address
 * @param rs Reference to allocation size
 * @param fn Function to add instructions to
 */
void
salloc(Ref rt, Ref rs, Fn *fn)
{
	Ref r0, r1;
	int64_t sz;

	/* we need to make sure
	 * the stack remains aligned
	 * (rsp = 0) mod 16
	 */
	fn->dynalloc = 1;
	if (rtype(rs) == RCon) {
		sz = fn->con[rs.val].bits.i;
		if (sz < 0 || sz >= INT_MAX-15)
			err("invalid alloc size %"PRId64, sz);
		sz = (sz + 15)  & -16;
		emit(Osalloc, Kl, rt, getcon(sz, fn), R);
	} else {
		/* r0 = (r + 15) & -16 */
		r0 = newtmp("isel", Kl, fn);
		r1 = newtmp("isel", Kl, fn);
		emit(Osalloc, Kl, rt, r0, R);
		emit(Oand, Kl, r0, r1, getcon(-16, fn));
		emit(Oadd, Kl, r1, rs, getcon(15, fn));
		if (fn->tmp[rs.val].slot != -1)
			err("unlikely alloc argument %%%s for %%%s",
				fn->tmp[rs.val].name, fn->tmp[rt.val].name);
	}
}

/**
 * Initializes a bitset for use.
 * Allocates storage for the specified number of elements.
 * 
 * @param bs Bitset to initialize
 * @param n Number of elements the bitset should support
 */
void
bsinit(BSet *bs, uint n)
{
	n = (n + NBit-1) / NBit;
	bs->nt = n;
	bs->t = alloc(n * sizeof bs->t[0]);
}

MAKESURE(NBit_is_64, NBit == 64);

/**
 * Counts the number of set bits in a 64-bit word.
 * Uses a parallel bit counting algorithm.
 * 
 * @param b 64-bit word to count bits in
 * @return Number of set bits
 */
inline static uint
popcnt(bits b)
{
	b = (b & 0x5555555555555555) + ((b>>1) & 0x5555555555555555);
	b = (b & 0x3333333333333333) + ((b>>2) & 0x3333333333333333);
	b = (b & 0x0f0f0f0f0f0f0f0f) + ((b>>4) & 0x0f0f0f0f0f0f0f0f);
	b += (b>>8);
	b += (b>>16);
	b += (b>>32);
	return b & 0xff;
}

/**
 * Finds the position of the first set bit in a 64-bit word.
 * Returns the least significant bit position (0-63).
 * 
 * @param b 64-bit word to find first bit in
 * @return Position of first set bit (0-63)
 */
inline static int
firstbit(bits b)
{
	int n;

	n = 0;
	if (!(b & 0xffffffff)) {
		n += 32;
		b >>= 32;
	}
	if (!(b & 0xffff)) {
		n += 16;
		b >>= 16;
	}
	if (!(b & 0xff)) {
		n += 8;
		b >>= 8;
	}
	if (!(b & 0xf)) {
		n += 4;
		b >>= 4;
	}
	n += (char[16]){4,0,1,0,2,0,1,0,3,0,1,0,2,0,1,0}[b & 0xf];
	return n;
}

/**
 * Counts the number of set elements in a bitset.
 * 
 * @param bs Bitset to count
 * @return Number of set elements
 */
uint
bscount(BSet *bs)
{
	uint i, n;

	n = 0;
	for (i=0; i<bs->nt; i++)
		n += popcnt(bs->t[i]);
	return n;
}

/**
 * Gets the maximum element number a bitset can represent.
 * 
 * @param bs Bitset to check
 * @return Maximum element number
 */
static inline uint
bsmax(BSet *bs)
{
	return bs->nt * NBit;
}

/**
 * Sets a bit in a bitset.
 * 
 * @param bs Bitset to modify
 * @param elt Element number to set
 */
void
bsset(BSet *bs, uint elt)
{
	assert(elt < bsmax(bs));
	bs->t[elt/NBit] |= BIT(elt%NBit);
}

/**
 * Clears a bit in a bitset.
 * 
 * @param bs Bitset to modify
 * @param elt Element number to clear
 */
void
bsclr(BSet *bs, uint elt)
{
	assert(elt < bsmax(bs));
	bs->t[elt/NBit] &= ~BIT(elt%NBit);
}

#define BSOP(f, op)                           \
	void                                  \
	f(BSet *a, BSet *b)                   \
	{                                     \
		uint i;                       \
		                              \
		assert(a->nt == b->nt);       \
		for (i=0; i<a->nt; i++)       \
			a->t[i] op b->t[i];   \
	}

BSOP(bscopy, =)
BSOP(bsunion, |=)
BSOP(bsinter, &=)
BSOP(bsdiff, &= ~)

/**
 * Compares two bitsets for equality.
 * 
 * @param a First bitset
 * @param b Second bitset
 * @return 1 if bitsets are equal, 0 otherwise
 */
int
bsequal(BSet *a, BSet *b)
{
	uint i;

	assert(a->nt == b->nt);
	for (i=0; i<a->nt; i++)
		if (a->t[i] != b->t[i])
			return 0;
	return 1;
}

/**
 * Clears all bits in a bitset.
 * 
 * @param bs Bitset to clear
 */
void
bszero(BSet *bs)
{
	memset(bs->t, 0, bs->nt * sizeof bs->t[0]);
}

/* iterates on a bitset, use as follows
 *
 * 	for (i=0; bsiter(set, &i); i++)
 * 		use(i);
 *
 */

/**
 * Iterates over set elements in a bitset.
 * Updates the element pointer to the next set element.
 * 
 * @param bs Bitset to iterate over
 * @param elt Pointer to current element (will be updated)
 * @return 1 if more elements exist, 0 if iteration is complete
 */
int
bsiter(BSet *bs, int *elt)
{
	bits b;
	uint t, i;

	i = *elt;
	t = i/NBit;
	if (t >= bs->nt)
		return 0;
	b = bs->t[t];
	b &= ~(BIT(i%NBit) - 1);
	while (!b) {
		++t;
		if (t >= bs->nt)
			return 0;
		b = bs->t[t];
	}
	*elt = NBit*t + firstbit(b);
	return 1;
}

/**
 * Prints a bitset of temporaries for debugging.
 * Shows the names of temporaries in the set.
 * 
 * @param bs Bitset to print
 * @param tmp Array of temporaries
 * @param f Output file
 */
void
dumpts(BSet *bs, Tmp *tmp, FILE *f)
{
	int t;

	fprintf(f, "[");
	for (t=Tmp0; bsiter(bs, &t); t++)
		fprintf(f, " %s", tmp[t].name);
	fprintf(f, " ]\n");
}

/**
 * Executes a pattern matching bytecode against a reference.
 * Used for instruction pattern matching and transformation.
 * The bytecode implements a simple stack-based virtual machine.
 * 
 * @param code Bytecode to execute
 * @param tn Array of temporary numbers for pattern matching
 * @param ref Reference to match against
 * @param var Array to store matched variables
 */
void
runmatch(uchar *code, Num *tn, Ref ref, Ref *var)
{
	Ref stkbuf[20], *stk;
	uchar *s, *pc;
	int bc, i;
	int n, nl, nr;

	assert(rtype(ref) == RTmp);
	stk = stkbuf;
	pc = code;
	while ((bc = *pc))
		switch (bc) {
		case 1: /* pushsym */
		case 2: /* push */
			assert(stk < &stkbuf[20]);
			assert(rtype(ref) == RTmp);
			nl = tn[ref.val].nl;
			nr = tn[ref.val].nr;
			if (bc == 1 && nl > nr) {
				*stk++ = tn[ref.val].l;
				ref = tn[ref.val].r;
			} else {
				*stk++ = tn[ref.val].r;
				ref = tn[ref.val].l;
			}
			pc++;
			break;
		case 3: /* set */
			var[*++pc] = ref;
			if (*(pc + 1) == 0)
				return;
			/* fall through */
		case 4: /* pop */
			assert(stk > &stkbuf[0]);
			ref = *--stk;
			pc++;
			break;
		case 5: /* switch */
			assert(rtype(ref) == RTmp);
			n = tn[ref.val].n;
			s = pc + 1;
			for (i=*s++; i>0; i--, s++)
				if (n == *s++)
					break;
			pc += *s;
			break;
		default: /* jump */
			assert(bc >= 10);
			pc = code + (bc - 10);
			break;
		}
}
