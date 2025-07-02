#include "all.h"

/**
 * Generates block copy instructions for memory-to-memory operations.
 * 
 * This function breaks down a block copy operation into a sequence of
 * smaller load/store operations. It handles different data sizes (1, 2, 4, 8 bytes)
 * and supports both forward and backward copying.
 * 
 * The function generates a series of instructions that:
 * 1. Load data from the source address
 * 2. Store data to the destination address
 * 3. Update both addresses for the next iteration
 * 
 * It uses a table-driven approach to select the appropriate load/store
 * instruction pairs based on the data size.
 * 
 * @param sd Array containing source and destination references
 * @param sz Size of the block copy (negative for backward copy)
 * @param fn The function containing the block copy
 */
static void
blit(Ref sd[2], int sz, Fn *fn)
{
	struct { int st, ld, cls, size; } *p, tbl[] = {
		{ Ostorel, Oload,   Kl, 8 },
		{ Ostorew, Oload,   Kw, 4 },
		{ Ostoreh, Oloaduh, Kw, 2 },
		{ Ostoreb, Oloadub, Kw, 1 }
	};
	Ref r, r1, ro;
	int off, fwd, n;

	fwd = sz >= 0;
	sz = abs(sz);
	off = fwd ? sz : 0;
	for (p=tbl; sz; p++)
		for (n=p->size; sz>=n; sz-=n) {
			off -= fwd ? n : 0;
			r = newtmp("blt", Kl, fn);
			r1 = newtmp("blt", Kl, fn);
			ro = getcon(off, fn);
			emit(p->st, 0, R, r, r1);
			emit(Oadd, Kl, r1, sd[1], ro);
			r1 = newtmp("blt", Kl, fn);
			emit(p->ld, p->cls, r, r1, R);
			emit(Oadd, Kl, r1, sd[0], ro);
			off += fwd ? 0 : n;
		}
}

/**
 * Lookup table for computing the base-2 logarithm of powers of 2.
 * 
 * This table maps 64-bit values that are powers of 2 to their logarithm.
 * It uses a perfect hash function to index into the table efficiently.
 * The table is used by ulog2() to quickly compute logarithms.
 */
static int
ulog2_tab64[64] = {
	63,  0,  1, 41, 37,  2, 16, 42,
	38, 29, 32,  3, 12, 17, 43, 55,
	39, 35, 30, 53, 33, 21,  4, 23,
	13,  9, 18,  6, 25, 44, 48, 56,
	62, 40, 36, 15, 28, 31, 11, 54,
	34, 52, 20, 22,  8,  5, 24, 47,
	61, 14, 27, 10, 51, 19,  7, 46,
	60, 26, 50, 45, 59, 49, 58, 57,
};

/**
 * Computes the base-2 logarithm of a power of 2.
 * 
 * This function uses a perfect hash function and lookup table to quickly
 * compute the logarithm of values that are known to be powers of 2.
 * The hash function (multiplying by a magic constant and shifting) maps
 * each power of 2 to a unique index in the lookup table.
 * 
 * @param pow2 A value that must be a power of 2
 * @return The base-2 logarithm of the input value
 */
static int
ulog2(uint64_t pow2)
{
	return ulog2_tab64[(pow2 * 0x5b31ab928877a7e) >> 58];
}

/**
 * Checks if a value is a power of 2.
 * 
 * This function uses a bit manipulation trick to determine if a value
 * is a power of 2. A number is a power of 2 if and only if it has
 * exactly one bit set, which means (v & (v - 1)) == 0 for non-zero v.
 * 
 * @param v The value to check
 * @return 1 if the value is a power of 2, 0 otherwise
 */
static int
ispow2(uint64_t v)
{
	return v && (v & (v - 1)) == 0;
}

/**
 * Simplifies individual instructions during the simplification pass.
 * 
 * This function applies various peephole optimizations to instructions,
 * including:
 * - Converting block copy operations (Oblit0/Oblit1) into explicit load/store sequences
 * - Optimizing unsigned division and remainder by powers of 2 into shifts and masks
 * 
 * The function modifies instructions in place and may generate additional
 * instructions when simplifying complex operations like block copies.
 * 
 * @param pi Pointer to the instruction pointer (may be modified)
 * @param new Pointer to flag indicating if new instructions were generated
 * @param b The block containing the instruction
 * @param fn The function containing the instruction
 */
static void
ins(Ins **pi, int *new, Blk *b, Fn *fn)
{
	ulong ni;
	Con *c;
	Ins *i;
	Ref r;
	int n;

	i = *pi;
	/* simplify more instructions here;
	 * copy 0 into xor, bit rotations,
	 * etc. */
	switch (i->op) {
	case Oblit1:
		assert(i > b->ins);
		assert((i-1)->op == Oblit0);
		if (!*new) {
			curi = &insb[NIns];
			ni = &b->ins[b->nins] - (i+1);
			curi -= ni;
			icpy(curi, i+1, ni);
			*new = 1;
		}
		blit((i-1)->arg, rsval(i->arg[0]), fn);
		*pi = i-1;
		return;
	case Oudiv:
	case Ourem:
		r = i->arg[1];
		if (KBASE(i->cls) == 0)
		if (rtype(r) == RCon) {
			c = &fn->con[r.val];
			if (c->type == CBits)
			if (ispow2(c->bits.i)) {
				n = ulog2(c->bits.i);
				if (i->op == Ourem) {
					i->op = Oand;
					i->arg[1] = getcon((1ull<<n) - 1, fn);
				} else {
					i->op = Oshr;
					i->arg[1] = getcon(n, fn);
				}
			}
		}
		break;
	}
	if (*new)
		emiti(*i);
}

/**
 * Performs instruction simplification for an entire function.
 * 
 * This function applies peephole optimizations to all instructions in
 * a function, working backwards through each block. It handles:
 * - Block copy operations that need to be expanded into explicit loads/stores
 * - Arithmetic optimizations like division/remainder by powers of 2
 * - Other instruction-level simplifications
 * 
 * The function processes instructions in reverse order within each block
 * to ensure that optimizations don't interfere with each other. When
 * new instructions are generated, they are inserted into the block.
 * 
 * @param fn The function to simplify
 */
void
simpl(Fn *fn)
{
	Blk *b;
	Ins *i;
	int new;

	for (b=fn->start; b; b=b->link) {
		new = 0;
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			--i;
			ins(&i, &new, b, fn);
		}
		if (new)
			idup(b, curi, &insb[NIns]-curi);
	}
}
