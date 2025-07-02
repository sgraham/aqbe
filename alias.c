#include "all.h"

/**
 * Retrieves alias information for a given reference.
 * 
 * This function analyzes a reference (temporary or constant) and fills in
 * the alias structure with information about what memory location it refers to.
 * For temporaries, it looks up the alias information stored in the function's
 * temporary table. For constants, it determines if they represent addresses
 * (symbols) or immediate values.
 * 
 * The function handles different alias types:
 * - Stack-based aliases (ALoc, AEsc) with slot information
 * - Symbol-based aliases (ASym) for global variables
 * - Constant-based aliases (ACon) for immediate values
 * - Unknown aliases (AUnk) for complex expressions
 * 
 * @param a Pointer to the alias structure to be filled
 * @param r The reference to analyze (temporary or constant)
 * @param fn The function containing the reference
 */
void
getalias(Alias *a, Ref r, Fn *fn)
{
	Con *c;

	switch (rtype(r)) {
	default:
		die("unreachable");
	case RTmp:
		*a = fn->tmp[r.val].alias;
		if (astack(a->type))
			a->type = a->slot->type;
		assert(a->type != ABot);
		break;
	case RCon:
		c = &fn->con[r.val];
		if (c->type == CAddr) {
			a->type = ASym;
			a->u.sym = c->sym;
		} else
			a->type = ACon;
		a->offset = c->bits.i;
		a->slot = 0;
		break;
	}
}

/**
 * Determines if two memory references alias each other.
 * 
 * This function performs alias analysis between two memory references,
 * considering their base addresses, offsets, and sizes. It returns one of
 * three possible results:
 * - NoAlias: The references definitely do not overlap
 * - MayAlias: The references might overlap (conservative analysis)
 * - MustAlias: The references definitely overlap
 * 
 * The analysis handles various cases:
 * - Stack-based references (same or different slots)
 * - Symbol-based references (global variables)
 * - Constant-based references (immediate addresses)
 * - Unknown references (complex expressions)
 * 
 * The function computes the offset difference and overlap detection
 * to make precise alias decisions when possible.
 * 
 * @param p First memory reference
 * @param op Offset for the first reference
 * @param sp Size of the first reference
 * @param q Second memory reference
 * @param sq Size of the second reference
 * @param delta Pointer to store the offset difference
 * @param fn The function containing the references
 * @return Alias relationship (NoAlias, MayAlias, or MustAlias)
 */
int
alias(Ref p, int op, int sp, Ref q, int sq, int *delta, Fn *fn)
{
	Alias ap, aq;
	int ovlap;

	getalias(&ap, p, fn);
	getalias(&aq, q, fn);
	ap.offset += op;
	/* when delta is meaningful (ovlap == 1),
	 * we do not overflow int because sp and
	 * sq are bounded by 2^28 */
	*delta = ap.offset - aq.offset;
	ovlap = ap.offset < aq.offset + sq && aq.offset < ap.offset + sp;

	if (astack(ap.type) && astack(aq.type)) {
		/* if both are offsets of the same
		 * stack slot, they alias iif they
		 * overlap */
		if (ap.base == aq.base && ovlap)
			return MustAlias;
		return NoAlias;
	}

	if (ap.type == ASym && aq.type == ASym) {
		/* they conservatively alias if the
		 * symbols are different, or they
		 * alias for sure if they overlap */
		if (!symeq(ap.u.sym, aq.u.sym))
			return MayAlias;
		if (ovlap)
			return MustAlias;
		return NoAlias;
	}

	if ((ap.type == ACon && aq.type == ACon)
	|| (ap.type == aq.type && ap.base == aq.base)) {
		assert(ap.type == ACon || ap.type == AUnk);
		/* if they have the same base, we
		 * can rely on the offsets only */
		if (ovlap)
			return MustAlias;
		return NoAlias;
	}

	/* if one of the two is unknown
	 * there may be aliasing unless
	 * the other is provably local */
	if (ap.type == AUnk && aq.type != ALoc)
		return MayAlias;
	if (aq.type == AUnk && ap.type != ALoc)
		return MayAlias;

	return NoAlias;
}

/**
 * Checks if a reference escapes the current function scope.
 * 
 * This function determines whether a reference (typically a temporary)
 * can be accessed outside the current function. A reference escapes if:
 * - It's not a temporary (e.g., constants always escape)
 * - It's a stack-based reference that has been marked as escaped
 * 
 * This information is crucial for optimization decisions, as escaped
 * references cannot be safely optimized or eliminated.
 * 
 * @param r The reference to check for escaping
 * @param fn The function containing the reference
 * @return 1 if the reference escapes, 0 otherwise
 */
int
escapes(Ref r, Fn *fn)
{
	Alias *a;

	if (rtype(r) != RTmp)
		return 1;
	a = &fn->tmp[r.val].alias;
	return !astack(a->type) || a->slot->type == AEsc;
}

/**
 * Marks a reference as escaped.
 * 
 * This function marks a reference as having escaped the function scope,
 * which prevents certain optimizations from being applied to it.
 * For temporaries, it updates the slot type to AEsc if the reference
 * is stack-based.
 * 
 * @param r The reference to mark as escaped
 * @param fn The function containing the reference
 */
static void
esc(Ref r, Fn *fn)
{
	Alias *a;

	assert(rtype(r) <= RType);
	if (rtype(r) == RTmp) {
		a = &fn->tmp[r.val].alias;
		if (astack(a->type))
			a->slot->type = AEsc;
	}
}

/**
 * Updates the liveness mask for a stack slot based on a store operation.
 * 
 * This function tracks which bits of a stack slot are modified by a store
 * operation. It updates the liveness mask to reflect which bits are
 * definitely written, which helps with dead code elimination and
 * optimization of stack operations.
 * 
 * The function handles cases where the store size and offset might
 * exceed the bit tracking limits, in which case it marks all bits
 * as potentially modified.
 * 
 * @param r The reference being stored to
 * @param sz The size of the store operation in bytes
 * @param fn The function containing the store
 */
static void
store(Ref r, int sz, Fn *fn)
{
	Alias *a;
	int64_t off;
	bits m;

	if (rtype(r) == RTmp) {
		a = &fn->tmp[r.val].alias;
		if (a->slot) {
			assert(astack(a->type));
			off = a->offset;
			if (sz >= NBit
			|| (off < 0 || off >= NBit))
				m = -1;
			else
				m = (BIT(sz) - 1) << off;
			a->slot->u.loc.m |= m;
		}
	}
}

/**
 * Performs comprehensive alias analysis for an entire function.
 * 
 * This function analyzes all memory references in a function to determine
 * their alias relationships and escape properties. It processes:
 * - All temporaries, initializing their alias information
 * - Phi nodes, marking their results as unknown aliases
 * - All instructions, tracking memory operations and their effects
 * - Function parameters and return values for escape analysis
 * 
 * The analysis builds a complete picture of memory usage patterns,
 * which enables various optimizations including:
 * - Dead code elimination
 * - Load/store optimization
 * - Register allocation decisions
 * - Stack slot optimization
 * 
 * The function handles special cases like:
 * - Allocation instructions (Oalloc)
 * - Copy instructions that propagate alias information
 * - Address arithmetic (Oadd)
 * - Memory operations (loads/stores)
 * - Block copy operations (Oblit0/Oblit1)
 * 
 * @param fn The function to analyze
 */
void
fillalias(Fn *fn)
{
	uint n;
	int t, sz;
	int64_t x;
	Blk *b;
	Phi *p;
	Ins *i;
	Con *c;
	Alias *a, a0, a1;

	for (t=0; t<fn->ntmp; t++)
		fn->tmp[t].alias.type = ABot;
	for (n=0; n<fn->nblk; ++n) {
		b = fn->rpo[n];
		for (p=b->phi; p; p=p->link) {
			assert(rtype(p->to) == RTmp);
			a = &fn->tmp[p->to.val].alias;
			assert(a->type == ABot);
			a->type = AUnk;
			a->base = p->to.val;
			a->offset = 0;
			a->slot = 0;
		}
		for (i=b->ins; i<&b->ins[b->nins]; ++i) {
			a = 0;
			if (!req(i->to, R)) {
				assert(rtype(i->to) == RTmp);
				a = &fn->tmp[i->to.val].alias;
				assert(a->type == ABot);
				if (Oalloc <= i->op && i->op <= Oalloc1) {
					a->type = ALoc;
					a->slot = a;
					a->u.loc.sz = -1;
					if (rtype(i->arg[0]) == RCon) {
						c = &fn->con[i->arg[0].val];
						x = c->bits.i;
						if (c->type == CBits)
						if (0 <= x && x <= NBit)
							a->u.loc.sz = x;
					}
				} else {
					a->type = AUnk;
					a->slot = 0;
				}
				a->base = i->to.val;
				a->offset = 0;
			}
			if (i->op == Ocopy) {
				assert(a);
				getalias(a, i->arg[0], fn);
			}
			if (i->op == Oadd) {
				getalias(&a0, i->arg[0], fn);
				getalias(&a1, i->arg[1], fn);
				if (a0.type == ACon) {
					*a = a1;
					a->offset += a0.offset;
				}
				else if (a1.type == ACon) {
					*a = a0;
					a->offset += a1.offset;
				}
			}
			if (req(i->to, R) || a->type == AUnk)
			if (i->op != Oblit0) {
				if (!isload(i->op))
					esc(i->arg[0], fn);
				if (!isstore(i->op))
				if (i->op != Oargc)
					esc(i->arg[1], fn);
			}
			if (i->op == Oblit0) {
				++i;
				assert(i->op == Oblit1);
				assert(rtype(i->arg[0]) == RInt);
				sz = abs(rsval(i->arg[0]));
				store((i-1)->arg[1], sz, fn);
			}
			if (isstore(i->op))
				store(i->arg[1], storesz(i), fn);
		}
		if (b->jmp.type != Jretc)
			esc(b->jmp.arg, fn);
	}
	for (b=fn->start; b; b=b->link)
		for (p=b->phi; p; p=p->link)
			for (n=0; n<p->narg; n++)
				esc(p->arg[n], fn);
}
