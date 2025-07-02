#include "all.h"

typedef struct Ext Ext;

struct Ext {
	char zext;
	char nopw; /* is a no-op if arg width is <= nopw */
	char usew; /* uses only the low usew bits of arg */
};

/**
 * Extracts extension instruction properties from an instruction.
 * 
 * This function analyzes extension instructions (extsb, extub, extsh, etc.)
 * and fills in the Ext structure with information about the extension:
 * - zext: Whether it's a zero extension (1) or sign extension (0)
 * - nopw: Maximum argument width for which this extension is a no-op
 * - usew: Number of bits from the argument that are actually used
 * 
 * The function uses a static table to map extension opcodes to their
 * properties, enabling efficient analysis of extension operations.
 * 
 * @param i The instruction to analyze
 * @param e Pointer to the Ext structure to fill
 * @return 1 if the instruction is an extension, 0 otherwise
 */
static int
ext(Ins *i, Ext *e)
{
	static Ext tbl[] = {
		/*extsb*/ {0,  7,  8},
		/*extub*/ {1,  8,  8},
		/*extsh*/ {0, 15, 16},
		/*extuh*/ {1, 16, 16},
		/*extsw*/ {0, 31, 32},
		/*extuw*/ {1, 32, 32},
	};

	if (!isext(i->op))
		return 0;
	*e = tbl[i->op - Oextsb];
	return 1;
}

/**
 * Calculates the minimum number of bits needed to represent a value.
 * 
 * This function determines the bit width required to represent an unsigned
 * 64-bit value. It uses a binary search approach to efficiently find the
 * highest set bit, which represents the minimum width needed.
 * 
 * For example, a value of 5 (binary 101) requires 3 bits, while a value
 * of 255 (binary 11111111) requires 8 bits.
 * 
 * @param v The 64-bit unsigned value to analyze
 * @return The minimum number of bits needed to represent the value
 */
static int
bitwidth(uint64_t v)
{
	int n;

	n = 0;
	if (v >> 32) { n += 32; v >>= 32; }
	if (v >> 16) { n += 16; v >>= 16; }
	if (v >>  8) { n +=  8; v >>=  8; }
	if (v >>  4) { n +=  4; v >>=  4; }
	if (v >>  2) { n +=  2; v >>=  2; }
	if (v >>  1) { n +=  1; v >>=  1; }
	return n+v;
}

/* no more than w bits are used */
/**
 * Checks if a reference is used with a width no greater than the specified limit.
 * 
 * This function analyzes all uses of a temporary to determine if it's only
 * used in contexts where no more than 'w' bits are needed. It handles:
 * - Phi node uses (recursively checking the phi result)
 * - Copy instruction uses (propagating the width constraint)
 * - Extension instruction uses (checking if the extension is redundant)
 * - Bitwise AND operations (checking if the mask constrains the width)
 * 
 * This analysis is crucial for determining when extensions can be eliminated
 * or when narrower types can be used instead of wider ones.
 * 
 * @param fn The function containing the reference
 * @param r The reference to analyze (must be a temporary)
 * @param w The maximum width in bits that should be used
 * @return 1 if the reference is only used with width <= w, 0 otherwise
 */
static int
usewidthle(Fn *fn, Ref r, int w)
{
	Ext e;
	Tmp *t;
	Use *u;
	Phi *p;
	Ins *i;
	Ref rc;
	int64_t v;
	int b;

	assert(rtype(r) == RTmp);
	t = &fn->tmp[r.val];
	for (u=t->use; u<&t->use[t->nuse]; u++) {
		switch (u->type) {
		case UPhi:
			p = u->u.phi;
			/* during gvn, phi nodes may be
			 * replaced by other temps; in
			 * this case, the replaced phi
			 * uses are added to the
			 * replacement temp uses and
			 * Phi.to is set to R */
			if (p->visit || req(p->to, R))
				continue;
			p->visit = 1;
			b = usewidthle(fn, p->to, w);
			p->visit = 0;
			if (b)
				continue;
			break;
		case UIns:
			i = u->u.ins;
			assert(i != 0);
			if (i->op == Ocopy)
				if (usewidthle(fn, i->to, w))
					continue;
			if (ext(i, &e)) {
				if (e.usew <= w)
					continue;
				if (usewidthle(fn, i->to, w))
					continue;
			}
			if (i->op == Oand) {
				if (req(r, i->arg[0]))
					rc = i->arg[1];
				else {
					assert(req(r, i->arg[1]));
					rc = i->arg[0];
				}
				if (isconbits(fn, rc, &v)
				&& bitwidth(v) <= w)
					continue;
				break;
			}
			break;
		default:
			break;
		}
		return 0;
	}
	return 1;
}

/**
 * Returns the minimum of two integer values.
 * 
 * A simple utility function to find the smaller of two integers.
 * Used throughout the copy elimination analysis for width calculations.
 * 
 * @param v1 First integer value
 * @param v2 Second integer value
 * @return The smaller of the two values
 */
static int
min_(int v1, int v2)
{
	return v1 < v2 ? v1 : v2;
}

/* is the ref narrower than w bits */
/**
 * Checks if a reference is defined with a width no greater than the specified limit.
 * 
 * This function analyzes how a temporary is defined to determine if it
 * can be represented with no more than 'w' bits. It handles various
 * definition patterns:
 * - Constants (checking their bit width)
 * - Copy instructions (recursively checking the source)
 * - Shift operations (adjusting width based on shift amount)
 * - Comparison operations (always 1 bit result)
 * - Bitwise operations (AND, OR, XOR with width analysis)
 * - Extension operations (checking if they're redundant)
 * 
 * This analysis works together with usewidthle() to determine when
 * extensions can be eliminated or when narrower types can be used.
 * 
 * @param fn The function containing the reference
 * @param r The reference to analyze
 * @param w The maximum width in bits that should be sufficient
 * @return 1 if the reference can be defined with width <= w, 0 otherwise
 */
static int
defwidthle(Fn *fn, Ref r, int w)
{
	Ext e;
	Tmp *t;
	Phi *p;
	Ins *i;
	uint n;
	int64_t v;
	int x;

	if (isconbits(fn, r, &v)
	&& bitwidth(v) <= w)
		return 1;
	if (rtype(r) != RTmp)
		return 0;
	t = &fn->tmp[r.val];
	if (t->cls != Kw)
		return 0;

	if (!t->def) {
		/* phi def */
		for (p=fn->rpo[t->bid]->phi; p; p=p->link)
			if (req(p->to, r))
				break;
		assert(p);
		if (p->visit)
			return 1;
		p->visit = 1;
		for (n=0; n<p->narg; n++)
			if (!defwidthle(fn, p->arg[n], w)) {
				p->visit = 0;
				return 0;
			}
		p->visit = 0;
		return 1;
	}

	i = t->def;
	if (i->op == Ocopy)
                return defwidthle(fn, i->arg[0], w);
	if (i->op == Oshr || i->op == Osar) {
		if (isconbits(fn, i->arg[1], &v))
		if (0 < v && v <= 32) {
			if (i->op == Oshr && w+v >= 32)
				return 1;
			if (w < 32) {
				if (i->op == Osar)
					w = min_(31, w+v);
				else
					w = min_(32, w+v);
			}
		}
		return defwidthle(fn, i->arg[0], w);
	}
	if (iscmp(i->op, &x, &x))
		return w >= 1;
	if (i->op == Oand) {
		if (defwidthle(fn, i->arg[0], w)
		|| defwidthle(fn, i->arg[1], w))
			return 1;
		return 0;
	}
	if (i->op == Oor || i->op == Oxor) {
		if (defwidthle(fn, i->arg[0], w)
		&& defwidthle(fn, i->arg[1], w))
			return 1;
		return 0;
	}
	if (ext(i, &e)) {
		if (e.zext && e.usew <= w)
			return 1;
		w = min_(w, e.nopw);
		return defwidthle(fn, i->arg[0], w);
	}

	return 0;
}

/**
 * Checks if a reference is defined as a single bit value.
 * 
 * This is a convenience function that checks if a reference can be
 * defined with a width of 1 bit, which is useful for boolean
 * operations and conditional expressions.
 * 
 * @param fn The function containing the reference
 * @param r The reference to check
 * @return 1 if the reference is defined as a single bit, 0 otherwise
 */
static int
isw1(Fn *fn, Ref r)
{
	return defwidthle(fn, r, 1);
}

/* insert early extub/extuh instructions
 * for pars used only narrowly; this
 * helps factoring extensions out of
 * loops
 *
 * needs use; breaks use */
/**
 * Inserts early extension instructions for parameters used only narrowly.
 * 
 * This optimization inserts zero-extension instructions (extub, extuh)
 * early in the function for parameters that are only used with narrow
 * widths. This helps factor extensions out of loops, improving
 * performance by moving expensive operations to the function entry.
 * 
 * The function only applies this optimization to functions containing
 * loops, as the benefit comes from avoiding repeated extensions
 * within loop bodies. It analyzes parameter uses to determine the
 * minimum width needed and inserts appropriate extensions.
 * 
 * This optimization requires use analysis and may break existing
 * use information, requiring it to be recomputed.
 * 
 * @param fn The function to optimize
 */
void
narrowpars(Fn *fn)
{
	Blk *b;
	int loop;
	Ins ext, *i, *ins;
	uint npar, nins;
	Ref r;

	/* only useful for functions with loops */
	loop = 0;
	for (b=fn->start; b; b=b->link)
		if (b->loop > 1) {
			loop = 1;
			break;
		}
	if (!loop)
		return;

	b = fn->start;

	npar = 0;
	for (i=b->ins; i<&b->ins[b->nins]; i++) {
		if (!ispar(i->op))
			break;
		npar++;
	}
	if (npar == 0)
		return;

	nins = b->nins + npar;
	ins = vnew(nins, sizeof ins[0], PFn);
	icpy(ins, b->ins, npar);
	icpy(ins + 2*npar, b->ins+npar, b->nins-npar);
	b->ins = ins;
	b->nins = nins;

	for (i=b->ins; i<&b->ins[b->nins]; i++) {
		if (!ispar(i->op))
			break;
		ext = (Ins){.op = Onop};
		if (i->cls == Kw)
		if (usewidthle(fn, i->to, 16)) {
			ext.op = Oextuh;
			if (usewidthle(fn, i->to, 8))
				ext.op = Oextub;
			r = newtmp("vw", i->cls, fn);
			ext.cls = i->cls;
			ext.to = i->to;
			ext.arg[0] = r;
			i->to = r;
		}
		*(i+npar) = ext;
	}
}

/**
 * Attempts to find a copy-equivalent reference for an instruction.
 * 
 * This function analyzes an instruction to determine if it can be
 * replaced by a simpler reference. It handles various cases:
 * - Direct copy instructions
 * - Identity operations (e.g., x + 0, x * 1)
 * - Idempotent operations with identical arguments
 * - Comparison operations with identical arguments
 * - Zero/non-zero comparisons with constant inference
 * - Redundant bitwise AND operations with power-of-2 masks
 * - Redundant extension operations
 * 
 * The function uses width analysis to ensure that type safety is
 * maintained when eliminating extensions or other operations.
 * 
 * @param fn The function containing the instruction
 * @param b The block containing the instruction
 * @param i The instruction to analyze
 * @return A reference that can replace the instruction, or R if no replacement is possible
 */
Ref
copyref(Fn *fn, Blk *b, Ins *i)
{
	/* which extensions are copies for a given
	 * argument width */
	static bits extcpy[] = {
		[WFull] = 0,
		[Wsb] = BIT(Wsb) | BIT(Wsh) | BIT(Wsw),
		[Wub] = BIT(Wub) | BIT(Wuh) | BIT(Wuw),
		[Wsh] = BIT(Wsh) | BIT(Wsw),
		[Wuh] = BIT(Wuh) | BIT(Wuw),
		[Wsw] = BIT(Wsw),
		[Wuw] = BIT(Wuw),
	};
	Ext e;
	Tmp *t;
	int64_t v;
	int w, z;

	if (i->op == Ocopy)
		return i->arg[0];

	/* op identity value */
	if (optab[i->op].hasid
	&& KBASE(i->cls) == 0 /* integer only - fp NaN! */
	&& req(i->arg[1], con01[optab[i->op].idval])
	&& (!optab[i->op].cmpeqwl || isw1(fn, i->arg[0])))
		return i->arg[0];

	/* idempotent op with identical args */
	if (optab[i->op].idemp
	&& req(i->arg[0], i->arg[1]))
		return i->arg[0];

	/* integer cmp with identical args */
	if ((optab[i->op].cmpeqwl || optab[i->op].cmplgtewl)
	&& req(i->arg[0], i->arg[1]))
		return con01[optab[i->op].eqval];

	/* cmpeq/ne 0 with 0/non-0 inference */
	if (optab[i->op].cmpeqwl
	&& req(i->arg[1], CON_Z)
	&& zeroval(fn, b, i->arg[0], argcls(i, 0), &z))
		return con01[optab[i->op].eqval^z^1];

	/* redundant and mask */
	if (i->op == Oand
	&& isconbits(fn, i->arg[1], &v)
	&& (v > 0 && ((v+1) & v) == 0)
	&& defwidthle(fn, i->arg[0], bitwidth(v)))
		return i->arg[0];

	if (i->cls == Kw
	&& (i->op == Oextsw || i->op == Oextuw))
		return i->arg[0];

	if (ext(i, &e) && rtype(i->arg[0]) == RTmp) {
		t = &fn->tmp[i->arg[0].val];
		assert(KBASE(t->cls) == 0);

		/* do not break typing by returning
		 * a narrower temp */
		if (KWIDE(i->cls) > KWIDE(t->cls))
			return R;

		w  = Wsb + (i->op - Oextsb);
		if (BIT(w) & extcpy[t->width])
			return i->arg[0];

		/* avoid eliding extensions of params
		 * inserted in the start block; their
		 * point is to make further extensions
		 * redundant */
		if ((!t->def || !ispar(t->def->op))
		&& usewidthle(fn, i->to, e.usew))
			return i->arg[0];

		if (defwidthle(fn, i->arg[0], e.nopw))
			return i->arg[0];
	}

	return R;
}

/**
 * Checks if two phi nodes have equivalent arguments.
 * 
 * This function compares two phi nodes to determine if they have
 * the same arguments in the same order. It's used to identify
 * redundant phi nodes that can be eliminated.
 * 
 * The function assumes that both phi nodes have the same number
 * of arguments and compares them block by block.
 * 
 * @param pa First phi node to compare
 * @param pb Second phi node to compare
 * @return 1 if the phi nodes are equivalent, 0 otherwise
 */
static int
phieq(Phi *pa, Phi *pb)
{
	Ref r;
	uint n;

	assert(pa->narg == pb->narg);
	for (n=0; n<pa->narg; n++) {
		r = phiarg(pb, pa->blk[n]);
		if (!req(pa->arg[n], r))
			return 0;
	}
	return 1;
}

/**
 * Attempts to find a copy-equivalent reference for a phi node.
 * 
 * This function analyzes a phi node to determine if it can be
 * replaced by a simpler reference. It handles various cases:
 * - Phi nodes with identical arguments (can be replaced by any argument)
 * - Phi nodes equivalent to previous phi nodes in the same block
 * - Phi nodes that can be replaced by a dominating conditional
 *   expression (when the phi represents a boolean selection)
 * 
 * The function uses dominance analysis to identify cases where
 * a phi node's value is determined by a conditional branch in
 * a dominating block.
 * 
 * @param fn The function containing the phi node
 * @param b The block containing the phi node
 * @param p The phi node to analyze
 * @return A reference that can replace the phi node, or R if no replacement is possible
 */
Ref
phicopyref(Fn *fn, Blk *b, Phi *p)
{
	Blk *d, **s;
	Phi *p1;
	uint n, c;

	/* identical args */
	for (n=0; n<p->narg-1; n++)
		if (!req(p->arg[n], p->arg[n+1]))
			break;
	if (n == p->narg-1)
		return p->arg[n];

	/* same as a previous phi */
	for (p1=b->phi; p1!=p; p1=p1->link) {
		assert(p1);
		if (phieq(p1, p))
			return p1->to;
	}

	/* can be replaced by a
	 * dominating jnz arg */
	d = b->idom;
	if (p->narg != 2
	|| d->jmp.type != Jjnz
	|| !isw1(fn, d->jmp.arg))
		return R;

	s = (Blk*[]){0, 0};
	for (n=0; n<2; n++)
		for (c=0; c<2; c++)
			if (req(p->arg[n], con01[c]))
				s[c] = p->blk[n];

	/* if s1 ends with a jnz on either b
	 * or s2; the inference below is wrong
	 * without the jump type checks */
	if (d->s1 == s[1] && d->s2 == s[0]
	&& d->s1->jmp.type == Jjmp
	&& d->s2->jmp.type == Jjmp)
		return d->jmp.arg;

	return R;
}
