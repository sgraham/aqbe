#include "all.h"

Ref con01[2];

/**
 * Combines two hash values using a simple mixing function.
 * 
 * This function is used to combine multiple hash values into a single
 * hash value for hash table lookups. It uses a simple linear combination
 * with a prime multiplier.
 * 
 * @param x0 First hash value
 * @param x1 Second hash value
 * @return Combined hash value
 */
static inline uint
mix(uint x0, uint x1)
{
	return x0 + 17*x1;
}

/**
 * Computes a hash value for a reference.
 * 
 * Creates a hash value from a reference by combining its type and value.
 * This is used for hash table lookups in global value numbering.
 * 
 * @param r The reference to hash
 * @return Hash value for the reference
 */
static inline uint
rhash(Ref r)
{
	return mix(r.type, r.val);
}

/**
 * Computes a hash value for an instruction.
 * 
 * Creates a hash value from an instruction by combining its operation,
 * class, and argument references. This is used for hash table lookups
 * to find equivalent instructions during global value numbering.
 * 
 * @param i The instruction to hash
 * @return Hash value for the instruction
 */
static uint
ihash(Ins *i)
{
	uint h;

	h = mix(i->op, i->cls);
	h = mix(h, rhash(i->arg[0]));
	h = mix(h, rhash(i->arg[1]));

	return h;
}

/**
 * Compares two instructions for equality.
 * 
 * Checks if two instructions are equivalent by comparing their operation,
 * class, and arguments. This is used to identify redundant instructions
 * during global value numbering.
 * 
 * @param ia First instruction
 * @param ib Second instruction
 * @return 1 if instructions are equal, 0 otherwise
 */
static int
ieq(Ins *ia, Ins *ib)
{
	if (ia->op == ib->op)
	if (ia->cls == ib->cls)
	if (req(ia->arg[0], ib->arg[0]))
	if (req(ia->arg[1], ib->arg[1]))
		return 1;
	return 0;
}

static Ins **gvntbl;
static uint gvntbln;

/**
 * Looks up or inserts an instruction in the global value numbering table.
 * 
 * Searches the hash table for an equivalent instruction. If found,
 * returns the existing instruction. If not found and insert is true,
 * adds the instruction to the table. This implements the core of
 * global value numbering by identifying redundant computations.
 * 
 * @param i The instruction to look up or insert
 * @param insert Whether to insert the instruction if not found
 * @return Pointer to equivalent instruction if found, NULL otherwise
 */
static Ins *
gvndup(Ins *i, int insert)
{
	uint idx, n;
	Ins *ii;

	idx = ihash(i) % gvntbln;
	for (n=1;; n++) {
		ii = gvntbl[idx];
		if (!ii)
			break;
		if (ieq(i, ii))
			return ii;

		idx++;
		if (gvntbln <= idx)
			idx = 0;
	}
	if (insert)
		gvntbl[idx] = i;
	return 0;
}

/**
 * Replaces all uses of one reference with another reference.
 * 
 * Updates a specific use of a reference to use a different reference instead.
 * This is used during global value numbering to replace redundant computations
 * with references to equivalent values. It also updates the use lists to
 * maintain proper tracking of variable usage.
 * 
 * @param fn The function containing the use
 * @param u The use to update
 * @param r1 The original reference to replace
 * @param r2 The new reference to use instead
 */
static void
replaceuse(Fn *fn, Use *u, Ref r1, Ref r2)
{
	Blk *b;
	Ins *i;
	Phi *p;
	Ref *pr;
	Tmp *t2;
	int n;

	t2 = 0;
	if (rtype(r2) == RTmp)
		t2 = &fn->tmp[r2.val];
	b = fn->rpo[u->bid];
	switch (u->type) {
	case UPhi:
		p = u->u.phi;
		for (pr=p->arg; pr<&p->arg[p->narg]; pr++)
			if (req(*pr, r1))
				*pr = r2;
		if (t2)
			adduse(t2, UPhi, b, p);
		break;
	case UIns:
		i = u->u.ins;
		for (n=0; n<2; n++)
			if (req(i->arg[n], r1))
				i->arg[n] = r2;
		if (t2)
			adduse(t2, UIns, b, i);
		break;
	case UJmp:
		if (req(b->jmp.arg, r1))
			b->jmp.arg = r2;
		if (t2)
			adduse(t2, UJmp, b);
		break;
	case UXXX:
		die("unreachable");
	}
}

/**
 * Replaces all uses of one reference with another reference throughout the function.
 * 
 * Updates every use of a reference to use a different reference instead.
 * This is used during global value numbering to eliminate redundant computations
 * by replacing all uses of a redundant value with a reference to the equivalent
 * value that was computed earlier.
 * 
 * @param fn The function to update
 * @param r1 The original reference to replace
 * @param r2 The new reference to use instead
 */
static void
replaceuses(Fn *fn, Ref r1, Ref r2)
{
	Tmp *t1;
	Use *u;

	assert(rtype(r1) == RTmp);
	t1 = &fn->tmp[r1.val];
	for (u=t1->use; u<&t1->use[t1->nuse]; u++)
		replaceuse(fn, u, r1, r2);
	t1->nuse = 0;
}

/**
 * Removes redundant phi instructions from a block.
 * 
 * Analyzes phi instructions in a block to identify those that can be
 * replaced with copies of existing values. If a phi instruction can be
 * replaced with a simple copy, it updates all uses of the phi result
 * to use the copied value instead and removes the phi instruction.
 * 
 * @param fn The function containing the block
 * @param b The block to process
 */
static void
dedupphi(Fn *fn, Blk *b)
{
	Phi *p, **pp;
	Ref r;

	for (pp=&b->phi; (p=*pp);) {
		r = phicopyref(fn, b, p);
		if (!req(r, R)) {
			replaceuses(fn, p->to, r);
			p->to = R;
			*pp = p->link;
		} else
			pp = &p->link;
	}
}

/**
 * Compares two references for ordering.
 * 
 * Provides a consistent ordering for references based on their type
 * and value. This is used to normalize commutative operations by
 * ensuring arguments are in a consistent order.
 * 
 * @param a First reference
 * @param b Second reference
 * @return Negative if a < b, 0 if equal, positive if a > b
 */
static int
rcmp(Ref a, Ref b)
{
	if (rtype(a) != rtype(b))
		return rtype(a) - rtype(b);
	return a.val - b.val;
}

/**
 * Normalizes an instruction for better value numbering.
 * 
 * Performs several transformations to make instructions more amenable
 * to value numbering:
 * - Truncates constant values to appropriate bit widths
 * - Orders arguments of commutative operations consistently
 * - Prefers temporaries in the first argument position
 * 
 * @param fn The function containing the instruction
 * @param i The instruction to normalize
 */
static void
normins(Fn *fn, Ins *i)
{
	uint n;
	int64_t v;
	Ref r;

	/* truncate constant bits to
	 * 32 bits for s/w uses */
	for (n=0; n<2; n++) {
		if (!KWIDE(argcls(i, n)))
		if (isconbits(fn, i->arg[n], &v))
		if ((v & 0xffffffff) != v)
			i->arg[n] = getcon(v & 0xffffffff, fn);
	}
	/* order arg[0] <= arg[1] for
	 * commutative ops, preferring
	 * RTmp in arg[0] */
	if (optab[i->op].commutes)
	if (rcmp(i->arg[0], i->arg[1]) > 0) {
		r = i->arg[1];
		i->arg[1] = i->arg[0];
		i->arg[0] = r;
	}
}

/**
 * Negates a constant value.
 * 
 * Creates a new constant that is the negation of the given constant.
 * This is used during constant folding and value numbering to handle
 * negation operations.
 * 
 * @param cls The class of the constant
 * @param c The constant to negate
 * @return 1 if negation was successful, 0 otherwise
 */
static int
negcon(int cls, Con *c)
{
	static Con z = {.type = CBits, .bits.i = 0};

	return foldint(c, Osub, cls, &z, c);
}

/**
 * Performs constant association optimization on an instruction.
 * 
 * Looks for opportunities to combine constants in associative operations.
 * If an instruction has a constant argument and its other argument is
 * defined by an instruction with the same operation and a constant,
 * it can combine the constants to create a single constant operation.
 * 
 * @param fn The function containing the instruction
 * @param b The block containing the instruction
 * @param i1 The instruction to optimize
 */
static void
assoccon(Fn *fn, Blk *b, Ins *i1)
{
	Tmp *t2;
	Ins *i2;
	int op, fail;
	Con c, c1, c2;

	op = i1->op;
	if (op == Osub)
		op = Oadd;

	if (!optab[op].assoc
	|| KBASE(i1->cls) != 0
	|| rtype(i1->arg[0]) != RTmp
	|| rtype(i1->arg[1]) != RCon)
		return;
	c1 = fn->con[i1->arg[1].val];

	t2 = &fn->tmp[i1->arg[0].val];
	if (t2->def == 0)
		return;
	i2 = t2->def;

	if (op != (i2->op == Osub ? Oadd : i2->op)
	|| rtype(i2->arg[1]) != RCon)
		return;
	c2 = fn->con[i2->arg[1].val];

	assert(KBASE(i2->cls) == 0);
	assert(KWIDE(i2->cls) >= KWIDE(i1->cls));

	if (i1->op == Osub && negcon(i1->cls, &c1))
		return;
	if (i2->op == Osub && negcon(i2->cls, &c2))
		return;
	if (foldint(&c, op, i1->cls, &c1, &c2))
		return;

	if (op == Oadd && c.type == CBits)
	if ((i1->cls == Kl  && c.bits.i < 0)
	|| (i1->cls == Kw && (int32_t)c.bits.i < 0)) {
		fail = negcon(i1->cls, &c);
		assert(fail == 0);
		op = Osub;
	}

	i1->op = op;
	i1->arg[0] = i2->arg[0];
	i1->arg[1] = newcon(&c, fn);
	adduse(&fn->tmp[i1->arg[0].val], UIns, b, i1);
}

/**
 * Replaces an instruction with a reference and marks it as a no-op.
 * 
 * This function is used during global value numbering to eliminate
 * redundant instructions. It replaces all uses of the instruction's
 * result with the given reference and then converts the instruction
 * to a no-op.
 * 
 * @param fn The function containing the instruction
 * @param i The instruction to kill
 * @param r The reference to replace the instruction result with
 */
static void
killins(Fn *fn, Ins *i, Ref r)
{
	replaceuses(fn, i->to, r);
	*i = (Ins){.op = Onop};
}

/**
 * Performs global value numbering on a single instruction.
 * 
 * This function attempts to eliminate redundant computations by:
 * 1. Normalizing the instruction for better value numbering
 * 2. Checking if the instruction can be replaced with a copy
 * 3. Checking if the instruction can be constant-folded
 * 4. Looking up the instruction in the global value numbering table
 * 
 * If any of these optimizations succeed, the instruction is replaced
 * with the equivalent value.
 * 
 * @param fn The function containing the instruction
 * @param b The block containing the instruction
 * @param i The instruction to optimize
 */
static void
dedupins(Fn *fn, Blk *b, Ins *i)
{
	Ref r;
	Ins *i1;

	normins(fn, i);
	if (i->op == Onop || pinned(i))
		return;

	assert(!req(i->to, R));
	assoccon(fn, b, i);

	r = copyref(fn, b, i);
	if (!req(r, R)) {
		killins(fn, i, r);
		return;
	}
	r = foldref(fn, i);
	if (!req(r, R)) {
		killins(fn, i, r);
		return;
	}
	i1 = gvndup(i, 1);
	if (i1) {
		killins(fn, i, i1->to);
		return;
	}
}

/**
 * Checks if a reference represents a comparison with zero.
 * 
 * Analyzes the definition of a reference to see if it's a comparison
 * operation that compares a value with zero. If so, extracts the
 * compared value and comparison information.
 * 
 * @param fn The function containing the reference
 * @param r The reference to check
 * @param arg Output parameter for the compared value
 * @param cls Output parameter for the class of the comparison
 * @param eqval Output parameter for the equality value
 * @return 1 if the reference is a comparison with zero, 0 otherwise
 */
int
cmpeqz(Fn *fn, Ref r, Ref *arg, int *cls, int *eqval)
{
	Ins *i;

	if (rtype(r) != RTmp)
		return 0;
	i = fn->tmp[r.val].def;
	if (i)
	if (optab[i->op].cmpeqwl)
	if (req(i->arg[1], CON_Z)) {
		*arg = i->arg[0];
		*cls = argcls(i, 0);
		*eqval = optab[i->op].eqval;
		return 1;
	}
	return 0;
}

/**
 * Checks if a block is dominated by one branch of a conditional jump.
 * 
 * Determines if a block is reachable only through one specific branch
 * of a conditional jump, which can be used to infer value information
 * about the jump condition in that block.
 * 
 * @param fn The function containing the blocks
 * @param bif The block with the conditional jump
 * @param bbr1 The first branch target
 * @param bbr2 The second branch target
 * @param b The block to check
 * @return 1 if b is dominated by bbr1 and not reachable via bbr2, 0 otherwise
 */
static int
branchdom(Fn *fn, Blk *bif, Blk *bbr1, Blk *bbr2, Blk *b)
{
	assert(bif->jmp.type == Jjnz);

	if (b != bif
	&& dom(bbr1, b)
	&& !reachesnotvia(fn, bbr2, b, bif))
		return 1;

	return 0;
}

/**
 * Determines if a block is dominated by a specific branch of a conditional jump.
 * 
 * Checks if a block is dominated by one branch of a conditional jump and
 * sets the output parameter to indicate which branch (0 or 1) dominates it.
 * 
 * @param fn The function containing the blocks
 * @param d The block with the conditional jump
 * @param b The block to check
 * @param z Output parameter indicating which branch dominates (0 or 1)
 * @return 1 if the block is dominated by one branch, 0 otherwise
 */
static int
domzero(Fn *fn, Blk *d, Blk *b, int *z)
{
	if (branchdom(fn, d, d->s1, d->s2, b)) {
		*z = 0;
		return 1;
	}
	if (branchdom(fn, d, d->s2, d->s1, b)) {
		*z = 1;
		return 1;
	}
	return 0;
}

/* infer 0/non-0 value from dominating jnz */
/**
 * Infers whether a value is zero or non-zero based on dominating conditional jumps.
 * 
 * Analyzes the dominator tree to find conditional jumps that can provide
 * information about whether a value is zero or non-zero in the current block.
 * This is used for jump optimization and constant propagation.
 * 
 * @param fn The function containing the blocks
 * @param b The block where the value is used
 * @param r The reference to check
 * @param cls The class of the value
 * @param z Output parameter indicating if the value is zero (1) or non-zero (0)
 * @return 1 if zero/non-zero information could be inferred, 0 otherwise
 */
int
zeroval(Fn *fn, Blk *b, Ref r, int cls, int *z)
{
	Blk *d;
	Ref arg;
	int cls1, eqval;

	for (d=b->idom; d; d=d->idom) {
		if (d->jmp.type != Jjnz)
			continue;
		if (req(r, d->jmp.arg)
		&& cls == Kw
		&& domzero(fn, d, b, z)) {
			return 1;
		}
		if (cmpeqz(fn, d->jmp.arg, &arg, &cls1, &eqval)
		&& req(r, arg)
		&& cls == cls1
		&& domzero(fn, d, b, z)) {
			*z ^= eqval;
			return 1;
		}
	}
	return 0;
}

/**
 * Determines the class of a use of a reference.
 * 
 * Analyzes how a reference is used to determine the appropriate class
 * for that use. This is important for ensuring that optimizations
 * don't change the semantics of the program, especially when dealing
 * with different bit widths.
 * 
 * @param u The use to analyze
 * @param r The reference being used
 * @param cls The default class to use
 * @return The appropriate class for this use
 */
static int
usecls(Use *u, Ref r, int cls)
{
	int k;

	switch (u->type) {
	case UIns:
		k = Kx;  /* widest use */
		if (req(u->u.ins->arg[0], r))
			k = argcls(u->u.ins, 0);
		if (req(u->u.ins->arg[1], r))
		if (k == Kx || !KWIDE(k))
			k = argcls(u->u.ins, 1);
		return k == Kx ? cls : k;
	case UPhi:
		if (req(u->u.phi->to, R))
			return cls; /* eliminated */
		return u->u.phi->cls;
	case UJmp:
		return Kw;
	default:
		break;
	}
	die("unreachable");
}

/**
 * Propagates zero values through conditional jump branches.
 * 
 * When a conditional jump is known to branch based on a value being zero,
 * this function propagates that knowledge to blocks that are only reachable
 * through the zero branch. It replaces uses of the value with zero constants
 * in those blocks.
 * 
 * @param fn The function containing the blocks
 * @param bif The block with the conditional jump
 * @param s0 The block reached when the condition is zero
 * @param snon0 The block reached when the condition is non-zero
 * @param r The reference to propagate
 * @param cls The class of the reference
 */
static void
propjnz0(Fn *fn, Blk *bif, Blk *s0, Blk *snon0, Ref r, int cls)
{
	Blk *b;
	Tmp *t;
	Use *u;

	if (s0->npred != 1 || rtype(r) != RTmp)
		return;
	t = &fn->tmp[r.val];
	for (u=t->use; u<&t->use[t->nuse]; u++) {
		b = fn->rpo[u->bid];
		/* we may compare an l temp with a w
		 * comparison; so check that the use
		 * does not involve high bits */
		if (usecls(u, r, cls) == cls)
		if (branchdom(fn, bif, s0, snon0, b))
			replaceuse(fn, u, r, CON_Z);
	}
}

/**
 * Optimizes conditional jumps in a block.
 * 
 * Performs several optimizations on conditional jumps:
 * - Propagates zero values through jump branches
 * - Collapses trivial or constant conditional jumps to unconditional jumps
 * - Eliminates dead branches when the condition is known to be constant
 * 
 * @param fn The function containing the block
 * @param b The block to optimize
 */
static void
dedupjmp(Fn *fn, Blk *b)
{
	Blk **ps;
	int64_t v;
	Ref arg;
	int cls, eqval, z;

	if (b->jmp.type != Jjnz)
		return;

	/* propagate jmp arg as 0 through s2 */
	propjnz0(fn, b, b->s2, b->s1, b->jmp.arg, Kw);
	/* propagate cmp eq/ne 0 def of jmp arg as 0 */
	if (cmpeqz(fn, b->jmp.arg, &arg, &cls, &eqval)) {
		ps = (Blk*[]){b->s1, b->s2};
		propjnz0(fn, b, ps[eqval^1], ps[eqval], arg, cls);
	}

	/* collapse trivial/constant jnz to jmp */
	v = 1;
	z = 0;
	if (b->s1 == b->s2
	|| isconbits(fn, b->jmp.arg, &v)
	|| zeroval(fn, b, b->jmp.arg, Kw, &z)) {
		if (v == 0 || z)
			b->s1 = b->s2;
		/* we later move active ins out of dead blks */
		b->s2 = 0;
		b->jmp.type = Jjmp;
		b->jmp.arg = R;
	}
}

/**
 * Rebuilds the control flow graph after global value numbering.
 * 
 * After global value numbering may have eliminated some blocks or
 * changed the control flow, this function rebuilds the control flow
 * graph and moves any active instructions from unreachable blocks
 * to the start block to preserve their semantics.
 * 
 * @param fn The function to rebuild
 */
static void
rebuildcfg(Fn *fn)
{
	uint n, nblk;
	Blk *b, *s, **rpo;
	Ins *i;

	nblk = fn->nblk;
	rpo = emalloc(nblk * sizeof rpo[0]);
	memcpy(rpo, fn->rpo, nblk * sizeof rpo[0]);

	fillcfg(fn);

	/* move instructions that were in
	 * killed blocks and may be active
	 * in the computation in the start
	 * block */
	s = fn->start;
	for (n=0; n<nblk; n++) {
		b = rpo[n];
		if (b->id != -1u)
			continue;
		/* blk unreachable after GVN */
		assert(b != s);
		for (i=b->ins; i<&b->ins[b->nins]; i++)
			if (!optab[i->op].pinned)
			if (gvndup(i, 0) == i)
				addins(&s->ins, &s->nins, i);
	}
	free(rpo);
}

/* requires rpo pred ssa use
 * recreates rpo preds
 * breaks pred use dom ssa (GCM fixes ssa) */
/**
 * Performs global value numbering on a function.
 * 
 * Global value numbering is an optimization that eliminates redundant
 * computations by identifying instructions that compute the same value
 * and replacing them with references to a single computation. The process
 * involves:
 * - Computing loop information and narrowing parameters
 * - Building use/def information and validating SSA form
 * - Creating a hash table for value numbering
 * - Processing each block to eliminate redundant instructions and jumps
 * - Rebuilding the control flow graph
 * 
 * This optimization can significantly reduce code size and improve
 * performance by eliminating unnecessary computations.
 * 
 * @param fn The function to optimize
 */
void
gvn(Fn *fn)
{
	Blk *b;
	Phi *p;
	Ins *i;
	uint n, nins;

	con01[0] = getcon(0, fn);
	con01[1] = getcon(1, fn);

	/* copy.c uses the visit bit */
	for (b=fn->start; b; b=b->link)
		for (p=b->phi; p; p=p->link)
			p->visit = 0;

	fillloop(fn);
	narrowpars(fn);
	filluse(fn);
	ssacheck(fn);

	nins = 0;
	for (b=fn->start; b; b=b->link) {
		b->visit = 0;
		nins += b->nins;
	}

	gvntbln = nins + nins/2;
	gvntbl = emalloc(gvntbln * sizeof gvntbl[0]);
	for (n=0; n<fn->nblk; n++) {
		b = fn->rpo[n];
		dedupphi(fn, b);
		for (i=b->ins; i<&b->ins[b->nins]; i++)
			dedupins(fn, b, i);
		dedupjmp(fn, b);
	}
	rebuildcfg(fn);
	free(gvntbl);
	gvntbl = 0;

	if (debug['G']) {
		fprintf(stderr, "\n> After GVN:\n");
		printfn(fn, stderr);
	}
}
