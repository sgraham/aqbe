#include "all.h"

#define NOBID (-1u)

/**
 * Checks if an instruction is a division or remainder operation.
 * 
 * This function identifies division and remainder operations that
 * are considered pinned (cannot be moved) during global code motion.
 * Only operations with base class 0 (integer operations) are considered.
 * 
 * @param i The instruction to check
 * @return 1 if the instruction is a division/remainder operation, 0 otherwise
 */
static int
isdivwl(Ins *i)
{
	switch (i->op) {
	case Odiv:
	case Orem:
	case Oudiv:
	case Ourem:
		return KBASE(i->cls) == 0;
	default:
		return 0;
	}
}

/**
 * Checks if an instruction is pinned (cannot be moved).
 * 
 * A pinned instruction cannot be moved during global code motion
 * because it has side effects or must be executed at a specific
 * point in the program. This includes operations marked as pinned
 * in the operation table and division/remainder operations.
 * 
 * @param i The instruction to check
 * @return 1 if the instruction is pinned, 0 otherwise
 */
int
pinned(Ins *i)
{
	return optab[i->op].pinned || isdivwl(i);
}

/* pinned ins that can be eliminated if unused */
/**
 * Checks if a pinned instruction can be eliminated if unused.
 * 
 * Some pinned instructions can be removed if their result is not used,
 * even though they cannot be moved. This includes loads, allocations,
 * and division operations.
 * 
 * @param i The instruction to check
 * @return 1 if the instruction can be eliminated when unused, 0 otherwise
 */
static int
canelim(Ins *i)
{
	return isload(i->op) || isalloc(i->op) || isdivwl(i);
}

static uint earlyins(Fn *, Blk *, Ins *);

/**
 * Computes the earliest block where a reference can be scheduled.
 * 
 * This function determines the earliest point in the control flow graph
 * where a temporary can be computed. It uses a depth-first search through
 * the use-def chains to find the earliest block that dominates all uses
 * of the temporary.
 * 
 * @param fn The function containing the reference
 * @param r The reference to schedule
 * @return The block ID where the reference can be scheduled earliest
 */
static uint
schedearly(Fn *fn, Ref r)
{
	Tmp *t;
	Blk *b;

	if (rtype(r) != RTmp)
		return 0;

	t = &fn->tmp[r.val];
	if (t->gcmbid != NOBID)
		return t->gcmbid;

	b = fn->rpo[t->bid];
	if (t->def) {
		assert(b->ins <= t->def && t->def < &b->ins[b->nins]);
		t->gcmbid = 0;  /* mark as visiting */
		t->gcmbid = earlyins(fn, b, t->def);
	} else {
		/* phis do not move */
		t->gcmbid = t->bid;
	}

	return t->gcmbid;
}

/**
 * Computes the earliest block for an instruction.
 * 
 * This function determines the earliest block where an instruction
 * can be scheduled by finding the latest of its operand's earliest
 * blocks. If the instruction is pinned, it must remain in its
 * current block.
 * 
 * @param fn The function containing the instruction
 * @param b The block containing the instruction
 * @param i The instruction to schedule
 * @return The earliest block ID where the instruction can be scheduled
 */
static uint
earlyins(Fn *fn, Blk *b, Ins *i)
{
	uint b0, b1;

	b0 = schedearly(fn, i->arg[0]);
	assert(b0 != NOBID);
	b1 = schedearly(fn, i->arg[1]);
	assert(b1 != NOBID);
	if (fn->rpo[b0]->depth < fn->rpo[b1]->depth) {
		assert(dom(fn->rpo[b0], fn->rpo[b1]));
		b0 = b1;
	}
	return pinned(i) ? b->id : b0;
}

/**
 * Computes earliest scheduling for all instructions in a block.
 * 
 * This function processes all instructions in a block to compute
 * their earliest scheduling points. It handles phi instructions,
 * regular instructions, and jump instructions.
 * 
 * @param fn The function containing the block
 * @param bid The block ID to process
 */
static void
earlyblk(Fn *fn, uint bid)
{
	Blk *b;
	Phi *p;
	Ins *i;
	uint n;

	b = fn->rpo[bid];
	for (p=b->phi; p; p=p->link)
		for (n=0; n<p->narg; n++)
			schedearly(fn, p->arg[n]);
	for (i=b->ins; i<&b->ins[b->nins]; i++)
		if (pinned(i)) {
			schedearly(fn, i->arg[0]);
			schedearly(fn, i->arg[1]);
		}
	schedearly(fn, b->jmp.arg);
}

/* least common ancestor in dom tree */
/**
 * Finds the least common ancestor of two blocks in the dominator tree.
 * 
 * This function computes the least common ancestor of two blocks
 * in the dominator tree, which represents the earliest point where
 * both blocks can be reached.
 * 
 * @param fn The function containing the blocks
 * @param bid1 First block ID
 * @param bid2 Second block ID
 * @return The block ID of the least common ancestor
 */
static uint
lcabid(Fn *fn, uint bid1, uint bid2)
{
	Blk *b;

	if (bid1 == NOBID)
		return bid2;
	if (bid2 == NOBID)
		return bid1;

	b = lca(fn->rpo[bid1], fn->rpo[bid2]);
	assert(b);
	return b->id;
}

/**
 * Finds the best block for scheduling between early and late bounds.
 * 
 * This function finds the optimal block for scheduling an instruction
 * between its earliest and latest possible positions. It prefers blocks
 * with lower loop nesting to minimize register pressure.
 * 
 * @param fn The function containing the blocks
 * @param earlybid The earliest block where the instruction can be scheduled
 * @param latebid The latest block where the instruction can be scheduled
 * @return The best block ID for scheduling
 */
static uint
bestbid(Fn *fn, uint earlybid, uint latebid)
{
	Blk *curb, *earlyb, *bestb;

	if (latebid == NOBID)
		return NOBID; /* unused */

	assert(earlybid != NOBID);

	earlyb = fn->rpo[earlybid];
	bestb = curb = fn->rpo[latebid];
	assert(dom(earlyb, curb));

	while (curb != earlyb) {
		curb = curb->idom;
		if (curb->loop < bestb->loop)
			bestb = curb;
	}
	return bestb->id;
}

static uint lateins(Fn *, Blk *, Ins *, Ref r);
static uint latephi(Fn *, Phi *, Ref r);
static uint latejmp(Blk *, Ref r);

/* return lca bid of ref uses */
/**
 * Computes the latest block where a reference can be scheduled.
 * 
 * This function determines the latest point in the control flow graph
 * where a temporary can be computed. It analyzes all uses of the
 * temporary to find the latest block that post-dominates all uses.
 * 
 * @param fn The function containing the reference
 * @param r The reference to schedule
 * @return The latest block ID where the reference can be scheduled
 */
static uint
schedlate(Fn *fn, Ref r)
{
	Tmp *t;
	Blk *b;
	Use *u;
	uint earlybid;
	uint latebid;
	uint uselatebid;

	if (rtype(r) != RTmp)
		return NOBID;

	t = &fn->tmp[r.val];
	if (t->visit)
		return t->gcmbid;

	t->visit = 1;
	earlybid = t->gcmbid;
	if (earlybid == NOBID)
		return NOBID; /* not used */

	/* reuse gcmbid for late bid */
	t->gcmbid = t->bid;
	latebid = NOBID;
	for (u=t->use; u<&t->use[t->nuse]; u++) {
		assert(u->bid < fn->nblk);
		b = fn->rpo[u->bid];
		switch (u->type) {
		case UXXX:
			die("unreachable");
			break;
		case UPhi:
			uselatebid = latephi(fn, u->u.phi, r);
			break;
		case UIns:
			uselatebid = lateins(fn, b, u->u.ins, r);
			break;
		case UJmp:
			uselatebid = latejmp(b, r);
			break;
		}
		latebid = lcabid(fn, latebid, uselatebid);
	}
	/* latebid may be NOBID if the temp is used
	 * in fixed instructions that may be eliminated
	 * and are themselves unused transitively */

	if (t->def && !pinned(t->def))
		t->gcmbid = bestbid(fn, earlybid, latebid);
	/* else, keep the early one */

	/* now, gcmbid is the best bid */
	return t->gcmbid;
}

/* returns lca bid of uses or NOBID if
 * the definition can be eliminated */
/**
 * Computes the latest block for a reference used in an instruction.
 * 
 * This function determines the latest block where a reference can be
 * computed when it's used as an operand in an instruction. If the
 * instruction is pinned, the reference must be available before the
 * instruction. If the instruction can be eliminated, the reference
 * might not be needed at all.
 * 
 * @param fn The function containing the instruction
 * @param b The block containing the instruction
 * @param i The instruction using the reference
 * @param r The reference being used
 * @return The latest block ID where the reference can be computed
 */
static uint
lateins(Fn *fn, Blk *b, Ins *i, Ref r)
{
	uint latebid;

	assert(b->ins <= i && i < &b->ins[b->nins]);
	assert(req(i->arg[0], r) || req(i->arg[1], r));

	latebid = schedlate(fn, i->to);
	if (pinned(i)) {
		if (latebid == NOBID)
		if (canelim(i))
			return NOBID;
		return b->id;
	}

	return latebid;
}

/**
 * Computes the latest block for a reference used in a phi instruction.
 * 
 * This function determines the latest block where a reference can be
 * computed when it's used as an argument in a phi instruction. It
 * finds the least common ancestor of all blocks that provide the
 * reference to the phi.
 * 
 * @param fn The function containing the phi instruction
 * @param p The phi instruction using the reference
 * @param r The reference being used
 * @return The latest block ID where the reference can be computed
 */
static uint
latephi(Fn *fn, Phi *p, Ref r)
{
	uint n;
	uint latebid;

	if (!p->narg)
		return NOBID; /* marked as unused */

	latebid = NOBID;
	for (n = 0; n < p->narg; n++)
		if (req(p->arg[n], r))
			latebid = lcabid(fn, latebid, p->blk[n]->id);

	assert(latebid != NOBID);
	return latebid;
}

/**
 * Computes the latest block for a reference used in a jump instruction.
 * 
 * This function determines the latest block where a reference can be
 * computed when it's used as the argument in a jump instruction.
 * The reference must be available in the block containing the jump.
 * 
 * @param b The block containing the jump instruction
 * @param r The reference being used in the jump
 * @return The block ID where the reference can be computed
 */
static uint
latejmp(Blk *b, Ref r)
{
	if (req(b->jmp.arg, R))
		return NOBID;
	else {
		assert(req(b->jmp.arg, r));
		return b->id;
	}
}

/**
 * Computes latest scheduling for all instructions in a block.
 * 
 * This function processes all instructions in a block to compute
 * their latest scheduling points. It also removes unused phi
 * instructions and marks them for elimination.
 * 
 * @param fn The function containing the block
 * @param bid The block ID to process
 */
static void
lateblk(Fn *fn, uint bid)
{
	Blk *b;
	Phi **pp;
	Ins *i;

	b = fn->rpo[bid];
	for (pp=&b->phi; *(pp);)
		if (schedlate(fn, (*pp)->to) == NOBID) {
			(*pp)->narg = 0; /* mark unused */
			*pp = (*pp)->link; /* remove phi */
		} else
			pp = &(*pp)->link;

	for (i=b->ins; i<&b->ins[b->nins]; i++)
		if (pinned(i))
			schedlate(fn, i->to);
}

/**
 * Adds instructions to their target blocks during global code motion.
 * 
 * This function adds instructions that have been moved to their
 * target blocks during the global code motion phase. It uses the
 * gcmbid field to determine where each instruction should be placed.
 * 
 * @param fn The function containing the instructions
 * @param vins Array of instructions to add
 * @param nins Number of instructions in the array
 */
static void
addgcmins(Fn *fn, Ins *vins, uint nins)
{
	Ins *i;
	Tmp *t;
	Blk *b;

	for (i=vins; i<&vins[nins]; i++) {
		assert(rtype(i->to) == RTmp);
		t = &fn->tmp[i->to.val];
		b = fn->rpo[t->gcmbid];
		addins(&b->ins, &b->nins, i);
	}
}

/* move live instructions to the
 * end of their target block; use-
 * before-def errors are fixed by
 * schedblk */
/**
 * Moves live instructions to their target blocks.
 * 
 * This function performs the actual movement of instructions during
 * global code motion. It collects instructions that need to be moved
 * and adds them to their target blocks. Instructions that are pinned
 * and cannot be eliminated are left in place.
 * 
 * @param fn The function to optimize
 */
static void
gcmmove(Fn *fn)
{
	Tmp *t;
	Ins *vins, *i;
	uint nins;

	nins = 0;
	vins = vnew(nins, sizeof vins[0], PFn);

	for (t=fn->tmp; t<&fn->tmp[fn->ntmp]; t++) {
		if (t->def == 0)
			continue;
		if (t->bid == t->gcmbid)
			continue;
		i = t->def;
		if (pinned(i) && !canelim(i))
			continue;
		assert(rtype(i->to) == RTmp);
		assert(t == &fn->tmp[i->to.val]);
		if (t->gcmbid != NOBID)
			addins(&vins, &nins, i);
		*i = (Ins){.op = Onop};
	}
	addgcmins(fn, vins, nins);
}

/* dfs ordering */
/**
 * Schedules instructions within a block using depth-first search.
 * 
 * This function performs instruction scheduling within a block by
 * using a depth-first search to ensure that instructions are ordered
 * correctly with respect to their dependencies. It groups instructions
 * and schedules them in dependency order.
 * 
 * @param fn The function containing the block
 * @param b The block to schedule
 * @param i The instruction to start scheduling from
 * @param pvins Pointer to the instruction array
 * @param pnins Pointer to the number of instructions
 * @return Pointer to the next instruction after the scheduled group
 */
static Ins *
schedins(Fn *fn, Blk *b, Ins *i, Ins **pvins, uint *pnins)
{
	Ins *i0, *i1;
	Tmp *t;
	uint n;

	igroup(b, i, &i0, &i1);
	for (i=i0; i<i1; i++)
		for (n=0; n<2; n++) {
			if (rtype(i->arg[n]) != RTmp)
				continue;
			t = &fn->tmp[i->arg[n].val];
			if (t->bid != b->id || !t->def)
				continue;
			schedins(fn, b, t->def, pvins, pnins);
		}
	for (i=i0; i<i1; i++) {
		addins(pvins, pnins, i);
		*i = (Ins){.op = Onop};
	}
	return i1;
}

/* order ins within a block */
/**
 * Orders instructions within each block.
 * 
 * This function performs instruction scheduling within each block
 * to ensure proper ordering of instructions with respect to their
 * dependencies. It uses a depth-first search approach to schedule
 * instructions correctly.
 * 
 * @param fn The function to schedule
 */
static void
schedblk(Fn *fn)
{
	Blk *b;
	Ins *i, *vins;
	uint nins;

	vins = vnew(0, sizeof vins[0], PHeap);
	for (b=fn->start; b; b=b->link) {
		nins = 0;
		for (i=b->ins; i<&b->ins[b->nins];)
			i = schedins(fn, b, i, &vins, &nins);
		idup(b, vins, nins);
	}
	vfree(vins);
}

/**
 * Checks if an instruction is cheap to compute.
 * 
 * This function determines if an instruction is considered "cheap"
 * and can be sunk to its point of use to reduce register pressure.
 * Cheap instructions are typically simple arithmetic and logical
 * operations that have low computational cost.
 * 
 * @param i The instruction to check
 * @return 1 if the instruction is cheap, 0 otherwise
 */
static int
cheap(Ins *i)
{
	int x;

	if (KBASE(i->cls) != 0)
		return 0;
	switch (i->op) {
	case Oneg:
	case Oadd:
	case Osub:
	case Omul:
	case Oand:
	case Oor:
	case Oxor:
	case Osar:
	case Oshr:
	case Oshl:
		return 1;
	default:
		return iscmp(i->op, &x, &x);
	}
}

/**
 * Sinks a reference to its point of use if beneficial.
 * 
 * This function attempts to sink the definition of a reference to
 * its point of use if the definition is cheap to compute and can
 * be moved. This helps reduce register pressure by computing values
 * closer to where they are used.
 * 
 * @param fn The function containing the reference
 * @param b The block where the reference is used
 * @param pr Pointer to the reference to sink
 */
static void
sinkref(Fn *fn, Blk *b, Ref *pr)
{
	Ins i;
	Tmp *t;
	Ref r;

	if (rtype(*pr) != RTmp)
		return;
	t = &fn->tmp[pr->val];
	if (!t->def
	|| t->bid == b->id
	|| pinned(t->def)
	|| !cheap(t->def))
		return;

	/* sink t->def to b */
	i = *t->def;
	r = newtmp("snk", t->cls, fn);
	t = 0;  /* invalidated */
	*pr = r;
	i.to = r;
	fn->tmp[r.val].gcmbid = b->id;
	emiti(i);
	sinkref(fn, b, &i.arg[0]);
	sinkref(fn, b, &i.arg[1]);
}

/* redistribute trivial ops to point of
 * use to reduce register pressure
 * requires rpo, use; breaks use */
/**
 * Performs instruction sinking to reduce register pressure.
 * 
 * This function redistributes trivial operations to their points of
 * use to reduce register pressure. It sinks cheap instructions that
 * are used in loads, stores, and jumps to minimize the number of
 * live temporaries at any point in the program.
 * 
 * The optimization requires reverse post-order numbering and use
 * information, and may break the use information.
 * 
 * @param fn The function to optimize
 */
static void
sink(Fn *fn)
{
	Blk *b;
	Ins *i;

	for (b=fn->start; b; b=b->link) {
		for (i=b->ins; i<&b->ins[b->nins]; i++)
			if (isload(i->op))
				sinkref(fn, b, &i->arg[0]);
			else if (isstore(i->op))
				sinkref(fn, b, &i->arg[1]);
		sinkref(fn, b, &b->jmp.arg);
	}
	addgcmins(fn, curi, &insb[NIns] - curi);
}

/* requires use dom
 * maintains rpo pred dom
 * breaks use */
/**
 * Performs global code motion optimization on a function.
 * 
 * This function implements global code motion, which moves instructions
 * to optimal positions in the control flow graph to improve performance
 * and reduce register pressure. The optimization:
 * - Computes earliest and latest scheduling points for each instruction
 * - Moves instructions to their optimal positions
 * - Sinks cheap instructions to their points of use
 * - Maintains proper instruction ordering within blocks
 * 
 * The optimization requires use information and dominator relationships,
 * and maintains reverse post-order numbering and predecessor information.
 * 
 * @param fn The function to optimize
 */
void
gcm(Fn *fn)
{
	Tmp *t;
	uint bid;

	filldepth(fn);
	fillloop(fn);

	for (t=fn->tmp; t<&fn->tmp[fn->ntmp]; t++) {
		t->visit = 0;
		t->gcmbid = NOBID;
	}
	for (bid=0; bid<fn->nblk; bid++)
		earlyblk(fn, bid);
	for (bid=0; bid<fn->nblk; bid++)
		lateblk(fn, bid);

	gcmmove(fn);
	filluse(fn);
	curi = &insb[NIns];
	sink(fn);
	filluse(fn);
	schedblk(fn);
	
	if (debug['G']) {
		fprintf(stderr, "\n> After GCM:\n");
		printfn(fn, stderr);
	}
}
