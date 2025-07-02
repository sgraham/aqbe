#include "all.h"

/**
 * Aggregates loop information at loop headers.
 * 
 * This function accumulates liveness and loop information from loop
 * bodies to their headers. It merges the generated sets and updates
 * the maximum live count for each register class. This information
 * is used to make better spilling decisions in loops.
 * 
 * @param hd The loop header block
 * @param b The loop body block
 */
static void
aggreg(Blk *hd, Blk *b)
{
	int k;

	/* aggregate looping information at
	 * loop headers */
	bsunion(hd->gen, b->gen);
	for (k=0; k<2; k++)
		if (b->nlive[k] > hd->nlive[k])
			hd->nlive[k] = b->nlive[k];
}

/**
 * Updates usage statistics for a reference.
 * 
 * This function recursively processes a reference to update usage
 * statistics for temporaries. It handles memory references by
 * processing their base and index registers, and updates the
 * usage count, definition count, and cost for temporaries.
 * 
 * The cost is weighted by the loop level, making temporaries
 * used in deeper loops more expensive to spill.
 * 
 * @param r The reference to process
 * @param use Whether this is a use (1) or definition (0)
 * @param loop The current loop level
 * @param fn The function containing the reference
 */
static void
tmpuse(Ref r, int use, int loop, Fn *fn)
{
	Mem *m;
	Tmp *t;

	if (rtype(r) == RMem) {
		m = &fn->mem[r.val];
		tmpuse(m->base, 1, loop, fn);
		tmpuse(m->index, 1, loop, fn);
	}
	else if (rtype(r) == RTmp && r.val >= Tmp0) {
		t = &fn->tmp[r.val];
		t->nuse += use;
		t->ndef += !use;
		t->cost += loop;
	}
}

/* evaluate spill costs of temporaries,
 * this also fills usage information
 * requires rpo, preds */
/**
 * Evaluates spill costs for all temporaries in a function.
 * 
 * This function computes the spill cost for each temporary based on
 * its usage patterns and loop nesting. The cost is used to prioritize
 * which temporaries to keep in registers when register pressure is high.
 * 
 * The function:
 * 1. Aggregates loop information using loopiter()
 * 2. Initializes cost and usage statistics for all temporaries
 * 3. Processes phi nodes, instructions, and jump arguments
 * 4. Weights costs by loop depth to prefer keeping temporaries
 *    in registers in deeper loops
 * 
 * @param fn The function to analyze
 */
void
fillcost(Fn *fn)
{
	int n;
	uint a;
	Blk *b;
	Ins *i;
	Tmp *t;
	Phi *p;

	loopiter(fn, aggreg);
	if (debug['S']) {
		fprintf(stderr, "\n> Loop information:\n");
		for (b=fn->start; b; b=b->link) {
			for (a=0; a<b->npred; ++a)
				if (b->id <= b->pred[a]->id)
					break;
			if (a != b->npred) {
				fprintf(stderr, "\t%-10s", b->name);
				fprintf(stderr, " (% 3d ", b->nlive[0]);
				fprintf(stderr, "% 3d) ", b->nlive[1]);
				dumpts(b->gen, fn->tmp, stderr);
			}
		}
	}
	for (t=fn->tmp; t-fn->tmp < fn->ntmp; t++) {
		t->cost = t-fn->tmp < Tmp0 ? UINT_MAX : 0;
		t->nuse = 0;
		t->ndef = 0;
	}
	for (b=fn->start; b; b=b->link) {
		for (p=b->phi; p; p=p->link) {
			t = &fn->tmp[p->to.val];
			tmpuse(p->to, 0, 0, fn);
			for (a=0; a<p->narg; a++) {
				n = p->blk[a]->loop;
				t->cost += n;
				tmpuse(p->arg[a], 1, n, fn);
			}
		}
		n = b->loop;
		for (i=b->ins; i<&b->ins[b->nins]; i++) {
			tmpuse(i->to, 0, n, fn);
			tmpuse(i->arg[0], 1, n, fn);
			tmpuse(i->arg[1], 1, n, fn);
		}
		tmpuse(b->jmp.arg, 1, n, fn);
	}
	if (debug['S']) {
		fprintf(stderr, "\n> Spill costs:\n");
		for (n=Tmp0; n<fn->ntmp; n++)
			fprintf(stderr, "\t%-10s %d\n",
				fn->tmp[n].name,
				fn->tmp[n].cost);
		fprintf(stderr, "\n");
	}
}

static BSet *fst; /* temps to prioritize in registers (for tcmp1) */
static Tmp *tmp;  /* current temporaries (for tcmpX) */
static int ntmp;  /* current # of temps (for limit) */
static int locs;  /* stack size used by locals */
static int slot4; /* next slot of 4 bytes */
static int slot8; /* ditto, 8 bytes */
static BSet mask[2][1]; /* class masks */

/**
 * Comparison function for sorting temporaries by spill cost.
 * 
 * This function compares two temporaries based on their spill cost,
 * with higher costs (more expensive to spill) sorted first. This
 * ensures that the most valuable temporaries are kept in registers
 * when register pressure is high.
 * 
 * @param pa Pointer to first temporary index
 * @param pb Pointer to second temporary index
 * @return Negative if a has higher cost, positive if b does
 */
static int
tcmp0(const void *pa, const void *pb)
{
	uint ca, cb;

	ca = tmp[*(int *)pa].cost;
	cb = tmp[*(int *)pb].cost;
	return (cb < ca) ? -1 : (cb > ca);
}

/**
 * Comparison function that prioritizes temporaries in a preferred set.
 * 
 * This function first compares temporaries based on whether they are
 * in a preferred set (fst), then falls back to cost-based comparison.
 * This allows the spiller to prioritize specific temporaries (like
 * those with register hints) over others with similar costs.
 * 
 * @param pa Pointer to first temporary index
 * @param pb Pointer to second temporary index
 * @return Negative if a has higher priority, positive if b does
 */
static int
tcmp1(const void *pa, const void *pb)
{
	int c;

	c = bshas(fst, *(int *)pb) - bshas(fst, *(int *)pa);
	return c ? c : tcmp0(pa, pb);
}

/**
 * Allocates a stack slot for a temporary.
 * 
 * This function manages stack slot allocation for spilled temporaries,
 * implementing a sophisticated packing algorithm to minimize stack usage.
 * It handles different slot sizes (4 and 8 bytes) and maintains
 * alignment requirements.
 * 
 * The algorithm uses two slot counters (slot4 and slot8) to track
 * available slots of different sizes, with logic to pack them efficiently
 * and avoid fragmentation.
 * 
 * @param t The temporary to allocate a slot for
 * @return Reference to the allocated stack slot
 */
static Ref
slot(int t)
{
	int s;

	assert(t >= Tmp0 && "cannot spill register");
	s = tmp[t].slot;
	if (s == -1) {
		/* specific to NAlign == 3 */
		/* nice logic to pack stack slots
		 * on demand, there can be only
		 * one hole and slot4 points to it
		 *
		 * invariant: slot4 <= slot8
		 */
		if (KWIDE(tmp[t].cls)) {
			s = slot8;
			if (slot4 == slot8)
				slot4 += 2;
			slot8 += 2;
		} else {
			s = slot4;
			if (slot4 == slot8) {
				slot8 += 2;
				slot4 += 1;
			} else
				slot4 = slot8;
		}
		s += locs;
		tmp[t].slot = s;
	}
	return SLOT(s);
}

/* restricts b to hold at most k
 * temporaries, preferring those
 * present in f (if given), then
 * those with the largest spill
 * cost */
/**
 * Limits a bit set to contain at most k temporaries.
 * 
 * This function restricts a bit set to hold at most k temporaries,
 * preferring those in a given set (f) if provided, then those with
 * the highest spill cost. It uses the comparison functions tcmp0
 * and tcmp1 to sort temporaries by priority.
 * 
 * Temporaries that don't fit in the limit are spilled to stack slots.
 * 
 * @param b The bit set to limit
 * @param k Maximum number of temporaries to keep
 * @param f Optional preferred set of temporaries
 */
static void
limit(BSet *b, int k, BSet *f)
{
	static int *tarr, maxt;
	int i, t, nt;

	nt = bscount(b);
	if (nt <= k)
		return;
	if (nt > maxt) {
		free(tarr);
		tarr = emalloc(nt * sizeof tarr[0]);
		maxt = nt;
	}
	for (i=0, t=0; bsiter(b, &t); t++) {
		bsclr(b, t);
		tarr[i++] = t;
	}
	if (nt > 1) {
		if (!f)
			qsort(tarr, nt, sizeof tarr[0], tcmp0);
		else {
			fst = f;
			qsort(tarr, nt, sizeof tarr[0], tcmp1);
		}
	}
	for (i=0; i<k && i<nt; i++)
		bsset(b, tarr[i]);
	for (; i<nt; i++)
		slot(tarr[i]);
}

/* spills temporaries to fit the
 * target limits using the same
 * preferences as limit(); assumes
 * that k1 gprs and k2 fprs are
 * currently in use */

/**
 * Limits register usage for both integer and floating-point registers.
 * 
 * This function applies the limit() function separately to integer
 * and floating-point temporaries, ensuring that each register class
 * respects its own limits. It takes into account the current usage
 * of each register class.
 * 
 * @param b1 Bit set containing all temporaries
 * @param k1 Current number of integer registers in use
 * @param k2 Current number of floating-point registers in use
 * @param f Optional preferred set of temporaries
 */
static void
limit2(BSet *b1, int k1, int k2, BSet *f)
{
	BSet b2[1];

	bsinit(b2, ntmp); /* todo, free those */
	bscopy(b2, b1);
	bsinter(b1, mask[0]);
	bsinter(b2, mask[1]);
	limit(b1, T.ngpr - k1, f);
	limit(b2, T.nfpr - k2, f);
	bsunion(b1, b2);
}

/**
 * Sets register hints for temporaries in a bit set.
 * 
 * This function updates the register hints for all temporaries in
 * a bit set, indicating that the specified registers are preferred
 * for these temporaries. This helps guide future register allocation
 * decisions.
 * 
 * @param u Bit set of temporaries to update
 * @param r Bit mask of preferred registers
 */
static void
sethint(BSet *u, bits r)
{
	int t;

	for (t=Tmp0; bsiter(u, &t); t++)
		tmp[phicls(t, tmp)].hint.m |= r;
}

/* reloads temporaries in u that are
 * not in v from their slots */
/**
 * Reloads temporaries from their spill slots.
 * 
 * This function generates load instructions for temporaries that are
 * in a source set (u) but not in a destination set (v), effectively
 * reloading them from their spill slots into registers.
 * 
 * @param u Bit set of temporaries that should be in registers
 * @param v Bit set of temporaries currently in registers
 */
static void
reloads(BSet *u, BSet *v)
{
	int t;

	for (t=Tmp0; bsiter(u, &t); t++)
		if (!bshas(v, t))
			emit(Oload, tmp[t].cls, TMP(t), slot(t), R);
}

/**
 * Stores a temporary to its spill slot.
 * 
 * This function generates a store instruction to save a temporary
 * to its allocated stack slot. It only generates the store if a
 * valid slot is provided.
 * 
 * @param r Reference to the temporary to store
 * @param s Stack slot number (-1 if no slot allocated)
 */
static void
store(Ref r, int s)
{
	if (s != -1)
		emit(Ostorew + tmp[r.val].cls, 0, R, r, SLOT(s));
}

/**
 * Checks if an instruction is a register-to-register copy.
 * 
 * This function determines if an instruction is a copy operation
 * where the source is a register. Such instructions are handled
 * specially during spilling.
 * 
 * @param i The instruction to check
 * @return 1 if it's a register copy, 0 otherwise
 */
static int
regcpy(Ins *i)
{
	return i->op == Ocopy && isreg(i->arg[0]);
}

/**
 * Processes parallel moves at the beginning of a block.
 * 
 * This function handles a sequence of register-to-register copy
 * instructions at the start of a block, managing register pressure
 * and generating spill/reload instructions as needed. It also
 * handles function calls by managing caller-saved registers.
 * 
 * @param b The block containing the moves
 * @param i Pointer to the first instruction to process
 * @param v Bit set of temporaries currently in registers
 * @return Pointer to the instruction after the processed moves
 */
static Ins *
dopm(Blk *b, Ins *i, BSet *v)
{
	int n, t;
	BSet u[1];
	Ins *i1;
	bits r;

	bsinit(u, ntmp); /* todo, free those */
	/* consecutive copies from
	 * registers need to be handled
	 * as one large instruction
	 *
	 * fixme: there is an assumption
	 * that calls are always followed
	 * by copy instructions here, this
	 * might not be true if previous
	 * passes change
	 */
	i1 = ++i;
	do {
		i--;
		t = i->to.val;
		if (!req(i->to, R))
		if (bshas(v, t)) {
			bsclr(v, t);
			store(i->to, tmp[t].slot);
		}
		bsset(v, i->arg[0].val);
	} while (i != b->ins && regcpy(i-1));
	bscopy(u, v);
	if (i != b->ins && (i-1)->op == Ocall) {
		v->t[0] &= ~T.retregs((i-1)->arg[1], 0);
		limit2(v, T.nrsave[0], T.nrsave[1], 0);
		for (n=0, r=0; T.rsave[n]>=0; n++)
			r |= BIT(T.rsave[n]);
		v->t[0] |= T.argregs((i-1)->arg[1], 0);
	} else {
		limit2(v, 0, 0, 0);
		r = v->t[0];
	}
	sethint(v, r);
	reloads(u, v);
	do
		emiti(*--i1);
	while (i1 != i);
	return i;
}

/**
 * Merges liveness information from two blocks.
 * 
 * This function combines liveness information from two blocks,
 * taking into account loop nesting. For blocks in the same loop
 * level, it performs a union operation. For blocks in different
 * loop levels, it only includes temporaries that haven't been
 * spilled yet.
 * 
 * @param u Bit set to store the merged result
 * @param bu First block
 * @param v Bit set from second block
 * @param bv Second block
 */
static void
merge(BSet *u, Blk *bu, BSet *v, Blk *bv)
{
	int t;

	if (bu->loop <= bv->loop)
		bsunion(u, v);
	else
		for (t=0; bsiter(v, &t); t++)
			if (tmp[t].slot == -1)
				bsset(u, t);
}

/* spill code insertion
 * requires spill costs, rpo, liveness
 *
 * Note: this will replace liveness
 * information (in, out) with temporaries
 * that must be in registers at block
 * borders
 *
 * Be careful with:
 * - Ocopy instructions to ensure register
 *   constraints */
/**
 * Performs register spilling for an entire function.
 * 
 * This function implements a complete spilling pass that:
 * 1. Determines which temporaries must be in registers at block boundaries
 * 2. Processes instructions to maintain register pressure within limits
 * 3. Generates spill and reload instructions as needed
 * 4. Handles special cases like function calls and phi nodes
 * 
 * The algorithm works backwards through the control flow graph,
 * maintaining register maps at block boundaries and ensuring that
 * register pressure never exceeds the target limits.
 * 
 * The function handles complex cases including:
 * - Loop back-edges with special register preservation
 * - Function calls with argument/return register management
 * - Phi nodes with register constraints
 * - Memory operations requiring register operands
 * 
 * @param fn The function to spill
 */
void
spill(Fn *fn)
{
	Blk *b, *s1, *s2, *hd, **bp;
	int j, l, t, k, lvarg[2];
	uint n;
	BSet u[1], v[1], w[1];
	Ins *i;
	Phi *p;
	Mem *m;
	bits r;

	tmp = fn->tmp;
	ntmp = fn->ntmp;
	bsinit(u, ntmp);
	bsinit(v, ntmp);
	bsinit(w, ntmp);
	bsinit(mask[0], ntmp);
	bsinit(mask[1], ntmp);
	locs = fn->slot;
	slot4 = 0;
	slot8 = 0;
	for (t=0; t<ntmp; t++) {
		k = 0;
		if (t >= T.fpr0 && t < T.fpr0 + T.nfpr)
			k = 1;
		if (t >= Tmp0)
			k = KBASE(tmp[t].cls);
		bsset(mask[k], t);
	}

	for (bp=&fn->rpo[fn->nblk]; bp!=fn->rpo;) {
		b = *--bp;
		/* invariant: all blocks with bigger rpo got
		 * their in,out updated. */

		/* 1. find temporaries in registers at
		 * the end of the block (put them in v) */
		curi = 0;
		s1 = b->s1;
		s2 = b->s2;
		hd = 0;
		if (s1 && s1->id <= b->id)
			hd = s1;
		if (s2 && s2->id <= b->id)
		if (!hd || s2->id >= hd->id)
			hd = s2;
		if (hd) {
			/* back-edge */
			bszero(v);
			hd->gen->t[0] |= T.rglob; /* don't spill registers */
			for (k=0; k<2; k++) {
				n = k == 0 ? T.ngpr : T.nfpr;
				bscopy(u, b->out);
				bsinter(u, mask[k]);
				bscopy(w, u);
				bsinter(u, hd->gen);
				bsdiff(w, hd->gen);
				if (bscount(u) < n) {
					j = bscount(w); /* live through */
					l = hd->nlive[k];
					limit(w, n - (l - j), 0);
					bsunion(u, w);
				} else
					limit(u, n, 0);
				bsunion(v, u);
			}
		} else if (s1) {
			/* avoid reloading temporaries
			 * in the middle of loops */
			bszero(v);
			liveon(w, b, s1);
			merge(v, b, w, s1);
			if (s2) {
				liveon(u, b, s2);
				merge(v, b, u, s2);
				bsinter(w, u);
			}
			limit2(v, 0, 0, w);
		} else {
			bscopy(v, b->out);
			if (rtype(b->jmp.arg) == RCall)
				v->t[0] |= T.retregs(b->jmp.arg, 0);
		}
		for (t=Tmp0; bsiter(b->out, &t); t++)
			if (!bshas(v, t))
				slot(t);
		bscopy(b->out, v);

		/* 2. process the block instructions */
		if (rtype(b->jmp.arg) == RTmp) {
			t = b->jmp.arg.val;
			assert(KBASE(tmp[t].cls) == 0);
			lvarg[0] = bshas(v, t);
			bsset(v, t);
			bscopy(u, v);
			limit2(v, 0, 0, NULL);
			if (!bshas(v, t)) {
				if (!lvarg[0])
					bsclr(u, t);
				b->jmp.arg = slot(t);
			}
			reloads(u, v);
		}
		curi = &insb[NIns];
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			i--;
			if (regcpy(i)) {
				i = dopm(b, i, v);
				continue;
			}
			bszero(w);
			if (!req(i->to, R)) {
				assert(rtype(i->to) == RTmp);
				t = i->to.val;
				if (bshas(v, t))
					bsclr(v, t);
				else {
					/* make sure we have a reg
					 * for the result */
					assert(t >= Tmp0 && "dead reg");
					bsset(v, t);
					bsset(w, t);
				}
			}
			j = T.memargs(i->op);
			for (n=0; n<2; n++)
				if (rtype(i->arg[n]) == RMem)
					j--;
			for (n=0; n<2; n++)
				switch (rtype(i->arg[n])) {
				case RMem:
					t = i->arg[n].val;
					m = &fn->mem[t];
					if (rtype(m->base) == RTmp) {
						bsset(v, m->base.val);
						bsset(w, m->base.val);
					}
					if (rtype(m->index) == RTmp) {
						bsset(v, m->index.val);
						bsset(w, m->index.val);
					}
					break;
				case RTmp:
					t = i->arg[n].val;
					lvarg[n] = bshas(v, t);
					bsset(v, t);
					if (j-- <= 0)
						bsset(w, t);
					break;
				}
			bscopy(u, v);
			limit2(v, 0, 0, w);
			for (n=0; n<2; n++)
				if (rtype(i->arg[n]) == RTmp) {
					t = i->arg[n].val;
					if (!bshas(v, t)) {
						/* do not reload if the
						 * argument is dead
						 */
						if (!lvarg[n])
							bsclr(u, t);
						i->arg[n] = slot(t);
					}
				}
			reloads(u, v);
			if (!req(i->to, R)) {
				t = i->to.val;
				store(i->to, tmp[t].slot);
				if (t >= Tmp0)
					/* in case i->to was a
					 * dead temporary */
					bsclr(v, t);
			}
			emiti(*i);
			r = v->t[0]; /* Tmp0 is NBit */
			if (r)
				sethint(v, r);
		}
		if (b == fn->start)
			assert(v->t[0] == (T.rglob | fn->reg));
		else
			assert(v->t[0] == T.rglob);

		for (p=b->phi; p; p=p->link) {
			assert(rtype(p->to) == RTmp);
			t = p->to.val;
			if (bshas(v, t)) {
				bsclr(v, t);
				store(p->to, tmp[t].slot);
			} else if (bshas(b->in, t))
				/* only if the phi is live */
				p->to = slot(p->to.val);
		}
		bscopy(b->in, v);
		idup(b, curi, &insb[NIns]-curi);
	}

	/* align the locals to a 16 byte boundary */
	/* specific to NAlign == 3 */
	slot8 += slot8 & 3;
	fn->slot += slot8;

	if (debug['S']) {
		fprintf(stderr, "\n> Block information:\n");
		for (b=fn->start; b; b=b->link) {
			fprintf(stderr, "\t%-10s (% 5d) ", b->name, b->loop);
			dumpts(b->out, fn->tmp, stderr);
		}
		fprintf(stderr, "\n> After spilling:\n");
		printfn(fn, stderr);
	}
}
