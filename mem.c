#include "all.h"

typedef struct Range Range;
typedef struct Store Store;
typedef struct Slot Slot;

/* require use, maintains use counts */

// Where possible, turns alloca'd slots into temporaries (which are more
// amendable to optimization that storing/loading into the stack repeatedly).

/**
 * Promotes stack slots to temporaries when possible.
 * 
 * This function analyzes allocation instructions in the entry block
 * and converts stack slots to temporaries when they are used uniformly
 * (only by loads and stores of the same size). This optimization
 * makes the slots more amenable to other optimizations like load
 * elimination and slot coalescing.
 * 
 * The function only processes allocations in the entry block because
 * it's easier to determine that they're not in loops or complex
 * control flow structures.
 * 
 * @param fn The function to optimize
 */
void promote(Fn* fn) {
  /* promote uniform stack slots to temporaries */

  // Only processing the instructions in the entry block of the function, and
  // only handling the OallocN instructions. I think this is a future
  // optimization opportunity; if the allocas aren't in the entry block, then we
  // can't trivially know they're not in a loop, etc. so they don't get
  // promoted. But this means that even a trivial empty block like:
  //   function w $func() {
  //   @abc
  //   @realentry
  //       %thing =l alloc8, 8
  //       storel 123, %thing
  //   @end
  //       ret 0
  //   }
  // means the promotion of %thing won't happen, and as a result the pointless
  // store will make it into the final output.
  Blk* b = fn->start;
  for (Ins* i = b->ins; i < &b->ins[b->nins]; i++) {
    if (i->op < Oalloc || i->op > Oalloc1) {
      continue;
    }
    /* specific to NAlign == 3 */
    assert(rtype(i->to) == RTmp);
    Tmp* t = &fn->tmp[i->to.val];
    if (t->ndef != 1) {
      goto Skip;
    }
    // For each use of the stack slot, if it's used only by load and store
    // instructions (not phis, jumps, or any arithmetic, etc.) and the
    // load/store are always the same size, then it can be promoted to a
    // temporary. (Some cases that aren't optimized here can get handled later
    // in load elimination and slot coalescing though.)
    int k = -1;
    int s = -1;
    for (Use* u = t->use; u < &t->use[t->nuse]; u++) {
      if (u->type != UIns) {
        goto Skip;
      }
      Ins* ins = u->u.ins;
      if (isload(ins->op)) {
        if (s == -1 || s == loadsz(ins)) {
          s = loadsz(ins);
          continue;
        }
      }
      if (isstore(ins->op)) {
        if (req(i->to, ins->arg[1]) && !req(i->to, ins->arg[0])) {
          if (s == -1 || s == storesz(ins)) {
            if (k == -1 || k == optab[ins->op].argcls[0][0]) {
              s = storesz(ins);
              k = optab[ins->op].argcls[0][0];
              continue;
            }
          }
        }
      }
      goto Skip;
    }
    /* get rid of the alloc and replace uses */
    *i = (Ins){.op = Onop};
    t->ndef--;
    Use* ue = &t->use[t->nuse];
    for (Use* u = t->use; u != ue; u++) {
      Ins* ins = u->u.ins;
      if (isstore(ins->op)) {
        ins->cls = k;
        ins->op = Ocopy;
        ins->to = ins->arg[1];
        ins->arg[1] = R;
        t->nuse--;
        t->ndef++;
      } else {
        if (k == -1) {
          err("slot %%%s is read but never stored to",
              fn->tmp[ins->arg[0].val].name);
        }
        /* try to turn loads into copies so we
         * can eliminate them later */
        switch (ins->op) {
          case Oloadsw:
          case Oloaduw:
            if (k == Kl) {
              goto Extend;
            }
            /* fall through */
          case Oload:
            if (KBASE(k) != KBASE(ins->cls)) {
              ins->op = Ocast;
            } else {
              ins->op = Ocopy;
            }
            break;
          default:
          Extend:
            ins->op = Oextsb + (ins->op - Oloadsb);
            break;
        }
      }
    }
  Skip:;
  }
  if (debug['M']) {
    fprintf(stderr, "\n> After slot promotion:\n");
    printfn(fn, stderr);
  }
}

/* [a, b) with 0 <= a */
struct Range {
	int a, b;
};

struct Store {
	int ip;
	Ins *i;
};

struct Slot {
	int t;
	int sz;
	bits m;
	bits l;
	Range r;
	Slot *s;
	Store *st;
	int nst;
};

/**
 * Checks if a number is within a range.
 * 
 * This function checks if a number n is within the range [a, b),
 * where the range is inclusive of a but exclusive of b.
 * 
 * @param r The range to check
 * @param n The number to check
 * @return 1 if n is in the range, 0 otherwise
 */
static inline int
rin(Range r, int n)
{
	return r.a <= n && n < r.b;
}

/**
 * Checks if two ranges overlap.
 * 
 * This function determines if two ranges [a0, b0) and [a1, b1)
 * have any overlap. Two ranges overlap if they share any common
 * elements.
 * 
 * @param r0 First range
 * @param r1 Second range
 * @return 1 if the ranges overlap, 0 otherwise
 */
static inline int
rovlap(Range r0, Range r1)
{
	return r0.b && r1.b && r0.a < r1.b && r1.a < r0.b;
}

/**
 * Extends a range to include a number.
 * 
 * This function modifies a range to include the given number.
 * If the range is empty, it becomes [n, n+1). Otherwise, it
 * extends the range to include n if necessary.
 * 
 * @param r Pointer to the range to modify
 * @param n The number to include in the range
 */
static void
radd(Range *r, int n)
{
	if (!r->b)
		*r = (Range){n, n+1};
	else if (n < r->a)
		r->a = n;
	else if (n >= r->b)
		r->b = n+1;
}

/**
 * Finds the slot associated with a reference.
 * 
 * This function looks up the slot information for a given reference.
 * It uses alias analysis to determine if the reference points to a
 * local variable and returns the corresponding slot if found.
 * 
 * @param ps Output parameter for the slot pointer
 * @param off Output parameter for the offset within the slot
 * @param r The reference to look up
 * @param fn The function containing the reference
 * @param sl Array of slots
 * @return 1 if a slot was found, 0 otherwise
 */
static int
slot(Slot **ps, int64_t *off, Ref r, Fn *fn, Slot *sl)
{
	Alias a;
	Tmp *t;

	getalias(&a, r, fn);
	if (a.type != ALoc)
		return 0;
	t = &fn->tmp[a.base];
	if (t->visit < 0)
		return 0;
	*off = a.offset;
	*ps = &sl[t->visit];
	return 1;
}

/**
 * Records a load operation on a slot.
 * 
 * This function updates the slot information to reflect a load
 * operation. It marks the loaded bits as live and updates the
 * slot's range to include the instruction position.
 * 
 * @param r The reference being loaded
 * @param x Bit mask indicating which bits are loaded
 * @param ip Instruction position
 * @param fn The function containing the load
 * @param sl Array of slots
 */
static void
load(Ref r, bits x, int ip, Fn *fn, Slot *sl)
{
	int64_t off;
	Slot *s;

	if (slot(&s, &off, r, fn, sl)) {
		s->l |= x << off;
		s->l &= s->m;
		if (s->l)
			radd(&s->r, ip);
	}
}

/**
 * Records a store operation on a slot.
 * 
 * This function updates the slot information to reflect a store
 * operation. It marks the stored bits as modified and records
 * the store instruction for later analysis.
 * 
 * @param r The reference being stored to
 * @param x Bit mask indicating which bits are stored
 * @param ip Instruction position
 * @param i The store instruction
 * @param fn The function containing the store
 * @param sl Array of slots
 */
static void
store(Ref r, bits x, int ip, Ins *i, Fn *fn, Slot *sl)
{
	int64_t off;
	Slot *s;

	if (slot(&s, &off, r, fn, sl)) {
		if (s->l) {
			radd(&s->r, ip);
			s->l &= ~(x << off);
		} else {
			vgrow(&s->st, ++s->nst);
			s->st[s->nst-1].ip = ip;
			s->st[s->nst-1].i = i;
		}
	}
}

/**
 * Compares two slots for sorting.
 * 
 * This function is used as a comparison function for qsort to order
 * slots by size (larger slots first) and then by range start position.
 * This ordering helps with slot coalescing by processing larger slots
 * first.
 * 
 * @param pa Pointer to first slot
 * @param pb Pointer to second slot
 * @return Negative if a < b, 0 if equal, positive if a > b
 */
static int
scmp(const void *pa, const void *pb)
{
	Slot *a, *b;

	a = (Slot *)pa, b = (Slot *)pb;
	if (a->sz != b->sz)
		return b->sz - a->sz;
	return a->r.a - b->r.a;
}

/**
 * Updates the maximum reverse post-order number for a loop.
 * 
 * This function is used during loop analysis to track the maximum
 * reverse post-order number within a loop. It's called by the
 * loop iteration function to build loop information.
 * 
 * @param hd The loop header block
 * @param b The block being processed
 */
static void
maxrpo(Blk *hd, Blk *b)
{
	if (hd->loop < (int)b->id)
		hd->loop = b->id;
}

/**
 * Performs slot coalescing to minimize stack usage.
 * 
 * This function analyzes the liveness of stack slots and attempts
 * to coalesce slots that have non-overlapping live ranges. This
 * optimization reduces the total stack space required by the function
 * by allowing multiple variables to share the same stack location.
 * 
 * The algorithm performs a one-pass liveness analysis and then
 * sorts slots by size and range to find coalescing opportunities.
 * 
 * @param fn The function to optimize
 */
void
coalesce(Fn *fn)
{
	Range r, *br;
	Slot *s, *s0, *sl;
	Blk *b, **ps, *succ[3];
	Ins *i, **bl;
	Use *u;
	Tmp *t, *ts;
	Ref *arg;
	bits x;
	int64_t off0, off1;
	int n, m, ip, sz, nsl, nbl, *stk;
	uint total, freed, fused;

	/* minimize the stack usage
	 * by coalescing slots
	 */
	nsl = 0;
	sl = vnew(0, sizeof sl[0], PHeap);
	for (n=Tmp0; n<fn->ntmp; n++) {
		t = &fn->tmp[n];
		t->visit = -1;
		if (t->alias.type == ALoc)
		if (t->alias.slot == &t->alias)
		if (t->bid == fn->start->id)
		if (t->alias.u.loc.sz != -1) {
			t->visit = nsl;
			vgrow(&sl, ++nsl);
			s = &sl[nsl-1];
			s->t = n;
			s->sz = t->alias.u.loc.sz;
			s->m = t->alias.u.loc.m;
			s->s = 0;
			s->st = vnew(0, sizeof s->st[0], PHeap);
			s->nst = 0;
		}
	}

	/* one-pass liveness analysis */
	for (b=fn->start; b; b=b->link)
		b->loop = -1;
	loopiter(fn, maxrpo);
	nbl = 0;
	bl = vnew(0, sizeof bl[0], PHeap);
	br = emalloc(fn->nblk * sizeof br[0]);
	ip = INT_MAX - 1;
	for (n=fn->nblk-1; n>=0; n--) {
		b = fn->rpo[n];
		succ[0] = b->s1;
		succ[1] = b->s2;
		succ[2] = 0;
		br[n].b = ip--;
		for (s=sl; s<&sl[nsl]; s++) {
			s->l = 0;
			for (ps=succ; *ps; ps++) {
				m = (*ps)->id;
				if (m > n && rin(s->r, br[m].a)) {
					s->l = s->m;
					radd(&s->r, ip);
				}
			}
		}
		if (b->jmp.type == Jretc)
			load(b->jmp.arg, -1, --ip, fn, sl);
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			--i;
			arg = i->arg;
			if (i->op == Oargc) {
				load(arg[1], -1, --ip, fn, sl);
			}
			if (isload(i->op)) {
				x = BIT(loadsz(i)) - 1;
				load(arg[0], x, --ip, fn, sl);
			}
			if (isstore(i->op)) {
				x = BIT(storesz(i)) - 1;
				store(arg[1], x, ip--, i, fn, sl);
			}
			if (i->op == Oblit0) {
				assert((i+1)->op == Oblit1);
				assert(rtype((i+1)->arg[0]) == RInt);
				sz = abs(rsval((i+1)->arg[0]));
				x = sz >= NBit ? (bits)-1 : BIT(sz) - 1;
				store(arg[1], x, ip--, i, fn, sl);
				load(arg[0], x, ip, fn, sl);
				vgrow(&bl, ++nbl);
				bl[nbl-1] = i;
			}
		}
		for (s=sl; s<&sl[nsl]; s++)
			if (s->l) {
				radd(&s->r, ip);
				if (b->loop != -1) {
					assert(b->loop >= n);
					radd(&s->r, br[b->loop].b - 1);
				}
			}
		br[n].a = ip;
	}
	free(br);

	/* kill dead stores */
	for (s=sl; s<&sl[nsl]; s++)
		for (n=0; n<s->nst; n++)
			if (!rin(s->r, s->st[n].ip)) {
				i = s->st[n].i;
				if (i->op == Oblit0)
					*(i+1) = (Ins){.op = Onop};
				*i = (Ins){.op = Onop};
			}

	/* kill slots with an empty live range */
	total = 0;
	freed = 0;
	stk = vnew(0, sizeof stk[0], PHeap);
	n = 0;
	for (s=s0=sl; s<&sl[nsl]; s++) {
		total += s->sz;
		if (!s->r.b) {
			vfree(s->st);
			vgrow(&stk, ++n);
			stk[n-1] = s->t;
			freed += s->sz;
		} else
			*s0++ = *s;
	}
	nsl = s0-sl;
	if (debug['M']) {
		fputs("\n> Slot coalescing:\n", stderr);
		if (n) {
			fputs("\tkill [", stderr);
			for (m=0; m<n; m++)
				fprintf(stderr, " %%%s",
					fn->tmp[stk[m]].name);
			fputs(" ]\n", stderr);
		}
	}
	while (n--) {
		t = &fn->tmp[stk[n]];
		assert(t->ndef == 1 && t->def);
		i = t->def;
		if (isload(i->op)) {
			i->op = Ocopy;
			i->arg[0] = UNDEF;
			continue;
		}
		*i = (Ins){.op = Onop};
		for (u=t->use; u<&t->use[t->nuse]; u++) {
			if (u->type == UJmp) {
				b = fn->rpo[u->bid];
				assert(isret(b->jmp.type));
				b->jmp.type = Jret0;
				b->jmp.arg = R;
				continue;
			}
			assert(u->type == UIns);
			i = u->u.ins;
			if (!req(i->to, R)) {
				assert(rtype(i->to) == RTmp);
				vgrow(&stk, ++n);
				stk[n-1] = i->to.val;
			} else if (isarg(i->op)) {
				assert(i->op == Oargc);
				i->arg[1] = CON_Z;  /* crash */
			} else {
				if (i->op == Oblit0)
					*(i+1) = (Ins){.op = Onop};
				*i = (Ins){.op = Onop};
			}
		}
	}
	vfree(stk);

	/* fuse slots by decreasing size */
	qsort(sl, nsl, sizeof *sl, scmp);
	fused = 0;
	for (n=0; n<nsl; n++) {
		s0 = &sl[n];
		if (s0->s)
			continue;
		s0->s = s0;
		r = s0->r;
		for (s=s0+1; s<&sl[nsl]; s++) {
			if (s->s || !s->r.b)
				goto Skip;
			if (rovlap(r, s->r))
				/* O(n); can be approximated
				 * by 'goto Skip;' if need be
				 */
				for (m=n; &sl[m]<s; m++)
					if (sl[m].s == s0)
					if (rovlap(sl[m].r, s->r))
						goto Skip;
			radd(&r, s->r.a);
			radd(&r, s->r.b - 1);
			s->s = s0;
			fused += s->sz;
		Skip:;
		}
	}

	/* substitute fused slots */
	for (s=sl; s<&sl[nsl]; s++) {
		t = &fn->tmp[s->t];
		/* the visit link is stale,
		 * reset it before the slot()
		 * calls below
		 */
		t->visit = s-sl;
		assert(t->ndef == 1 && t->def);
		if (s->s == s)
			continue;
		*t->def = (Ins){.op = Onop};
		ts = &fn->tmp[s->s->t];
		assert(t->bid == ts->bid);
		if (t->def < ts->def) {
			/* make sure the slot we
			 * selected has a def that
			 * dominates its new uses
			 */
			*t->def = *ts->def;
			*ts->def = (Ins){.op = Onop};
			ts->def = t->def;
		}
		for (u=t->use; u<&t->use[t->nuse]; u++) {
			if (u->type == UJmp) {
				b = fn->rpo[u->bid];
				b->jmp.arg = TMP(s->s->t);
				continue;
			}
			assert(u->type == UIns);
			arg = u->u.ins->arg;
			for (n=0; n<2; n++)
				if (req(arg[n], TMP(s->t)))
					arg[n] = TMP(s->s->t);
		}
	}

	/* fix newly overlapping blits */
	for (n=0; n<nbl; n++) {
		i = bl[n];
		if (i->op == Oblit0)
		if (slot(&s, &off0, i->arg[0], fn, sl))
		if (slot(&s0, &off1, i->arg[1], fn, sl))
		if (s->s == s0->s) {
			if (off0 < off1) {
				sz = rsval((i+1)->arg[0]);
				assert(sz >= 0);
				(i+1)->arg[0] = INT(-sz);
			} else if (off0 == off1) {
				*i = (Ins){.op = Onop};
				*(i+1) = (Ins){.op = Onop};
			}
		}
	}
	vfree(bl);

	if (debug['M']) {
		for (s0=sl; s0<&sl[nsl]; s0++) {
			if (s0->s != s0)
				continue;
			fprintf(stderr, "\tfuse (% 3db) [", s0->sz);
			for (s=s0; s<&sl[nsl]; s++) {
				if (s->s != s0)
					continue;
				fprintf(stderr, " %%%s", fn->tmp[s->t].name);
				if (s->r.b)
					fprintf(stderr, "[%d,%d)",
						s->r.a-ip, s->r.b-ip);
				else
					fputs("{}", stderr);
			}
			fputs(" ]\n", stderr);
		}
		fprintf(stderr, "\tsums %u/%u/%u (killed/fused/total)\n\n",
			freed, fused, total);
		printfn(fn, stderr);
	}

	for (s=sl; s<&sl[nsl]; s++)
		vfree(s->st);
	vfree(sl);
}
