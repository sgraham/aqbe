#include "all.h"

Blk *
newblk(void)
{
	static Blk z;
	Blk *b;

	b = alloc(sizeof *b);
	*b = z;
	b->ins = vnew(0, sizeof b->ins[0], PFn);
	b->pred = vnew(0, sizeof b->pred[0], PFn);
	return b;
}

// It looks like this squashes out any dead blocks, but I'm not sure how that
// can happen right after parse, as I think the phi instruction would fail if
// the predecessors aren't matched.
// XXX try to write a test where this is needed.
// XXX fillcfg() is used multiple times in the main function processing, so it
// must be possible to break the invariant elsewhere. There's no test that fails
// currently without this function though.
#if 0
static void fix_phis_of_function(Fn* f) {
  for (Blk* b = f->start; b; b = b->link) {
    assert(b->id < f->nblk);
    for (Phi* p = b->phi; p; p = p->link) {
      uint n0 = 0;
      for (uint n = 0; n < p->narg; n++) {
        if (p->blk[n]->id != -1u) {
          p->blk[n0] = p->blk[n];
          p->arg[n0] = p->arg[n];
          n0++;
        }
      }
      assert(n0 > 0);
      p->narg = n0;
    }
  }
}
#endif

static void addpred(Blk* bp, Blk* b) {
  vgrow(&b->pred, ++b->npred);
  b->pred[b->npred - 1] = bp;
}

// Each block has a vector of predecessor blocks.
// s1/s2 for each block is filled out during parse. 's' is maybe "subsequent" or
// "successor"? and indicates the edges out of the block.
// - In the case of fallthrough, s1 will be set to the following block, and s2
// will be unset.
// - For an unconditional jump, s1 will be set to the target, s2 will be unset.
// - For a conditional jump, s1 and s2 will be set to the true and false arms.
void fill_preds_of_function(Fn* f) {
  for (Blk* b = f->start; b; b = b->link) {
    b->npred = 0;
  }
  // For each block in the function, add this block to s1's and (if s1 is
  // different than s2) to s2's as one of its predecessors. (i.e. the block
  // we're walking is the one being added, we're building a back-list, not
  // building the list for |b| in this loop).
  for (Blk* b = f->start; b; b = b->link) {
    if (b->s1) {
      addpred(b, b->s1);
    }
    if (b->s2 && b->s2 != b->s1) {
      addpred(b, b->s2);
    }
  }
}

// Recurse through blocks in post-order. The root of the walk will end up with
// the highest block id. Also count the total number of (reachable) blocks in
// the function to use for allocating the rpo vector.
static void post_order_walk_impl(Blk* b, uint* npo) {
  if (!b || b->id != -1u) {
    return;
  }
  b->id = 0;  // Don't visit again, but id isn't assigned until later below.
  Blk* s1 = b->s1;
  Blk* s2 = b->s2;
  if (s1 && s2 && s1->loop > s2->loop) {  // XXX: what is loop?
    s1 = b->s2;
    s2 = b->s1;
  }
  post_order_walk_impl(s1, npo);
  post_order_walk_impl(s2, npo);
  b->id = (*npo)++;
}

static void fill_rpo_of_function(Fn* f) {
  // Reset all block ids to -1 to mark as unhandled.
  for (Blk* b = f->start; b; b = b->link) {
    b->id = -1u;
  }
  f->nblk = 0;
  post_order_walk_impl(f->start, &f->nblk);
  vgrow(&f->rpo, f->nblk);
  for (Blk** p = &f->start, *b = NULL; (b = *p);) {
    if (b->id == -1u) {
      // If the block wasn't visited by the post-order walk, then it's dead,
      // just skip to the next one in the block list.
      *p = b->link;
    } else {
      // Otherwise, invert the id. Latest visited were given the highest ids
      // during the walk, now the first visited will instead have id (and index)
      // 0. XXX: Just assign in order during walk? (would have to be +1 biased
      // to maintain 0 as a marker during walk, but would be clearer than
      // inverting)
      b->id = f->nblk - b->id - 1;
      // Stash the block in order into the rpo vector, and advance.
      f->rpo[b->id] = b;
      p = &b->link;  // XXX investigate why advance is slightly different here
                     // vs. above
    }
  }
}

/* fill rpo, preds; prune dead blks */
void fillcfg(Fn* f) {
  fill_rpo_of_function(f);
  fill_preds_of_function(f);
  //fix_phis_of_function(f);
}

/* for dominators computation, read
 * "A Simple, Fast Dominance Algorithm"
 * by K. Cooper, T. Harvey, and K. Kennedy.
 */

static Blk *
inter(Blk *b1, Blk *b2)
{
	Blk *bt;

	if (b1 == 0)
		return b2;
	while (b1 != b2) {
		if (b1->id < b2->id) {
			bt = b1;
			b1 = b2;
			b2 = bt;
		}
		while (b1->id > b2->id) {
			b1 = b1->idom;
			assert(b1);
		}
	}
	return b1;
}

void
filldom(Fn *fn)
{
	Blk *b, *d;
	int ch;
	uint n, p;

	for (b=fn->start; b; b=b->link) {
		b->idom = 0;
		b->dom = 0;
		b->dlink = 0;
	}
	do {
		ch = 0;
		for (n=1; n<fn->nblk; n++) {
			b = fn->rpo[n];
			d = 0;
			for (p=0; p<b->npred; p++)
				if (b->pred[p]->idom
				||  b->pred[p] == fn->start)
					d = inter(d, b->pred[p]);
			if (d != b->idom) {
				ch++;
				b->idom = d;
			}
		}
	} while (ch);
	for (b=fn->start; b; b=b->link)
		if ((d=b->idom)) {
			assert(d != b);
			b->dlink = d->dom;
			d->dom = b;
		}
}

int
sdom(Blk *b1, Blk *b2)
{
	assert(b1 && b2);
	if (b1 == b2)
		return 0;
	while (b2->id > b1->id)
		b2 = b2->idom;
	return b1 == b2;
}

int
dom(Blk *b1, Blk *b2)
{
	return b1 == b2 || sdom(b1, b2);
}

static void
addfron(Blk *a, Blk *b)
{
	uint n;

	for (n=0; n<a->nfron; n++)
		if (a->fron[n] == b)
			return;
	if (!a->nfron)
		a->fron = vnew(++a->nfron, sizeof a->fron[0], PFn);
	else
		vgrow(&a->fron, ++a->nfron);
	a->fron[a->nfron-1] = b;
}

/* fill the dominance frontier */
// Computes the dominance frontier for each block in the function.
// The dominance frontier of a block b is the set of blocks where control can
// arrive from both b and another block not strictly dominated by b.
// This is used in SSA construction to determine where phi nodes are needed.
void fillfron(Fn* fn) {
  // First, clear the dominance frontier for all blocks.
  for (Blk* b = fn->start; b; b = b->link) {
    b->nfron = 0;
  }

  // For each block, walk up the dominator tree from the block to the root,
  // adding the block's successors to the dominance frontier of each ancestor
  // until reaching a block that dominates the successor.
  // This ensures that the dominance frontier is correctly populated for SSA.
  for (Blk* b = fn->start; b; b = b->link) {
    if (b->s1) {
      for (Blk* a = b; !sdom(a, b->s1); a = a->idom) {
        addfron(a, b->s1);
      }
    }
    if (b->s2) {
      for (Blk* a = b; !sdom(a, b->s2); a = a->idom) {
        addfron(a, b->s2);
      }
    }
  }
}

static void
loopmark(Blk *hd, Blk *b, void f(Blk *, Blk *))
{
	uint p;

	if (b->id < hd->id || b->visit == hd->id)
		return;
	b->visit = hd->id;
	f(hd, b);
	for (p=0; p<b->npred; ++p)
		loopmark(hd, b->pred[p], f);
}

void
loopiter(Fn *fn, void f(Blk *, Blk *))
{
	uint n, p;
	Blk *b;

	for (b=fn->start; b; b=b->link)
		b->visit = -1u;
	for (n=0; n<fn->nblk; ++n) {
		b = fn->rpo[n];
		for (p=0; p<b->npred; ++p)
			if (b->pred[p]->id >= n)
				loopmark(b, b->pred[p], f);
	}
}

/* dominator tree depth */
void
filldepth(Fn *fn)
{
	Blk *b, *d;
	int depth;

	for (b=fn->start; b; b=b->link)
		b->depth = -1;

	fn->start->depth = 0;

	for (b=fn->start; b; b=b->link) {
		if (b->depth != -1)
			continue;
		depth = 1;
		for (d=b->idom; d->depth==-1; d=d->idom)
			depth++;
		depth += d->depth;
		b->depth = depth;
		for (d=b->idom; d->depth==-1; d=d->idom)
			d->depth = --depth;
	}
}

/* least common ancestor in dom tree */
Blk *
lca(Blk *b1, Blk *b2)
{
	if (!b1)
		return b2;
	if (!b2)
		return b1;
	while (b1->depth > b2->depth)
		b1 = b1->idom;
	while (b2->depth > b1->depth)
		b2 = b2->idom;
	while (b1 != b2) {
		b1 = b1->idom;
		b2 = b2->idom;
	}
	return b1;
}

void
multloop(Blk *hd, Blk *b)
{
	(void)hd;
	b->loop *= 10;
}

void
fillloop(Fn *fn)
{
	Blk *b;

	for (b=fn->start; b; b=b->link)
		b->loop = 1;
	loopiter(fn, multloop);
}

static void
uffind(Blk **pb, Blk **uf)
{
	Blk **pb1;

	pb1 = &uf[(*pb)->id];
	if (*pb1) {
		uffind(pb1, uf);
		*pb = *pb1;
	}
}

/* requires rpo and no phis, breaks cfg */
void
simpljmp(Fn *fn)
{

	Blk **uf; /* union-find */
	Blk **p, *b, *ret;

	ret = newblk();
	ret->id = fn->nblk++;
	ret->jmp.type = Jret0;
	uf = emalloc(fn->nblk * sizeof uf[0]);
	for (b=fn->start; b; b=b->link) {
		assert(!b->phi);
		if (b->jmp.type == Jret0) {
			b->jmp.type = Jjmp;
			b->s1 = ret;
		}
		if (b->nins == 0)
		if (b->jmp.type == Jjmp) {
			uffind(&b->s1, uf);
			if (b->s1 != b)
				uf[b->id] = b->s1;
		}
	}
	for (p=&fn->start; (b=*p); p=&b->link) {
		if (b->s1)
			uffind(&b->s1, uf);
		if (b->s2)
			uffind(&b->s2, uf);
		if (b->s1 && b->s1 == b->s2) {
			b->jmp.type = Jjmp;
			b->s2 = 0;
		}
	}
	*p = ret;
	free(uf);
}

static int
reachrec(Blk *b, Blk *to)
{
	if (b == to)
		return 1;
	if (!b || b->visit)
		return 0;

	b->visit = 1;
	if (reachrec(b->s1, to))
		return 1;
	if (reachrec(b->s2, to))
		return 1;

	return 0;
}

/* Blk.visit needs to be clear at entry */
int
reaches(Fn *fn, Blk *b, Blk *to)
{
	int r;

	assert(to);
	r = reachrec(b, to);
	for (b=fn->start; b; b=b->link)
		b->visit = 0;
	return r;
}

/* can b reach 'to' not through excl
 * Blk.visit needs to be clear at entry */
int
reachesnotvia(Fn *fn, Blk *b, Blk *to, Blk *excl)
{
	excl->visit = 1;
	return reaches(fn, b, to);
}
