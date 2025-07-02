#include "all.h"

/**
 * Creates a new basic block.
 * 
 * Allocates and initializes a new basic block structure with empty
 * instruction and predecessor arrays. The block is allocated from
 * the function's memory pool.
 * 
 * @return Pointer to the newly created block
 */
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

/**
 * Adds a predecessor block to a basic block.
 * 
 * Adds a block to the predecessor list of another block and updates
 * the predecessor count. This is used to build the control flow graph
 * by establishing predecessor relationships between blocks.
 * 
 * @param bp The predecessor block to add
 * @param b The block to add the predecessor to
 */
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
/**
 * Builds the predecessor lists for all blocks in a function.
 * 
 * This function constructs the control flow graph by analyzing the
 * successor relationships (s1/s2) of each block and building the
 * corresponding predecessor lists. It handles:
 * - Fallthrough edges (s1 set, s2 unset)
 * - Unconditional jumps (s1 set to target, s2 unset)
 * - Conditional jumps (s1 and s2 set to true/false branches)
 * 
 * @param f The function to build predecessors for
 */
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
/**
 * Performs a post-order traversal of the control flow graph.
 * 
 * Recursively visits blocks in post-order, assigning block IDs based on
 * the traversal order. The root of the walk gets the highest block ID.
 * This function also counts the total number of reachable blocks.
 * 
 * @param b The current block to process
 * @param npo Pointer to the counter for post-order numbering
 */
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

/**
 * Computes the reverse post-order (RPO) numbering for all blocks.
 * 
 * This function performs a post-order traversal of the control flow graph
 * and assigns block IDs in reverse post-order. It also removes unreachable
 * blocks from the function and builds the RPO array. The RPO ordering is
 * important for many compiler optimizations.
 * 
 * @param f The function to compute RPO for
 */
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
/*-*
 * Builds the complete control flow graph for a function.
 * 
 * This function performs the main control flow graph construction by:
 * - Computing reverse post-order numbering for all blocks
 * - Building predecessor lists for all blocks
 * - Removing unreachable blocks
 * 
 * The resulting CFG is used by many subsequent optimization passes.
 * 
 * @param f The function to build the CFG for
 */
void fillcfg(Fn* f) {
  fill_rpo_of_function(f);
  fill_preds_of_function(f);
  //fix_phis_of_function(f);
}

/* for dominators computation, read
 * "A Simple, Fast Dominance Algorithm"
 * by K. Cooper, T. Harvey, and K. Kennedy.
 */

/**
 * Finds the intersection of two blocks in the dominator tree.
 * 
 * This function implements the intersection operation used in the
 * iterative dominator algorithm. It finds the closest common ancestor
 * of two blocks in the dominator tree by walking up the tree until
 * a common dominator is found.
 * 
 * @param b1 First block
 * @param b2 Second block
 * @return The closest common dominator of b1 and b2
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

/**
 * Computes the dominator tree for a function.
 * 
 * This function implements the iterative dominator algorithm described
 * in "A Simple, Fast Dominance Algorithm" by Cooper, Harvey, and Kennedy.
 * It computes the immediate dominator (idom) for each block and builds
 * the dominator tree structure. The algorithm iterates until no changes
 * occur in the dominator relationships.
 * 
 * @param fn The function to compute dominators for
 */
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

/**
 * Checks if one block strictly dominates another.
 * 
 * A block b1 strictly dominates b2 if b1 dominates b2 and b1 != b2.
 * This function uses the dominator tree to efficiently check this
 * relationship by walking up the dominator tree.
 * 
 * @param b1 The potential dominator block
 * @param b2 The block to check for strict domination
 * @return 1 if b1 strictly dominates b2, 0 otherwise
 */
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

/**
 * Checks if one block dominates another.
 * 
 * A block b1 dominates b2 if b1 == b2 or b1 strictly dominates b2.
 * This function checks for the dominance relationship using the
 * dominator tree.
 * 
 * @param b1 The potential dominator block
 * @param b2 The block to check for domination
 * @return 1 if b1 dominates b2, 0 otherwise
 */
int
dom(Blk *b1, Blk *b2)
{
	return b1 == b2 || sdom(b1, b2);
}

/**
 * Adds a block to the dominance frontier of another block.
 * 
 * Adds a block to the dominance frontier list of another block,
 * ensuring no duplicates are added. The dominance frontier is used
 * in SSA construction to determine where phi nodes are needed.
 * 
 * @param a The block whose dominance frontier to add to
 * @param b The block to add to the dominance frontier
 */
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
/*
 * Computes the dominance frontier for all blocks in a function.
 * 
 * The dominance frontier of a block b is the set of blocks where control
 * can arrive from both b and another block not strictly dominated by b.
 * This is used in SSA construction to determine where phi nodes are needed.
 * 
 * The algorithm walks up the dominator tree from each block to its root,
 * adding the block's successors to the dominance frontier of each ancestor
 * until reaching a block that dominates the successor.
 * 
 * @param fn The function to compute dominance frontiers for
 */
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

/**
 * Marks blocks that are part of a loop with a given header.
 * 
 * This function recursively marks all blocks that are part of a loop
 * starting from the given header block. It uses a depth-first search
 * to traverse the control flow graph and mark all blocks reachable
 * from the header through back edges.
 * 
 * @param hd The loop header block
 * @param b The current block being processed
 * @param f Function to call for each block in the loop
 */
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

/**
 * Identifies and processes all loops in a function.
 * 
 * This function identifies all loops in the control flow graph and
 * calls a user-provided function for each loop. A loop is identified
 * when a block has a predecessor that comes later in the reverse
 * post-order traversal (indicating a back edge).
 * 
 * @param fn The function to analyze for loops
 * @param f Function to call for each loop (header, body)
 */
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
/**
 * Computes the depth of each block in the dominator tree.
 * 
 * This function assigns a depth value to each block based on its
 * position in the dominator tree. The start block has depth 0,
 * and each child has depth one more than its immediate dominator.
 * This information is useful for efficient least common ancestor
 * computations.
 * 
 * @param fn The function to compute depths for
 */
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
/**
 * Finds the least common ancestor of two blocks in the dominator tree.
 * 
 * This function finds the closest common ancestor of two blocks in
 * the dominator tree. It uses the depth information to efficiently
 * walk up the tree from both blocks until they meet at their least
 * common ancestor.
 * 
 * @param b1 First block
 * @param b2 Second block
 * @return The least common ancestor of b1 and b2 in the dominator tree
 */
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

/**
 * Marks a block as part of a multiple-entry loop.
 * 
 * This function is called during loop analysis to mark blocks that
 * are part of loops with multiple entry points. It increases the
 * loop counter for the block to indicate it's part of a complex loop.
 * 
 * @param hd The loop header (unused in this implementation)
 * @param b The block to mark as part of a multiple-entry loop
 */
void
multloop(Blk *hd, Blk *b)
{
	(void)hd;
	b->loop *= 10;
}

/**
 * Computes loop information for all blocks in a function.
 * 
 * This function analyzes the control flow graph to identify loops
 * and mark blocks with loop information. It uses the loopiter
 * function to identify all loops and mark blocks accordingly.
 * 
 * @param fn The function to analyze for loops
 */
void
fillloop(Fn *fn)
{
	Blk *b;

	for (b=fn->start; b; b=b->link)
		b->loop = 1;
	loopiter(fn, multloop);
}

/**
 * Performs union-find path compression for jump simplification.
 * 
 * This function implements the find operation of a union-find data structure
 * with path compression. It's used during jump simplification to efficiently
 * track which blocks have been merged together.
 * 
 * @param pb Pointer to the block to find the representative for
 * @param uf Union-find array mapping block IDs to their representatives
 */
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
/**
 * Simplifies jumps in the control flow graph.
 * 
 * This function performs several jump optimizations:
 * - Converts return instructions to jumps to a common return block
 * - Eliminates empty blocks by redirecting jumps through them
 * - Merges blocks that have identical successors
 * - Simplifies conditional jumps where both branches go to the same target
 * 
 * The function requires reverse post-order numbering and no phi instructions.
 * It may break the control flow graph structure, which is later repaired.
 * 
 * @param fn The function to optimize
 */
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

/**
 * Recursively checks if a block can reach another block.
 * 
 * This function performs a depth-first search to determine if there
 * is a path from the current block to the target block. It uses the
 * visit field to avoid cycles in the control flow graph.
 * 
 * @param b The current block being explored
 * @param to The target block to reach
 * @return 1 if b can reach to, 0 otherwise
 */
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
/**
 * Checks if one block can reach another block in the control flow graph.
 * 
 * This function determines if there is a path from block b to block to
 * by performing a depth-first search. It clears the visit field for all
 * blocks after the search to prepare for future calls.
 * 
 * @param fn The function containing the blocks
 * @param b The source block
 * @param to The target block
 * @return 1 if b can reach to, 0 otherwise
 */
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
/**
 * Checks if a block can reach another block without going through an excluded block.
 * 
 * This function determines if there is a path from block b to block to
 * that does not pass through the excluded block. It's used in dominance
 * frontier computation and other control flow analyses.
 * 
 * @param fn The function containing the blocks
 * @param b The source block
 * @param to The target block
 * @param excl The block to avoid in the path
 * @return 1 if b can reach to without going through excl, 0 otherwise
 */
int
reachesnotvia(Fn *fn, Blk *b, Blk *to, Blk *excl)
{
	excl->visit = 1;
	return reaches(fn, b, to);
}
