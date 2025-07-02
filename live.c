#include "all.h"

/**
 * Computes the liveness information for a block based on its successor.
 * 
 * This function calculates which temporaries are live at the entry of a block
 * based on the liveness information of its successor block. It handles:
 * - Copying the successor's live-in set as a starting point
 * - Removing temporaries that are defined by phi nodes in the successor
 * - Adding temporaries that are used as phi arguments from the current block
 * 
 * The function is a key component of the backward dataflow analysis used
 * in liveness computation. It ensures that phi nodes are handled correctly
 * by considering both their definitions and their uses.
 * 
 * @param v Bit set to store the computed liveness information
 * @param b The current block being analyzed
 * @param s The successor block whose liveness information is used
 */
void
liveon(BSet *v, Blk *b, Blk *s)
{
	Phi *p;
	uint a;

	bscopy(v, s->in);
	for (p=s->phi; p; p=p->link)
		if (rtype(p->to) == RTmp)
			bsclr(v, p->to.val);
	for (p=s->phi; p; p=p->link)
		for (a=0; a<p->narg; a++)
			if (p->blk[a] == b)
			if (rtype(p->arg[a]) == RTmp) {
				bsset(v, p->arg[a].val);
				bsset(b->gen, p->arg[a].val);
			}
}

/**
 * Adds a reference to the live set of a block.
 * 
 * This helper function adds a temporary reference to the live set of a block
 * and updates the live count for the appropriate register class. It only
 * adds temporaries that aren't already in the live set to avoid double-counting.
 * 
 * The function is used during the backward scan of instructions to build
 * the complete liveness information for a block.
 * 
 * @param r The reference to add to the live set
 * @param b The block whose live set is being updated
 * @param nlv Array of live counts for each register class
 * @param tmp Array of temporary information
 */
static void
bset(Ref r, Blk *b, int *nlv, Tmp *tmp)
{

	if (rtype(r) != RTmp)
		return;
	bsset(b->gen, r.val);
	if (!bshas(b->in, r.val)) {
		nlv[KBASE(tmp[r.val].cls)]++;
		bsset(b->in, r.val);
	}
}

/* liveness analysis
 * requires rpo computation */
/**
 * Performs liveness analysis for an entire function.
 * 
 * This function implements a backward dataflow analysis to determine
 * which temporaries are live at each point in the function. Liveness
 * analysis is crucial for register allocation and optimization.
 * 
 * The analysis works by:
 * 1. Initializing all blocks with empty live sets
 * 2. Iteratively propagating liveness information backward through the CFG
 * 3. Handling special cases like function calls and phi nodes
 * 4. Computing live counts for register allocation
 * 
 * The function handles complex cases including:
 * - Function calls with argument and return register management
 * - Memory operations with base and index register tracking
 * - Phi nodes with proper liveness propagation
 * - Global register usage and caller-saved register handling
 * 
 * The analysis requires that the function's blocks are in reverse
 * post-order (RPO) for efficient convergence.
 * 
 * @param f The function to analyze
 */
void
filllive(Fn *f)
{
	Blk *b;
	Ins *i;
	int k, t, m[2], n, chg, nlv[2];
	BSet u[1], v[1];
	Mem *ma;

	bsinit(u, f->ntmp);
	bsinit(v, f->ntmp);
	for (b=f->start; b; b=b->link) {
		bsinit(b->in, f->ntmp);
		bsinit(b->out, f->ntmp);
		bsinit(b->gen, f->ntmp);
	}
	chg = 1;
Again:
	for (n=f->nblk-1; n>=0; n--) {
		b = f->rpo[n];

		bscopy(u, b->out);
		if (b->s1) {
			liveon(v, b, b->s1);
			bsunion(b->out, v);
		}
		if (b->s2) {
			liveon(v, b, b->s2);
			bsunion(b->out, v);
		}
		chg |= !bsequal(b->out, u);

		memset(nlv, 0, sizeof nlv);
		b->out->t[0] |= T.rglob;
		bscopy(b->in, b->out);
		for (t=0; bsiter(b->in, &t); t++)
			nlv[KBASE(f->tmp[t].cls)]++;
		if (rtype(b->jmp.arg) == RCall) {
			assert((int)bscount(b->in) == T.nrglob &&
				b->in->t[0] == T.rglob);
			b->in->t[0] |= T.retregs(b->jmp.arg, nlv);
		} else
			bset(b->jmp.arg, b, nlv, f->tmp);
		for (k=0; k<2; k++)
			b->nlive[k] = nlv[k];
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			if ((--i)->op == Ocall && rtype(i->arg[1]) == RCall) {
				b->in->t[0] &= ~T.retregs(i->arg[1], m);
				for (k=0; k<2; k++) {
					nlv[k] -= m[k];
					/* caller-save registers are used
					 * by the callee, in that sense,
					 * right in the middle of the call,
					 * they are live: */
					nlv[k] += T.nrsave[k];
					if (nlv[k] > b->nlive[k])
						b->nlive[k] = nlv[k];
				}
				b->in->t[0] |= T.argregs(i->arg[1], m);
				for (k=0; k<2; k++) {
					nlv[k] -= T.nrsave[k];
					nlv[k] += m[k];
				}
			}
			if (!req(i->to, R)) {
				assert(rtype(i->to) == RTmp);
				t = i->to.val;
				if (bshas(b->in, t))
					nlv[KBASE(f->tmp[t].cls)]--;
				bsset(b->gen, t);
				bsclr(b->in, t);
			}
			for (k=0; k<2; k++)
				switch (rtype(i->arg[k])) {
				case RMem:
					ma = &f->mem[i->arg[k].val];
					bset(ma->base, b, nlv, f->tmp);
					bset(ma->index, b, nlv, f->tmp);
					break;
				default:
					bset(i->arg[k], b, nlv, f->tmp);
					break;
				}
			for (k=0; k<2; k++)
				if (nlv[k] > b->nlive[k])
					b->nlive[k] = nlv[k];
		}
	}
	if (chg) {
		chg = 0;
		goto Again;
	}

	if (debug['L']) {
		fprintf(stderr, "\n> Liveness analysis:\n");
		for (b=f->start; b; b=b->link) {
			fprintf(stderr, "\t%-10sin:   ", b->name);
			dumpts(b->in, f->tmp, stderr);
			fprintf(stderr, "\t          out:  ");
			dumpts(b->out, f->tmp, stderr);
			fprintf(stderr, "\t          gen:  ");
			dumpts(b->gen, f->tmp, stderr);
			fprintf(stderr, "\t          live: ");
			fprintf(stderr, "%d %d\n", b->nlive[0], b->nlive[1]);
		}
	}
}
