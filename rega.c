#include "all.h"

#ifdef TEST_PMOV
	#undef assert
	#define assert(x) assert_test(#x, x)
#endif

typedef struct RMap RMap;

struct RMap {
	int t[Tmp0];
	int r[Tmp0];
	int w[Tmp0];   /* wait list, for unmatched hints */
	BSet b[1];
	int n;
};

static bits regu;      /* registers used */
static Tmp *tmp;       /* function temporaries */
static Mem *mem;       /* function mem references */
static struct {
	Ref src, dst;
	int cls;
} pm[Tmp0];            /* parallel move constructed */
static int npm;        /* size of pm */
static int loop;       /* current loop level */

static uint stmov;     /* stats: added moves */
static uint stblk;     /* stats: added blocks */

/**
 * Returns a pointer to the hint register for a temporary.
 * 
 * This function retrieves the register hint for a temporary based on
 * its phi class. Register hints are used to guide register allocation
 * decisions, helping to minimize the number of register-to-register
 * copies needed.
 * 
 * @param t The temporary index
 * @return Pointer to the hint register field
 */
static int *
hint(int t)
{
	return &tmp[phicls(t, tmp)].hint.r;
}

/**
 * Sets a register hint for a temporary.
 * 
 * This function establishes a register preference for a temporary,
 * which helps the register allocator make better decisions. The hint
 * is only set if no hint exists or if the current loop level is
 * deeper than the existing hint's loop level.
 * 
 * @param t The temporary index
 * @param r The register to hint for
 */
static void
sethint(int t, int r)
{
	Tmp *p;

	p = &tmp[phicls(t, tmp)];
	if (p->hint.r == -1 || p->hint.w > loop) {
		p->hint.r = r;
		p->hint.w = loop;
		tmp[t].visit = -1;
	}
}

/**
 * Copies register mapping information from one map to another.
 * 
 * This function performs a deep copy of register mapping data,
 * including temporary-to-register mappings, wait lists, and bit sets.
 * It's used to save and restore register allocation state during
 * the allocation process.
 * 
 * @param ma Destination register map
 * @param mb Source register map
 */
static void
rcopy(RMap *ma, RMap *mb)
{
	memcpy(ma->t, mb->t, sizeof ma->t);
	memcpy(ma->r, mb->r, sizeof ma->r);
	memcpy(ma->w, mb->w, sizeof ma->w);
	bscopy(ma->b, mb->b);
	ma->n = mb->n;
}

/**
 * Finds the register allocated to a temporary in a register map.
 * 
 * This function searches through a register map to find which register
 * (if any) is currently allocated to a given temporary. It returns -1
 * if no register is allocated.
 * 
 * @param m The register map to search
 * @param t The temporary to look up
 * @return The register number, or -1 if not found
 */
static int
rfind(RMap *m, int t)
{
	int i;

	for (i=0; i<m->n; i++)
		if (m->t[i] == t)
			return m->r[i];
	return -1;
}

/**
 * Returns a reference to a temporary's allocated register or spill slot.
 * 
 * This function provides a unified way to access a temporary's location,
 * whether it's in a register or spilled to memory. If the temporary is
 * in a register, it returns a register reference; otherwise, it returns
 * a slot reference for the spilled temporary.
 * 
 * @param m The register map
 * @param t The temporary index
 * @return Reference to the temporary's location (register or slot)
 */
static Ref
rref(RMap *m, int t)
{
	int r, s;

	r = rfind(m, t);
	if (r == -1) {
		s = tmp[t].slot;
		assert(s != -1 && "should have spilled");
		return SLOT(s);
	} else
		return TMP(r);
}

/**
 * Adds a temporary-to-register mapping to a register map.
 * 
 * This function establishes a mapping between a temporary and a register,
 * updating the register map's data structures and tracking register usage.
 * It performs various validity checks to ensure the allocation is legal.
 * 
 * @param m The register map to update
 * @param t The temporary to allocate
 * @param r The register to allocate to the temporary
 */
static void
radd(RMap *m, int t, int r)
{
	assert((t >= Tmp0 || t == r) && "invalid temporary");
	assert(((T.gpr0 <= r && r < T.gpr0 + T.ngpr)
		|| (T.fpr0 <= r && r < T.fpr0 + T.nfpr))
		&& "invalid register");
	assert(!bshas(m->b, t) && "temporary has mapping");
	assert(!bshas(m->b, r) && "register already allocated");
	assert(m->n <= T.ngpr+T.nfpr && "too many mappings");
	bsset(m->b, t);
	bsset(m->b, r);
	m->t[m->n] = t;
	m->r[m->n] = r;
	m->n++;
	regu |= BIT(r);
}

/**
 * Attempts to allocate a register for a temporary.
 * 
 * This function tries to find an available register for a temporary,
 * using hints and fallback strategies. If the 'try' parameter is true,
 * it returns R (no allocation) instead of failing when no register
 * is available. This allows for graceful handling of register pressure.
 * 
 * The allocation strategy:
 * 1. Use the temporary's visit field if available
 * 2. Use the temporary's hint if available
 * 3. Find any available register in the appropriate class
 * 4. Spill a register if necessary
 * 
 * @param m The register map
 * @param t The temporary to allocate
 * @param try If true, return R instead of failing
 * @return Reference to the allocated register, or R if allocation failed
 */
static Ref
ralloctry(RMap *m, int t, int try)
{
	bits regs;
	int h, r, r0, r1;

	if (t < Tmp0) {
		assert(bshas(m->b, t));
		return TMP(t);
	}
	if (bshas(m->b, t)) {
		r = rfind(m, t);
		assert(r != -1);
		return TMP(r);
	}
	r = tmp[t].visit;
	if (r == -1 || bshas(m->b, r))
		r = *hint(t);
	if (r == -1 || bshas(m->b, r)) {
		if (try)
			return R;
		regs = tmp[phicls(t, tmp)].hint.m;
		regs |= m->b->t[0];
		if (KBASE(tmp[t].cls) == 0) {
			r0 = T.gpr0;
			r1 = r0 + T.ngpr;
		} else {
			r0 = T.fpr0;
			r1 = r0 + T.nfpr;
		}
		for (r=r0; r<r1; r++)
			if (!(regs & BIT(r)))
				goto Found;
		for (r=r0; r<r1; r++)
			if (!bshas(m->b, r))
				goto Found;
		die("no more regs");
	}
Found:
	radd(m, t, r);
	sethint(t, r);
	tmp[t].visit = r;
	h = *hint(t);
	if (h != -1 && h != r)
		m->w[h] = t;
	return TMP(r);
}

/**
 * Allocates a register for a temporary, failing if none available.
 * 
 * This is a convenience wrapper around ralloctry() that always
 * attempts to allocate a register and fails if none is available.
 * 
 * @param m The register map
 * @param t The temporary to allocate
 * @return Reference to the allocated register
 */
static inline Ref
ralloc(RMap *m, int t)
{
	return ralloctry(m, t, 0);
}

/**
 * Frees a register allocation for a temporary.
 * 
 * This function removes a temporary-to-register mapping from a register
 * map, updating all related data structures. It returns the register
 * that was freed, or -1 if the temporary wasn't allocated.
 * 
 * @param m The register map
 * @param t The temporary to free
 * @return The register that was freed, or -1 if not found
 */
static int
rfree(RMap *m, int t)
{
	int i, r;

	assert(t >= Tmp0 || !(BIT(t) & T.rglob));
	if (!bshas(m->b, t))
		return -1;
	for (i=0; m->t[i] != t; i++)
		assert(i+1 < m->n);
	r = m->r[i];
	bsclr(m->b, t);
	bsclr(m->b, r);
	m->n--;
	memmove(&m->t[i], &m->t[i+1], (m->n-i) * sizeof m->t[0]);
	memmove(&m->r[i], &m->r[i+1], (m->n-i) * sizeof m->r[0]);
	assert(t >= Tmp0 || t == r);
	return r;
}

/**
 * Dumps register mapping information for debugging.
 * 
 * This function prints the current register allocations in a human-readable
 * format, showing which temporaries are mapped to which registers.
 * 
 * @param m The register map to dump
 */
static void
mdump(RMap *m)
{
	int i;

	for (i=0; i<m->n; i++)
		if (m->t[i] >= Tmp0)
			fprintf(stderr, " (%s, R%d)",
				tmp[m->t[i]].name,
				m->r[i]);
	fprintf(stderr, "\n");
}

/**
 * Adds a move to the parallel move list.
 * 
 * This function adds a source-to-destination move to the parallel move
 * list, which will be processed later to generate optimal move sequences.
 * The moves are collected to handle complex register allocation scenarios
 * efficiently.
 * 
 * @param src Source reference
 * @param dst Destination reference
 * @param k The class of the move
 */
static void
pmadd(Ref src, Ref dst, int k)
{
	if (npm == Tmp0)
		die("cannot have more moves than registers");
	pm[npm].src = src;
	pm[npm].dst = dst;
	pm[npm].cls = k;
	npm++;
}

enum PMStat { ToMove, Moving, Moved };

/**
 * Recursively processes parallel moves to handle cycles.
 * 
 * This function implements a recursive algorithm to process parallel moves
 * while detecting and handling cycles. It uses a depth-first search approach
 * with three states for each move: ToMove, Moving, and Moved.
 * 
 * When a cycle is detected, it generates a swap instruction to break the
 * cycle. For non-cyclic moves, it generates copy instructions.
 * 
 * @param status Array tracking the state of each move
 * @param i Index of the current move to process
 * @param k Pointer to the class of the current move sequence
 * @return Index of the cycle start, or -1 if no cycle
 */
static int
pmrec(enum PMStat *status, int i, int *k)
{
	int j, c;

	/* note, this routine might emit
	 * too many large instructions
	 */
	if (req(pm[i].src, pm[i].dst)) {
		status[i] = Moved;
		return -1;
	}
	assert(KBASE(pm[i].cls) == KBASE(*k));
	assert((Kw|Kl) == Kl && (Ks|Kd) == Kd);
	*k |= pm[i].cls;
	for (j=0; j<npm; j++)
		if (req(pm[j].dst, pm[i].src))
			break;
	switch (j == npm ? Moved : status[j]) {
	case Moving:
		c = j; /* start of cycle */
		emit(Oswap, *k, R, pm[i].src, pm[i].dst);
		break;
	case ToMove:
		status[i] = Moving;
		c = pmrec(status, j, k);
		if (c == i) {
			c = -1; /* end of cycle */
			break;
		}
		if (c != -1) {
			emit(Oswap, *k, R, pm[i].src, pm[i].dst);
			break;
		}
		/* fall through */
	case Moved:
		c = -1;
		emit(Ocopy, pm[i].cls, pm[i].dst, pm[i].src, R);
		break;
	default:
		die("unreachable");
	}
	status[i] = Moved;
	return c;
}

/**
 * Generates instructions for all parallel moves.
 * 
 * This function processes the entire parallel move list, generating
 * the necessary instructions to perform all moves while handling
 * cycles efficiently. It uses the recursive pmrec() function to
 * process each move in the correct order.
 */
static void
pmgen()
{
	int i;
	enum PMStat *status;

	status = alloc(npm * sizeof status[0]);
	assert(!npm || status[npm-1] == ToMove);
	for (i=0; i<npm; i++)
		if (status[i] == ToMove)
			pmrec(status, i, (int[]){pm[i].cls});
}

/**
 * Moves a register to a new location, handling conflicts.
 * 
 * This function moves a register to a new location (register or temporary),
 * handling any conflicts that arise. If the destination is already occupied,
 * it spills the current occupant and reallocates it elsewhere.
 * 
 * @param r The register to move
 * @param to The destination reference
 * @param m The register map
 */
static void
move(int r, Ref to, RMap *m)
{
	int n, t, r1;

	r1 = req(to, R) ? -1 : rfree(m, to.val);
	if (bshas(m->b, r)) {
		/* r is used and not by to */
		assert(r1 != r);
		for (n=0; m->r[n] != r; n++)
			assert(n+1 < m->n);
		t = m->t[n];
		rfree(m, t);
		bsset(m->b, r);
		ralloc(m, t);
		bsclr(m->b, r);
	}
	t = req(to, R) ? r : to.val;
	radd(m, t, r);
}

/**
 * Checks if an instruction is a register-to-register copy.
 * 
 * This function determines if an instruction is a copy operation
 * where the source is a register. Such instructions are handled
 * specially during register allocation.
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
 * instructions at the start of a block, converting them into
 * parallel moves and generating optimal move sequences. It also
 * handles function calls by managing caller-saved registers.
 * 
 * @param b The block containing the moves
 * @param i Pointer to the first instruction to process
 * @param m The register map
 * @return Pointer to the instruction after the processed moves
 */
static Ins *
dopm(Blk *b, Ins *i, RMap *m)
{
	RMap m0;
	int n, r, r1, t, s;
	Ins *i1, *ip;
	bits def;

	m0 = *m; /* okay since we don't use m0.b */
	m0.b->t = 0;
	i1 = ++i;
	do {
		i--;
		move(i->arg[0].val, i->to, m);
	} while (i != b->ins && regcpy(i-1));
	assert(m0.n <= m->n);
	if (i != b->ins && (i-1)->op == Ocall) {
		def = T.retregs((i-1)->arg[1], 0) | T.rglob;
		for (r=0; T.rsave[r]>=0; r++)
			if (!(BIT(T.rsave[r]) & def))
				move(T.rsave[r], R, m);
	}
	for (npm=0, n=0; n<m->n; n++) {
		t = m->t[n];
		s = tmp[t].slot;
		r1 = m->r[n];
		r = rfind(&m0, t);
		if (r != -1)
			pmadd(TMP(r1), TMP(r), tmp[t].cls);
		else if (s != -1)
			pmadd(TMP(r1), SLOT(s), tmp[t].cls);
	}
	for (ip=i; ip<i1; ip++) {
		if (!req(ip->to, R))
			rfree(m, ip->to.val);
		r = ip->arg[0].val;
		if (rfind(m, r) == -1)
			radd(m, r, r);
	}
	pmgen();
	return i;
}

/**
 * Compares two references for allocation priority.
 * 
 * This function implements a simple heuristic to determine which
 * reference should be allocated first. Currently, it prioritizes
 * references that have register hints.
 * 
 * @param r1 First reference
 * @param r2 Second reference
 * @return Positive if r1 has higher priority, negative if r2 does
 */
static int
prio1(Ref r1, Ref r2)
{
	/* trivial heuristic to begin with,
	 * later we can use the distance to
	 * the definition instruction
	 */
	(void) r2;
	return *hint(r1.val) != -1;
}

/**
 * Inserts a reference into a priority-sorted array.
 * 
 * This function maintains a sorted array of references based on
 * allocation priority. It uses insertion sort to keep the array
 * ordered by the prio1() comparison function.
 * 
 * @param r The reference to insert
 * @param rs Array of reference pointers
 * @param p Current position in the array
 */
static void
insert(Ref *r, Ref **rs, int p)
{
	int i;

	rs[i = p] = r;
	while (i-- > 0 && prio1(*r, *rs[i])) {
		rs[i+1] = rs[i];
		rs[i] = r;
	}
}

/**
 * Processes register allocation for a single block.
 * 
 * This function performs register allocation for all instructions
 * in a block, working backwards from the end. It handles:
 * - Function calls and their register requirements
 * - Register-to-register copies
 * - Memory operations with register operands
 * - Register hints and optimizations
 * 
 * The function maintains a register map that tracks which temporaries
 * are in which registers, and generates move instructions as needed.
 * 
 * @param b The block to process
 * @param cur The current register map
 */
static void
doblk(Blk *b, RMap *cur)
{
	int t, x, r, rf, rt, nr;
	bits rs;
	Ins *i, *i1;
	Mem *m;
	Ref *ra[4];

	if (rtype(b->jmp.arg) == RTmp)
		b->jmp.arg = ralloc(cur, b->jmp.arg.val);
	curi = &insb[NIns];
	for (i1=&b->ins[b->nins]; i1!=b->ins;) {
		emiti(*--i1);
		i = curi;
		rf = -1;
		switch (i->op) {
		case Ocall:
			rs = T.argregs(i->arg[1], 0) | T.rglob;
			for (r=0; T.rsave[r]>=0; r++)
				if (!(BIT(T.rsave[r]) & rs))
					rfree(cur, T.rsave[r]);
			break;
		case Ocopy:
			if (regcpy(i)) {
				curi++;
				i1 = dopm(b, i1, cur);
				stmov += i+1 - curi;
				continue;
			}
			if (isreg(i->to))
			if (rtype(i->arg[0]) == RTmp)
				sethint(i->arg[0].val, i->to.val);
			/* fall through */
		default:
			if (!req(i->to, R)) {
				assert(rtype(i->to) == RTmp);
				r = i->to.val;
				if (r < Tmp0 && (BIT(r) & T.rglob))
					break;
				rf = rfree(cur, r);
				if (rf == -1) {
					assert(!isreg(i->to));
					curi++;
					continue;
				}
				i->to = TMP(rf);
			}
			break;
		}
		for (x=0, nr=0; x<2; x++)
			switch (rtype(i->arg[x])) {
			case RMem:
				m = &mem[i->arg[x].val];
				if (rtype(m->base) == RTmp)
					insert(&m->base, ra, nr++);
				if (rtype(m->index) == RTmp)
					insert(&m->index, ra, nr++);
				break;
			case RTmp:
				insert(&i->arg[x], ra, nr++);
				break;
			}
		for (r=0; r<nr; r++)
			*ra[r] = ralloc(cur, ra[r]->val);
		if (i->op == Ocopy && req(i->to, i->arg[0]))
			curi++;

		/* try to change the register of a hinted
		 * temporary if rf is available */
		if (rf != -1 && (t = cur->w[rf]) != 0)
		if (!bshas(cur->b, rf) && *hint(t) == rf
		&& (rt = rfree(cur, t)) != -1) {
			tmp[t].visit = -1;
			ralloc(cur, t);
			assert(bshas(cur->b, rf));
			emit(Ocopy, tmp[t].cls, TMP(rt), TMP(rf), R);
			stmov += 1;
			cur->w[rf] = 0;
			for (r=0; r<nr; r++)
				if (req(*ra[r], TMP(rt)))
					*ra[r] = TMP(rf);
			/* one could iterate this logic with
			 * the newly freed rt, but in this case
			 * the above loop must be changed */
		}
	}
	idup(b, curi, &insb[NIns]-curi);
}

/* qsort() comparison function to peel
 * loop nests from inside out */
static int
carve(const void *a, const void *b)
{
	Blk *ba, *bb;

	/* todo, evaluate if this order is really
	 * better than the simple postorder */
	ba = *(Blk**)a;
	bb = *(Blk**)b;
	if (ba->loop == bb->loop)
		return ba->id > bb->id ? -1 : ba->id < bb->id;
	return ba->loop > bb->loop ? -1 : +1;
}

/* comparison function to order temporaries
 * for allocation at the end of blocks */
static int
prio2(int t1, int t2)
{
	if ((tmp[t1].visit ^ tmp[t2].visit) < 0)  /* != signs */
		return tmp[t1].visit != -1 ? +1 : -1;
	if ((*hint(t1) ^ *hint(t2)) < 0)
		return *hint(t1) != -1 ? +1 : -1;
	return tmp[t1].cost - tmp[t2].cost;
}

/* register allocation
 * depends on rpo, phi, cost, (and obviously spill) */
/**
 * Performs register allocation for an entire function.
 * 
 * This function implements a complete register allocation pass that:
 * 1. Sets up the allocation environment and initializes data structures
 * 2. Assigns registers to temporaries in each block
 * 3. Emits copies for phi nodes and block transitions
 * 4. Creates new blocks for complex move sequences
 * 
 * The algorithm uses a backward dataflow approach, processing blocks
 * in reverse post-order and maintaining register maps at block boundaries.
 * It handles complex cases like:
 * - Phi nodes with register constraints
 * - Function calls with argument/return register management
 * - Parallel moves and cycle detection
 * - Register hints and optimizations
 * 
 * The function generates the necessary move instructions to maintain
 * correct register assignments across the control flow graph.
 * 
 * @param fn The function to allocate registers for
 */
void
rega(Fn *fn)
{
	int j, t, r, x, rl[Tmp0];
	Blk *b, *b1, *s, ***ps, *blist, **blk, **bp;
	RMap *end, *beg, cur, old, *m;
	Ins *i;
	Phi *p;
	uint u, n;
	Ref src, dst;

	/* 1. setup */
	stmov = 0;
	stblk = 0;
	regu = 0;
	tmp = fn->tmp;
	mem = fn->mem;
	blk = alloc(fn->nblk * sizeof blk[0]);
	end = alloc(fn->nblk * sizeof end[0]);
	beg = alloc(fn->nblk * sizeof beg[0]);
	for (n=0; n<fn->nblk; n++) {
		bsinit(end[n].b, fn->ntmp);
		bsinit(beg[n].b, fn->ntmp);
	}
	bsinit(cur.b, fn->ntmp);
	bsinit(old.b, fn->ntmp);

	loop = INT_MAX;
	for (t=0; t<fn->ntmp; t++) {
		tmp[t].hint.r = t < Tmp0 ? t : -1;
		tmp[t].hint.w = loop;
		tmp[t].visit = -1;
	}
	for (bp=blk, b=fn->start; b; b=b->link)
		*bp++ = b;
	qsort(blk, fn->nblk, sizeof blk[0], carve);
	for (b=fn->start, i=b->ins; i<&b->ins[b->nins]; i++)
		if (i->op != Ocopy || !isreg(i->arg[0]))
			break;
		else {
			assert(rtype(i->to) == RTmp);
			sethint(i->to.val, i->arg[0].val);
		}

	/* 2. assign registers */
	for (bp=blk; bp<&blk[fn->nblk]; bp++) {
		b = *bp;
		n = b->id;
		loop = b->loop;
		cur.n = 0;
		bszero(cur.b);
		memset(cur.w, 0, sizeof cur.w);
		for (x=0, t=Tmp0; bsiter(b->out, &t); t++) {
			j = x++;
			rl[j] = t;
			while (j-- > 0 && prio2(t, rl[j]) > 0) {
				rl[j+1] = rl[j];
				rl[j] = t;
			}
		}
		for (r=0; bsiter(b->out, &r) && r<Tmp0; r++)
			radd(&cur, r, r);
		for (j=0; j<x; j++)
			ralloctry(&cur, rl[j], 1);
		for (j=0; j<x; j++)
			ralloc(&cur, rl[j]);
		rcopy(&end[n], &cur);
		doblk(b, &cur);
		bscopy(b->in, cur.b);
		for (p=b->phi; p; p=p->link)
			if (rtype(p->to) == RTmp)
				bsclr(b->in, p->to.val);
		rcopy(&beg[n], &cur);
	}

	/* 3. emit copies shared by multiple edges
	 * to the same block */
	for (s=fn->start; s; s=s->link) {
		if (s->npred <= 1)
			continue;
		m = &beg[s->id];

		/* rl maps a register that is live at the
		 * beginning of s to the one used in all
		 * predecessors (if any, -1 otherwise) */
		memset(rl, 0, sizeof rl);

		/* to find the register of a phi in a
		 * predecessor, we have to find the
		 * corresponding argument */
		for (p=s->phi; p; p=p->link) {
			if (rtype(p->to) != RTmp
			|| (r=rfind(m, p->to.val)) == -1)
				continue;
			for (u=0; u<p->narg; u++) {
				b = p->blk[u];
				src = p->arg[u];
				if (rtype(src) != RTmp)
					continue;
				x = rfind(&end[b->id], src.val);
				if (x == -1) /* spilled */
					continue;
				rl[r] = (!rl[r] || rl[r] == x) ? x : -1;
			}
			if (rl[r] == 0)
				rl[r] = -1;
		}

		/* process non-phis temporaries */
		for (j=0; j<m->n; j++) {
			t = m->t[j];
			r = m->r[j];
			if (rl[r] || t < Tmp0 /* todo, remove this */)
				continue;
			for (bp=s->pred; bp<&s->pred[s->npred]; bp++) {
				x = rfind(&end[(*bp)->id], t);
				if (x == -1) /* spilled */
					continue;
				rl[r] = (!rl[r] || rl[r] == x) ? x : -1;
			}
			if (rl[r] == 0)
				rl[r] = -1;
		}

		npm = 0;
		for (j=0; j<m->n; j++) {
			t = m->t[j];
			r = m->r[j];
			x = rl[r];
			assert(x != 0 || t < Tmp0 /* todo, ditto */);
			if (x > 0 && !bshas(m->b, x)) {
				pmadd(TMP(x), TMP(r), tmp[t].cls);
				m->r[j] = x;
				bsset(m->b, x);
			}
		}
		curi = &insb[NIns];
		pmgen();
		j = &insb[NIns] - curi;
		if (j == 0)
			continue;
		stmov += j;
		s->nins += j;
		i = alloc(s->nins * sizeof(Ins));
		icpy(icpy(i, curi, j), s->ins, s->nins-j);
		s->ins = i;
	}

	if (debug['R'])  {
		fprintf(stderr, "\n> Register mappings:\n");
		for (n=0; n<fn->nblk; n++) {
			b = fn->rpo[n];
			fprintf(stderr, "\t%-10s beg", b->name);
			mdump(&beg[n]);
			fprintf(stderr, "\t           end");
			mdump(&end[n]);
		}
		fprintf(stderr, "\n");
	}

	/* 4. emit remaining copies in new blocks */
	blist = 0;
	for (b=fn->start;; b=b->link) {
		ps = (Blk**[3]){&b->s1, &b->s2, (Blk*[1]){0}};
		for (; (s=**ps); ps++) {
			npm = 0;
			for (p=s->phi; p; p=p->link) {
				dst = p->to;
				assert(rtype(dst)==RSlot || rtype(dst)==RTmp);
				if (rtype(dst) == RTmp) {
					r = rfind(&beg[s->id], dst.val);
					if (r == -1)
						continue;
					dst = TMP(r);
				}
				for (u=0; p->blk[u]!=b; u++)
					assert(u+1 < p->narg);
				src = p->arg[u];
				if (rtype(src) == RTmp)
					src = rref(&end[b->id], src.val);
				pmadd(src, dst, p->cls);
			}
			for (t=Tmp0; bsiter(s->in, &t); t++) {
				src = rref(&end[b->id], t);
				dst = rref(&beg[s->id], t);
				pmadd(src, dst, tmp[t].cls);
			}
			curi = &insb[NIns];
			pmgen();
			if (curi == &insb[NIns])
				continue;
			b1 = newblk();
			b1->loop = (b->loop+s->loop) / 2;
			b1->link = blist;
			blist = b1;
			fn->nblk++;
			strf(b1->name, "%s_%s", b->name, s->name);
			stmov += &insb[NIns]-curi;
			stblk += 1;
			idup(b1, curi, &insb[NIns]-curi);
			b1->jmp.type = Jjmp;
			b1->s1 = s;
			**ps = b1;
		}
		if (!b->link) {
			b->link = blist;
			break;
		}
	}
	for (b=fn->start; b; b=b->link)
		b->phi = 0;
	fn->reg = regu;

	if (debug['R']) {
		fprintf(stderr, "\n> Register allocation statistics:\n");
		fprintf(stderr, "\tnew moves:  %d\n", stmov);
		fprintf(stderr, "\tnew blocks: %d\n", stblk);
		fprintf(stderr, "\n> After register allocation:\n");
		printfn(fn, stderr);
	}
}
