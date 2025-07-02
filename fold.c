#include "all.h"

/* boring folding code */

/**
 * Checks if a constant has a specific value.
 * 
 * Compares a constant with a given value, handling both 32-bit and 64-bit
 * comparisons based on the width parameter. This is used during constant
 * folding to check for special cases like division by zero.
 * 
 * @param c The constant to check
 * @param w Width flag (0 for 32-bit, 1 for 64-bit)
 * @param k The value to compare against
 * @return 1 if the constant equals k, 0 otherwise
 */
static int
iscon(Con *c, int w, uint64_t k)
{
	if (c->type != CBits)
		return 0;
	if (w)
		return (uint64_t)c->bits.i == k;
	else
		return (uint32_t)c->bits.i == (uint32_t)k;
}

/**
 * Performs constant folding for integer operations.
 * 
 * This function evaluates constant expressions at compile time by
 * performing the specified operation on two constant operands. It handles
 * arithmetic, logical, comparison, and conversion operations. The function
 * also handles special cases like division by zero and overflow conditions.
 * 
 * @param res Output parameter for the result constant
 * @param op The operation to perform
 * @param w Width flag (0 for 32-bit, 1 for 64-bit)
 * @param cl Left operand constant
 * @param cr Right operand constant
 * @return 0 on success, 1 if the operation cannot be folded
 */
int
foldint(Con *res, int op, int w, Con *cl, Con *cr)
{
	union {
		int64_t s;
		uint64_t u;
		float fs;
		double fd;
	} l, r;
	uint64_t x;
	Sym sym;
	int typ;

	memset(&sym, 0, sizeof sym);
	typ = CBits;
	l.s = cl->bits.i;
	r.s = cr->bits.i;
	if (op == Oadd) {
		if (cl->type == CAddr) {
			if (cr->type == CAddr)
				return 1;
			typ = CAddr;
			sym = cl->sym;
		}
		else if (cr->type == CAddr) {
			typ = CAddr;
			sym = cr->sym;
		}
	}
	else if (op == Osub) {
		if (cl->type == CAddr) {
			if (cr->type != CAddr) {
				typ = CAddr;
				sym = cl->sym;
			} else if (!symeq(cl->sym, cr->sym))
				return 1;
		}
		else if (cr->type == CAddr)
			return 1;
	}
	else if (cl->type == CAddr || cr->type == CAddr)
		return 1;
	if (op == Odiv || op == Orem || op == Oudiv || op == Ourem) {
		if (iscon(cr, w, 0))
			return 1;
		if (op == Odiv || op == Orem) {
			x = w ? INT64_MIN : INT32_MIN;
			if (iscon(cr, w, -1))
			if (iscon(cl, w, x))
				return 1;
		}
	}
	switch (op) {
	case Oadd:  x = l.u + r.u; break;
	case Osub:  x = l.u - r.u; break;
	case Oneg:  x = -l.u; break;
	case Odiv:  x = w ? l.s / r.s : (int32_t)l.s / (int32_t)r.s; break;
	case Orem:  x = w ? l.s % r.s : (int32_t)l.s % (int32_t)r.s; break;
	case Oudiv: x = w ? l.u / r.u : (uint32_t)l.u / (uint32_t)r.u; break;
	case Ourem: x = w ? l.u % r.u : (uint32_t)l.u % (uint32_t)r.u; break;
	case Omul:  x = l.u * r.u; break;
	case Oand:  x = l.u & r.u; break;
	case Oor:   x = l.u | r.u; break;
	case Oxor:  x = l.u ^ r.u; break;
	case Osar:  x = (w ? l.s : (int32_t)l.s) >> (r.u & (31|w<<5)); break;
	case Oshr:  x = (w ? l.u : (uint32_t)l.u) >> (r.u & (31|w<<5)); break;
	case Oshl:  x = l.u << (r.u & (31|w<<5)); break;
	case Oextsb: x = (int8_t)l.u;   break;
	case Oextub: x = (uint8_t)l.u;  break;
	case Oextsh: x = (int16_t)l.u;  break;
	case Oextuh: x = (uint16_t)l.u; break;
	case Oextsw: x = (int32_t)l.u;  break;
	case Oextuw: x = (uint32_t)l.u; break;
	case Ostosi: x = w ? (int64_t)cl->bits.s : (int32_t)cl->bits.s; break;
	case Ostoui: x = w ? (uint64_t)cl->bits.s : (uint32_t)cl->bits.s; break;
	case Odtosi: x = w ? (int64_t)cl->bits.d : (int32_t)cl->bits.d; break;
	case Odtoui: x = w ? (uint64_t)cl->bits.d : (uint32_t)cl->bits.d; break;
	case Ocast:
		x = l.u;
		if (cl->type == CAddr) {
			typ = CAddr;
			sym = cl->sym;
		}
		break;
	default:
		if (Ocmpw <= op && op <= Ocmpl1) {
			if (op <= Ocmpw1) {
				l.u = (int32_t)l.u;
				r.u = (int32_t)r.u;
			} else
				op -= Ocmpl - Ocmpw;
			switch (op - Ocmpw) {
			case Ciule: x = l.u <= r.u; break;
			case Ciult: x = l.u < r.u;  break;
			case Cisle: x = l.s <= r.s; break;
			case Cislt: x = l.s < r.s;  break;
			case Cisgt: x = l.s > r.s;  break;
			case Cisge: x = l.s >= r.s; break;
			case Ciugt: x = l.u > r.u;  break;
			case Ciuge: x = l.u >= r.u; break;
			case Cieq:  x = l.u == r.u; break;
			case Cine:  x = l.u != r.u; break;
			default: die("unreachable");
			}
		}
		else if (Ocmps <= op && op <= Ocmps1) {
			switch (op - Ocmps) {
			case Cfle: x = l.fs <= r.fs; break;
			case Cflt: x = l.fs < r.fs;  break;
			case Cfgt: x = l.fs > r.fs;  break;
			case Cfge: x = l.fs >= r.fs; break;
			case Cfne: x = l.fs != r.fs; break;
			case Cfeq: x = l.fs == r.fs; break;
			case Cfo: x = l.fs < r.fs || l.fs >= r.fs; break;
			case Cfuo: x = !(l.fs < r.fs || l.fs >= r.fs); break;
			default: die("unreachable");
			}
		}
		else if (Ocmpd <= op && op <= Ocmpd1) {
			switch (op - Ocmpd) {
			case Cfle: x = l.fd <= r.fd; break;
			case Cflt: x = l.fd < r.fd;  break;
			case Cfgt: x = l.fd > r.fd;  break;
			case Cfge: x = l.fd >= r.fd; break;
			case Cfne: x = l.fd != r.fd; break;
			case Cfeq: x = l.fd == r.fd; break;
			case Cfo: x = l.fd < r.fd || l.fd >= r.fd; break;
			case Cfuo: x = !(l.fd < r.fd || l.fd >= r.fd); break;
			default: die("unreachable");
			}
		}
		else
			die("unreachable");
	}
	*res = (Con){.type=typ, .sym=sym, .bits={.i=x}};
	return 0;
}

/**
 * Performs constant folding for floating-point operations.
 * 
 * This function evaluates constant floating-point expressions at compile time
 * by performing the specified operation on two constant operands. It handles
 * arithmetic operations and type conversions between floating-point and integer
 * types. The function supports both single and double precision operations.
 * 
 * @param res Output parameter for the result constant
 * @param op The operation to perform
 * @param w Width flag (0 for single precision, 1 for double precision)
 * @param cl Left operand constant
 * @param cr Right operand constant
 */
static void
foldflt(Con *res, int op, int w, Con *cl, Con *cr)
{
	float xs, ls, rs;
	double xd, ld, rd;

	if (cl->type != CBits || cr->type != CBits)
		err("invalid address operand for '%s'", optab[op].name);
	*res = (Con){.type = CBits};
	memset(&res->bits, 0, sizeof(res->bits));
	if (w)  {
		ld = cl->bits.d;
		rd = cr->bits.d;
		switch (op) {
		case Oadd: xd = ld + rd; break;
		case Osub: xd = ld - rd; break;
		case Oneg: xd = -ld; break;
		case Odiv: xd = ld / rd; break;
		case Omul: xd = ld * rd; break;
		case Oswtof: xd = (int32_t)cl->bits.i; break;
		case Ouwtof: xd = (uint32_t)cl->bits.i; break;
		case Osltof: xd = (int64_t)cl->bits.i; break;
		case Oultof: xd = (uint64_t)cl->bits.i; break;
		case Oexts: xd = cl->bits.s; break;
		case Ocast: xd = ld; break;
		default: die("unreachable");
		}
		res->bits.d = xd;
		res->flt = 2;
	} else {
		ls = cl->bits.s;
		rs = cr->bits.s;
		switch (op) {
		case Oadd: xs = ls + rs; break;
		case Osub: xs = ls - rs; break;
		case Oneg: xs = -ls; break;
		case Odiv: xs = ls / rs; break;
		case Omul: xs = ls * rs; break;
		case Oswtof: xs = (int32_t)cl->bits.i; break;
		case Ouwtof: xs = (uint32_t)cl->bits.i; break;
		case Osltof: xs = (int64_t)cl->bits.i; break;
		case Oultof: xs = (uint64_t)cl->bits.i; break;
		case Otruncd: xs = cl->bits.d; break;
		case Ocast: xs = ls; break;
		default: die("unreachable");
		}
		res->bits.s = xs;
		res->flt = 1;
	}
}

/**
 * Performs constant folding for a specific operation and returns a reference.
 * 
 * This function is a wrapper around the constant folding functions that
 * creates a new constant reference in the function's constant table.
 * It handles both integer and floating-point operations and ensures
 * proper bit width truncation for 32-bit operations.
 * 
 * @param op The operation to perform
 * @param cls The class of the operation (Kw, Kl, Ks, Kd)
 * @param cl Left operand constant
 * @param cr Right operand constant
 * @param fn The function to add the constant to
 * @return Reference to the folded constant, or R if folding failed
 */
static Ref
opfold(int op, int cls, Con *cl, Con *cr, Fn *fn)
{
	Ref r;
	Con c;

	if (cls == Kw || cls == Kl) {
		if (foldint(&c, op, cls == Kl, cl, cr))
			return R;
	} else
		foldflt(&c, op, cls == Kd, cl, cr);
	if (!KWIDE(cls))
		c.bits.i &= 0xffffffff;
	r = newcon(&c, fn);
	assert(!(cls == Ks || cls == Kd) || c.flt);
	return r;
}

/* used by GVN */
/**
 * Attempts to fold an instruction into a constant reference.
 * 
 * This function checks if an instruction can be constant-folded by
 * examining its operands. If both operands are constants and the
 * operation supports folding, it evaluates the expression at compile
 * time and returns a reference to the result constant. This is used
 * by the global value numbering pass to eliminate redundant computations.
 * 
 * @param fn The function containing the instruction
 * @param i The instruction to attempt to fold
 * @return Reference to the folded constant, or R if folding is not possible
 */
Ref
foldref(Fn *fn, Ins *i)
{
	Ref rr;
	Con *cl, *cr;

	if (rtype(i->to) != RTmp)
		return R;
	if (optab[i->op].canfold) {
		if (rtype(i->arg[0]) != RCon)
			return R;
		cl = &fn->con[i->arg[0].val];
		rr = i->arg[1];
		if (req(rr, R))
		    rr = CON_Z;
		if (rtype(rr) != RCon)
			return R;
		cr = &fn->con[rr.val];

		return opfold(i->op, i->cls, cl, cr, fn);
	}
	return R;
}
