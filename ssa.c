#include <stdarg.h>
#include "all.h"

void adduse(Tmp* tmp, int ty, Blk* b, ...) {
  Use* u;
  int n;
  va_list ap;

  if (!tmp->use) {
    return;
  }
  va_start(ap, b);
  n = tmp->nuse;
  vgrow(&tmp->use, ++tmp->nuse);
  u = &tmp->use[n];
  u->type = ty;
  u->bid = b->id;
  switch (ty) {
    case UPhi:
      u->u.phi = va_arg(ap, Phi*);
      break;
    case UIns:
      u->u.ins = va_arg(ap, Ins*);
      break;
    case UJmp:
      break;
    default:
      die("unreachable");
  }
  va_end(ap);
}

/* fill usage, width, phi, and class information
 * must not change .visit fields
 */
// The main goal here is to fill out the |use| vector of all temporaries, as
// well as determining the correct size for them (based on what instruction
// creates the temporary, and its arguments).
void filluse(Fn* fn) {
  Tmp* tmp = fn->tmp;
  // Partial (?) reset of all temporaries. Not reset: name, use, cost, slot,
  // hint, alias, visit, gcmbid. XXX it seems like most of those are
  // incidentally not reset (because they're [over]written later presumably),
  // but the original comment above says .visit has to be maintained. It seems
  // strange to maintain visit while nuking the rest though?
  for (int t = Tmp0; t < fn->ntmp; t++) {
    tmp[t].def = 0;
    tmp[t].bid = -1u;
    tmp[t].ndef = 0;
    tmp[t].nuse = 0;
    tmp[t].cls = 0;
    tmp[t].phi = 0;
    tmp[t].width = WFull;
    if (tmp[t].use == NULL) {
      tmp[t].use = vnew(0, sizeof(Use), PFn);
    }
  }
  for (Blk* b = fn->start; b; b = b->link) {
    for (Phi* p = b->phi; p; p = p->link) {
      // If the block has phis (incoming) then the location to which the result
      // of the phi instruction is being stored has to be a temporary. Save the
      // block where it's defined, and for each argument to the phi instruction,
      // track the usages (in the Tmp::use vector) of each argument.
      assert(rtype(p->to) == RTmp);
      int tp = p->to.val;
      tmp[tp].bid = b->id;
      tmp[tp].ndef++;
      tmp[tp].cls = p->cls;

      // This recurses to find the top-most temp that's still a phi. I think it
      // must be collapsing usages if there's a chain of variables used in phis
      // so that this one can point directly at the 'original' source of a value
      // through copies and renamings.
      tp = phicls(tp, fn->tmp);

      for (uint a = 0; a < p->narg; a++) {
        if (rtype(p->arg[a]) == RTmp) {
          int ta = p->arg[a].val;
          adduse(&tmp[ta], UPhi, b, p);
          ta = phicls(ta, fn->tmp);
          if (ta != tp) {
            // If the argument isn't the output (?) then set the argument's phi
            // to the main instruction. XXX Not sure about this, or why.
            tmp[ta].phi = tp;
          }
        }
      }
    }

    // For each instruction in the block, if it has an output (which must be a
    // temporary), then figure out the correct width for that output. Mark the
    // |def|inition of the temporary as being this instruction. def doesn't
    // count as a use though, so it's not added to the |use| vector. For any
    // arguments of the instruction that are temporaries, note their uses.
    for (Ins* i = b->ins; i < &b->ins[b->nins]; i++) {
      if (!req(i->to, R)) {
        assert(rtype(i->to) == RTmp);
        int w = WFull;
        if (isparbh(i->op)) {
          w = Wsb + (i->op - Oparsb);
        }
        if (isload(i->op) && i->op != Oload) {
          w = Wsb + (i->op - Oloadsb);
        }
        if (isext(i->op)) {
          w = Wsb + (i->op - Oextsb);
        }
        int unused;
        if (iscmp(i->op, &unused, &unused)) {
          w = Wub;
        }
        if (w == Wsw || w == Wuw) {
          if (i->cls == Kw) {
            w = WFull;
          }
        }
        int t = i->to.val;
        tmp[t].width = w;
        tmp[t].def = i;
        tmp[t].bid = b->id;
        tmp[t].ndef++;
        tmp[t].cls = i->cls;
      }
      for (int m = 0; m < 2; m++) {
        if (rtype(i->arg[m]) == RTmp) {
          int t = i->arg[m].val;
          adduse(&tmp[t], UIns, b, i);
        }
      }
    }

    // If the jmp at the end of the block is conditional based on a temporary,
    // then note that use as well.
    if (rtype(b->jmp.arg) == RTmp) {
      adduse(&tmp[b->jmp.arg.val], UJmp, b);
    }
  }
}

static Ref refindex(int t, Fn* fn) {
  return newtmp(fn->tmp[t].name, fn->tmp[t].cls, fn);
}

// Inserts phi nodes for variables that require them to convert the function to
// SSA form. This function analyzes each temporary to determine where phi nodes
// are needed, based on the dominance frontier and the use/def information for
// each temporary. It avoids inserting unnecessary phi nodes for variables that
// are only defined and used in a single block. The algorithm is based on the
// classic SSA construction using dominance frontiers.
static void phiins(Fn* fn) {
  BSet u[1];
  bsinit(u, fn->nblk);
  BSet defs[1];
  bsinit(defs, fn->nblk);
  Blk** blist = emalloc(fn->nblk * sizeof blist[0]);
  Blk** be = &blist[fn->nblk];
  int nt = fn->ntmp;
  for (int t = Tmp0; t < nt; t++) {
    fn->tmp[t].visit = 0;
    // Skip if phi node already exists for this temporary.
    if (fn->tmp[t].phi != 0) {
      continue;
    }
    // Skip if the temporary is only defined once and all uses are in the same
    // block, or if the definition is in the start block.
    if (fn->tmp[t].ndef == 1) {
      int ok = 1;
      uint defb = fn->tmp[t].bid;
      Use* use = fn->tmp[t].use;
      for (uint n = fn->tmp[t].nuse; n--; use++) {
        ok &= use->bid == defb;
      }
      if (ok || defb == fn->start->id) {
        continue;
      }
    }
    // For temporaries that may need phi nodes, perform the phi insertion
    // algorithm.
    bszero(u);
    short k = Kx;
    Blk** bp = be;
    // Scan all blocks to find where the temporary is defined and used, and
    // collect candidate blocks.
    for (Blk* b = fn->start; b; b = b->link) {
      b->visit = 0;
      Ref r = R;
      for (Ins* i = b->ins; i < &b->ins[b->nins]; i++) {
        // If we have a replacement for t, update uses in this instruction.
        if (!req(r, R)) {
          if (req(i->arg[0], TMP(t))) {
            i->arg[0] = r;
          }
          if (req(i->arg[1], TMP(t))) {
            i->arg[1] = r;
          }
        }
        // If this instruction defines t, check if a phi is needed.
        if (req(i->to, TMP(t))) {
          if (!bshas(b->out, t)) {
            // If t is not live-out, assign a new SSA name.
            r = refindex(t, fn);
            i->to = r;
          } else {
            // If t is live-out, mark this block as needing a phi candidate.
            if (!bshas(u, b->id)) {
              bsset(u, b->id);
              *--bp = b;
            }
            // Merge class information for phi node.
            if (clsmerge(&k, i->cls)) {
              die("invalid input");
            }
          }
        }
      }
      // Also update jmp argument if it uses t.
      if (!req(r, R) && req(b->jmp.arg, TMP(t))) {
        b->jmp.arg = r;
      }
    }
    // Save the set of blocks where t is defined or needs a phi.
    bscopy(defs, u);
    // Iteratively place phi nodes in dominance frontiers.
    while (bp != be) {
      fn->tmp[t].visit = t;
      Blk* b = *bp++;
      bsclr(u, b->id);
      for (uint n = 0; n < b->nfron; n++) {
        Blk* a = b->fron[n];
        // Only insert a phi node if not already visited and t is live-in at a.
        if (a->visit++ == 0) {
          if (bshas(a->in, t)) {
            // Allocate and insert the phi node at the beginning of block a.
            Phi* p = alloc(sizeof *p);
            p->cls = k;
            p->to = TMP(t);
            p->link = a->phi;
            p->arg = vnew(0, sizeof p->arg[0], PFn);
            p->blk = vnew(0, sizeof p->blk[0], PFn);
            a->phi = p;
            // If a is not already in defs or u, add it to the worklist for
            // further processing.
            if (!bshas(defs, a->id)) {
              if (!bshas(u, a->id)) {
                bsset(u, a->id);
                *--bp = a;
              }
            }
          }
        }
      }
    }
  }
  free(blist);
}

typedef struct Name Name;
struct Name {
  Ref r;
  Blk* b;
  Name* up;
};

static Name* namel;

static Name* nnew(Ref r, Blk* b, Name* up) {
  Name* n;

  if (namel) {
    n = namel;
    namel = n->up;
  } else {
    /* could use alloc, here
     * but namel should be reset
     */
    n = emalloc(sizeof *n);
  }
  n->r = r;
  n->b = b;
  n->up = up;
  return n;
}

static void nfree(Name* n) {
  n->up = namel;
  namel = n;
}

// Assigns a new SSA name to a definition (phi or instruction result) in block
// b. This function is called during SSA renaming to create a new version of a
// temporary when it is defined. It updates the stack of SSA names for the
// temporary, so that subsequent uses in dominated blocks will refer to the
// correct version. It also updates the .visit field to track the mapping from
// original to renamed temporaries.
static void rendef(Ref* r, Blk* b, Name** stk, Fn* fn) {
  Ref r1;
  int t;

  t = r->val;
  if (req(*r, R) || !fn->tmp[t].visit) {
    return;
  }
  r1 = refindex(t, fn);
  fn->tmp[r1.val].visit = t;
  stk[t] = nnew(r1, b, stk[t]);
  *r = r1;
}

static Ref getstk(int t, Blk* b, Name** stk) {
  Name *n, *n1;

  n = stk[t];
  while (n && !dom(n->b, b)) {
    n1 = n;
    n = n->up;
    nfree(n1);
  }
  stk[t] = n;
  if (!n) {
    /* uh, oh, warn */
    return UNDEF;
  } else {
    return n->r;
  }
}

/*
 * Recursively renames variables in a block and its dominated children as part
 * of SSA construction. This function traverses the dominator tree, updating
 * references to temporaries so that each use refers to the correct SSA version,
 * and managing the stacks of SSA names for each temporary. It also updates phi
 * nodes in successor blocks to reflect the correct incoming SSA values.
 */
static void renblk(Blk* b, Name** stk, Fn* fn) {
  Phi* p;
  Ins* i;
  Blk *s, **ps, *succ[3];
  int t, m;

  // Process phi nodes in this block: assign new SSA names for each phi
  // destination.
  for (p = b->phi; p; p = p->link) {
    rendef(&p->to, b, stk, fn);
  }

  // For each instruction, update arguments to refer to the current SSA name,
  // and assign new SSA names to instruction results.
  for (i = b->ins; i < &b->ins[b->nins]; i++) {
    for (m = 0; m < 2; m++) {
      t = i->arg[m].val;
      if (rtype(i->arg[m]) == RTmp) {
        if (fn->tmp[t].visit) {
          i->arg[m] = getstk(t, b, stk);
        }
      }
    }
    rendef(&i->to, b, stk, fn);
  }

  // Update jump argument to refer to the current SSA name if needed.
  t = b->jmp.arg.val;
  if (rtype(b->jmp.arg) == RTmp) {
    if (fn->tmp[t].visit) {
      b->jmp.arg = getstk(t, b, stk);
    }
  }

  // For each successor, update its phi nodes to record the value coming from
  // this block. This ensures that phi nodes in successor blocks have the
  // correct incoming SSA values.
  succ[0] = b->s1;
  succ[1] = b->s2 == b->s1 ? 0 : b->s2;
  succ[2] = 0;
  for (ps = succ; (s = *ps); ps++) {
    for (p = s->phi; p; p = p->link) {
      t = p->to.val;
      if ((t = fn->tmp[t].visit)) {
        m = p->narg++;
        vgrow(&p->arg, p->narg);
        vgrow(&p->blk, p->narg);
        p->arg[m] = getstk(t, b, stk);
        p->blk[m] = b;
      }
    }
  }

  // Recursively process all children in the dominator tree.
  for (s = b->dom; s; s = s->dlink) {
    renblk(s, stk, fn);
  }
}

/* require rpo and use */
// Converts the function to SSA (Static Single Assignment) form.
// This function assumes that the reverse postorder (rpo) and use information
// have already been computed for the function.
void ssa(Fn* fn) {
  int nt = fn->ntmp;
  Name** stk = emalloc(nt * sizeof stk[0]);
  int d = debug['L'];
  debug['L'] = 0;

  filldom(fn);  // Compute dominator tree for the function

  if (debug['N']) {
    fprintf(stderr, "\n> Dominators:\n");
    for (Blk* b1 = fn->start; b1; b1 = b1->link) {
      if (!b1->dom) {
        continue;
      }
      fprintf(stderr, "%10s:", b1->name);
      for (Blk* b = b1->dom; b; b = b->dlink) {
        fprintf(stderr, " %s", b->name);
      }
      fprintf(stderr, "\n");
    }
  }

  fillfron(fn);
  filllive(fn);
  phiins(fn);

  // Perform the actual SSA renaming pass, recursively traversing the dominator
  // tree.
  renblk(fn->start, stk, fn);

  // Clean up the temporary stack.
  while (nt--) {
    Name* n;
    while ((n = stk[nt])) {
      stk[nt] = n->up;
      nfree(n);
    }
  }

  debug['L'] = d;
  free(stk);

  if (debug['N']) {
    fprintf(stderr, "\n> After SSA construction:\n");
    printfn(fn, stderr);
  }
}

static int phicheck(Phi* p, Blk* b, Ref t) {
  for (uint n = 0; n < p->narg; n++) {
    if (req(p->arg[n], t)) {
      Blk* b1 = p->blk[n];
      if (b1 != b && !sdom(b, b1)) {
        return 1;
      }
    }
  }
  return 0;
}

/* require use and ssa */
void ssacheck(Fn* fn) {
  Tmp* t;
  Ins* i;
  Phi* p;
  Use* u;
  Blk *b, *bu;
  Ref r;

  // First, check that each SSA temporary is defined at most once,
  // and that every used temporary is defined somewhere.
  for (t = &fn->tmp[Tmp0]; t - fn->tmp < fn->ntmp; t++) {
    if (t->ndef > 1) {
      err("ssa temporary %%%s defined more than once", t->name);
    }
    if (t->nuse > 0 && t->ndef == 0) {
      bu = fn->rpo[t->use[0].bid];
      goto Err;
    }
  }

  // For each block, check that all uses of each SSA value are dominated by its
  // definition. This includes both phi nodes and regular instructions.
  for (b = fn->start; b; b = b->link) {
    // Check phis in the block.
    for (p = b->phi; p; p = p->link) {
      r = p->to;
      t = &fn->tmp[r.val];
      for (u = t->use; u < &t->use[t->nuse]; u++) {
        bu = fn->rpo[u->bid];
        // For phi uses, check that the use is properly dominated.
        if (u->type == UPhi) {
          if (phicheck(u->u.phi, b, r)) {
            goto Err;
          }
        } else
          // For non-phi uses, ensure the use is dominated by the definition.
          if (bu != b && !sdom(b, bu)) {
            goto Err;
          }
      }
    }
    // Check regular instructions in the block.
    for (i = b->ins; i < &b->ins[b->nins]; i++) {
      if (rtype(i->to) != RTmp) {
        continue;
      }
      r = i->to;
      t = &fn->tmp[r.val];
      for (u = t->use; u < &t->use[t->nuse]; u++) {
        bu = fn->rpo[u->bid];
        if (u->type == UPhi) {
          // For phi uses, check that the use is properly dominated.
          if (phicheck(u->u.phi, b, r)) {
            goto Err;
          }
        } else {
          // For non-phi uses, if the use is in the same block as the
          // definition, ensure the use occurs after the definition.
          if (bu == b) {
            if (u->type == UIns) {
              if (u->u.ins <= i) {
                goto Err;
              }
            }
          } else
            // Otherwise, ensure the use is dominated by the definition.
            if (!sdom(b, bu)) {
              goto Err;
            }
        }
      }
    }
  }
  return;
Err:
  if (t->visit) {
    die("%%%s violates ssa invariant", t->name);
  } else {
    err("ssa temporary %%%s is used undefined in @%s", t->name, bu->name);
  }
}
