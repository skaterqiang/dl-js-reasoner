'use strict';

// ---------------------------------------------------------------------------
// tableau/GroundDisjunction.js — a ground (variable-free) disjunction of atoms
// the tableau must satisfy by branching.
//
// Mirrors org.semanticweb.HermiT.tableau.{GroundDisjunction,
// GroundDisjunctionHeader}. When a DL-clause with n>1 head atoms matches, the
// matched head becomes a GroundDisjunction over concrete Nodes. The calculus
// picks one disjunct, asserts it, and records a DisjunctionBranchingPoint so it
// can try the others on backjump.
//
// A header is shared between all ground disjunctions with the same shape
// (same predicates + arities) so the disjunct layout is computed once.
// ---------------------------------------------------------------------------

const { AnnotatedEquality, EQUALITY } = require('../model/DLPredicate');

const _headers = new Map();

class GroundDisjunctionHeader {
  /**
   * @param {{dlPredicate:DLPredicate, arity:number}[]} disjuncts
   */
  constructor(disjuncts) {
    this.disjuncts = disjuncts;
    // disjunctStart[i] = offset into the flat argument array for disjunct i.
    this.disjunctStart = [];
    let off = 0;
    for (const d of disjuncts) { this.disjunctStart.push(off); off += d.arity; }
    this.numberOfArguments = off;
    this.numberOfDisjuncts = disjuncts.length;
    // Disjunct evaluation order. HermiT sorts by a backtracking heuristic; we
    // keep declaration order (correct, slightly less optimal).
    this.sortedDisjunctIndexes = disjuncts.map((_, i) => i);
  }

  getSortedDisjunctIndexes() { return this.sortedDisjunctIndexes; }
}

function getHeader(disjuncts) {
  const key = disjuncts.map(d => `${d.dlPredicate.kind}:${d.dlPredicate.toString()}/${d.arity}`).join('|');
  let h = _headers.get(key);
  if (!h) { h = new GroundDisjunctionHeader(disjuncts); _headers.set(key, h); }
  return h;
}

class GroundDisjunction {
  /**
   * @param {GroundDisjunctionHeader} header
   * @param {Node[]} arguments  flat argument nodes (header.numberOfArguments long)
   * @param {DependencySet} dependencySet
   * @param {boolean[]} [isCore] per-disjunct core flags (defaults to all true)
   */
  constructor(header, args, dependencySet, isCore) {
    this.header = header;
    this.arguments = args;
    this.dependencySet = dependencySet;
    this.isCoreFlags = isCore || header.disjuncts.map(() => true);
    // Doubly-linked list pointers (managed by the Tableau).
    this.previous = null;
    this.next = null;
  }

  getNumberOfDisjuncts() { return this.header.numberOfDisjuncts; }
  getDLPredicate(i) { return this.header.disjuncts[i].dlPredicate; }
  getArgument(i, argIndex) { return this.arguments[this.header.disjunctStart[i] + argIndex]; }
  getDependencySet() { return this.dependencySet; }
  getHeader() { return this.header; }
  isCore(i) { return !!this.isCoreFlags[i]; }

  /**
   * Called by Tableau.backtrackTo when the disjunction is rolled back. HermiT
   * releases the permanent dependency set here; our dependency sets are
   * interned and immutable, so this only drops the reference. The list links
   * are deliberately left intact: backtrackTo walks `next` *after* destroying.
   */
  destroy(tableau) {
    if (tableau && tableau.dependencySetFactory) {
      tableau.dependencySetFactory.removeUsage(this.dependencySet);
    }
    this.dependencySet = null;
  }

  isPruned() {
    for (const n of this.arguments) if (n.pruned) return true;
    return false;
  }

  /** True if some disjunct already holds in the current model. */
  isSatisfied(tableau) {
    const em = tableau.extensionManager;
    for (let i = 0; i < this.getNumberOfDisjuncts(); i++) {
      const pred = this.getDLPredicate(i);
      const arity = pred.getArity();
      if (arity === 1) {
        if (em.containsAssertion(pred, this.getArgument(i, 0).getCanonicalNode())) return true;
      } else if (arity === 2) {
        if (em.containsAssertion(pred, this.getArgument(i, 0).getCanonicalNode(), this.getArgument(i, 1).getCanonicalNode())) return true;
      } else if (arity === 3 && pred instanceof AnnotatedEquality) {
        if (em.containsAssertion(pred,
          this.getArgument(i, 0).getCanonicalNode(),
          this.getArgument(i, 1).getCanonicalNode(),
          this.getArgument(i, 2).getCanonicalNode())) return true;
      }
    }
    return false;
  }

  /** Assert disjunct `i` into the tableau under `dependencySet`. */
  addDisjunctToTableau(tableau, i, dependencySet) {
    const pred = this.getDLPredicate(i);
    const arity = pred.getArity();
    const core = this.isCore(i);
    let ds = dependencySet;
    if (arity === 1) {
      const n0 = this.getArgument(i, 0);
      ds = tableau.addCanonicalNodeDependencySet(n0, ds);
      return tableau.extensionManager.addAssertion(pred, n0.getCanonicalNode(), ds, core);
    }
    if (arity === 2) {
      const n0 = this.getArgument(i, 0), n1 = this.getArgument(i, 1);
      ds = tableau.addCanonicalNodeDependencySet(n0, ds);
      ds = tableau.addCanonicalNodeDependencySet(n1, ds);
      return tableau.extensionManager.addAssertion(pred, n0.getCanonicalNode(), n1.getCanonicalNode(), ds, core);
    }
    if (arity === 3 && pred instanceof AnnotatedEquality) {
      const n0 = this.getArgument(i, 0), n1 = this.getArgument(i, 1), n2 = this.getArgument(i, 2);
      ds = tableau.addCanonicalNodeDependencySet(n0, ds);
      ds = tableau.addCanonicalNodeDependencySet(n1, ds);
      ds = tableau.addCanonicalNodeDependencySet(n2, ds);
      return tableau.extensionManager.addAssertion(pred, n0.getCanonicalNode(), n1.getCanonicalNode(), n2.getCanonicalNode(), ds, core);
    }
    throw new Error(`Unsupported disjunct arity ${arity} for ${pred}`);
  }

  toString() {
    const parts = [];
    for (let i = 0; i < this.getNumberOfDisjuncts(); i++) {
      const pred = this.getDLPredicate(i);
      const args = [];
      for (let a = 0; a < pred.getArity(); a++) args.push(this.getArgument(i, a).nodeID);
      parts.push(`${pred}(${args.join(',')})`);
    }
    return parts.join(' v ');
  }
}

module.exports = { GroundDisjunction, GroundDisjunctionHeader, getHeader };
