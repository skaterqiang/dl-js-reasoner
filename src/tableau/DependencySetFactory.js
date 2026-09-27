'use strict';

// ---------------------------------------------------------------------------
// tableau/DependencySetFactory.js — the façade other tableau components use to
// build and recycle dependency sets.
//
// Mirrors org.semanticweb.HermiT.tableau.DependencySetFactory. HermiT's factory
// is a hand-rolled hash-consing pool with explicit reference counting
// (addUsage/removeUsage/removeUnusedSets) so that PermanentDependencySet
// objects can be recycled between reasoning runs.
//
// In this port DependencySet objects are already interned and immutable
// (see DependencySet.js), so reference counting is unnecessary — the JS garbage
// collector does the job. This class therefore keeps the *API* (so the rest of
// the tableau reads exactly like HermiT) but the bookkeeping methods are no-ops.
// ---------------------------------------------------------------------------

const { PERMANENT, getDependencySet, dependencySetFrom } = require('./DependencySet');

class DependencySetFactory {
  constructor() {
    /** Number of distinct non-permanent sets handed out (diagnostics only). */
    this.numberOfSets = 0;
  }

  /** The empty (permanent) dependency set. */
  emptySet() { return PERMANENT; }

  /**
   * Interning lookup. HermiT returns a PermanentDependencySet that must be
   * released with removeUsage; here the sets are shared and immutable.
   */
  getPermanent(dependencySet) {
    if (dependencySet === null || dependencySet === undefined) return PERMANENT;
    if (dependencySet instanceof Object && Array.isArray(dependencySet.levels)) {
      return getDependencySet(dependencySet.levels);
    }
    return dependencySet;
  }

  /** Build a set from an iterable of branching-point levels. */
  create(levels) { return dependencySetFrom(levels); }

  addBranchingPoint(dependencySet, branchingPoint) {
    const base = dependencySet || PERMANENT;
    return base.addBranchingPoint(branchingPoint);
  }

  removeBranchingPoint(dependencySet, branchingPoint) {
    const base = dependencySet || PERMANENT;
    return base.removeBranchingPoint(branchingPoint);
  }

  unionWith(set1, set2) {
    const a = set1 || PERMANENT;
    const b = set2 || PERMANENT;
    return a.union(b);
  }

  // ---- reference counting (no-ops: sets are interned & immutable) -----------

  addUsage(/* dependencySet */) { }
  removeUsage(/* dependencySet */) { }
  removeUnusedSets() { }
  clear() { this.numberOfSets = 0; }
}

module.exports = { DependencySetFactory };
