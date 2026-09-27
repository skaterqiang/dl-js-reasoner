'use strict';

// ---------------------------------------------------------------------------
// tableau/DependencySet.js — the set of branching points a derived fact depends
// on. Mirrors org.semanticweb.HermiT.tableau.{DependencySet,
// PermanentDependencySet, UnionDependencySet}.
//
// A DependencySet is an immutable sorted set of branching-point levels (ints).
// The empty set is the PERMANENT dependency set (a fact that holds on every
// branch). On a clash, the tableau reads the clash's dependency set, takes its
// maximum level, and backjumps straight to that branching point — this is
// dependency-directed backjumping, not chronological backtracking.
//
// Implemented as a sorted array of levels; interned for identity comparison.
// ---------------------------------------------------------------------------

class DependencySet {
  /** @param {number[]} sortedLevels strictly ascending */
  constructor(sortedLevels) {
    this.levels = sortedLevels;
    this.isPermanent = sortedLevels.length === 0;
  }

  isEmpty() { return this.levels.length === 0; }

  /** The largest branching-point level in this set, or -1 if permanent. */
  maximum() {
    return this.levels.length === 0 ? -1 : this.levels[this.levels.length - 1];
  }

  contains(level) { return this.levels.includes(level); }

  /** Union of two dependency sets. */
  union(other) {
    if (this.isPermanent) return other;
    if (other.isPermanent) return this;
    const merged = [];
    let i = 0, j = 0;
    while (i < this.levels.length && j < other.levels.length) {
      const a = this.levels[i], b = other.levels[j];
      if (a < b) { merged.push(a); i++; }
      else if (b < a) { merged.push(b); j++; }
      else { merged.push(a); i++; j++; }
    }
    while (i < this.levels.length) merged.push(this.levels[i++]);
    while (j < other.levels.length) merged.push(other.levels[j++]);
    return getDependencySet(merged);
  }

  /** This set plus a branching-point level. */
  addBranchingPoint(level) {
    if (this.contains(level)) return this;
    const merged = this.levels.slice();
    // insert keeping sorted
    let pos = merged.length;
    while (pos > 0 && merged[pos - 1] > level) pos--;
    merged.splice(pos, 0, level);
    return getDependencySet(merged);
  }

  /** This set minus a branching-point level. */
  removeBranchingPoint(level) {
    if (!this.contains(level)) return this;
    return getDependencySet(this.levels.filter(l => l !== level));
  }

  toString() {
    return this.isPermanent ? '{}' : `{${this.levels.join(', ')}}`;
  }
}

// ---- interning --------------------------------------------------------------

/**
 * The empty dependency set: a fact that holds on every branch. It is a real
 * DependencySet instance so that `union`/`maximum`/`contains` work uniformly.
 */
const PERMANENT = Object.freeze(new DependencySet(Object.freeze([])));

const _cache = new Map();
_cache.set('', PERMANENT);

function getDependencySet(levels) {
  if (levels.length === 0) return PERMANENT;
  const key = levels.join(',');
  let ds = _cache.get(key);
  if (!ds) {
    ds = new DependencySet(levels);
    _cache.set(key, ds);
  }
  return ds;
}

/** Build a dependency set from an unsorted iterable of levels. */
function dependencySetFrom(levels) {
  const sorted = [...new Set(levels)].sort((a, b) => a - b);
  return getDependencySet(sorted);
}

module.exports = {
  DependencySet,
  PERMANENT,
  getDependencySet,
  dependencySetFrom
};
