'use strict';

// ---------------------------------------------------------------------------
// tableau/ExtensionTable.js — the store of all ground tuples of one arity.
//
// Mirrors org.semanticweb.HermiT.tableau.ExtensionTable (+ the tuple-index
// machinery). A tuple is [dlPredicate, node0, node1?, node2?]; tuple[0] is the
// predicate and the remaining slots are Nodes. Each tuple carries the
// DependencySet recording which branching points it depends on.
//
// Three capabilities the calculus relies on:
//   1. containsTuple / getDependencySet — O(1) membership by interned key.
//   2. The three delta windows (HermiT's m_afterExtensionOldTupleIndex /
//      m_afterExtensionThisTupleIndex / m_afterDeltaNewTupleIndex):
//
//         [0 .................. old) [old ............. this) [this ...... new)
//              extension-old              extension-new            delta-new
//
//      propagateDeltaNew() rotates the windows and returns whether delta-new
//      was non-empty. Hyperresolution is triggered from the *extension-old*
//      window (tuples added before the previous propagation) and matches
//      against *extension-this* (everything currently present) — exactly
//      HermiT's View.DELTA_OLD / View.EXTENSION_THIS split. Getting this right
//      is what makes the saturation loop terminate and fire each clause once
//      per relevant tuple.
//
//   3. checkpoint / backtrack — a branching point records the three window
//      indices; on backtrack everything added afterwards is removed.
//
// Tuples whose nodes have been merged/pruned become "inactive"; they stay in
// the table (so backtracking can restore them) but are skipped by retrieval.
//
// Note (faithful to HermiT): re-adding an existing tuple with a *weaker*
// dependency set updates the stored set but does NOT re-propagate the tuple.
// Every derivation that used the old set already fired, and the union only
// weakens the result, so re-firing would be redundant work.
// ---------------------------------------------------------------------------

const { PERMANENT } = require('./DependencySet');
const { THING, RDFS_LITERAL } = require('../model/DLPredicate');

/** Stable identity key for an interned predicate. */
function predicateKey(p) {
  return `${p.kind}\u0001${p.toString()}`;
}

/** Key for a whole tuple (predicate + node ids). */
function tupleKey(tuple) {
  let k = predicateKey(tuple[0]);
  for (let i = 1; i < tuple.length; i++) {
    k += '\u0002' + (tuple[i] ? tuple[i].nodeID : 'null');
  }
  return k;
}

class ExtensionTable {
  /**
   * @param {object} tableau     owning Tableau (for isTupleActive checks)
   * @param {number} arity       number of slots including the predicate
   */
  constructor(tableau, arity) {
    this.tableau = tableau;
    this.arity = arity;

    /** key → entry {tuple, dependencySet, isCore, key, index} */
    this.entries = new Map();
    /** entries in insertion order (the "tuple table") */
    this.order = [];
    /** secondary index: predicateKey → entry[] (fast retrieval by predicate) */
    this.byPredicate = new Map();

    // The three delta windows (indices into `order`).
    this.afterExtensionOld = 0;
    this.afterExtensionThis = 0;
    this.afterDeltaNew = 0;

    /**
     * Window snapshots indexed by ABSOLUTE branching-point level, exactly like
     * HermiT's `m_indicesByBranchingPoint[level*3 .. level*3+2]`.
     *
     * This must NOT be a push/pop stack: dependency-directed backjumping can
     * skip levels (a clash whose dependency set is {0} backjumps straight from
     * level 1 to level 0), and `Tableau.backtrackTo` calls `backtrack()` only
     * once per backjump. A stack would then pop the wrong snapshot and leave
     * stale tuples in the table.
     * @type {[number,number,number][]}
     */
    this.indicesByBranchingPoint = [];
  }

  // ---- core operations ------------------------------------------------------

  /**
   * Add a tuple. Returns true if it was newly added (false if already present,
   * in which case the dependency set is unioned into the existing entry).
   *
   * @param {Array} tuple           [predicate, node...]
   * @param {DependencySet} dependencySet
   * @param {boolean} isCore        core flag (only used by validated blocking)
   */
  addTuple(tuple, dependencySet, isCore = true) {
    if (!this.isTupleActive(tuple)) return false;

    // HermiT never stores owl:Thing / rdfs:Literal unless some DL-clause uses
    // them as a delta predicate: containsConceptAssertion(THING, abstractNode)
    // and containsDataRangeAssertion(RDFS_LITERAL, concreteNode) answer `true`
    // directly, so the tuples would be dead weight (and would make every node
    // fire the delta loop).
    const t = this.tableau;
    if (t) {
      if (tuple[0] === THING && !t.needsThingExtension) return false;
      if (tuple[0] === RDFS_LITERAL && !t.needsRDFSLiteralExtension) return false;
    }

    const key = tupleKey(tuple);
    const existing = this.entries.get(key);
    if (existing) {
      // Already present. HermiT (ExtensionTableWithTupleIndexes.addTuple)
      // deliberately leaves the stored dependency set ALONE here and only
      // widens the core flag — do not "helpfully" union the two sets.
      //
      // Unioning looks harmless but breaks dependency-directed backjumping:
      // the entry was appended BEFORE this branching point's checkpoint, so
      // `backtrack()` truncates the table above the checkpoint and never
      // touches this entry. A mutation to `existing.dependencySet` is therefore
      // invisible to the snapshot and is never undone. The stale level then
      // keeps reappearing in every later clash dependency set, so
      // `Tableau.doIteration` backjumps to the SAME branching point over and
      // over and `DisjunctionBranchingPoint.startNextChoice` eventually runs
      // past its last disjunct (`header.disjuncts[undefined]` → TypeError).
      //
      // Keeping the original set is sound: it records one concrete derivation
      // of the fact, and a clash that uses it backjumps to a level at or below
      // the one that really introduced it. At worst that is a slightly more
      // conservative jump, never a wrong one.
      if (isCore && !existing.isCore) {
        existing.isCore = true;
        // ExtensionTableWithTupleIndexes.addTuple notifies the strategy so
        // validated blocking can widen its core labels.
        if (t && typeof t.assertionCoreSet === 'function') t.assertionCoreSet(tuple);
      }
      return false;
    }

    const entry = {
      tuple,
      dependencySet: dependencySet || PERMANENT,
      isCore,
      key,
      index: this.order.length
    };
    this.entries.set(key, entry);
    this.order.push(entry);
    let list = this.byPredicate.get(predicateKey(tuple[0]));
    if (!list) { list = []; this.byPredicate.set(predicateKey(tuple[0]), list); }
    list.push(entry);
    this.afterDeltaNew = this.order.length;
    // postAdd (HermiT: ExtensionTable.postAdd) — node counters, existential
    // bookkeeping, expansion-strategy notification and clash detection.
    if (this.tableau && typeof this.tableau.tupleAdded === 'function') {
      this.tableau.tupleAdded(this, tuple, entry.dependencySet, isCore);
    }
    return true;
  }

  containsTuple(tuple) {
    const entry = this.entries.get(tupleKey(tuple));
    return entry !== undefined && this.isTupleActive(entry.tuple);
  }

  /** Raw membership ignoring node activity. */
  containsTupleRaw(tuple) {
    return this.entries.has(tupleKey(tuple));
  }

  getDependencySet(tuple) {
    const entry = this.entries.get(tupleKey(tuple));
    return entry ? entry.dependencySet : null;
  }

  getEntry(tuple) {
    return this.entries.get(tupleKey(tuple)) || null;
  }

  isCore(tuple) {
    const entry = this.entries.get(tupleKey(tuple));
    return entry ? !!entry.isCore : false;
  }

  /** All active entries with the given predicate. */
  getTuplesByPredicate(predicate) {
    const list = this.byPredicate.get(predicateKey(predicate));
    if (!list) return [];
    return list.filter(e => this.isTupleActive(e.tuple));
  }

  /** Every active entry in the table (insertion order). */
  getAllEntries() {
    return this.order.filter(e => this.isTupleActive(e.tuple));
  }

  /**
   * All active entries matching a partially-specified pattern.
   * @param {DLPredicate|null} predicate null = match any predicate
   * @param {(Node|null)[]} argPattern slots 1..arity-1; null = unbound
   */
  retrieve(predicate, argPattern) {
    const out = [];
    const lists = predicate === null
      ? [...this.byPredicate.values()]
      : (this.byPredicate.get(predicateKey(predicate)) ? [this.byPredicate.get(predicateKey(predicate))] : []);
    for (const list of lists) {
      for (const e of list) {
        if (!this.isTupleActive(e.tuple)) continue;
        let ok = true;
        for (let i = 0; i < argPattern.length; i++) {
          const want = argPattern[i];
          if (want !== null && want !== undefined && e.tuple[i + 1] !== want) { ok = false; break; }
        }
        if (ok) out.push(e);
      }
    }
    return out;
  }

  /**
   * A tuple is active iff every node slot is active (not merged, not pruned).
   * Mirrors ExtensionTable.isTupleActive.
   */
  isTupleActive(tuple) {
    for (let i = 1; i < tuple.length; i++) {
      const n = tuple[i];
      if (n && !n.isActive()) return false;
    }
    return true;
  }

  // ---- the three delta windows ------------------------------------------------

  /**
   * Rotate the windows: extension-old ← extension-this, extension-this ←
   * delta-new, delta-new ← empty. Returns true iff delta-new was non-empty
   * (i.e. the previous round produced new facts worth re-firing clauses over).
   *
   * Mirrors ExtensionTable.propagateDeltaNew.
   */
  propagateDeltaNew() {
    const deltaNewNotEmpty = this.afterExtensionThis !== this.afterDeltaNew;
    this.afterExtensionOld = this.afterExtensionThis;
    this.afterExtensionThis = this.afterDeltaNew;
    return deltaNewNotEmpty;
  }

  hasDeltaNew() {
    return this.afterExtensionThis !== this.afterDeltaNew;
  }

  /**
   * Snapshot of the extension-old window: the entries hyperresolution should
   * fire over this round. Indices are stable because entries are only ever
   * appended (removal happens solely on backtrack, which resets the windows).
   */
  getDeltaOldEntries() {
    return this.order.slice(this.afterExtensionOld, this.afterExtensionThis);
  }

  /** Snapshot of the delta-new window (used by the datatype manager). */
  getDeltaNewSnapshot() {
    return this.order.slice(this.afterExtensionThis, this.afterDeltaNew);
  }

  /** Number of entries in the extension-old window. */
  getDeltaOldSize() {
    return this.afterExtensionThis - this.afterExtensionOld;
  }

  // ---- checkpointing / backtracking ----------------------------------------

  branchingPointPushed() {
    const level = this.tableau.getCurrentBranchingPoint().level;
    this.indicesByBranchingPoint[level] = [
      this.afterExtensionOld,
      this.afterExtensionThis,
      this.afterDeltaNew
    ];
  }

  /**
   * Undo everything added after the checkpoint of the CURRENT branching point
   * (`Tableau.backtrackTo` has already lowered `currentBranchingPoint`).
   * Removed entries are returned so the Tableau can also undo node-structure
   * side effects.
   */
  backtrack() {
    const level = this.tableau.getCurrentBranchingPoint().level;
    const snapshot = this.indicesByBranchingPoint[level];
    if (!snapshot) return [];
    const [oldIdx, thisIdx, newIdx] = snapshot;
    const removed = [];
    while (this.order.length > newIdx) {
      const entry = this.order.pop();
      this.entries.delete(entry.key);
      const list = this.byPredicate.get(predicateKey(entry.tuple[0]));
      if (list) {
        const idx = list.indexOf(entry);
        if (idx >= 0) list.splice(idx, 1);
      }
      // postRemove (HermiT: ExtensionTable.postRemove).
      if (this.tableau && typeof this.tableau.tupleRemoved === 'function') {
        this.tableau.tupleRemoved(this, entry.tuple, entry);
      }
      removed.push(entry);
    }
    this.afterExtensionOld = oldIdx;
    this.afterExtensionThis = thisIdx;
    this.afterDeltaNew = newIdx;
    return removed;
  }

  clear() {
    this.entries.clear();
    this.order.length = 0;
    this.byPredicate.clear();
    this.indicesByBranchingPoint.length = 0;
    this.afterExtensionOld = 0;
    this.afterExtensionThis = 0;
    this.afterDeltaNew = 0;
  }

  get size() { return this.order.length; }
}

module.exports = { ExtensionTable, tupleKey, predicateKey };
