'use strict';

// ---------------------------------------------------------------------------
// tableau/HyperresolutionManager.js — the DL-clause engine.
//
// Mirrors org.semanticweb.HermiT.tableau.{HyperresolutionManager,
// DLClauseEvaluator, BodyAtomsSwapper}.
//
// HermiT compiles each DL-clause into a small bytecode program (a chain of
// Worker objects) for speed. The compilation is a pure performance device: its
// observable behaviour is "match the body conjunction against the extension
// tables, binding the delta tuple first, then derive the head". This module
// implements exactly that behaviour with a direct recursive matcher instead of
// a compiled program — same triggering discipline, same dependency-set algebra,
// same head derivation, without the bytecode layer.
//
// === Triggering discipline (the heart of hypertableau) =======================
//
// For every DL-clause and *every* body atom that has an extension, HermiT
// creates a variant of the clause with that atom moved to the front (the
// "delta" atom) and the remaining atoms ordered by a goodness heuristic. The
// variant is indexed by the delta atom's predicate. During saturation the
// manager walks the DELTA_OLD window of each extension table (tuples added
// before the previous propagation round) and fires every clause variant indexed
// under that tuple's predicate, with the tuple pre-bound as the delta atom.
//
// This is what makes hypertableau terminate and stay fast:
//   • every clause fires once per newly added relevant tuple (not per round),
//   • the remaining body atoms are matched against EXTENSION_THIS (everything
//     currently true), so one new tuple can complete many partial matches,
//   • hyperresolution — whole conjunctions are resolved in one step, so no
//     intermediate ground resolvents are ever materialised.
//
// === Head derivation =======================================================
//
//   head length 0 → the body is unsatisfiable: setClash(union of body dep sets)
//   head length 1 → deterministic consequence: add the ground atom
//   head length n → build a GroundDisjunction and hand it to the Tableau, which
//                   will branch on it (only if not already satisfied)
//
// The derived dependency set is the union of the dependency sets of all *real*
// body atoms; the ordering pseudo-atoms (NodeIDLessEqualThan,
// NodeIDsAscendingOrEqual) have no extension and contribute nothing.
// ---------------------------------------------------------------------------

const {
  AtomicRole,
  InverseRole,
  NodeIDLessEqualThan,
  NodeIDsAscendingOrEqual,
  NODE_ID_LESS_EQUAL_THAN,
  THING,
  INTERNAL_NAMED,
  RDFS_LITERAL
} = require('../model/DLPredicate');
const { Variable } = require('../model/Term');
const { createAtom } = require('../model/Atom');
const { createDLClause } = require('../model/DLClause');
const { GroundDisjunction, getHeader } = require('./GroundDisjunction');
const { PERMANENT } = require('./DependencySet');

/**
 * Ordering pseudo-predicates have no extension: they are evaluated directly on
 * node IDs rather than looked up in a table, and therefore can never be the
 * delta atom of a clause.
 */
function isPredicateWithExtension(dlPredicate) {
  return dlPredicate !== NODE_ID_LESS_EQUAL_THAN
    && !(dlPredicate instanceof NodeIDsAscendingOrEqual);
}

// ===========================================================================
// BodyAtomsSwapper — produce the clause variants indexed by delta predicate.
// ===========================================================================

/**
 * Mirrors HyperresolutionManager.BodyAtomsSwapper. getSwappedDLClause(i)
 * returns an equivalent clause whose body starts with atom i and whose
 * remaining atoms are ordered so that the most selective (most variables
 * already bound) come first — this keeps the matcher's intermediate result sets
 * small.
 */
class BodyAtomsSwapper {
  constructor(dlClause) {
    this.dlClause = dlClause;
    this.nodeIDComparisonAtoms = [];
    this.usedAtoms = new Array(dlClause.getBodyLength()).fill(false);
    this.reorderedAtoms = [];
    this.boundVariables = new Set();
  }

  getSwappedDLClause(bodyIndex) {
    const clause = this.dlClause;
    this.nodeIDComparisonAtoms.length = 0;
    for (let i = this.usedAtoms.length - 1; i >= 0; --i) {
      this.usedAtoms[i] = false;
      const atom = clause.getBodyAtom(i);
      if (atom.dlPredicate === NODE_ID_LESS_EQUAL_THAN) this.nodeIDComparisonAtoms.push(atom);
    }
    this.reorderedAtoms.length = 0;
    this.boundVariables.clear();

    const first = clause.getBodyAtom(bodyIndex);
    _collectVariables(first, this.boundVariables);
    this.reorderedAtoms.push(first);
    this.usedAtoms[bodyIndex] = true;

    while (this.reorderedAtoms.length !== this.usedAtoms.length) {
      let bestAtom = null, bestIndex = -1, bestGoodness = -Infinity;
      for (let i = this.usedAtoms.length - 1; i >= 0; --i) {
        if (this.usedAtoms[i]) continue;
        const atom = clause.getBodyAtom(i);
        const goodness = this._getAtomGoodness(atom);
        if (goodness > bestGoodness) {
          bestAtom = atom; bestGoodness = goodness; bestIndex = i;
        }
      }
      this.reorderedAtoms.push(bestAtom);
      this.usedAtoms[bestIndex] = true;
      _collectVariables(bestAtom, this.boundVariables);
      const cmpIdx = this.nodeIDComparisonAtoms.indexOf(bestAtom);
      if (cmpIdx >= 0) this.nodeIDComparisonAtoms.splice(cmpIdx, 1);
    }
    return createDLClause(clause.headAtoms, this.reorderedAtoms.slice());
  }

  /**
   * HermiT's goodness heuristic:
   *   NodeIDsAscendingOrEqual — all variables bound: 5000, else −5000
   *   NodeIDLessEqualThan     — both bound: 1000, else −2000
   *   regular atom            — 100·bound − 10·unbound, +5 if the single
   *                             unbound variable is constrained by a node-ID
   *                             comparison already in scope
   */
  _getAtomGoodness(atom) {
    const pred = atom.dlPredicate;
    if (pred instanceof NodeIDsAscendingOrEqual) {
      let unbound = 0;
      for (let i = atom.getArity() - 1; i >= 0; --i) {
        const v = atom.getArgumentVariable(i);
        if (v && !this.boundVariables.has(v)) unbound++;
      }
      return unbound > 0 ? -5000 : 5000;
    }
    if (pred === NODE_ID_LESS_EQUAL_THAN) {
      return (this.boundVariables.has(atom.getArgumentVariable(0))
        && this.boundVariables.has(atom.getArgumentVariable(1))) ? 1000 : -2000;
    }
    let bound = 0, unbound = 0;
    for (let i = atom.getArity() - 1; i >= 0; --i) {
      const v = atom.getArgumentVariable(i);
      if (v) { if (this.boundVariables.has(v)) bound++; else unbound++; }
    }
    let goodness = bound * 100 - unbound * 10;
    if (atom.getArity() === 2 && unbound === 1 && this.nodeIDComparisonAtoms.length > 0) {
      let unboundVariable = atom.getArgumentVariable(0);
      if (this.boundVariables.has(unboundVariable)) unboundVariable = atom.getArgumentVariable(1);
      for (let i = this.nodeIDComparisonAtoms.length - 1; i >= 0; --i) {
        const cmp = this.nodeIDComparisonAtoms[i];
        const a0 = cmp.getArgumentVariable(0), a1 = cmp.getArgumentVariable(1);
        if ((this.boundVariables.has(a0) || unboundVariable === a0)
          && (this.boundVariables.has(a1) || unboundVariable === a1)) {
          goodness += 5;
          break;
        }
      }
    }
    return goodness;
  }
}

function _collectVariables(atom, into) {
  for (let i = 0; i < atom.getArity(); i++) {
    const v = atom.getArgumentVariable(i);
    if (v) into.add(v);
  }
}

// ===========================================================================
// DLClauseEvaluator — match one swapped clause body and derive its heads.
// ===========================================================================

class DLClauseEvaluator {
  /**
   * @param {object} tableau
   * @param {DLClause} swappedDLClause  body[0] is the delta atom
   * @param {DLClause[]} headDLClauses  all clauses sharing this body
   */
  constructor(tableau, swappedDLClause, headDLClauses) {
    this.tableau = tableau;
    this.extensionManager = tableau.extensionManager;
    this.bodyAtoms = swappedDLClause.bodyAtoms;
    this.headClauses = headDLClauses;
    this.deltaAtom = this.bodyAtoms[0];

    // Variable → buffer index. Order is irrelevant to correctness; HermiT uses
    // it only to size the shared values buffer.
    this.variables = [];
    this.variableIndex = new Map();
    const addVar = (v) => {
      if (v && !this.variableIndex.has(v)) {
        this.variableIndex.set(v, this.variables.length);
        this.variables.push(v);
      }
    };
    for (const atom of this.bodyAtoms) _forEachVariable(atom, addVar);
    for (const clause of headDLClauses) {
      for (let i = 0; i < clause.getHeadLength(); i++) _forEachVariable(clause.getHeadAtom(i), addVar);
    }

    // Number of body atoms that actually contribute a dependency set.
    this.numberOfRealAtoms = 0;
    for (const atom of this.bodyAtoms) {
      if (isPredicateWithExtension(atom.dlPredicate)) this.numberOfRealAtoms++;
    }

    // Cache: arity → extension table (avoids a Map lookup per match step).
    this._tables = new Map();
  }

  _tableFor(arity) {
    let t = this._tables.get(arity);
    if (!t) { t = this.extensionManager.getExtensionTable(arity); this._tables.set(arity, t); }
    return t;
  }

  /**
   * Fire this clause with `deltaTuple` (already in the extension table) bound
   * to the delta atom.
   */
  evaluate(deltaTuple, deltaDependencySet) {
    const atom = this.deltaAtom;
    const arity = atom.getArity();
    const values = new Array(this.variables.length).fill(null);

    for (let i = 0; i < arity; i++) {
      const term = atom.getArgument(i);
      const node = deltaTuple[i + 1];
      if (term instanceof Variable) {
        const idx = this.variableIndex.get(term);
        if (values[idx] !== null) { if (values[idx] !== node) return; }
        else values[idx] = node;
      } else {
        const ground = this._groundNode(term);
        if (ground === null || ground !== node.getCanonicalNode()) return;
      }
    }
    this._match(1, values, [deltaDependencySet]);
  }

  /** Recursively match bodyAtoms[atomIndex..] against the extension tables. */
  _match(atomIndex, values, depSets) {
    if (this.extensionManager.containsClash()) return;
    if (atomIndex === this.bodyAtoms.length) {
      this._deriveHeads(values, depSets);
      return;
    }

    const atom = this.bodyAtoms[atomIndex];
    const pred = atom.dlPredicate;

    // ---- ordering pseudo-atom: nodeID(a) <= nodeID(b) --------------------
    if (pred === NODE_ID_LESS_EQUAL_THAN) {
      const a = values[this.variableIndex.get(atom.getArgument(0))];
      const b = values[this.variableIndex.get(atom.getArgument(1))];
      if (a && b && a.nodeID <= b.nodeID) this._match(atomIndex + 1, values, depSets);
      return;
    }

    // ---- ordering pseudo-atom: strictly ascending XOR all equal ----------
    if (pred instanceof NodeIDsAscendingOrEqual) {
      const arity = atom.getArity();
      let last = values[this.variableIndex.get(atom.getArgument(0))];
      if (!last) return;
      let strictlyAscending = true, allEqual = true;
      for (let i = 1; i < arity; i++) {
        const n = values[this.variableIndex.get(atom.getArgument(i))];
        if (!n) return;
        if (last.nodeID >= n.nodeID) strictlyAscending = false;
        if (n.nodeID !== last.nodeID) allEqual = false;
        last = n;
      }
      if ((!strictlyAscending && allEqual) || (strictlyAscending && !allEqual)) {
        this._match(atomIndex + 1, values, depSets);
      }
      return;
    }

    // ---- regular atom: retrieve all matching ground tuples ---------------
    const arity = atom.getArity();
    const pattern = new Array(arity).fill(null);
    const unboundPositions = [];
    for (let i = 0; i < arity; i++) {
      const term = atom.getArgument(i);
      if (term instanceof Variable) {
        const idx = this.variableIndex.get(term);
        if (values[idx] !== null) pattern[i] = values[idx];
        else unboundPositions.push(i);
      } else {
        const g = this._groundNode(term);
        if (g === null) return; // unknown ground term ⇒ body can never match
        pattern[i] = g;
      }
    }

    const table = this._tableFor(arity + 1);
    const entries = table.retrieve(pred, pattern);
    for (const entry of entries) {
      if (this.extensionManager.containsClash()) return;
      // The tuple may have been deactivated by a merge triggered while deriving
      // a previous head. HermiT's retrieval skips these; the merged node's
      // assertions were copied to its canonical node and will re-trigger the
      // clause through the delta-new window.
      if (!table.isTupleActive(entry.tuple)) continue;

      const boundHere = [];
      let ok = true;
      for (const pos of unboundPositions) {
        const idx = this.variableIndex.get(atom.getArgument(pos));
        const node = entry.tuple[pos + 1];
        if (values[idx] !== null) {
          if (values[idx] !== node) { ok = false; break; }
        } else {
          values[idx] = node;
          boundHere.push(idx);
        }
      }
      if (ok) {
        depSets.push(entry.dependencySet);
        this._match(atomIndex + 1, values, depSets);
        depSets.pop();
      }
      for (const idx of boundHere) values[idx] = null;
    }
  }

  /** Derive every head of every clause sharing this body. */
  _deriveHeads(values, depSets) {
    let dependencySet = PERMANENT;
    for (const ds of depSets) dependencySet = dependencySet.union(ds);

    for (const clause of this.headClauses) {
      const headLength = clause.getHeadLength();

      // Empty head: the body is unsatisfiable.
      if (headLength === 0) {
        this.extensionManager.setClash(dependencySet);
        return;
      }

      // Single head atom: a deterministic (Horn) consequence.
      if (headLength === 1) {
        const atom = clause.getHeadAtom(0);
        const nodes = this._resolveArguments(atom, values);
        if (nodes) this.extensionManager.addTuple([atom.dlPredicate, ...nodes], dependencySet, true);
        if (this.extensionManager.containsClash()) return;
        continue;
      }

      // Disjunctive head: hand a GroundDisjunction to the Tableau, which will
      // branch on it. Skip if some disjunct already holds.
      const disjuncts = [];
      const args = [];
      let complete = true;
      for (let i = 0; i < headLength; i++) {
        const atom = clause.getHeadAtom(i);
        const nodes = this._resolveArguments(atom, values);
        if (!nodes) { complete = false; break; }
        disjuncts.push({ dlPredicate: atom.dlPredicate, arity: atom.getArity() });
        for (const n of nodes) args.push(n);
      }
      if (!complete) continue;
      const groundDisjunction = new GroundDisjunction(getHeader(disjuncts), args, dependencySet);
      if (!groundDisjunction.isSatisfied(this.tableau)) {
        this.tableau.addGroundDisjunction(groundDisjunction);
      }
      if (this.extensionManager.containsClash()) return;
    }
  }

  /** Resolve an atom's arguments to canonical nodes, or null if impossible. */
  _resolveArguments(atom, values) {
    const arity = atom.getArity();
    const nodes = new Array(arity);
    for (let i = 0; i < arity; i++) {
      const term = atom.getArgument(i);
      if (term instanceof Variable) {
        const n = values[this.variableIndex.get(term)];
        if (!n) return null;
        nodes[i] = n.getCanonicalNode();
      } else {
        const g = this._groundNode(term);
        if (g === null) return null;
        nodes[i] = g;
      }
    }
    return nodes;
  }

  /** The canonical node a ground term (Individual/Constant) denotes, or null. */
  _groundNode(term) {
    const map = this.tableau.termsToNodes;
    if (!map) return null;
    const node = map.get(term);
    return node ? node.getCanonicalNode() : null;
  }
}

function _forEachVariable(atom, fn) {
  for (let i = 0; i < atom.getArity(); i++) fn(atom.getArgumentVariable(i));
}

/**
 * Rewrite R⁻(X,Y) as R(Y,X). The extension tables only ever store atomic
 * roles (see ExtensionManager._addTuple), so a clause body containing an
 * InverseRole could never match. HermiT's clausifier performs the same swap in
 * `getRoleAtom`; doing it here makes the engine robust for hand-built clauses.
 */
function _normalizeAtom(atom) {
  if (atom.dlPredicate instanceof InverseRole) {
    return createAtom(atom.dlPredicate.inverseRole, atom.getArgument(1), atom.getArgument(0));
  }
  return atom;
}

function _normalizeClause(clause) {
  let changed = false;
  const head = clause.headAtoms.map(a => { const n = _normalizeAtom(a); if (n !== a) changed = true; return n; });
  const body = clause.bodyAtoms.map(a => { const n = _normalizeAtom(a); if (n !== a) changed = true; return n; });
  return changed ? createDLClause(head, body) : clause;
}

// ===========================================================================
// HyperresolutionManager
// ===========================================================================

class HyperresolutionManager {
  /**
   * @param {object} tableau
   * @param {Set<DLClause>|DLClause[]} dlClauses
   */
  constructor(tableau, dlClauses) {
    this.tableau = tableau;
    this.extensionManager = tableau.extensionManager;

    /** DLPredicate → DLClauseEvaluator[] (HermiT's linked CompiledDLClauseInfo chain) */
    this.tupleConsumersByDeltaPredicate = new Map();
    /** arities that have at least one delta predicate (sorted ascending) */
    this.deltaArities = [];

    // ---- group clauses by body (HermiT's DLClauseBodyKey) -----------------
    const clausesByBody = new Map();
    for (const rawClause of dlClauses) {
      const clause = _normalizeClause(rawClause);
      const key = _bodyKey(clause);
      let list = clausesByBody.get(key);
      if (!list) { list = []; clausesByBody.set(key, list); }
      list.push(clause);
    }

    // ---- compile one evaluator per (body, delta atom position) ------------
    const arities = new Set();
    for (const clauses of clausesByBody.values()) {
      const bodyClause = clauses[0];
      const swapper = new BodyAtomsSwapper(bodyClause);
      for (let i = 0; i < bodyClause.getBodyLength(); i++) {
        const deltaPredicate = bodyClause.getBodyAtom(i).dlPredicate;
        if (!isPredicateWithExtension(deltaPredicate)) continue;
        const swapped = swapper.getSwappedDLClause(i);
        const evaluator = new DLClauseEvaluator(tableau, swapped, clauses);
        let chain = this.tupleConsumersByDeltaPredicate.get(deltaPredicate);
        if (!chain) { chain = []; this.tupleConsumersByDeltaPredicate.set(deltaPredicate, chain); }
        chain.push(evaluator);
        arities.add(deltaPredicate.getArity() + 1);
      }
    }
    this.deltaArities = [...arities].sort((a, b) => a - b);

    // ---- extension flags (HermiT: updateFlagsDependentOnAdditionalOntology)
    this.needsThingExtension = this.tupleConsumersByDeltaPredicate.has(THING);
    this.needsNamedExtension = this.tupleConsumersByDeltaPredicate.has(INTERNAL_NAMED);
    this.needsRDFSLiteralExtension = this.tupleConsumersByDeltaPredicate.has(RDFS_LITERAL);
  }

  /**
   * Fire every clause whose delta predicate matches a tuple in the DELTA_OLD
   * window of the corresponding extension table. Stops early on a clash.
   *
   * Note on the guard-concept optimisation: HermiT additionally indexes
   * atomic-role-delta clauses by the concepts guarding their first two
   * arguments, so a role assertion only fires the clauses whose guard concept
   * is already present on the endpoint nodes. That is a pure pruning
   * optimisation over exactly the same set of firings performed here; we use
   * the unoptimised chain, which is always sound and complete.
   */
  applyDLClauses() {
    for (const arity of this.deltaArities) {
      const table = this.extensionManager.getExtensionTable(arity);
      const entries = table.getDeltaOldEntries();
      for (const entry of entries) {
        if (this.extensionManager.containsClash()) return;
        if (!table.isTupleActive(entry.tuple)) continue;
        const consumers = this.tupleConsumersByDeltaPredicate.get(entry.tuple[0]);
        if (!consumers) continue;
        for (const evaluator of consumers) {
          if (this.extensionManager.containsClash()) return;
          evaluator.evaluate(entry.tuple, entry.dependencySet);
        }
      }
    }
  }

  /** True if any clause is triggered by `predicate` appearing in a tuple. */
  hasConsumersFor(predicate) {
    return this.tupleConsumersByDeltaPredicate.has(predicate);
  }

  /** Number of compiled clause variants (diagnostics / tests). */
  get numberOfEvaluators() {
    let n = 0;
    for (const chain of this.tupleConsumersByDeltaPredicate.values()) n += chain.length;
    return n;
  }

  clear() {
    // Evaluators are immutable and hold no per-run state, so there is nothing
    // to reset beyond dropping references if the manager is discarded.
  }
}

/** Structural key for a clause body (HermiT's DLClauseBodyKey). */
function _bodyKey(clause) {
  let k = '';
  for (let i = 0; i < clause.getBodyLength(); i++) {
    if (i) k += '^';
    k += clause.getBodyAtom(i).toString();
  }
  return k;
}

module.exports = {
  HyperresolutionManager,
  DLClauseEvaluator,
  BodyAtomsSwapper,
  isPredicateWithExtension,
  // Exported for `datalog/ConjunctiveQuery`: a query body is always hand-built,
  // so nothing else normalizes its atoms the way the clausifier normalizes
  // clause bodies.
  normalizeAtom: _normalizeAtom
};
