'use strict';

// ---------------------------------------------------------------------------
// tableau/DatatypeManager.js — concrete-node data reasoning.
//
// Mirrors org.semanticweb.HermiT.tableau.DatatypeManager (+ DatatypeChecker).
//
// Two jobs, both driven by the delta-new tuples each saturation round:
//
//   1. applyUnknownDatatypeRestrictionSemantics — a datatype restriction we
//      cannot interpret is an uninterpreted predicate: if node1 ∈ DR and
//      node2 ∉ DR then node1 and node2 must denote different literals, so
//      assert Inequality(node1, node2).
//
//   2. checkDatatypeConstraints — for every concrete node, collect the whole
//      conjunction of data-range constraints hanging off it and decide
//      satisfiability (DatatypeReasoning.checkConstraintsSatisfiable). Then,
//      for each Inequality-connected component of concrete nodes whose value
//      spaces are all finite, check that a system of distinct representatives
//      exists (bipartite matching / Hall's condition) — this is what makes
//      "≥2 R.{a,b}" with only two literals clash.
//
// Clash dependency sets are the union of the dependency sets of every
// constraint that participated, so backjumping targets the right branch.
// ---------------------------------------------------------------------------

const {
  LiteralDataRange,
  AtomicNegationDataRange,
  DatatypeRestriction,
  InternalDatatype,
  ConstantEnumeration,
  INEQUALITY
} = require('../model/DLPredicate');
const {
  GROUP,
  groupOf,
  checkConstraintsSatisfiable,
  constantsEqual
} = require('../datatypes/DatatypeReasoning');

/** Is this predicate a (positive) data-range membership test? */
function isDataRangePredicate(p) {
  return p instanceof LiteralDataRange
    || p instanceof DatatypeRestriction
    || p instanceof InternalDatatype
    || p instanceof ConstantEnumeration;
}

/** A datatype restriction we cannot interpret (opaque base datatype). */
function isUnknownRestriction(dr) {
  return dr instanceof DatatypeRestriction && groupOf(dr.datatypeIRI) === GROUP.OTHER;
}

class DatatypeManager {
  /**
   * @param {Tableau} tableau
   */
  constructor(tableau) {
    this.tableau = tableau;
    this.extensionManager = tableau.extensionManager;
    this.unknownDatatypeRestrictions = new Set();
  }

  /** Register the restrictions the DLOntology declares as unknown. */
  setUnknownDatatypeRestrictions(set) {
    this.unknownDatatypeRestrictions = set || new Set();
  }

  clear() { /* no persistent state */ }

  // ---- unknown datatype restriction semantics --------------------------------

  /**
   * For every concrete node carrying an unknown restriction DR (or ¬DR), force
   * inequality with all nodes carrying the opposite. Mirrors
   * DatatypeManager.applyUnknownDatatypeRestrictionSemantics.
   *
   * NOTE: this runs *after* `ExtensionManager.propagateDeltaNew()` has rotated
   * the delta windows, so the freshly derived facts live in the DELTA-OLD
   * window — exactly as HermiT's `m_assertionsDeltaOldRetrieval`
   * (`ExtensionTable.View.DELTA_OLD`). Reading the delta-new window here would
   * always yield an empty snapshot and silently disable the whole rule.
   */
  applyUnknownDatatypeRestrictionSemantics() {
    const binary = this.extensionManager.binaryTable;
    let changed = false;
    for (const e of binary.getDeltaOldEntries()) {
      const pred = e.tuple[0];
      const node1 = e.tuple[1];
      if (pred instanceof DatatypeRestriction && this.unknownDatatypeRestrictions.has(pred)) {
        if (this._generateInequalitiesFor(pred, node1, e.dependencySet,
          require('../model/DLPredicate').internAtomicNegationDataRange(pred))) changed = true;
      } else if (pred instanceof AtomicNegationDataRange
        && pred.dataRange instanceof DatatypeRestriction
        && this.unknownDatatypeRestrictions.has(pred.dataRange)) {
        if (this._generateInequalitiesFor(pred, node1, e.dependencySet, pred.dataRange)) changed = true;
      }
    }
    return changed;
  }

  /**
   * Assert `Inequality(node1, node2)` for every node2 carrying the opposite
   * data range. Mirrors DatatypeManager.generateInequalitiesFor.
   *
   * `node1 === node2` is deliberately NOT skipped: when a concrete node carries
   * both DR and ¬DR, HermiT asserts `Inequality(n, n)`, which ClashManager
   * reports as a clash. Skipping it would make `DR ⊓ ¬DR` satisfiable and
   * flatten the data-property hierarchy (isSubDataPropertyOf would always
   * answer "yes").
   */
  _generateInequalitiesFor(dataRange1, node1, ds1, dataRange2) {
    const binary = this.extensionManager.binaryTable;
    let changed = false;
    for (const e of binary.retrieve(dataRange2, [null])) {
      const node2 = e.tuple[1];
      const unionDs = ds1.union(e.dependencySet);
      // isCore = false, matching HermiT's addAssertion(..., m_unionDependencySet, false).
      if (this.extensionManager.addAssertion(INEQUALITY, node1, node2, unionDs, false)) changed = true;
    }
    return changed;
  }

  // ---- constraint checking ---------------------------------------------------

  /**
   * Check every concrete node's data-range conjunction; then check distinctness
   * across inequality-connected components. Returns true if a clash was set.
   */
  checkDatatypeConstraints() {
    const em = this.extensionManager;
    if (em.containsClash()) return true;

    // Gather all concrete nodes that currently appear in the binary table.
    const concreteNodes = new Set();
    for (const e of em.binaryTable.getAllEntries()) {
      const node = e.tuple[1];
      if (node && node.isConcrete() && node.isActive()) concreteNodes.add(node);
    }

    // 1. Per-node conjunction satisfiability.
    const constraintsByNode = new Map();
    for (const node of concreteNodes) {
      const constraints = this._collectConstraints(node);
      constraintsByNode.set(node, constraints);
      if (constraints.length === 0) continue;
      const result = checkConstraintsSatisfiable(constraints);
      if (!result.satisfiable) {
        em.setClash(this._unionDependencySet(constraints, node));
        return true;
      }
    }

    // 2. Distinctness across inequality-connected components (finite spaces).
    if (this._checkInequalityComponents(concreteNodes, constraintsByNode)) return true;

    return em.containsClash();
  }

  /** All {predicate, positive, dependencySet} data-range constraints on a node. */
  _collectConstraints(node) {
    const out = [];
    for (const e of this.extensionManager.binaryTable.retrieve(null, [node])) {
      const pred = e.tuple[0];
      if (isDataRangePredicate(pred)) {
        out.push({ predicate: pred, positive: true, dependencySet: e.dependencySet });
      } else if (pred instanceof AtomicNegationDataRange) {
        out.push({ predicate: pred.dataRange, positive: false, dependencySet: e.dependencySet });
      }
    }
    return out;
  }

  _unionDependencySet(constraints, node) {
    let ds = constraints[0] ? constraints[0].dependencySet : require('./DependencySet').PERMANENT;
    for (let i = 1; i < constraints.length; i++) ds = ds.union(constraints[i].dependencySet);
    return ds;
  }

  /**
   * Build the graph of concrete nodes linked by Inequality, find connected
   * components, and for each component whose members all have a finite value
   * space, verify a perfect matching exists (each node gets a distinct value).
   * Returns true if a clash was detected.
   */
  _checkInequalityComponents(concreteNodes, constraintsByNode) {
    const em = this.extensionManager;
    // adjacency via Inequality
    const adj = new Map();
    for (const node of concreteNodes) adj.set(node, new Set());
    for (const e of em.ternaryTable.retrieve(INEQUALITY, [null, null])) {
      const a = e.tuple[1], b = e.tuple[2];
      if (concreteNodes.has(a) && concreteNodes.has(b) && a !== b) {
        adj.get(a).add(b);
        adj.get(b).add(a);
      }
    }

    const visited = new Set();
    for (const start of concreteNodes) {
      if (visited.has(start)) continue;
      // BFS the component.
      const component = [];
      const queue = [start];
      visited.add(start);
      while (queue.length > 0) {
        const n = queue.shift();
        component.push(n);
        for (const m of adj.get(n)) {
          if (!visited.has(m)) { visited.add(m); queue.push(m); }
        }
      }
      if (component.length < 2) continue;

      // Finite value space per node?
      const spaces = [];
      let allFinite = true;
      for (const node of component) {
        const space = this._finiteSpace(constraintsByNode.get(node) || []);
        if (space === null) { allFinite = false; break; }
        spaces.push(space);
      }
      if (!allFinite) continue;

      // Hall's condition via maximum bipartite matching (nodes → values).
      if (!this._hasPerfectMatching(component, spaces)) {
        // Clash: union of all constraint dependency sets + the inequalities.
        let ds = require('./DependencySet').PERMANENT;
        for (const node of component) {
          for (const c of (constraintsByNode.get(node) || [])) ds = ds.union(c.dependencySet);
        }
        for (const node of component) {
          for (const other of adj.get(node)) {
            const ineqDs = em.getAssertionDependencySet(INEQUALITY, node, other);
            if (ineqDs) ds = ds.union(ineqDs);
          }
        }
        em.setClash(ds);
        return true;
      }
    }
    return false;
  }

  /**
   * The finite set of literal values a node may take, or null if infinite /
   * unknown. Derived from positive ConstantEnumerations (intersection) or a
   * bounded integer range.
   */
  _finiteSpace(constraints) {
    const positives = constraints.filter(c => c.positive).map(c => c.predicate);
    const enums = positives.filter(p => p instanceof ConstantEnumeration);
    if (enums.length > 0) {
      let candidates = enums[0].constants.slice();
      for (const e of enums.slice(1)) {
        candidates = candidates.filter(c1 => e.constants.some(c2 => constantsEqual(c1, c2)));
      }
      // Filter by the remaining positive/negative constraints.
      const negatives = constraints.filter(c => !c.positive).map(c => c.predicate);
      const others = positives.filter(p => !(p instanceof ConstantEnumeration));
      const {
        constantSatisfies,
        constantDefinitelySatisfies
      } = require('../datatypes/DatatypeReasoning');
      // The negative test must use the DEFINITE form: an undecidable predicate
      // (an opaque `InternalDatatype`, an unrecognised facet) must not drop a
      // candidate, because a space that is too small makes `_hasPerfectMatching`
      // fail and report a clash the constraints do not imply.
      return candidates.filter(c =>
        others.every(p => constantSatisfies(c, p))
        && negatives.every(p => !constantDefinitelySatisfies(c, p)));
    }
    // Bounded integer space.
    const { enumerateFiniteSpace } = require('../datatypes/DatatypeReasoning');
    return enumerateFiniteSpace(positives);
  }

  /**
   * Maximum bipartite matching (augmenting paths). Values are compared by a
   * canonical key so identical literals across nodes share a column.
   * @returns {boolean} true if every node can get a distinct value
   */
  _hasPerfectMatching(component, spaces) {
    const valueKey = (c) => `${c.datatypeIRI || ''}\u0001${c.lexicalValue}`;
    const matchToNode = new Map(); // valueKey → component index
    const nodeMatch = new Array(component.length).fill(-1); // index → valueKey

    const tryAssign = (idx, seen) => {
      for (const value of spaces[idx]) {
        const key = valueKey(value);
        if (seen.has(key)) continue;
        seen.add(key);
        const holder = matchToNode.get(key);
        if (holder === undefined || tryAssign(holder, seen)) {
          matchToNode.set(key, idx);
          nodeMatch[idx] = key;
          return true;
        }
      }
      return false;
    };

    let matched = 0;
    for (let idx = 0; idx < component.length; idx++) {
      if (tryAssign(idx, new Set())) matched++;
    }
    return matched === component.length;
  }
}

module.exports = { DatatypeManager, isDataRangePredicate, isUnknownRestriction };
