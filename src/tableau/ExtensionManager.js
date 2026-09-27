'use strict';

// ---------------------------------------------------------------------------
// tableau/ExtensionManager.js — owns the extension tables, dispatches tuple
// additions, and detects clashes.
//
// Mirrors org.semanticweb.HermiT.tableau.{ExtensionManager, ClashManager}.
//
// Dispatch rules (ExtensionManager.addTuple):
//   • arity 0            → set clash
//   • Equality(n0,n1)    → tableau.mergeNodes(n0,n1)   (never stored)
//   • AnnotatedEquality  → tableau.nominalIntroduction (never stored as such)
//   • otherwise          → store in the extension table of that arity
//
// Special "always present" tuples (containsTuple):
//   • AtomicConcept.THING on any abstract node → true
//   • rdfs:Literal on any concrete node → true
//   • Equality(n0,n1) → true iff n0 === n1
//
// Clash detection (ClashManager.tupleAdded) fires the moment an offending tuple
// is added, so the calculus can backjump as early as possible:
//   1. NOTHING asserted, ¬rdfs:Literal asserted, or Inequality(n,n).
//   2. A concept and its negation on the same node; a data range and its
//      negation on the same node.
//   3. A role and its negation on the same edge.
//   4. When a role edge points at a concrete node, distinct concrete successors
//      of the same (node, role) are pairwise unequal → generate Inequality.
// ---------------------------------------------------------------------------

const { ExtensionTable } = require('./ExtensionTable');
const { PERMANENT } = require('./DependencySet');
const {
  AtomicConcept,
  AtomicNegationConcept,
  LiteralDataRange,
  AtomicNegationDataRange,
  InternalDatatype,
  DatatypeRestriction,
  ConstantEnumeration,
  AtomicRole,
  InverseRole,
  NegatedAtomicRole,
  Equality,
  Inequality,
  AnnotatedEquality,
  THING,
  NOTHING,
  LITERAL,
  RDFS_LITERAL,
  EQUALITY,
  INEQUALITY,
  internAtomicNegationDataRange
} = require('../model/DLPredicate');

/**
 * ¬rdfs:Literal — asserting it on a concrete node is a clash. HermiT negates
 * InternalDatatype.RDFS_LITERAL (the internal datatype), not LiteralDataRange.
 */
const NOT_RDFS_LITERAL = internAtomicNegationDataRange(RDFS_LITERAL);

class ExtensionManager {
  constructor(tableau) {
    this.tableau = tableau;
    this.tables = new Map();          // arity → ExtensionTable
    this.binaryTable = this._getTable(2);
    this.ternaryTable = this._getTable(3);
    this.quaternaryTable = this._getTable(4);
    this.clashDependencySet = null;   // non-null ⇒ clash present
    this._addActive = false;
  }

  _getTable(arity) {
    let t = this.tables.get(arity);
    if (!t) { t = new ExtensionTable(this.tableau, arity); this.tables.set(arity, t); }
    return t;
  }

  getExtensionTable(arity) { return this._getTable(arity); }
  getAllTables() { return [...this.tables.values()]; }

  // ---- clash state ----------------------------------------------------------

  clearClash() { this.clashDependencySet = null; }
  setClash(dependencySet) { this.clashDependencySet = dependencySet || PERMANENT; }
  containsClash() { return this.clashDependencySet !== null; }
  getClashDependencySet() { return this.clashDependencySet; }

  // ---- membership -----------------------------------------------------------

  containsConceptAssertion(concept, node) {
    if (node.isAbstract() && concept === THING) return true;
    return this.binaryTable.containsTuple([concept, node]);
  }

  containsDataRangeAssertion(range, node) {
    if (!node.isAbstract() && range === RDFS_LITERAL) return true;
    return this.binaryTable.containsTuple([range, node]);
  }

  containsRoleAssertion(role, from, to) {
    if (role instanceof AtomicRole) {
      return this.ternaryTable.containsTuple([role, from, to]);
    }
    // InverseRole: R⁻(a,b) ≡ R(b,a)
    return this.ternaryTable.containsTuple([role.inverseRole, to, from]);
  }

  containsAssertion(predicate, ...nodes) {
    if (predicate === THING) return true;
    if (predicate === EQUALITY) return nodes[0] === nodes[1];
    if (predicate instanceof AnnotatedEquality) {
      return this.tableau.nominalIntroduction
        && this.tableau.nominalIntroduction.canForgetAnnotation(predicate, nodes[0], nodes[1], nodes[2])
        && nodes[0] === nodes[1];
    }
    const arity = nodes.length + 1;
    return this._getTable(arity).containsTuple([predicate, ...nodes]);
  }

  containsTuple(tuple) {
    if (tuple.length === 0) return this.containsClash();
    if (tuple[0] === THING) return true;
    if (tuple[0] === EQUALITY) return tuple[1] === tuple[2];
    if (tuple[0] instanceof AnnotatedEquality) {
      return this.tableau.nominalIntroduction
        && this.tableau.nominalIntroduction.canForgetAnnotation(tuple[0], tuple[1], tuple[2], tuple[3])
        && tuple[1] === tuple[2];
    }
    return this._getTable(tuple.length).containsTuple(tuple);
  }

  getAssertionDependencySet(predicate, ...nodes) {
    if (predicate === THING) return PERMANENT;
    if (predicate === EQUALITY) return nodes[0] === nodes[1] ? PERMANENT : null;
    const arity = nodes.length + 1;
    return this._getTable(arity).getDependencySet([predicate, ...nodes]);
  }

  getConceptAssertionDependencySet(concept, node) {
    if (concept === THING) return PERMANENT;
    return this.binaryTable.getDependencySet([concept, node]);
  }

  getDataRangeAssertionDependencySet(range, node) {
    if (range === RDFS_LITERAL) return PERMANENT;
    return this.binaryTable.getDependencySet([range, node]);
  }

  getRoleAssertionDependencySet(role, from, to) {
    if (role instanceof AtomicRole) return this.ternaryTable.getDependencySet([role, from, to]);
    return this.ternaryTable.getDependencySet([role.inverseRole, to, from]);
  }

  getTupleDependencySet(tuple) {
    if (tuple.length === 0) return this.clashDependencySet;
    return this._getTable(tuple.length).getDependencySet(tuple);
  }

  // ---- addition -------------------------------------------------------------

  addConceptAssertion(concept, node, dependencySet, isCore = true) {
    return this._addTuple([concept, node], dependencySet, isCore);
  }

  addDataRangeAssertion(range, node, dependencySet, isCore = true) {
    return this._addTuple([range, node], dependencySet, isCore);
  }

  addRoleAssertion(role, from, to, dependencySet, isCore = true) {
    if (role instanceof AtomicRole) return this._addTuple([role, from, to], dependencySet, isCore);
    return this._addTuple([role.inverseRole, to, from], dependencySet, isCore);
  }

  /**
   * addAssertion(predicate, ...nodes, dependencySet [, isCore]).
   * The dependency set is the last argument unless a boolean follows it.
   */
  addAssertion(predicate, ...rest) {
    let isCore = true;
    if (typeof rest[rest.length - 1] === 'boolean') isCore = rest.pop();
    const dependencySet = rest.pop();
    return this._addTuple([predicate, ...rest], dependencySet, isCore);
  }

  /**
   * Central tuple addition with dispatch. Returns true if the tuple was newly
   * added (or a new clash/merge was triggered), false if it was already present.
   */
  addTuple(tuple, dependencySet, isCore = true) {
    return this._addTuple(tuple, dependencySet, isCore);
  }

  _addTuple(tuple, dependencySet, isCore = true) {
    const ds = dependencySet || PERMANENT;
    if (tuple.length === 0) {
      const wasNoClash = this.clashDependencySet === null;
      this.setClash(ds);
      return wasNoClash;
    }
    let predicate = tuple[0];
    // R⁻(a,b) is stored as R(b,a): the tables only ever hold atomic roles.
    if (predicate instanceof InverseRole) {
      predicate = predicate.inverseRole;
      tuple = [predicate, tuple[2], tuple[1]];
    }
    if (predicate === EQUALITY) {
      return this.tableau.mergingManager.mergeNodes(tuple[1], tuple[2], ds);
    }
    if (predicate instanceof AnnotatedEquality) {
      return this.tableau.nominalIntroduction
        .addAnnotatedEquality(predicate, tuple[1], tuple[2], tuple[3], ds);
    }
    if (this._addActive) {
      // Reentrant simple additions (e.g. Inequality generated during clash
      // detection) go straight to the table, mirroring HermiT's comment.
      return this._getTable(tuple.length).addTuple(tuple, ds, isCore);
    }
    this._addActive = true;
    try {
      const table = this._getTable(tuple.length);
      // ExtensionTable.addTuple already runs postAdd (node counters, strategy
      // notification, clash detection) for genuinely new tuples.
      return table.addTuple(tuple, ds, isCore);
    } finally {
      this._addActive = false;
    }
  }

  // ---- clash detection (ClashManager.tupleAdded) ----------------------------

  /**
   * ClashManager.tupleAdded. Invoked from Tableau.tupleAdded, which the
   * ExtensionTable calls for every genuinely new tuple.
   * @param {ExtensionTable} table the table the tuple was added to
   */
  detectClash(table, tuple, dependencySet, isCore = true) {
    return this._detectClash(tuple, dependencySet, table);
  }

  /** The negation of a unary predicate, or null when it has none. */
  negationOf(predicate) { return this._negationOf(predicate); }

  _detectClash(tuple, dependencySet, table) {
    const predicate = tuple[0];
    const node0 = tuple[1];

    // Rule 1: NOTHING, ¬rdfs:Literal, or Inequality(n,n).
    if (predicate === NOTHING || predicate === NOT_RDFS_LITERAL
      || (predicate === INEQUALITY && tuple[1] === tuple[2])) {
      this.setClash(dependencySet);
      return;
    }

    // Rule 2: concept/data-range and its negation on the same node.
    const isDataRangePred = predicate instanceof LiteralDataRange
      || predicate instanceof InternalDatatype
      || predicate instanceof DatatypeRestriction
      || predicate instanceof ConstantEnumeration;
    const isNegatedInternalDatatype = predicate instanceof AtomicNegationDataRange
      && predicate.dataRange instanceof InternalDatatype;

    if (isDataRangePred || isNegatedInternalDatatype
      || (predicate instanceof AtomicConcept && node0.numberOfNegatedAtomicConcepts > 0)
      || (predicate instanceof AtomicNegationConcept && node0.numberOfPositiveAtomicConcepts > 0)) {
      const negation = this._negationOf(predicate);
      if (negation) {
        const negTuple = [negation, node0];
        if (table.containsTuple(negTuple)) {
          const otherDs = table.getDependencySet(negTuple);
          this.setClash(dependencySet.union(otherDs));
          return;
        }
      }
    }

    // Rule 3 & 4: role and negated role on the same edge; concrete inequalities.
    if ((predicate instanceof AtomicRole && node0.numberOfNegatedRoleAssertions > 0)
      || predicate instanceof NegatedAtomicRole) {
      let searchPredicate;
      if (predicate instanceof AtomicRole) {
        searchPredicate = require('../model/DLPredicate').internNegatedAtomicRole(predicate);
      } else {
        searchPredicate = predicate.atomicRole;
      }
      const negTuple = [searchPredicate, node0, tuple[2]];
      if (this.ternaryTable.containsTuple(negTuple)) {
        const otherDs = this.ternaryTable.getDependencySet(negTuple);
        this.setClash(dependencySet.union(otherDs));
        return;
      }
      // Rule 4: if the target node is concrete, generate inequalities between
      // all distinct concrete successors of (node0, searchPredicate).
      if (tuple[2] && !tuple[2].isAbstract()) {
        this._generateConcreteInequalities(searchPredicate, node0, tuple[2], dependencySet);
      }
    }
  }

  _generateConcreteInequalities(searchPredicate, node0, concreteNode, dependencySet) {
    const entries = this.ternaryTable.retrieve(searchPredicate, [node0, null]);
    for (const e of entries) {
      const other = e.tuple[2];
      if (!other || other.isAbstract() || other === concreteNode) continue;
      const ineqTuple = [INEQUALITY, concreteNode, other];
      if (this.ternaryTable.containsTupleRaw(ineqTuple)) continue;
      const unionDs = dependencySet.union(e.dependencySet);
      // Reentrant add directly to the ternary table (mirrors HermiT). The table
      // itself notifies the Tableau, which runs clash detection.
      this.ternaryTable.addTuple(ineqTuple, unionDs, true);
    }
  }

  /** The negation predicate of a unary concept/data-range predicate, or null. */
  _negationOf(predicate) {
    // `getNegation()` already special-cases owl:Thing/owl:Nothing, so delegate
    // rather than calling the interners directly.
    if (predicate instanceof AtomicConcept
      || predicate instanceof AtomicNegationConcept
      || predicate instanceof LiteralDataRange
      || predicate instanceof AtomicNegationDataRange
      || predicate instanceof InternalDatatype
      || predicate instanceof DatatypeRestriction
      || predicate instanceof ConstantEnumeration) {
      return predicate.getNegation();
    }
    return null;
  }

  // ---- propagation / backtracking ------------------------------------------

  /**
   * Rotate the delta windows of every table. Returns true iff at least one
   * table had a non-empty delta-new window (i.e. new facts were produced).
   */
  propagateDeltaNew() {
    let changed = false;
    for (const table of this.tables.values()) {
      if (table.propagateDeltaNew()) changed = true;
    }
    return changed;
  }

  hasDeltaNew() {
    for (const table of this.tables.values()) if (table.hasDeltaNew()) return true;
    return false;
  }

  branchingPointPushed() {
    for (const table of this.tables.values()) table.branchingPointPushed();
  }

  backtrack() {
    const removed = [];
    for (const table of this.tables.values()) removed.push(...table.backtrack());
    return removed;
  }

  clear() {
    for (const table of this.tables.values()) table.clear();
    this.clashDependencySet = null;
  }
}

module.exports = { ExtensionManager, NOT_RDFS_LITERAL };
