'use strict';

// ---------------------------------------------------------------------------
// tableau/ExistentialExpansionManager.js — creates successors for ≥n R.C.
//
// Mirrors org.semanticweb.HermiT.tableau.ExistentialExpansionManager.
//
// Responsibilities:
//   • markExistentialProcessed — record that a restriction on a node has been
//     expanded (with branching-point undo, so backtracking re-opens it).
//   • tryFunctionalExpansion — if R (or a super-role) is functional and the
//     cardinality is 1, reuse the existing R-successor instead of creating a
//     fresh node; if cardinality > 1 and R is functional, that is a clash.
//   • doNormalExpansion — create n fresh successors (tree nodes for object
//     roles, concrete nodes for data roles) with pairwise Inequality.
//
// The expansion strategy (IndividualReuseStrategy) calls expand(); this class
// provides the mechanical node creation.
// ---------------------------------------------------------------------------

const {
  AtomicRole,
  InverseRole,
  AtLeastConcept,
  INEQUALITY,
  internInverseRole
} = require('../model/DLPredicate');

class ExistentialExpansionManager {
  /**
   * @param {Tableau} tableau
   */
  constructor(tableau) {
    this.tableau = tableau;
    this.extensionManager = tableau.extensionManager;

    // Records of expanded existentials: [{existentialConcept, forNode}].
    // Truncated on backtrack; entries after the checkpoint re-open their
    // restriction on the node.
    this.expandedExistentials = [];
    this.indicesByBranchingPoint = [0];

    // role → array of "relevant roles" (sub-roles of functional super-roles)
    this.functionalRoles = new Map();
    // set of roles declared functional (directly or via inverse functionality)
    this.declaredFunctionalRoles = new Set();

    this.auxiliaryNodes = [];
  }

  // ---- functional-role analysis (updateFunctionalRoles) ----------------------

  /**
   * Recompute which roles are functional, taking the role hierarchy (and
   * inverses) into account. Called once per DLOntology load.
   *
   * HermiT builds the super-role graph (edges for SubPropertyOf, symmetric
   * edges for inverse inclusions), closes it transitively, then for every role
   * collects the sub-roles of its functional super-roles as "relevant roles".
   */
  updateFunctionalRoles(dlOntology) {
    const superRoleEdges = new Map(); // role → Set(superroles)
    const declaredFunctional = new Set();

    const addEdge = (from, to) => {
      let s = superRoleEdges.get(from);
      if (!s) { s = new Set(); superRoleEdges.set(from, s); }
      s.add(to);
    };

    for (const clause of dlOntology.dlClauses) {
      if (clause.isAtomicRoleInclusion()) {
        const subrole = clause.bodyAtoms[0].dlPredicate;
        const superrole = clause.headAtoms[0].dlPredicate;
        addEdge(subrole, superrole);
        addEdge(inverseOf(subrole), inverseOf(superrole));
      } else if (clause.isAtomicRoleInverseInclusion()) {
        const subrole = clause.bodyAtoms[0].dlPredicate;
        const superrole = clause.headAtoms[0].dlPredicate;
        addEdge(subrole, inverseOf(superrole));
        addEdge(inverseOf(subrole), superrole);
      } else if (clause.isFunctionalityAxiom()) {
        declaredFunctional.add(clause.bodyAtoms[0].dlPredicate);
      } else if (clause.isInverseFunctionalityAxiom()) {
        declaredFunctional.add(inverseOf(clause.bodyAtoms[0].dlPredicate));
      }
    }

    // Every role is its own super-role; inverses too.
    const allRoles = new Set([...superRoleEdges.keys()]);
    for (const r of declaredFunctional) allRoles.add(r);
    for (const r of [...allRoles]) {
      addEdge(r, r);
      addEdge(inverseOf(r), inverseOf(r));
    }

    // Transitive closure.
    let changed = true;
    while (changed) {
      changed = false;
      for (const [role, supers] of superRoleEdges) {
        for (const sup of [...supers]) {
          const supSupers = superRoleEdges.get(sup);
          if (supSupers) {
            for (const ss of supSupers) {
              if (!supers.has(ss)) { supers.add(ss); changed = true; }
            }
          }
        }
      }
    }

    // subRoleGraph = inverse of superRoleGraph.
    const subRoleEdges = new Map(); // role → Set(subroles)
    for (const [role, supers] of superRoleEdges) {
      for (const sup of supers) {
        let s = subRoleEdges.get(sup);
        if (!s) { s = new Set(); subRoleEdges.set(sup, s); }
        s.add(role);
      }
    }

    // functionalRoles: role → relevant roles (sub-roles of functional supers).
    this.functionalRoles.clear();
    this.declaredFunctionalRoles = declaredFunctional;
    for (const role of superRoleEdges.keys()) {
      const relevant = new Set();
      const supers = superRoleEdges.get(role) || new Set();
      for (const sup of supers) {
        if (declaredFunctional.has(sup)) {
          const subs = subRoleEdges.get(sup);
          if (subs) for (const sub of subs) relevant.add(sub);
        }
      }
      if (relevant.size > 0) this.functionalRoles.set(role, [...relevant]);
    }
  }

  // ---- existential bookkeeping ----------------------------------------------

  markExistentialProcessed(existentialConcept, forNode) {
    this.expandedExistentials.push({ existentialConcept, forNode });
    forNode.removeFromUnprocessedExistentials(existentialConcept);
  }

  branchingPointPushed() {
    const level = this.tableau.getCurrentBranchingPoint().level;
    this.indicesByBranchingPoint[level] = this.expandedExistentials.length;
  }

  backtrack() {
    const level = this.tableau.getCurrentBranchingPoint().level;
    const newSize = this.indicesByBranchingPoint[level] || 0;
    for (let i = this.expandedExistentials.length - 1; i >= newSize; i--) {
      const { existentialConcept, forNode } = this.expandedExistentials[i];
      forNode.addToUnprocessedExistentials(existentialConcept);
    }
    this.expandedExistentials.length = newSize;
  }

  clear() {
    this.expandedExistentials.length = 0;
    this.indicesByBranchingPoint = [0];
    this.auxiliaryNodes.length = 0;
  }

  // ---- functional expansion --------------------------------------------------

  /**
   * If the at-least has cardinality 1 and the role is (inverse-)functional,
   * reuse the existing successor. If cardinality > 1 and the role is
   * functional, set a clash. Returns true if it handled the expansion.
   */
  tryFunctionalExpansion(atLeast, forNode) {
    if (atLeast.number === 1) {
      const found = this._getFunctionalExpansionNode(atLeast.onRole, forNode);
      if (found) {
        const { node: functionalityNode, dependencySet: roleDs } = found;
        const unionDs = this.extensionManager
          .getConceptAssertionDependencySet(atLeast, forNode)
          .union(roleDs);
        this.extensionManager.addRoleAssertion(atLeast.onRole, forNode, functionalityNode, unionDs);
        if (atLeast instanceof AtLeastConcept) {
          this.extensionManager.addConceptAssertion(atLeast.toConcept, functionalityNode, unionDs);
        } else {
          this.extensionManager.addDataRangeAssertion(atLeast.toDataRange, functionalityNode, unionDs);
        }
        return true;
      }
    } else if (atLeast.number > 1 && this.functionalRoles.has(atLeast.onRole)) {
      const ds = this.extensionManager.getConceptAssertionDependencySet(atLeast, forNode);
      this.extensionManager.setClash(ds);
      return true;
    }
    return false;
  }

  /**
   * Find an existing successor of forNode via a functional (relevant) role.
   * Returns {node, dependencySet} or null.
   */
  _getFunctionalExpansionNode(role, forNode) {
    const relevantRoles = this.functionalRoles.get(role);
    if (!relevantRoles) return null;
    const ternary = this.extensionManager.ternaryTable;
    for (const relevantRole of relevantRoles) {
      let entries, toIndex;
      if (relevantRole instanceof AtomicRole) {
        entries = ternary.retrieve(relevantRole, [forNode, null]);
        toIndex = 2;
      } else {
        // InverseRole: search R(?, forNode).
        entries = ternary.retrieve(relevantRole.inverseRole, [null, forNode]);
        toIndex = 1;
      }
      if (entries.length > 0) {
        return { node: entries[0].tuple[toIndex], dependencySet: entries[0].dependencySet };
      }
    }
    return null;
  }

  // ---- normal expansion ------------------------------------------------------

  /** Create fresh successors for ≥n R.C (object role). */
  doNormalExpansionConcept(atLeastConcept, forNode) {
    const ds = this.extensionManager.getConceptAssertionDependencySet(atLeastConcept, forNode);
    const cardinality = atLeastConcept.number;
    this.auxiliaryNodes.length = 0;
    for (let i = 0; i < cardinality; i++) {
      const newNode = this.tableau.createNewTreeNode(ds, forNode);
      this.extensionManager.addRoleAssertion(atLeastConcept.onRole, forNode, newNode, ds);
      this.extensionManager.addConceptAssertion(atLeastConcept.toConcept, newNode, ds);
      this.auxiliaryNodes.push(newNode);
    }
    this._addPairwiseInequalities(ds);
  }

  /** Create fresh successors for ≥n R.D (data role). */
  doNormalExpansionDataRange(atLeastDataRange, forNode) {
    const ds = this.extensionManager.getConceptAssertionDependencySet(atLeastDataRange, forNode);
    const cardinality = atLeastDataRange.number;
    this.auxiliaryNodes.length = 0;
    for (let i = 0; i < cardinality; i++) {
      const newNode = this.tableau.createNewConcreteNode(ds, forNode);
      this.extensionManager.addRoleAssertion(atLeastDataRange.onRole, forNode, newNode, ds);
      this.extensionManager.addDataRangeAssertion(atLeastDataRange.toDataRange, newNode, ds);
      this.auxiliaryNodes.push(newNode);
    }
    this._addPairwiseInequalities(ds);
  }

  _addPairwiseInequalities(ds) {
    const nodes = this.auxiliaryNodes;
    for (let outer = 0; outer < nodes.length; outer++) {
      for (let inner = outer + 1; inner < nodes.length; inner++) {
        this.extensionManager.addAssertion(INEQUALITY, nodes[outer], nodes[inner], ds);
      }
    }
    nodes.length = 0;
  }

  /** Dispatch: functional reuse first, else create fresh successors. */
  expand(atLeast, forNode) {
    if (!this.tryFunctionalExpansion(atLeast, forNode)) {
      if (atLeast instanceof AtLeastConcept) this.doNormalExpansionConcept(atLeast, forNode);
      else this.doNormalExpansionDataRange(atLeast, forNode);
    }
  }
}

function inverseOf(role) {
  if (role instanceof InverseRole) return role.inverseRole;
  return internInverseRole(role);
}

module.exports = { ExistentialExpansionManager };
