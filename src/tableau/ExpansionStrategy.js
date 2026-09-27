'use strict';

// ---------------------------------------------------------------------------
// tableau/ExpansionStrategy.js — decides how ≥n R.C restrictions are expanded.
//
// Mirrors org.semanticweb.HermiT.existentials.{AbstractExpansionStrategy,
// IndividualReuseStrategy}.
//
// expandExistentials(finalChance):
//   1. recompute blocking;
//   2. walk every active, unblocked node with unprocessed existentials;
//   3. for each ≥n R.C:
//        NOT_SATISFIED          → expand (create/reuse successors)
//        PERMANENTLY_SATISFIED  → mark processed (satisfied by a permanent
//                                 assertion; NN/NI merges cannot undo it)
//        CURRENTLY_SATISFIED    → leave unprocessed (a later nominal merge may
//                                 break it; re-checked next iteration)
//
// IndividualReuseStrategy (HermiT's default) additionally tries, in order:
//   a) functional expansion (reuse the single existing R-successor);
//   b) parent reuse (≥1 R.C with C already on the parent — edge to parent);
//   c) model reuse (≥1 R.C with C atomic: reuse/create ONE shared nominal-ish
//      root node per concept C, guarded by a branching point when the calculus
//      is non-deterministic);
//   d) normal expansion (fresh tree successors).
//
// Description-graph existentials (ExistsDescriptionGraph) are not supported —
// clausification never produces them in this port.
// ---------------------------------------------------------------------------

const { BranchingPoint } = require('./BranchingPoint');
const {
  AtomicConcept,
  AtomicRole,
  InverseRole,
  AtLeastConcept,
  AtLeastDataRange,
  INEQUALITY
} = require('../model/DLPredicate');

const SAT = Object.freeze({
  NOT_SATISFIED: 0,
  PERMANENTLY_SATISFIED: 1,
  CURRENTLY_SATISFIED: 2
});

class AbstractExpansionStrategy {
  /**
   * @param {BlockingStrategy} blockingStrategy
   * @param {boolean} expandNodeAtATime stop the sweep after the first expansion
   */
  constructor(blockingStrategy, expandNodeAtATime) {
    this.blockingStrategy = blockingStrategy;
    this.expandNodeAtATime = expandNodeAtATime;
    this.processedExistentials = [];
    this.auxiliaryNodes1 = [];
    this.auxiliaryNodes2 = [];
    this.tableau = null;
    this.extensionManager = null;
    this.existentialExpansionManager = null;
  }

  initialize(tableau) {
    this.tableau = tableau;
    this.extensionManager = tableau.extensionManager;
    this.existentialExpansionManager = tableau.existentialExpansionManager;
    this.blockingStrategy.initialize(tableau);
  }

  clear() {
    this.blockingStrategy.clear();
    this.processedExistentials.length = 0;
  }

  /**
   * Forwarded from `Tableau.setAdditionalDLOntology` / `clearAdditionalDLOntology`
   * so the blocking strategy can disable the signature cache while a query
   * (additional) ontology is in effect (HermiT's `updateBlockingSignatureCacheUsage`).
   */
  additionalDLOntologySet(additionalDLOntology) {
    if (typeof this.blockingStrategy.additionalDLOntologySet === 'function') {
      this.blockingStrategy.additionalDLOntologySet(additionalDLOntology);
    }
  }

  additionalDLOntologyCleared() {
    if (typeof this.blockingStrategy.additionalDLOntologyCleared === 'function') {
      this.blockingStrategy.additionalDLOntologyCleared();
    }
  }

  /**
   * One expansion sweep. Returns true if the extension changed (i.e. the
   * saturation loop must run again).
   */
  expandExistentials(finalChance) {
    this.blockingStrategy.computeBlocking(finalChance);
    let extensionsChanged = false;
    let node = this.tableau.firstTableauNode;
    while (node !== null && (!extensionsChanged || !this.expandNodeAtATime)) {
      if (node.isActive() && !node.isBlocked() && node.hasUnprocessedExistentials()) {
        // The node's unprocessed set may change during operation: copy it.
        this.processedExistentials.length = 0;
        for (const ec of node.unprocessedExistentials) this.processedExistentials.push(ec);
        // HermiT iterates the copy backwards.
        for (let index = this.processedExistentials.length - 1; index >= 0; index--) {
          const atLeast = this.processedExistentials[index];
          switch (this.isSatisfied(atLeast, node)) {
            case SAT.NOT_SATISFIED:
              this.expandExistential(atLeast, node);
              extensionsChanged = true;
              break;
            case SAT.PERMANENTLY_SATISFIED:
              this.existentialExpansionManager.markExistentialProcessed(atLeast, node);
              break;
            case SAT.CURRENTLY_SATISFIED:
              // Leave unprocessed: NN/NI merges may break the satisfier.
              break;
          }
          this.tableau.checkInterrupt();
        }
      }
      node = node.nextTableauNode;
      this.tableau.checkInterrupt();
    }
    return extensionsChanged;
  }

  // ---- satisfaction test ------------------------------------------------------

  /**
   * Is ≥n R.C already satisfied on forNode?
   * @returns {number} one of SAT.*
   */
  isSatisfied(atLeast, forNode) {
    const cardinality = atLeast.number;
    if (cardinality <= 0) return SAT.PERMANENTLY_SATISFIED;
    const onRole = atLeast.onRole;
    const em = this.extensionManager;
    const ternary = em.ternaryTable;

    // Retrieve candidate successors: R(forNode,?) or R⁻(?,forNode)≡RInv(forNode,?) swapped.
    let entries, toNodeIndex;
    if (onRole instanceof AtomicRole) {
      entries = ternary.retrieve(onRole, [forNode, null]);
      toNodeIndex = 2;
    } else {
      entries = ternary.retrieve(onRole.inverseRole, [null, forNode]);
      toNodeIndex = 1;
    }

    const isDataRange = atLeast instanceof AtLeastDataRange;
    const target = isDataRange ? atLeast.toDataRange : atLeast.toConcept;

    const hasTarget = (toNode) => {
      if (isDataRange) return em.containsDataRangeAssertion(target, toNode);
      // A blocked successor only counts if it is forNode's direct child
      // (its label is still fully present on the branch to the blocker).
      return (!toNode.isBlocked() || forNode.isParentOf(toNode))
        && em.containsConceptAssertion(target, toNode);
    };

    if (cardinality === 1) {
      for (const e of entries) {
        const toNode = e.tuple[toNodeIndex];
        if (hasTarget(toNode)) {
          if (this.isPermanentSatisfier(forNode, toNode)
            && this.blockingStrategy.isPermanentAssertion(target, toNode)) {
            return SAT.PERMANENTLY_SATISFIED;
          }
          return SAT.CURRENTLY_SATISFIED;
        }
      }
      return SAT.NOT_SATISFIED;
    }

    // cardinality > 1: collect satisfiers, then look for n pairwise-unequal ones.
    this.auxiliaryNodes1.length = 0;
    let allSatisfiersArePermanent = true;
    for (const e of entries) {
      const toNode = e.tuple[toNodeIndex];
      if (hasTarget(toNode)) {
        if (!this.isPermanentSatisfier(forNode, toNode)
          || !this.blockingStrategy.isPermanentAssertion(target, toNode)) {
          allSatisfiersArePermanent = false;
        }
        this.auxiliaryNodes1.push(toNode);
      }
    }
    if (this.auxiliaryNodes1.length >= cardinality) {
      this.auxiliaryNodes2.length = 0;
      if (this.containsSubsetOfNUnequalNodes(this.auxiliaryNodes1, 0, this.auxiliaryNodes2, cardinality)) {
        return allSatisfiersArePermanent ? SAT.PERMANENTLY_SATISFIED : SAT.CURRENTLY_SATISFIED;
      }
    }
    return SAT.NOT_SATISFIED;
  }

  /**
   * A satisfier is permanent when no future merge/prune can remove it: the
   * node itself, its parent, its child, or any root node.
   */
  isPermanentSatisfier(forNode, toNode) {
    return forNode === toNode
      || forNode.parent === toNode
      || toNode.parent === forNode
      || toNode.isRootNode();
  }

  /** Recursive selection of `cardinality` pairwise-Inequality nodes. */
  containsSubsetOfNUnequalNodes(nodes, startAt, selectedNodes, cardinality) {
    if (selectedNodes.length === cardinality) return true;
    outer:
    for (let index = startAt; index < nodes.length; index++) {
      const node = nodes[index];
      for (const selectedNode of selectedNodes) {
        if (!this.extensionManager.containsAssertion(INEQUALITY, node, selectedNode)
          && !this.extensionManager.containsAssertion(INEQUALITY, selectedNode, node)) {
          continue outer;
        }
      }
      selectedNodes.push(node);
      if (this.containsSubsetOfNUnequalNodes(nodes, index + 1, selectedNodes, cardinality)) return true;
      selectedNodes.pop();
    }
    return false;
  }

  // ---- notifications forwarded to the blocking strategy ----------------------

  assertionAddedConcept(concept, node) { this.blockingStrategy.assertionAddedConcept(concept, node); }
  assertionRemovedConcept(concept, node) { this.blockingStrategy.assertionRemovedConcept(concept, node); }
  assertionAddedRole(role, from, to) { this.blockingStrategy.assertionAddedRole(role, from, to); }
  assertionRemovedRole(role, from, to) { this.blockingStrategy.assertionRemovedRole(role, from, to); }
  nodesMerged(mergeFrom, mergeInto) { this.blockingStrategy.nodesMerged(mergeFrom, mergeInto); }
  nodesUnmerged(mergeFrom, mergeInto) { this.blockingStrategy.nodesUnmerged(mergeFrom, mergeInto); }
  nodeStatusChanged(node) { this.blockingStrategy.nodeStatusChanged(node); }
  nodeInitialized(node) { this.blockingStrategy.nodeInitialized(node); }
  nodeDestroyed(node) { this.blockingStrategy.nodeDestroyed(node); }
  branchingPointPushed() { /* base: nothing */ }
  backtrack() { /* base: nothing */ }
  modelFound() { this.blockingStrategy.modelFound(); }
  isExact() { return this.blockingStrategy.isExact(); }

  /** Abstract: perform the actual expansion of one restriction. */
  expandExistential(atLeast, forNode) {
    throw new Error('expandExistential must be implemented by subclass');
  }
}

// ===========================================================================
// IndividualReuseStrategy — HermiT's default strategy.
// ===========================================================================

class IndividualReuseBranchingPoint extends BranchingPoint {
  constructor(tableau, strategy, existential, node, wasParentReuse) {
    super(tableau);
    this.strategy = strategy;
    this.existential = existential;
    this.node = node;
    this.wasParentReuse = wasParentReuse;
  }

  startNextChoice(tableau, clashDependencySet) {
    if (!this.wasParentReuse) {
      this.strategy.dontReuseConceptsThisRun.add(this.existential.toConcept);
    }
    const dependencySet = tableau.dependencySetFactory.removeBranchingPoint(clashDependencySet, this.level);
    const existentialNode = tableau.createNewTreeNode(dependencySet, this.node);
    tableau.extensionManager.addConceptAssertion(this.existential.toConcept, existentialNode, dependencySet);
    tableau.extensionManager.addRoleAssertion(this.existential.onRole, this.node, existentialNode, dependencySet);
  }
}

class IndividualReuseStrategy extends AbstractExpansionStrategy {
  /**
   * @param {BlockingStrategy} blockingStrategy
   * @param {boolean} isDeterministic true when the ontology is Horn (no
   *        disjunctions can arise) — reuse then needs no branching points.
   */
  constructor(blockingStrategy, isDeterministic) {
    super(blockingStrategy, true);
    this.isDeterministicFlag = isDeterministic;
    /** AtomicConcept → {node, branchingPointLevel} */
    this.reusedNodes = new Map();
    this.doReuseConceptsAlways = new Set();
    this.dontReuseConceptsThisRun = new Set();
    this.dontReuseConceptsEver = new Set();
    // Backtracking: concepts registered per branching-point level.
    this.reuseBacktrackingTable = [];
    this.indicesByBranchingPoint = [0];
  }

  initialize(tableau) {
    super.initialize(tableau);
    this.doReuseConceptsAlways.clear();
    this.dontReuseConceptsEver.clear();
  }

  clear() {
    super.clear();
    this.reusedNodes.clear();
    this.reuseBacktrackingTable.length = 0;
    this.dontReuseConceptsThisRun.clear();
    for (const c of this.dontReuseConceptsEver) this.dontReuseConceptsThisRun.add(c);
  }

  branchingPointPushed() {
    const level = this.tableau.getCurrentBranchingPoint().level;
    this.indicesByBranchingPoint[level] = this.reuseBacktrackingTable.length;
  }

  backtrack() {
    const level = this.tableau.getCurrentBranchingPoint().level;
    const requiredSize = this.indicesByBranchingPoint[level] || 0;
    for (let i = this.reuseBacktrackingTable.length - 1; i >= requiredSize; i--) {
      this.reusedNodes.delete(this.reuseBacktrackingTable[i]);
    }
    this.reuseBacktrackingTable.length = requiredSize;
  }

  modelFound() {
    super.modelFound();
    for (const c of this.dontReuseConceptsThisRun) this.dontReuseConceptsEver.add(c);
  }

  isDeterministic() { return this.isDeterministicFlag; }

  // ---- the expansion itself ----------------------------------------------------

  expandExistential(atLeast, forNode) {
    // Mark processed BEFORE branching takes place (HermiT's discipline): the
    // branching point's alternative re-asserts via a fresh tree node, and the
    // restriction must not be re-expanded on the alternative branch.
    this.existentialExpansionManager.markExistentialProcessed(atLeast, forNode);
    if (this.existentialExpansionManager.tryFunctionalExpansion(atLeast, forNode)) return;
    if (atLeast instanceof AtLeastDataRange) {
      this.existentialExpansionManager.doNormalExpansionDataRange(atLeast, forNode);
      return;
    }
    if (this.tryParentReuse(atLeast, forNode)) return;
    if (this.expandWithModelReuse(atLeast, forNode)) return;
    this.existentialExpansionManager.doNormalExpansionConcept(atLeast, forNode);
  }

  /** ≥1 R.C where the parent already has C: point the edge at the parent. */
  tryParentReuse(atLeastConcept, node) {
    if (atLeastConcept.number !== 1) return false;
    const parent = node.parent;
    if (parent === null) return false;
    if (!this.extensionManager.containsConceptAssertion(atLeastConcept.toConcept, parent)) return false;
    let dependencySet = this.extensionManager.getConceptAssertionDependencySet(atLeastConcept, node);
    if (!this.isDeterministicFlag) {
      const bp = new IndividualReuseBranchingPoint(this.tableau, this, atLeastConcept, node, true);
      this.tableau.pushBranchingPoint(bp);
      dependencySet = this.tableau.dependencySetFactory.addBranchingPoint(dependencySet, bp.level);
    }
    this.extensionManager.addRoleAssertion(atLeastConcept.onRole, node, parent, dependencySet);
    return true;
  }

  /**
   * ≥1 R.C with C an external atomic concept: all such existentials share ONE
   * node per concept (created as a root "NI" node so keys don't apply).
   */
  expandWithModelReuse(atLeastConcept, node) {
    const toConcept = atLeastConcept.toConcept;
    if (!(toConcept instanceof AtomicConcept)) return false;
    if (this.tableau.isInternalIRI(toConcept.iri)) return false;
    if (atLeastConcept.number !== 1) return false;
    if (!this.doReuseConceptsAlways.has(toConcept) && this.dontReuseConceptsThisRun.has(toConcept)) return false;

    let dependencySet = this.extensionManager.getConceptAssertionDependencySet(atLeastConcept, node);
    let existentialNode;
    const reuseInfo = this.reusedNodes.get(toConcept);
    if (reuseInfo === undefined) {
      // First expansion for this concept: create the shared node.
      if (!this.isDeterministicFlag) {
        const bp = new IndividualReuseBranchingPoint(this.tableau, this, atLeastConcept, node, false);
        this.tableau.pushBranchingPoint(bp);
        dependencySet = this.tableau.dependencySetFactory.addBranchingPoint(dependencySet, bp.level);
      }
      existentialNode = this.tableau.createNewNINode(dependencySet);
      this.reusedNodes.set(toConcept, {
        node: existentialNode,
        branchingPointLevel: this.tableau.getCurrentBranchingPointLevel()
      });
      this.extensionManager.addConceptAssertion(toConcept, existentialNode, dependencySet);
      this.reuseBacktrackingTable.push(toConcept);
    } else {
      dependencySet = reuseInfo.node.addCanonicalNodeDependencySet(dependencySet);
      existentialNode = reuseInfo.node.getCanonicalNode();
      if (!this.isDeterministicFlag) {
        dependencySet = this.tableau.dependencySetFactory.addBranchingPoint(dependencySet, reuseInfo.branchingPointLevel);
      }
    }
    this.extensionManager.addRoleAssertion(atLeastConcept.onRole, node, existentialNode, dependencySet);
    return true;
  }
}

/**
 * HermiT's simplest strategy: expand every existential on the oldest node that
 * still has one, creating fresh successors. Always deterministic (it never
 * pushes a branching point), so it is used when the ontology is not Horn or
 * when individual reuse would be unsound.
 */
class CreationOrderStrategy extends AbstractExpansionStrategy {
  constructor(blockingStrategy) {
    super(blockingStrategy, true);
  }
  isDeterministic() { return true; }
  expandExistential(atLeast, forNode) {
    this.existentialExpansionManager.expand(atLeast, forNode);
    this.existentialExpansionManager.markExistentialProcessed(atLeast, forNode);
  }
}

module.exports = {
  AbstractExpansionStrategy,
  CreationOrderStrategy,
  IndividualReuseStrategy,
  SAT
};
