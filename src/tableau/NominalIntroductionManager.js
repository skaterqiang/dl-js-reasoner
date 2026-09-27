'use strict';

// ---------------------------------------------------------------------------
// tableau/NominalIntroductionManager.js — the NN/NI rules for nominals.
//
// Mirrors org.semanticweb.HermiT.tableau.NominalIntroductionManager.
//
// ≤n R.{o} restrictions clausify to AnnotatedEquality(n, R, C)(y₁,y₂,X)
// heads: "any n+1 R-successors of X in C must coincide". When such an atom
// matches on nodes (node0 ≈ node1 annotated by node2):
//
//   • canForgetAnnotation — the annotation is irrelevant (node0/node1 are
//     roots, or node2 is the parent of both): just merge node0 into node1.
//   • cardinality 1 — deterministic: apply the NI rule immediately.
//   • cardinality > 1 — non-deterministic: queue the annotated equality; the
//     main loop processes the queue, and the NI rule branches over WHICH of
//     the ≤n nominal root nodes the two successors are merged into.
//
// The NI rule creates (or reuses) a fresh root node per (node2, annotation,
// choice-number) triple and merges both successors into it — nominals become
// shared root individuals in the model.
// ---------------------------------------------------------------------------

const { BranchingPoint } = require('./BranchingPoint');
const { PERMANENT } = require('./DependencySet');

class NominalIntroductionManager {
  /**
   * @param {Tableau} tableau
   */
  constructor(tableau) {
    this.tableau = tableau;
    this.dependencySetFactory = tableau.dependencySetFactory;
    this.mergingManager = tableau.mergingManager;

    /** queued annotated equalities: {ae, node0, node1, node2, dependencySet} */
    this.annotatedEqualities = [];
    this.firstUnprocessedAnnotatedEquality = 0;

    /** (rootNode, ae, number) → NI root node */
    this.newRootNodes = new Map();

    this.indicesByBranchingPoint = [0, 0, 0];
  }

  clear() {
    this.annotatedEqualities.length = 0;
    this.firstUnprocessedAnnotatedEquality = 0;
    this.newRootNodes.clear();
    this.indicesByBranchingPoint = [0, 0, 0];
  }

  branchingPointPushed() {
    const level = this.tableau.getCurrentBranchingPoint().level;
    this.indicesByBranchingPoint[level] = [
      this.firstUnprocessedAnnotatedEquality,
      this.annotatedEqualities.length,
      this.newRootNodes.size
    ];
    // Also snapshot the key list so backtrack can delete the right entries.
    this.indicesByBranchingPoint[level].keys = [...this.newRootNodes.keys()];
  }

  backtrack() {
    const level = this.tableau.getCurrentBranchingPoint().level;
    const snapshot = this.indicesByBranchingPoint[level];
    // No checkpoint at this level. This happens for the non-backtrackable
    // "dummy dependency" branching point, which `Tableau.isSatisfiable`
    // installs by assigning `branchingPoints[0]` directly and so never routes
    // through `pushBranchingPoint` → `branchingPointPushed`. Nothing to undo.
    //
    // NOTE: the old `|| [0, 0, 0, []]` fallback could never work — see the
    // `keys` comment below, a bare array makes `new Set(...)` throw.
    if (!snapshot) return;

    this.firstUnprocessedAnnotatedEquality = snapshot[0];
    this.annotatedEqualities.length = snapshot[1];

    // Restore the root-node map to its snapshot key set.
    //
    // `keys` is an OWN property attached by `branchingPointPushed`. It must be
    // read with a hasOwnProperty guard rather than the `snapshot.keys || []`
    // idiom: `snapshot` is an Array, and every array inherits
    // `Array.prototype.keys` — a FUNCTION. So on any snapshot lacking the own
    // property, `snapshot.keys || []` yields that function (truthy) and
    // `new Set(fn)` throws "function is not iterable".
    const keep = new Set(
      Object.prototype.hasOwnProperty.call(snapshot, 'keys') ? snapshot.keys : []
    );
    for (const key of [...this.newRootNodes.keys()]) {
      if (!keep.has(key)) this.newRootNodes.delete(key);
    }
  }

  /**
   * The annotation can be forgotten when the merge it demands is independent
   * of the ≤n context: either side is already a root, or the annotating node
   * is the parent of both sides (then the successors are plain tree nodes).
   */
  canForgetAnnotation(annotatedEquality, node0, node1, node2) {
    return node0.isRootNode() || node1.isRootNode() || !node2.isRootNode()
      || (node2.isParentOf(node0) && node2.isParentOf(node1));
  }

  /**
   * Entry point from ExtensionManager when an AnnotatedEquality tuple is added.
   */
  addAnnotatedEquality(annotatedEquality, node0, node1, node2, dependencySet) {
    if (!node0.isActive() || !node1.isActive() || !node2.isActive()) return false;
    if (this.canForgetAnnotation(annotatedEquality, node0, node1, node2)) {
      return this.mergingManager.mergeNodes(node0, node1, dependencySet);
    }
    if (annotatedEquality.cardinality === 1) {
      return this.applyNIRule(annotatedEquality, node0, node1, node2, dependencySet);
    }
    // Non-deterministic: queue for later processing (permanent dependency set;
    // the branching happens when the rule is applied).
    this.annotatedEqualities.push({
      annotatedEquality, node0, node1, node2,
      dependencySet: dependencySet || PERMANENT
    });
    return true;
  }

  /**
   * Drain the queue of annotated equalities. Called from the main loop after
   * saturation and before/after existential expansion.
   * @returns {boolean} true if anything changed
   */
  processAnnotatedEqualities() {
    let result = false;
    while (this.firstUnprocessedAnnotatedEquality < this.annotatedEqualities.length) {
      const entry = this.annotatedEqualities[this.firstUnprocessedAnnotatedEquality++];
      if (this.applyNIRule(entry.annotatedEquality, entry.node0, entry.node1, entry.node2, entry.dependencySet)) {
        result = true;
      }
      this.tableau.checkInterrupt();
    }
    return result;
  }

  applyNIRule(annotatedEquality, node0, node1, node2, dependencySet) {
    if (node0.pruned || node1.pruned || node2.pruned) return false;
    let ds = dependencySet;
    ds = node0.addCanonicalNodeDependencySet(ds);
    ds = node1.addCanonicalNodeDependencySet(ds);
    ds = node2.addCanonicalNodeDependencySet(ds);
    node0 = node0.getCanonicalNode();
    node1 = node1.getCanonicalNode();
    node2 = node2.getCanonicalNode();
    if (this.canForgetAnnotation(annotatedEquality, node0, node1, node2)) {
      return this.mergingManager.mergeNodes(node0, node1, ds);
    }
    // Pick the NI target: a non-root node not parented by node2.
    let niTargetNode, otherNode;
    if (!node0.isRootNode() && !node2.isParentOf(node0)) {
      niTargetNode = node0; otherNode = node1;
    } else {
      niTargetNode = node1; otherNode = node0;
    }
    if (annotatedEquality.cardinality > 1) {
      const bp = new NominalIntroductionBranchingPoint(
        this.tableau, this, node2, niTargetNode, otherNode, annotatedEquality);
      this.tableau.pushBranchingPoint(bp);
      ds = this.dependencySetFactory.addBranchingPoint(ds, bp.level);
    }
    let newRootNode = this.getNIRootFor(ds, node2, annotatedEquality, 1);
    if (!newRootNode.isActive()) {
      ds = newRootNode.addCanonicalNodeDependencySet(ds);
      newRootNode = newRootNode.getCanonicalNode();
    }
    this.mergingManager.mergeNodes(niTargetNode, newRootNode, ds);
    if (!otherNode.pruned) {
      ds = otherNode.addCanonicalNodeDependencySet(ds);
      this.mergingManager.mergeNodes(otherNode.getCanonicalNode(), newRootNode, ds);
    }
    return true;
  }

  /**
   * The shared NI root node for (rootNode, annotatedEquality, number): created
   * on first use so different branches of the NI rule reuse the same nominal
   * individual.
   */
  getNIRootFor(dependencySet, rootNode, annotatedEquality, number) {
    const key = `${rootNode.nodeID}|${annotatedEquality.toString()}|${number}`;
    let node = this.newRootNodes.get(key);
    if (node === undefined) {
      node = this.tableau.createNewNINode(dependencySet);
      this.newRootNodes.set(key, node);
    }
    return node;
  }
}

class NominalIntroductionBranchingPoint extends BranchingPoint {
  constructor(tableau, niManager, rootNode, niTargetNode, otherNode, annotatedEquality) {
    super(tableau);
    this.niManager = niManager;
    this.rootNode = rootNode;
    this.niTargetNode = niTargetNode;
    this.otherNode = otherNode;
    this.annotatedEquality = annotatedEquality;
    // The first merge (choice 1) was performed by applyNIRule itself.
    this.currentRootNode = 1;
  }

  startNextChoice(tableau, clashDependencySet) {
    this.currentRootNode++;
    let dependencySet = clashDependencySet;
    if (this.currentRootNode === this.annotatedEquality.cardinality) {
      dependencySet = tableau.dependencySetFactory.removeBranchingPoint(dependencySet, this.level);
    }
    let newRootNode = this.niManager.getNIRootFor(dependencySet, this.rootNode, this.annotatedEquality, this.currentRootNode);
    if (!newRootNode.isActive()) {
      dependencySet = newRootNode.addCanonicalNodeDependencySet(dependencySet);
      newRootNode = newRootNode.getCanonicalNode();
    }
    this.niManager.mergingManager.mergeNodes(this.niTargetNode, newRootNode, dependencySet);
    if (!this.otherNode.pruned) {
      dependencySet = this.otherNode.addCanonicalNodeDependencySet(dependencySet);
      this.niManager.mergingManager.mergeNodes(this.otherNode.getCanonicalNode(), newRootNode, dependencySet);
    }
  }
}

module.exports = { NominalIntroductionManager, NominalIntroductionBranchingPoint };
