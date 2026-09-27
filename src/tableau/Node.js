'use strict';

// ---------------------------------------------------------------------------
// tableau/Node.js — a node of the model being built.
//
// Mirrors org.semanticweb.HermiT.tableau.{Node,NodeType}. A node is an
// individual in the candidate model: a named individual, an anonymous tree
// node created by existential expansion, or a concrete (data) node holding a
// literal value. Nodes form a tree via `parent`; merges redirect a node to its
// canonical representative via `mergedInto`.
// ---------------------------------------------------------------------------

const { PERMANENT } = require('./DependencySet');

// Mirrors org.semanticweb.HermiT.tableau.NodeType. Each type carries three
// flags HermiT relies on:
//   mergePrecedence — lower merges into higher (0 = named individual, most
//                     "canonical"; 2 = tree/concrete node, least).
//   isNITarget      — may be the target of the nominal-introduction (NI) rule.
//   isAbstract      — an object-domain node (vs. a concrete data node).
const NODE_TYPE = Object.freeze({
  NAMED_NODE: 'NamedNode',                 // a named individual from the ABox
  NI_NODE: 'NINode',                       // nominal-introduction root node
  ROOT_CONSTANT_NODE: 'RootConstantNode',  // a data constant used as a root
  TREE_NODE: 'TreeNode',                   // anonymous successor from ∃-expansion
  CONCRETE_NODE: 'ConcreteNode'            // data node holding a literal value
});

/** mergePrecedence per node type (mirrors the first NodeType enum argument). */
const MERGE_PRECEDENCE = Object.freeze({
  [NODE_TYPE.NAMED_NODE]: 0,
  [NODE_TYPE.NI_NODE]: 1,
  [NODE_TYPE.ROOT_CONSTANT_NODE]: 1,
  [NODE_TYPE.TREE_NODE]: 2,
  [NODE_TYPE.CONCRETE_NODE]: 2
});

/** isNITarget per node type (mirrors the second NodeType enum argument). */
const IS_NI_TARGET = Object.freeze({
  [NODE_TYPE.NAMED_NODE]: false,
  [NODE_TYPE.NI_NODE]: false,
  [NODE_TYPE.ROOT_CONSTANT_NODE]: false,
  [NODE_TYPE.TREE_NODE]: true,
  [NODE_TYPE.CONCRETE_NODE]: false
});

/** isAbstract per node type (mirrors the third NodeType enum argument). */
const IS_ABSTRACT = Object.freeze({
  [NODE_TYPE.NAMED_NODE]: true,
  [NODE_TYPE.NI_NODE]: true,
  [NODE_TYPE.ROOT_CONSTANT_NODE]: false,
  [NODE_TYPE.TREE_NODE]: true,
  [NODE_TYPE.CONCRETE_NODE]: false
});

let _nodeCounter = 0;

class Node {
  /**
   * @param {number} nodeID    unique, monotonically increasing
   * @param {string} nodeType  one of NODE_TYPE
   * @param {Node|null} parent
   */
  constructor(nodeID, nodeType, parent = null) {
    this.nodeID = nodeID;
    this.nodeType = nodeType;
    this.parent = parent;
    this.treeDepth = parent ? parent.treeDepth + 1 : 0;

    // Merge / pruning state.
    this.mergedInto = null;   // canonical node this was merged into (or null)
    this.mergedIntoDependencySet = null; // why this node was merged
    this.pruned = false;      // removed from the model (subtree of a merged node)

    // Blocking state (see blocking/).
    this.blocker = null;          // the node blocking this one (or null)
    this.directlyBlocked = false; // blocked by an ancestor vs. by a descendant-of-ancestor

    // Label bookkeeping used by blocking, merging & clash detection. These
    // counters mirror Node.m_numberOf* and let ClashManager detect a clash the
    // instant an offending tuple is added, without scanning the whole label.
    this.concepts = new Set();       // set of unary DLPredicates asserted on this node
    this.numberOfPositiveAtomicConcepts = 0;
    this.numberOfNegatedAtomicConcepts = 0;
    this.numberOfNegatedRoleAssertions = 0;

    // NOTE: HermiT's Node also carries `m_dataConstraints` for concrete nodes.
    // This port deliberately does NOT: datatype reasoning is handled entirely by
    // ExtensionTable tuples (`>=n T(x)` / `T(x, "lit"^^dt)`), so a per-node
    // constraint list would be a second, unsynchronised source of truth.

    // Existential bookkeeping.
    // unprocessedExistentials: ≥n R.C restrictions asserted on this node that
    // have NOT yet been expanded (drives expandExistentials). HermiT keeps a
    // list+set pair; a Set suffices (iteration order = insertion order).
    this.unprocessedExistentials = new Set();

    // Tree structure: children in creation order.
    this.children = [];

    // Edges: role assertions involving this node, kept for fast merge copying.
    this.outgoingEdges = [];  // [{role, to, dependencySet}]
    this.incomingEdges = [];  // [{role, from, dependencySet}]

    // Intrusive list links maintained by the Tableau (mirrors Node.m_*Node).
    this.previousTableauNode = null;
    this.nextTableauNode = null;
    this.previousMergedOrPrunedNode = null;

    // Opaque slot for the blocking strategy's per-node data.
    this.blockingObject = null;
  }


  // ---- lifecycle (HermiT: Node.initialize / Node.destroy) -------------------

  /**
   * (Re-)activate a pooled node. The Tableau owns the node list and calls this
   * right after taking a node off the free list (or allocating a fresh one).
   */
  initialize(nodeID, parent, nodeType, treeDepth) {
    this.nodeID = nodeID;
    this.parent = parent;
    this.nodeType = nodeType;
    this.treeDepth = treeDepth;
    this.mergedInto = null;
    this.mergedIntoDependencySet = null;
    this.pruned = false;
    this.blocker = null;
    this.directlyBlocked = false;
    this.concepts.clear();
    this.numberOfPositiveAtomicConcepts = 0;
    this.numberOfNegatedAtomicConcepts = 0;
    this.numberOfNegatedRoleAssertions = 0;
    this.unprocessedExistentials.clear();
    this.children.length = 0;
    this.outgoingEdges.length = 0;
    this.incomingEdges.length = 0;
    this.previousTableauNode = null;
    this.nextTableauNode = null;
    this.previousMergedOrPrunedNode = null;
    this.blockingObject = null;
    return this;
  }

  /** Reset a node that is about to go back onto the free list. */
  destroy(tableau) {
    this.nodeID = -1;
    this.parent = null;
    this.nodeType = null;
    this.mergedInto = null;
    this.mergedIntoDependencySet = null;
    this.pruned = false;
    this.blocker = null;
    this.directlyBlocked = false;
    this.concepts.clear();
    this.numberOfPositiveAtomicConcepts = 0;
    this.numberOfNegatedAtomicConcepts = 0;
    this.numberOfNegatedRoleAssertions = 0;
    this.unprocessedExistentials.clear();
    this.children.length = 0;
    this.outgoingEdges.length = 0;
    this.incomingEdges.length = 0;
    this.previousTableauNode = null;
    this.nextTableauNode = null;
    this.previousMergedOrPrunedNode = null;
    this.blockingObject = null;
    if (tableau && typeof tableau.putExistentialConceptsBuffer === 'function') {
      /* buffer pooling hook (kept for symmetry with HermiT) */
    }
  }

  // ---- existential bookkeeping ---------------------------------------------

  addToUnprocessedExistentials(existentialConcept) {
    this.unprocessedExistentials.add(existentialConcept);
  }

  removeFromUnprocessedExistentials(existentialConcept) {
    this.unprocessedExistentials.delete(existentialConcept);
  }

  hasUnprocessedExistentials() {
    return this.unprocessedExistentials.size > 0;
  }

  /**
   * Weaken a dependency set with the merge history of this node: if the node
   * was merged into its canonical representative under some branching point,
   * any fact stated about the canonical node depends on that choice too.
   * Mirrors Node.addCanonicalNodeDependencySet.
   */
  addCanonicalNodeDependencySet(dependencySet) {
    let node = this;
    let ds = dependencySet;
    const seen = new Set();
    while (node.mergedInto !== null && !seen.has(node)) {
      seen.add(node);
      ds = ds.union(node.mergedIntoDependencySet);
      node = node.mergedInto;
    }
    return ds;
  }

  /**
   * The dependency set of the merge chain leading to this node's canonical
   * representative. Empty (i.e. `PERMANENT`) iff the node was never merged
   * under a branching point — classification uses that to decide whether a
   * model can be trusted to read known subsumers off.
   *
   * Mirrors Node.getCanonicalNodeDependencySet. HermiT routes through
   * `m_tableau.m_dependencySetFactory.m_emptySet`; this port uses the interned
   * `PERMANENT` constant directly (nodes hold no tableau back-reference).
   */
  getCanonicalNodeDependencySet() {
    return this.addCanonicalNodeDependencySet(PERMANENT);
  }

  isAbstract() {
    return IS_ABSTRACT[this.nodeType];
  }

  isConcrete() { return !IS_ABSTRACT[this.nodeType]; }

  /** May this node be the target of the nominal-introduction rule? */
  isNITarget() { return IS_NI_TARGET[this.nodeType]; }

  isActive() { return !this.pruned && this.mergedInto === null; }
  isMerged() { return this.mergedInto !== null; }

  getMergePrecedence() { return MERGE_PRECEDENCE[this.nodeType]; }

  /** A node with no parent is a root of the (forest) model. */
  isRootNode() { return this.parent === null; }

  isParentOf(potentialChild) { return potentialChild.parent === this; }

  isAncestorOf(potentialDescendant) {
    let n = potentialDescendant;
    const seen = new Set();
    while (n !== null && !seen.has(n)) {
      seen.add(n);
      n = n.parent;
      if (n === this) return true;
    }
    return false;
  }

  getTreeDepth() { return this.treeDepth; }

  /** The anchor of the tree this node belongs to (tree nodes anchor themselves). */
  getClusterAnchor() {
    return this.nodeType === NODE_TYPE.TREE_NODE ? this : this.parent;
  }

  /** Follow merge redirections to the live representative. */
  getCanonicalNode() {
    let n = this;
    const seen = new Set();
    while (n.mergedInto !== null && !seen.has(n)) {
      seen.add(n);
      n = n.mergedInto;
    }
    return n;
  }

  /** True if this node is blocked (has a blocker). */
  isBlocked() { return this.blocker !== null; }
  isDirectlyBlocked() { return this.directlyBlocked; }
  isIndirectlyBlocked() { return this.blocker !== null && !this.directlyBlocked; }
  getBlocker() { return this.blocker; }
  setBlocked(blocker, directlyBlocked) {
    this.blocker = blocker;
    this.directlyBlocked = !!directlyBlocked;
  }

  /** True if this node or any ancestor is blocked (expansion must stop here). */
  isEffectivelyBlocked() {
    if (this.blocker !== null) return true;
    let p = this.parent;
    const seen = new Set();
    while (p !== null && !seen.has(p)) {
      seen.add(p);
      if (p.blocker !== null) return true;
      p = p.parent;
    }
    return false;
  }

  /** Ancestors from parent up to the root. */
  *ancestors() {
    let p = this.parent;
    const seen = new Set();
    while (p !== null && !seen.has(p)) {
      seen.add(p);
      yield p;
      p = p.parent;
    }
  }

  toString() {
    return `${this.nodeType}#${this.nodeID}${this.mergedInto ? `→#${this.mergedInto.nodeID}` : ''}${this.pruned ? '(pruned)' : ''}`;
  }
}
/**
 * Sentinel blocker used when a node is blocked by a remembered
 * BlockingSignatureCache entry rather than by a live node (HermiT
 * `Node.SIGNATURE_CACHE_BLOCKER`). It carries a `nodeID` so the debug dump in
 * `Tableau` (`node.blocker.nodeID`) never dereferences null.
 */
Node.SIGNATURE_CACHE_BLOCKER = { nodeID: 'signature-cache' };
/** Allocate a fresh node id. */
function nextNodeID() { return _nodeCounter++; }
function resetNodeIDs() { _nodeCounter = 0; }

module.exports = { Node, NODE_TYPE, MERGE_PRECEDENCE, IS_NI_TARGET, IS_ABSTRACT, nextNodeID, resetNodeIDs };
