'use strict';
/**
 * Classification for deterministic (Horn) tableaux.
 *
 * Port of `org.semanticweb.HermiT.hierarchy.DeterministicClassification`.
 *
 * When the tableau is deterministic there is at most one model, so a concept's
 * subsumers can simply be READ OFF that model: assert `C(fresh)` once per
 * concept, run the calculus, and collect every atomic concept asserted on the
 * fresh individual's canonical node. That is O(|C|) tableau runs instead of the
 * O(|C|²) subsumption tests `QuasiOrderClassification` needs.
 *
 * The resulting "subsumer graph" is then converted into a hierarchy by
 * computing its strongly connected components (mutual subsumption = equivalence)
 * and topologically ordering them.
 */

const { Hierarchy, HierarchyNode } = require('./Hierarchy');
const { createAnonymousIndividual } = require('../model/Term');
const { createAtom } = require('../model/Atom');

/**
 * A node of the raw subsumer graph, before SCC condensation.
 *
 * `successors` are the elements this element is subsumed by (edges point
 * UPWARD, toward more general concepts) — matching HermiT, where
 * `visit` starts at the BOTTOM element and follows successors to the top.
 */
class GraphNode {
  /**
   * @param {*} element
   * @param {Set<*>} successors
   */
  constructor(element, successors) {
    this.element = element;
    this.successors = successors;
    this.dfsIndex = -1;
    this.sccHead = null;
    this.topologicalOrderIndex = -1;
  }

  notVisited() { return this.dfsIndex === -1; }
  isAssignedToSCC() { return this.topologicalOrderIndex !== -1; }
}

class DeterministicClassification {
  /**
   * @param {object} tableau
   * @param {{elementClassified: (element: *) => void}} progressMonitor
   * @param {*} topElement     e.g. `AtomicConcept.THING`
   * @param {*} bottomElement  e.g. `AtomicConcept.NOTHING`
   * @param {Set<*>} elements  every element to classify (must include top/bottom)
   */
  constructor(tableau, progressMonitor, topElement, bottomElement, elements) {
    this.tableau = tableau;
    this.progressMonitor = progressMonitor;
    this.topElement = topElement;
    this.bottomElement = bottomElement;
    this.elements = elements;
  }

  /** @returns {Hierarchy} */
  classify() {
    if (!this.tableau.isDeterministic()) {
      throw new Error('Internal error: DeterministicClassification can be used only with a deterministic tableau.');
    }
    const freshIndividual = createAnonymousIndividual('fresh-individual');
    const freshAtom = createAtom(this.topElement, freshIndividual);

    // If even owl:Thing is unsatisfiable the whole ontology is inconsistent:
    // everything collapses into one node.
    if (!this.tableau.isSatisfiable({
      loadPermanentABox: true,
      perTestPositiveFactsNoDependency: [freshAtom],
      reasoningTaskDescription: `isConceptSatisfiable(${this.topElement})`
    })) {
      return Hierarchy.emptyHierarchy(this.elements, this.topElement, this.bottomElement);
    }

    const binaryTable = this.tableau.getExtensionManager().getExtensionTable(2);
    const allSubsumers = new Map();
    for (const element of this.elements) {
      let subsumers;
      const nodesForIndividuals = new Map([[freshIndividual, null]]);
      if (!this.tableau.isSatisfiable({
        loadPermanentABox: true,
        perTestPositiveFactsNoDependency: [createAtom(element, freshIndividual)],
        nodesForIndividuals,
        reasoningTaskDescription: `isConceptSatisfiable(${element})`
      })) {
        // Unsatisfiable element: subsumed by everything, so it lands in the
        // bottom node.
        subsumers = new Set(this.elements);
      } else {
        subsumers = new Set([this.topElement]);
        const canonical = nodesForIndividuals.get(freshIndividual).getCanonicalNode();
        // Every active `(predicate, canonical)` tuple in the binary table.
        for (const entry of binaryTable.retrieve(null, [canonical])) {
          const subsumer = entry.tuple[0];
          if (this.elements.has(subsumer)) subsumers.add(subsumer);
        }
      }
      allSubsumers.set(element, new GraphNode(element, subsumers));
      if (this.progressMonitor) this.progressMonitor.elementClassified(element);
    }
    return DeterministicClassification.buildHierarchy(
      this.topElement, this.bottomElement, allSubsumers);
  }

  /**
   * Condense a subsumer graph into a hierarchy.
   *
   * Tarjan-style SCC computation (iterative, to avoid blowing the JS stack on
   * large ontologies) followed by transitive-edge pruning: a node keeps an edge
   * to a successor only if that successor is not already reachable through
   * another successor.
   *
   * @template T
   * @param {T} topElement
   * @param {T} bottomElement
   * @param {Map<T, GraphNode<T>>} graphNodes
   * @returns {Hierarchy<T>}
   */
  static buildHierarchy(topElement, bottomElement, graphNodes) {
    const topNode = new HierarchyNode(topElement);
    const bottomNode = new HierarchyNode(bottomElement);
    const hierarchy = new Hierarchy(topNode, bottomNode);

    // ---- SCC + topological order -------------------------------------------
    const topologicalOrder = [];
    const dfsIndex = { value: 0 };
    const bottomGraphNode = graphNodes.get(bottomElement);
    if (bottomGraphNode) {
      DeterministicClassification._visit(
        [], dfsIndex, graphNodes, bottomGraphNode, hierarchy, topologicalOrder);
    }
    // Elements unreachable from the bottom node (should not happen when every
    // element has topElement among its successors, but be safe).
    for (const graphNode of graphNodes.values()) {
      if (graphNode.notVisited()) {
        DeterministicClassification._visit(
          [], dfsIndex, graphNodes, graphNode, hierarchy, topologicalOrder);
      }
    }

    // ---- transitive reduction ----------------------------------------------
    const reachableFrom = new Map();
    const allSuccessors = [];
    for (const node of topologicalOrder) {
      const reachableFromNode = new Set([node]);
      reachableFrom.set(node, reachableFromNode);
      allSuccessors.length = 0;
      for (const element of node.equivalentElements) {
        const graphNode = graphNodes.get(element);
        if (!graphNode) continue;
        for (const successor of graphNode.successors) {
          const successorGraphNode = graphNodes.get(successor);
          if (successorGraphNode) allSuccessors.push(successorGraphNode);
        }
      }
      allSuccessors.sort((a, b) => a.topologicalOrderIndex - b.topologicalOrderIndex);
      // Walk from the most general successor downwards: the first edge to any
      // not-yet-reachable node is a direct one, everything after is redundant.
      for (let i = allSuccessors.length - 1; i >= 0; i--) {
        const successorNode = hierarchy.nodesByElements.get(allSuccessors[i].element);
        if (!successorNode) continue;
        if (!reachableFromNode.has(successorNode)) {
          node.parentNodes.add(successorNode);
          successorNode.childNodes.add(node);
          reachableFromNode.add(successorNode);
          for (const r of reachableFrom.get(successorNode)) reachableFromNode.add(r);
        }
      }
    }
    return hierarchy;
  }

  /**
   * Iterative Tarjan DFS. `stack` is the SCC candidate stack; the call stack is
   * simulated with frames so deep hierarchies do not overflow.
   *
   * @private
   */
  static _visit(stack, dfsIndex, graphNodes, rootGraphNode, hierarchy, topologicalOrder) {
    // frame = { graphNode, successors: [...], i }
    const frames = [];
    const pushFrame = (graphNode) => {
      graphNode.dfsIndex = dfsIndex.value++;
      graphNode.sccHead = graphNode;
      stack.push(graphNode);
      frames.push({ graphNode, successors: [...graphNode.successors], i: 0 });
    };

    pushFrame(rootGraphNode);
    while (frames.length > 0) {
      const frame = frames[frames.length - 1];
      const graphNode = frame.graphNode;
      if (frame.i < frame.successors.length) {
        const successor = frame.successors[frame.i++];
        const successorGraphNode = graphNodes.get(successor);
        if (!successorGraphNode) continue;
        if (successorGraphNode.notVisited()) {
          pushFrame(successorGraphNode);
        } else if (!successorGraphNode.isAssignedToSCC()
          && successorGraphNode.sccHead.dfsIndex < graphNode.sccHead.dfsIndex) {
          graphNode.sccHead = successorGraphNode.sccHead;
        }
        continue;
      }
      frames.pop();
      // Returning into the parent frame: propagate the SCC head upward.
      if (frames.length > 0) {
        const parent = frames[frames.length - 1].graphNode;
        if (!graphNode.isAssignedToSCC()
          && graphNode.sccHead.dfsIndex < parent.sccHead.dfsIndex) {
          parent.sccHead = graphNode.sccHead;
        }
      }
      if (graphNode.sccHead === graphNode) {
        const nextTopologicalOrderIndex = topologicalOrder.length;
        const equivalentElements = new Set();
        let poppedNode;
        do {
          poppedNode = stack.pop();
          poppedNode.topologicalOrderIndex = nextTopologicalOrderIndex;
          equivalentElements.add(poppedNode.element);
        } while (poppedNode !== graphNode);

        let hierarchyNode;
        if (equivalentElements.has(hierarchy.getTopNode().representative)) {
          hierarchyNode = hierarchy.getTopNode();
        } else if (equivalentElements.has(hierarchy.getBottomNode().representative)) {
          hierarchyNode = hierarchy.getBottomNode();
        } else {
          hierarchyNode = new HierarchyNode(graphNode.element);
        }
        for (const element of equivalentElements) {
          hierarchyNode.equivalentElements.add(element);
          hierarchy.nodesByElements.set(element, hierarchyNode);
        }
        topologicalOrder.push(hierarchyNode);
      }
    }
  }
}

module.exports = { DeterministicClassification, GraphNode };
