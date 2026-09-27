'use strict';
/**
 * A node of a {@link Hierarchy}: one equivalence class of elements together
 * with the nodes directly above and below it.
 *
 * Port of `org.semanticweb.HermiT.hierarchy.HierarchyNode`.
 *
 * Elements are compared by identity (`===`), which is exactly what HermiT gets
 * from `AtomicConcept`/`AtomicRole` interning. Sets are therefore plain JS
 * `Set`s.
 */

/**
 * Breadth-first closure of `inputNodes` under `getSuccessors`.
 *
 * HermiT declares this as a static method on `HierarchyNode`; it is a free
 * function here because JS has no static-generic dispatch worth emulating.
 *
 * @template T
 * @param {Iterable<T>} inputNodes
 * @param {(node: T) => Iterable<T>} getSuccessors
 * @returns {Set<T>} the closure, INCLUDING the input nodes
 */
function transitiveClosure(inputNodes, getSuccessors) {
  const result = new Set();
  const toVisit = [...inputNodes];
  while (toVisit.length > 0) {
    const current = toVisit.shift();
    if (!result.has(current)) {
      result.add(current);
      for (const next of getSuccessors(current)) toVisit.push(next);
    }
  }
  return result;
}

/**
 * @template T
 * @param {Iterable<T>} inputNodes
 * @returns {Set<T>} every ancestor of every input node, plus the inputs
 */
function getAncestorNodes(inputNodes) {
  return transitiveClosure(inputNodes, (n) => n.getParentNodes());
}

/**
 * @template T
 * @param {Iterable<T>} inputNodes
 * @returns {Set<T>} every descendant of every input node, plus the inputs
 */
function getDescendantNodes(inputNodes) {
  return transitiveClosure(inputNodes, (n) => n.getChildNodes());
}

class HierarchyNode {
  /**
   * @param {*} representative
   * @param {Set<*>} [equivalentElements]  defaults to `{representative}`
   * @param {Set<HierarchyNode>} [parentNodes]
   * @param {Set<HierarchyNode>} [childNodes]
   */
  constructor(representative, equivalentElements, parentNodes, childNodes) {
    this.representative = representative;
    this.equivalentElements = equivalentElements || new Set([representative]);
    this.parentNodes = parentNodes || new Set();
    this.childNodes = childNodes || new Set();
  }

  getRepresentative() { return this.representative; }

  /** @returns {Set<*>} the elements this node stands for (read-only by convention) */
  getEquivalentElements() { return this.equivalentElements; }

  /** @returns {Set<HierarchyNode>} */
  getParentNodes() { return this.parentNodes; }

  /** @returns {Set<HierarchyNode>} */
  getChildNodes() { return this.childNodes; }

  isEquivalentElement(element) { return this.equivalentElements.has(element); }

  /**
   * True iff `ancestor` is equivalent to this node or to one of its ancestors.
   *
   * NOTE: `getAncestorNodes()` includes `this`, so — exactly as in HermiT — this
   * also returns true when `ancestor` is equivalent to the node itself. Callers
   * that want a *strict* ancestor test must check `isEquivalentElement` first
   * (see `Reasoner.isSubClassOf`).
   */
  isAncestorElement(ancestor) {
    for (const node of this.getAncestorNodes()) {
      if (node.isEquivalentElement(ancestor)) return true;
    }
    return false;
  }

  /**
   * True iff `descendant` is equivalent to this node or to one of its
   * descendants. Includes the self case, mirroring `isAncestorElement`.
   */
  isDescendantElement(descendant) {
    for (const node of this.getDescendantNodes()) {
      if (node.isEquivalentElement(descendant)) return true;
    }
    return false;
  }

  /** @returns {Set<HierarchyNode>} this node plus all of its ancestors */
  getAncestorNodes() { return getAncestorNodes([this]); }

  /** @returns {Set<HierarchyNode>} this node plus all of its descendants */
  getDescendantNodes() { return getDescendantNodes([this]); }

  toString() {
    return `{${[...this.equivalentElements].join(', ')}}`;
  }
}

module.exports = {
  HierarchyNode,
  getAncestorNodes,
  getDescendantNodes,
  transitiveClosure
};
