'use strict';
/**
 * A quasi-order over a set of elements, stored as a DAG of
 * {@link HierarchyNode}s plus a top and a bottom node.
 *
 * Port of `org.semanticweb.HermiT.hierarchy.Hierarchy`.
 *
 * Two elements end up in the same node iff they are mutually subsuming
 * (equivalent). The DAG only keeps *direct* subsumption edges, so
 * `getSuperClasses(x, true)` is a single hop.
 */

const { HierarchyNode } = require('./HierarchyNode');

/**
 * Depth-first visitor contract. Implement `redirect(buffer)` and
 * `visit(level, node, parentNode, firstVisit)`.
 *
 * `redirect` receives a 2-element array `[node, parentNode]` and may overwrite
 * its entries to send the traversal elsewhere; returning `false` prunes the
 * branch. HermiT uses this in `HierarchyPrinterFSS`.
 *
 * @typedef {{
 *   redirect: (buffer: Array) => boolean,
 *   visit: (level: number, node: HierarchyNode, parentNode: HierarchyNode|null, firstVisit: boolean) => void
 * }} HierarchyNodeVisitor
 */

class Hierarchy {
  /**
   * @param {HierarchyNode} topNode
   * @param {HierarchyNode} bottomNode
   */
  constructor(topNode, bottomNode) {
    this.topNode = topNode;
    this.bottomNode = bottomNode;
    /** @type {Map<*, HierarchyNode>} */
    this.nodesByElements = new Map();
    for (const element of topNode.equivalentElements) this.nodesByElements.set(element, topNode);
    for (const element of bottomNode.equivalentElements) this.nodesByElements.set(element, bottomNode);
  }

  getTopNode() { return this.topNode; }
  getBottomNode() { return this.bottomNode; }

  /** True iff the hierarchy holds nothing but top and bottom. */
  isEmpty() {
    return this.nodesByElements.size === 2
      && this.topNode.equivalentElements.size === 1
      && this.bottomNode.equivalentElements.size === 1;
  }

  /** @returns {HierarchyNode|undefined} undefined for an unknown element */
  getNodeForElement(element) { return this.nodesByElements.get(element); }

  /** @returns {Set<HierarchyNode>} every distinct node */
  getAllNodesSet() { return new Set(this.nodesByElements.values()); }

  /** @returns {Set<*>} every element in the hierarchy */
  getAllElements() { return new Set(this.nodesByElements.keys()); }

  /** Longest path from the top node down to the bottom node. */
  getDepth() {
    let depth = 0;
    this.traverseDepthFirst({
      redirect: () => true,
      visit: (level, node) => {
        if (node === this.bottomNode && level > depth) depth = level;
      }
    });
    return depth;
  }

  /**
   * Rebuild this hierarchy with each element mapped through `transformer`.
   *
   * @template T
   * @param {{transform: (e: *) => T, determineRepresentative: (oldRep: *, newEqs: Set<T>) => T}} transformer
   * @param {((a: T, b: T) => number)|null} [comparator]  when given, equivalent
   *        elements / parents / children are kept sorted
   * @returns {Hierarchy<T>}
   */
  transform(transformer, comparator) {
    const newNodeComparator = comparator
      ? (n1, n2) => comparator(n1.representative, n2.representative)
      : null;
    const makeSet = (cmp) => (cmp ? new SortedSet(cmp) : new Set());

    const oldToNew = new Map();
    for (const oldNode of this.nodesByElements.values()) {
      if (oldToNew.has(oldNode)) continue;
      const newEquivalentElements = makeSet(comparator);
      for (const oldElement of oldNode.equivalentElements) {
        newEquivalentElements.add(transformer.transform(oldElement));
      }
      const newRepresentative = transformer.determineRepresentative(
        oldNode.representative, newEquivalentElements);
      oldToNew.set(oldNode, new HierarchyNode(
        newRepresentative,
        newEquivalentElements,
        makeSet(newNodeComparator),
        makeSet(newNodeComparator)));
    }
    for (const oldParentNode of this.nodesByElements.values()) {
      const newParentNode = oldToNew.get(oldParentNode);
      for (const oldChildNode of oldParentNode.childNodes) {
        const newChildNode = oldToNew.get(oldChildNode);
        newParentNode.childNodes.add(newChildNode);
        newChildNode.parentNodes.add(newParentNode);
      }
    }
    const newHierarchy = new Hierarchy(oldToNew.get(this.topNode), oldToNew.get(this.bottomNode));
    for (const newNode of oldToNew.values()) {
      for (const newElement of newNode.equivalentElements) {
        newHierarchy.nodesByElements.set(newElement, newNode);
      }
    }
    return newHierarchy;
  }

  /**
   * Depth-first walk from the top node. `firstVisit` is false when the node has
   * already been seen on another branch (the DAG is not a tree).
   *
   * @param {HierarchyNodeVisitor} visitor
   */
  traverseDepthFirst(visitor) {
    const redirectBuffer = new Array(2);
    const visited = new Set();
    const walk = (level, node, parentNode) => {
      redirectBuffer[0] = node;
      redirectBuffer[1] = parentNode;
      if (!visitor.redirect(redirectBuffer)) return;
      node = redirectBuffer[0];
      parentNode = redirectBuffer[1];
      const firstVisit = !visited.has(node);
      if (firstVisit) visited.add(node);
      visitor.visit(level, node, parentNode, firstVisit);
      if (firstVisit) {
        for (const childNode of [...node.childNodes]) walk(level + 1, childNode, node);
      }
    };
    walk(0, this.topNode, null);
  }

  /**
   * Indented `child -> parent` listing, matching `Hierarchy.toString()`.
   * The bottom node is skipped.
   */
  toString() {
    const lines = [];
    this.traverseDepthFirst({
      redirect: () => true,
      visit: (level, node, parentNode, firstVisit) => {
        if (node === this.bottomNode) return;
        const equivalences = node.getEquivalentElements();
        const printSubClassOf = parentNode !== null;
        const printEquivalences = firstVisit && equivalences.size > 1;
        if (!printSubClassOf && !printEquivalences) return;
        let line = ' '.repeat(4 * level) + String(node.getRepresentative());
        if (printEquivalences) {
          const others = [];
          for (const element of equivalences) {
            if (element !== node.getRepresentative()) others.push(String(element));
          }
          line += `[${others.join(' ')}]`;
        }
        if (printSubClassOf) line += ` -> ${String(parentNode.getRepresentative())}`;
        lines.push(line);
      }
    });
    return lines.join('\n') + (lines.length > 0 ? '\n' : '');
  }

  /**
   * A hierarchy in which every element — including top and bottom — collapses
   * into a single node. This is what an inconsistent ontology classifies to.
   *
   * @template T
   * @param {Iterable<T>} elements
   * @param {T} topElement
   * @param {T} bottomElement
   * @returns {Hierarchy<T>}
   */
  static emptyHierarchy(elements, topElement, bottomElement) {
    const topBottomNode = new HierarchyNode(topElement);
    topBottomNode.equivalentElements.add(topElement);
    topBottomNode.equivalentElements.add(bottomElement);
    for (const element of elements) topBottomNode.equivalentElements.add(element);
    return new Hierarchy(topBottomNode, topBottomNode);
  }

  /**
   * The two-node hierarchy `top -> bottom` with nothing in between.
   *
   * @template T
   * @param {T} topElement
   * @param {T} bottomElement
   * @returns {Hierarchy<T>}
   */
  static trivialHierarchy(topElement, bottomElement) {
    const topNode = new HierarchyNode(topElement);
    const bottomNode = new HierarchyNode(bottomElement);
    topNode.childNodes.add(bottomNode);
    bottomNode.parentNodes.add(topNode);
    return new Hierarchy(topNode, bottomNode);
  }
}

/**
 * Minimal `Set`-shaped wrapper that keeps insertion order sorted by a
 * comparator, so `Hierarchy.transform` can reproduce Java's `TreeSet`.
 *
 * Only the handful of methods the hierarchy code uses is implemented.
 */
class SortedSet {
  constructor(comparator) {
    this.comparator = comparator;
    this._items = [];
  }

  get size() { return this._items.length; }

  /**
   * Java's `TreeSet` decides membership by `compare(...) == 0`, not by
   * identity, so this does the same.
   */
  has(value) { return this._indexOf(value) !== -1; }

  _indexOf(value) {
    const cmp = this.comparator;
    for (let i = 0; i < this._items.length; i++) {
      if (cmp(this._items[i], value) === 0) return i;
    }
    return -1;
  }

  add(value) {
    if (this.has(value)) return this;
    const cmp = this.comparator;
    let i = 0;
    while (i < this._items.length && cmp(this._items[i], value) < 0) i++;
    this._items.splice(i, 0, value);
    return this;
  }

  delete(value) {
    const i = this._indexOf(value);
    if (i === -1) return false;
    this._items.splice(i, 1);
    return true;
  }

  clear() { this._items.length = 0; }

  [Symbol.iterator]() { return this._items[Symbol.iterator](); }

  forEach(fn, thisArg) { this._items.forEach(fn, thisArg); }

  /** @returns {Set} a plain copy (used where a real Set is required) */
  toSet() { return new Set(this._items); }
}

module.exports = { Hierarchy, HierarchyNode, SortedSet };
