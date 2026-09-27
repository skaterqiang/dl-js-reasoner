'use strict';
/**
 * A directed graph over arbitrary elements, used by the classification code to
 * accumulate known / possible subsumptions.
 *
 * Port of `org.semanticweb.HermiT.graph.Graph`.
 *
 * `getSuccessors(node)` returns the LIVE set (not a copy) — HermiT relies on
 * callers mutating it (`removeAll`, `clear`), so this port does too.
 */

const EMPTY = Object.freeze(new Set());

class Graph {
  constructor() {
    /** @type {Set<*>} */
    this.elements = new Set();
    /** @type {Map<*, Set<*>>} */
    this.successorsByNodes = new Map();
  }

  /**
   * @param {*} from
   * @param {*} to
   */
  addEdge(from, to) {
    this._successorsOf(from).add(to);
    this.elements.add(from);
    this.elements.add(to);
  }

  /**
   * @param {*} from
   * @param {Iterable<*>} to
   */
  addEdges(from, to) {
    const successors = this._successorsOf(from);
    for (const t of to) {
      successors.add(t);
      this.elements.add(t);
    }
    this.elements.add(from);
  }

  _successorsOf(from) {
    let s = this.successorsByNodes.get(from);
    if (!s) { s = new Set(); this.successorsByNodes.set(from, s); }
    return s;
  }

  getElements() { return this.elements; }

  /**
   * The direct successors of `node`. Returns the live mutable set, or a shared
   * frozen empty set when the node has none (HermiT returns
   * `Collections.emptySet()`).
   *
   * NOTE: mutating the returned empty set throws — callers that intend to
   * mutate must use {@link mutableSuccessors}.
   */
  getSuccessors(node) {
    return this.successorsByNodes.get(node) || EMPTY;
  }

  /** Like {@link getSuccessors} but always returns a mutable, owned set. */
  mutableSuccessors(node) { return this._successorsOf(node); }

  /** Replace every successor set with its transitive closure. */
  transitivelyClose() {
    for (const reachable of this.successorsByNodes.values()) {
      const toProcess = [...reachable];
      while (toProcess.length > 0) {
        const elementOnPath = toProcess.pop();
        const elementOnPathSuccessors = this.successorsByNodes.get(elementOnPath);
        if (elementOnPathSuccessors) {
          for (const successor of elementOnPathSuccessors) {
            if (!reachable.has(successor)) {
              reachable.add(successor);
              toProcess.push(successor);
            }
          }
        }
      }
    }
  }

  /** @returns {Graph} a copy with every edge reversed */
  getInverse() {
    const result = new Graph();
    for (const [from, successors] of this.successorsByNodes) {
      for (const successor of successors) result.addEdge(successor, from);
    }
    return result;
  }

  /** @returns {Graph} a deep copy */
  clone() {
    const result = new Graph();
    for (const element of this.elements) result.elements.add(element);
    for (const [from, successors] of this.successorsByNodes) {
      for (const successor of successors) result.addEdge(from, successor);
    }
    return result;
  }

  /** Remove `elements` as both nodes and edge endpoints. */
  removeElements(elements) {
    for (const element of elements) {
      this.elements.delete(element);
      this.successorsByNodes.delete(element);
      for (const successors of this.successorsByNodes.values()) successors.delete(element);
    }
  }

  /** True iff `toNode` is reachable from `fromNode` (or they are equal). */
  isReachableSuccessor(fromNode, toNode) {
    if (fromNode === toNode) return true;
    const visited = new Set();
    const toVisit = [fromNode];
    while (toVisit.length > 0) {
      const current = toVisit.shift();
      const successors = this.getSuccessors(current);
      if (successors.has(toNode)) return true;
      if (!visited.has(current)) {
        visited.add(current);
        for (const s of successors) toVisit.push(s);
      }
    }
    return false;
  }

  /**
   * Every node reachable from `fromNode`, INCLUDING `fromNode` itself.
   * @returns {Set<*>}
   */
  getReachableSuccessors(fromNode) {
    const result = new Set();
    const toVisit = [fromNode];
    while (toVisit.length > 0) {
      const current = toVisit.shift();
      if (!result.has(current)) {
        result.add(current);
        for (const s of this.getSuccessors(current)) toVisit.push(s);
      }
    }
    return result;
  }

  toString() {
    const parts = [];
    for (const [from, successors] of this.successorsByNodes) {
      for (const to of successors) parts.push(`${String(from)} -> ${String(to)}`);
    }
    return parts.join('\n');
  }
}

module.exports = { Graph };
