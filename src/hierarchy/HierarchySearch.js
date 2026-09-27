'use strict';
/**
 * Locating a new element inside an existing {@link Hierarchy}.
 *
 * Port of `org.semanticweb.HermiT.hierarchy.HierarchySearch`.
 *
 * The algorithm is a two-phase search:
 *   1. walk DOWN from the top node collecting the most specific nodes that
 *      subsume `element`  → `parentNodes`;
 *   2. walk UP from the bottom node (restricted to descendants of
 *      `parentNodes`) collecting the most general nodes subsumed by `element`
 *      → `childNodes`.
 * If both phases agree, `element` belongs to that existing node; otherwise a
 * fresh node is created and spliced in between.
 */

const { HierarchyNode } = require('./HierarchyNode');

/**
 * @typedef {{ doesSubsume: (parent: *, child: *) => boolean }} Relation
 * @typedef {{
 *   getSuccessorElements: (u: *) => Iterable<*>,
 *   getPredecessorElements: (u: *) => Iterable<*>,
 *   trueOf: (u: *) => boolean
 * }} SearchPredicate
 */

/**
 * Memoising wrapper around a {@link SearchPredicate}.
 *
 * `trueOf` is monotone along the predecessor direction: if any predecessor is
 * false, the element is false. Caching avoids re-running (expensive) tableau
 * subsumption tests on the same node.
 */
class SearchCache {
  /**
   * @param {SearchPredicate} searchPredicate
   * @param {Set<*>|null} possibilities  when non-null, anything outside is false
   */
  constructor(searchPredicate, possibilities) {
    this.searchPredicate = searchPredicate;
    this.possibilities = possibilities || null;
    this.positives = new Set();
    this.negatives = new Set();
  }

  trueOf(element) {
    if (this.positives.has(element)) return true;
    if (this.negatives.has(element)) return false;
    if (this.possibilities !== null && !this.possibilities.has(element)) return false;
    for (const superordinateElement of this.searchPredicate.getPredecessorElements(element)) {
      if (!this.trueOf(superordinateElement)) {
        this.negatives.add(element);
        return false;
      }
    }
    if (this.searchPredicate.trueOf(element)) {
      this.positives.add(element);
      return true;
    }
    this.negatives.add(element);
    return false;
  }
}

/**
 * Collect the maximal elements of `startSearch`'s successor-closure that
 * satisfy `searchPredicate.trueOf`.
 *
 * @param {SearchPredicate} searchPredicate
 * @param {Iterable<*>} startSearch
 * @param {Set<*>|null} possibilities
 * @returns {Set<*>}
 */
function search(searchPredicate, startSearch, possibilities) {
  const cache = new SearchCache(searchPredicate, possibilities);
  const result = new Set();
  const visited = new Set(startSearch);
  const toProcess = [...startSearch];
  while (toProcess.length > 0) {
    const current = toProcess.shift();
    let foundSubordinateElement = false;
    for (const subordinateElement of searchPredicate.getSuccessorElements(current)) {
      if (cache.trueOf(subordinateElement)) {
        foundSubordinateElement = true;
        if (!visited.has(subordinateElement)) {
          visited.add(subordinateElement);
          toProcess.push(subordinateElement);
        }
      }
    }
    if (!foundSubordinateElement) result.add(current);
  }
  return result;
}

/**
 * The nodes directly above where `element` belongs: the most specific existing
 * nodes that subsume it.
 *
 * @param {Relation} hierarchyRelation
 * @param {*} element
 * @param {HierarchyNode} topNode
 * @returns {Set<HierarchyNode>}
 */
function findParents(hierarchyRelation, element, topNode) {
  return search({
    getSuccessorElements: (u) => u.childNodes,
    getPredecessorElements: (u) => u.parentNodes,
    trueOf: (u) => hierarchyRelation.doesSubsume(u.getRepresentative(), element)
  }, [topNode], null);
}

/**
 * The nodes directly below where `element` belongs: the most general existing
 * nodes it subsumes, restricted to the part of the hierarchy under
 * `parentNodes`.
 *
 * @param {Relation} hierarchyRelation
 * @param {*} element
 * @param {HierarchyNode} bottomNode
 * @param {Set<HierarchyNode>} parentNodes
 * @returns {Set<HierarchyNode>}
 */
function findChildren(hierarchyRelation, element, bottomNode, parentNodes) {
  const parents = [...parentNodes];
  // `element` is equivalent to its single parent: no new node is needed.
  if (parents.length === 1
    && hierarchyRelation.doesSubsume(element, parents[0].getRepresentative())) {
    return parentNodes;
  }

  // Intersect the descendant sets of all parents. HermiT does this by marking:
  // start from the first parent's descendants, then for each further parent
  // keep only the marked nodes reachable from it (plus everything below those).
  let marked = parents[0].getDescendantNodes();
  for (let i = 1; i < parents.length; i++) {
    const freshlyMarked = new Set();
    const visited = new Set();
    const toProcess = [parents[i]];
    while (toProcess.length > 0) {
      const currentNode = toProcess.shift();
      for (const childNode of currentNode.childNodes) {
        if (marked.has(childNode)) freshlyMarked.add(childNode);
        else if (!visited.has(childNode)) {
          visited.add(childNode);
          toProcess.push(childNode);
        }
      }
    }
    for (const node of freshlyMarked) toProcess.push(node);
    while (toProcess.length > 0) {
      const currentNode = toProcess.shift();
      for (const childNode of currentNode.childNodes) {
        if (!freshlyMarked.has(childNode)) {
          freshlyMarked.add(childNode);
          toProcess.push(childNode);
        }
      }
    }
    marked = freshlyMarked;
  }

  // Of the marked nodes, keep those directly above the bottom node that
  // `element` subsumes.
  const aboveBottomNodes = new Set();
  for (const node of marked) {
    if (node.childNodes.has(bottomNode)
      && hierarchyRelation.doesSubsume(element, node.getRepresentative())) {
      aboveBottomNodes.add(node);
    }
  }
  if (aboveBottomNodes.size === 0) return new Set([bottomNode]);

  return search({
    getSuccessorElements: (u) => u.parentNodes,
    getPredecessorElements: (u) => u.childNodes,
    trueOf: (u) => hierarchyRelation.doesSubsume(element, u.getRepresentative())
  }, aboveBottomNodes, marked);
}

/**
 * Find (or create) the node `element` belongs to.
 *
 * The returned node is NOT yet linked into the hierarchy — the caller
 * (`QuasiOrderClassification`, `DeterministicClassification`) does that.
 *
 * @template E
 * @param {Relation<E>} hierarchyRelation
 * @param {E} element
 * @param {HierarchyNode<E>} topNode
 * @param {HierarchyNode<E>} bottomNode
 * @returns {HierarchyNode<E>}
 */
function findPosition(hierarchyRelation, element, topNode, bottomNode) {
  const parentNodes = findParents(hierarchyRelation, element, topNode);
  const childNodes = findChildren(hierarchyRelation, element, bottomNode, parentNodes);
  if (parentNodes.size === childNodes.size
    && [...parentNodes].every((n) => childNodes.has(n))) {
    return [...parentNodes][0];
  }
  return new HierarchyNode(element, new Set([element]), parentNodes, childNodes);
}

module.exports = {
  findPosition,
  findParents,
  findChildren,
  search,
  SearchCache
};
