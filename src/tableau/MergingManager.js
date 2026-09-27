'use strict';

// ---------------------------------------------------------------------------
// tableau/MergingManager.js — the ≈ rule: identify two nodes.
//
// Mirrors org.semanticweb.HermiT.tableau.MergingManager.
//
// mergeNodes(node0, node1, ds):
//   1. pick the merge direction by node-type precedence
//      (NAMED/ROOT 0 < CONCRETE 1 < TREE 2 — lower merges into higher; ties
//      broken by cluster-anchor proximity, then by label richness);
//   2. prune the subtree hanging off mergeFrom (its descendants die with it);
//   3. copy every active unary/binary assertion mentioning mergeFrom onto
//      mergeInto, unioning the dependency sets (self-loops R(mergeFrom,
//      mergeFrom) become R(mergeInto, mergeInto));
//   4. tableau.mergeNode(mergeFrom, mergeInto, ds) — redirect the node.
//
// Copies go through extensionManager.addTuple, so clash detection and further
// dispatch (e.g. a copied Inequality(n,n)) happen automatically.
// ---------------------------------------------------------------------------

class MergingManager {
  /**
   * @param {Tableau} tableau
   */
  constructor(tableau) {
    this.tableau = tableau;
    this.extensionManager = tableau.extensionManager;
  }

  clear() { /* no state */ }

  /**
   * Merge two nodes (direction chosen automatically).
   * @returns {boolean} true if a merge happened
   */
  mergeNodes(node0, node1, dependencySet) {
    if (!node0.isActive() || !node1.isActive() || node0 === node1) return false;

    let mergeFrom, mergeInto;
    const p0 = node0.getMergePrecedence();
    const p1 = node1.getMergePrecedence();
    if (p0 < p1) {
      mergeFrom = node1; mergeInto = node0;
    } else if (p0 > p1) {
      mergeFrom = node0; mergeInto = node1;
    } else {
      // Same precedence: use cluster anchors to pick a legal direction.
      const anchor0 = node0.getClusterAnchor();
      const anchor1 = node1.getClusterAnchor();
      const canMerge0Into1 = node0.parent === node1.parent
        || isDescendantOfAtMostThreeLevels(node0, anchor1);
      const canMerge1Into0 = node0.parent === node1.parent
        || isDescendantOfAtMostThreeLevels(node1, anchor0);
      if (canMerge0Into1 && canMerge1Into0) {
        if (node0.numberOfPositiveAtomicConcepts > node1.numberOfPositiveAtomicConcepts) {
          mergeFrom = node1; mergeInto = node0;
        } else {
          mergeFrom = node0; mergeInto = node1;
        }
      } else if (canMerge0Into1) {
        mergeFrom = node0; mergeInto = node1;
      } else if (canMerge1Into0) {
        mergeFrom = node1; mergeInto = node0;
      } else {
        throw new Error('Internal error: unsupported merge type.');
      }
    }

    // Prune every active node whose parent chain leads through mergeFrom.
    // (Successors of mergeFrom all come after it in the node list.)
    let node = mergeFrom;
    while (node !== null) {
      if (node.isActive() && node.parent !== null
        && (!node.parent.isActive() || node.parent === mergeFrom)) {
        this.tableau.pruneNode(node);
      }
      node = node.nextTableauNode;
    }

    const em = this.extensionManager;

    // Copy unary assertions [pred, mergeFrom] → [pred, mergeInto].
    for (const e of em.binaryTable.retrieve(null, [mergeFrom])) {
      const ds = e.dependencySet.union(dependencySet);
      em.addTuple([e.tuple[0], mergeInto], ds);
    }

    // Copy ternary assertions with mergeFrom in position 1.
    for (const e of em.ternaryTable.retrieve(null, [mergeFrom, null])) {
      const ds = e.dependencySet.union(dependencySet);
      const arg2 = e.tuple[2] === mergeFrom ? mergeInto : e.tuple[2];
      em.addTuple([e.tuple[0], mergeInto, arg2], ds);
    }

    // Copy ternary assertions with mergeFrom in position 2.
    for (const e of em.ternaryTable.retrieve(null, [null, mergeFrom])) {
      const ds = e.dependencySet.union(dependencySet);
      const arg1 = e.tuple[1] === mergeFrom ? mergeInto : e.tuple[1];
      em.addTuple([e.tuple[0], arg1, mergeInto], ds);
    }

    // Copy quaternary assertions (AnnotatedEquality is never stored, but be
    // defensive for any future 3-argument stored predicates).
    for (const e of em.quaternaryTable.retrieve(null, [mergeFrom, null, null])) {
      const ds = e.dependencySet.union(dependencySet);
      const t = e.tuple;
      em.addTuple([t[0], mergeInto, t[2] === mergeFrom ? mergeInto : t[2], t[3] === mergeFrom ? mergeInto : t[3]], ds);
    }
    for (const e of em.quaternaryTable.retrieve(null, [null, mergeFrom, null])) {
      const ds = e.dependencySet.union(dependencySet);
      const t = e.tuple;
      em.addTuple([t[0], t[1] === mergeFrom ? mergeInto : t[1], mergeInto, t[3] === mergeFrom ? mergeInto : t[3]], ds);
    }
    for (const e of em.quaternaryTable.retrieve(null, [null, null, mergeFrom])) {
      const ds = e.dependencySet.union(dependencySet);
      const t = e.tuple;
      em.addTuple([t[0], t[1] === mergeFrom ? mergeInto : t[1], t[2] === mergeFrom ? mergeInto : t[2], mergeInto], ds);
    }

    // Finally redirect the node itself.
    this.tableau.mergeNode(mergeFrom, mergeInto, dependencySet);
    return true;
  }
}

/** True if `descendant` is at most three parent hops below `ancestor`. */
function isDescendantOfAtMostThreeLevels(descendant, ancestor) {
  if (descendant !== null) {
    const p1 = descendant.parent;
    if (p1 === ancestor) return true;
    if (p1 !== null) {
      const p2 = p1.parent;
      if (p2 === ancestor) return true;
      if (p2 !== null) {
        const p3 = p2.parent;
        if (p3 === ancestor) return true;
      }
    }
  }
  return false;
}

module.exports = { MergingManager, isDescendantOfAtMostThreeLevels };
