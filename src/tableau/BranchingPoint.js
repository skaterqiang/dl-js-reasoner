'use strict';

// ---------------------------------------------------------------------------
// tableau/BranchingPoint.js — non-deterministic choice points.
//
// Mirrors org.semanticweb.HermiT.tableau.{BranchingPoint,
// DisjunctionBranchingPoint}.
//
// A branching point snapshots everything the Tableau must be able to restore
// when it backjumps:
//   • level                          — the dependency-set level assigned to it
//   • lastTableauNode                — nodes created after this are destroyed
//   • lastMergedOrPrunedNode         — merges/prunes after this are undone
//   • firstGroundDisjunction         — disjunctions created after this die
//   • firstUnprocessedGroundDisjunction — the work-list position is rewound
//
// DisjunctionBranchingPoint additionally remembers which disjuncts of a ground
// disjunction have been tried; startNextChoice() negates the failed ones and
// asserts the next candidate (last candidate ⇒ the branching point level is
// removed from the dependency set, so a clash there backjumps past it).
// ---------------------------------------------------------------------------

const {
  AtomicConcept,
  AnnotatedEquality,
  EQUALITY,
  INEQUALITY
} = require('../model/DLPredicate');

class BranchingPoint {
  /**
   * @param {Tableau} tableau
   */
  constructor(tableau) {
    this.level = tableau.currentBranchingPoint + 1;
    this.lastTableauNode = tableau.lastTableauNode;
    this.lastMergedOrPrunedNode = tableau.lastMergedOrPrunedNode;
    this.firstGroundDisjunction = tableau.firstGroundDisjunction;
    this.firstUnprocessedGroundDisjunction = tableau.firstUnprocessedGroundDisjunction;
  }

  getLevel() { return this.level; }

  /**
   * Called after backtracking to this point with the clash dependency set.
   * Base implementation does nothing (e.g. nominal-introduction points do the
   * work themselves).
   */
  startNextChoice(tableau, clashDependencySet) { /* no-op */ }
}

class DisjunctionBranchingPoint extends BranchingPoint {
  /**
   * @param {Tableau} tableau
   * @param {GroundDisjunction} groundDisjunction
   * @param {number[]} sortedDisjunctIndexes evaluation order of the disjuncts
   */
  constructor(tableau, groundDisjunction, sortedDisjunctIndexes) {
    super(tableau);
    this.groundDisjunction = groundDisjunction;
    this.sortedDisjunctIndexes = sortedDisjunctIndexes;
    // Disjunct 0 was already asserted by the Tableau main loop before this
    // branching point was pushed.
    this.currentIndex = 0;
  }

  startNextChoice(tableau, clashDependencySet) {
    this.currentIndex++;
    const currentDisjunctIndex = this.sortedDisjunctIndexes[this.currentIndex];
    let dependencySet = clashDependencySet;
    // Last choice: a clash here must backjump past this branching point.
    if (this.currentIndex + 1 === this.groundDisjunction.getNumberOfDisjuncts()) {
      dependencySet = tableau.dependencySetFactory.removeBranchingPoint(dependencySet, this.level);
    }
    // Negate every previously tried disjunct.
    for (let previousIndex = 0; previousIndex < this.currentIndex; previousIndex++) {
      const previousDisjunctIndex = this.sortedDisjunctIndexes[previousIndex];
      const dlPredicate = this.groundDisjunction.getDLPredicate(previousDisjunctIndex);
      if (dlPredicate === EQUALITY || dlPredicate instanceof AnnotatedEquality) {
        tableau.extensionManager.addAssertion(
          INEQUALITY,
          this.groundDisjunction.getArgument(previousDisjunctIndex, 0),
          this.groundDisjunction.getArgument(previousDisjunctIndex, 1),
          dependencySet);
      } else if (dlPredicate instanceof AtomicConcept) {
        tableau.extensionManager.addConceptAssertion(
          dlPredicate.getNegation(),
          this.groundDisjunction.getArgument(previousDisjunctIndex, 0),
          dependencySet);
      }
    }
    this.groundDisjunction.addDisjunctToTableau(tableau, currentDisjunctIndex, dependencySet);
  }
}

module.exports = { BranchingPoint, DisjunctionBranchingPoint };
