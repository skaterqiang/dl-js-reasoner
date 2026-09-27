'use strict';
/**
 * Classification for non-deterministic (non-Horn) tableaux.
 *
 * Port of `org.semanticweb.HermiT.hierarchy.QuasiOrderClassification`.
 *
 * When the ontology is not Horn there is no single model to read subsumption
 * off, so each pair has to be tested by a tableau run:
 * `C ⊑ D` iff `C(fresh) ∧ ¬D(fresh)` is unsatisfiable. Doing that for all
 * O(n²) pairs is far too slow, so HermiT maintains two graphs:
 *
 *   - `knownSubsumptions`    — pairs already proven (edges point UPWARD);
 *   - `possibleSubsumptions` — pairs not yet ruled out.
 *
 * A model built for one concept yields information about MANY pairs at once:
 * every concept asserted on an unblocked node is a *possible* subsumer of every
 * concept asserted on that node, and every concept asserted on the root node
 * under an empty dependency set is a *known* subsumer. The "leaf node strategy"
 * walks the hierarchy bottom-up, building one model per leaf, which prunes the
 * possible-subsumer graph very quickly. Only what survives then needs an actual
 * subsumption test.
 */

const { Graph } = require('../graph/Graph');
const { Hierarchy } = require('./Hierarchy');
const { DeterministicClassification, GraphNode } = require('./DeterministicClassification');
const { createAnonymousIndividual } = require('../model/Term');
const { createAtom } = require('../model/Atom');
const { AtomicConcept } = require('../model/DLPredicate');

class QuasiOrderClassification {
  /**
   * @param {object} tableau
   * @param {{elementClassified: (element: *) => void}} progressMonitor
   * @param {AtomicConcept} topElement
   * @param {AtomicConcept} bottomElement
   * @param {Set<AtomicConcept>} elements  must include top and bottom
   */
  constructor(tableau, progressMonitor, topElement, bottomElement, elements) {
    this.tableau = tableau;
    this.progressMonitor = progressMonitor || { elementClassified() {} };
    this.topElement = topElement;
    this.bottomElement = bottomElement;
    this.elements = elements;
    this.knownSubsumptions = new Graph();
    this.possibleSubsumptions = new Graph();
  }

  /** @returns {Hierarchy<AtomicConcept>} */
  classify() {
    const self = this;
    const relation = {
      doesSubsume(parent, child) {
        if (self.getAllKnownSubsumers(child).has(parent)) return true;
        if (!self.possibleSubsumptions.getSuccessors(child).has(parent)) return false;

        const freshIndividual = createAnonymousIndividual('fresh-individual');
        const nodesForIndividuals = new Map([[freshIndividual, null]]);
        const isSubsumedBy = !self.tableau.isSatisfiable({
          loadPermanentABox: true,
          perTestPositiveFactsNoDependency: [createAtom(child, freshIndividual)],
          perTestNegativeFactsDummyDependency: [createAtom(parent, freshIndividual)],
          nodesForIndividuals,
          reasoningTaskDescription: self.getSubsumptionTestDescription(child, parent)
        });
        if (!isSubsumedBy) self.prunePossibleSubsumers();
        self.readKnownSubsumersFromRootNode(child, nodesForIndividuals.get(freshIndividual));
        const known = self.getAllKnownSubsumers(child);
        const possible = self.possibleSubsumptions.mutableSuccessors(child);
        for (const k of known) possible.delete(k);
        return isSubsumedBy;
      }
    };
    return this.buildHierarchy(relation);
  }

  /**
   * The main driver: seed the graphs, run the leaf-node strategy, then resolve
   * whatever is still unknown with enhanced traversal.
   *
   * @param {{doesSubsume: (parent: *, child: *) => boolean}} hierarchyRelation
   * @returns {Hierarchy}
   */
  buildHierarchy(hierarchyRelation) {
    const totalNumberOfTasks = this.elements.size;
    this.makeConceptUnsatisfiable(this.bottomElement);
    this.initialiseKnownSubsumptionsUsingToldSubsumers();
    let tasksPerformed = this.updateSubsumptionsUsingLeafNodeStrategy(totalNumberOfTasks);

    // Unlike Shearer's paper, `possibleSubsumptions` holds only the STILL
    // UNKNOWN candidates, so known subsumers are subtracted here.
    const unclassifiedElements = new Set();
    for (const element of this.elements) {
      if (!this.isUnsatisfiable(element)) {
        const possible = this.possibleSubsumptions.mutableSuccessors(element);
        for (const k of this.getAllKnownSubsumers(element)) possible.delete(k);
        if (possible.size > 0) unclassifiedElements.add(element);
      }
    }

    const classifiedElements = new Set();
    while (unclassifiedElements.size > 0) {
      let unclassifiedElement = null;
      for (const element of unclassifiedElements) {
        const possible = this.possibleSubsumptions.mutableSuccessors(element);
        for (const k of this.getAllKnownSubsumers(element)) possible.delete(k);
        if (possible.size > 0) {
          unclassifiedElement = element;
          break;
        }
        classifiedElements.add(element);
        while (unclassifiedElements.size < (totalNumberOfTasks - tasksPerformed)) {
          this.progressMonitor.elementClassified(element);
          tasksPerformed++;
        }
      }
      for (const e of classifiedElements) unclassifiedElements.delete(e);
      if (unclassifiedElements.size === 0) break;

      const unknownPossibleSubsumers =
        this.possibleSubsumptions.mutableSuccessors(unclassifiedElement);
      if (!this.isEveryPossibleSubsumerNonSubsumer(unknownPossibleSubsumers, unclassifiedElement, 2, 7)
        && unknownPossibleSubsumers.size > 0) {
        const smallHierarchy = this.buildHierarchyOfUnknownPossible(unknownPossibleSubsumers);
        this.checkUnknownSubsumersUsingEnhancedTraversal(
          hierarchyRelation, smallHierarchy.getTopNode(), unclassifiedElement);
      }
      unknownPossibleSubsumers.clear();
    }
    return this.buildTransitivelyReducedHierarchy(this.knownSubsumptions, this.elements);
  }

  /**
   * A throw-away hierarchy over just the unknown candidates, used to order the
   * enhanced traversal so that few subsumption tests are needed.
   */
  buildHierarchyOfUnknownPossible(unknownSubsumers) {
    const smallKnownSubsumptions = new Graph();
    for (const unknownSubsumer0 of unknownSubsumers) {
      smallKnownSubsumptions.addEdge(this.bottomElement, unknownSubsumer0);
      smallKnownSubsumptions.addEdge(unknownSubsumer0, this.topElement);
      const knownSubsumersOfElement = this.getAllKnownSubsumers(unknownSubsumer0);
      for (const unknownSubsumer1 of unknownSubsumers) {
        if (knownSubsumersOfElement.has(unknownSubsumer1)) {
          smallKnownSubsumptions.addEdge(unknownSubsumer0, unknownSubsumer1);
        }
      }
    }
    const withTopBottom = new Set(unknownSubsumers);
    withTopBottom.add(this.bottomElement);
    withTopBottom.add(this.topElement);
    return this.buildTransitivelyReducedHierarchy(smallKnownSubsumptions, withTopBottom);
  }

  /**
   * The leaf-node strategy: build a model for each concept, starting from the
   * ones closest to the bottom of the current (partial) hierarchy, and harvest
   * known + possible subsumptions from it.
   *
   * @param {number} totalNumberOfTasks
   * @returns {number} how many progress ticks were consumed
   */
  updateSubsumptionsUsingLeafNodeStrategy(totalNumberOfTasks) {
    let conceptsProcessed = 0;
    const hierarchy = this.buildTransitivelyReducedHierarchy(
      this.knownSubsumptions, this.elements);
    const toProcess = [...hierarchy.getBottomNode().getParentNodes()];
    const unsatHierarchyNodes = new Set();

    while (toProcess.length > 0) {
      const currentHierarchyElement = toProcess.pop();
      const currentHierarchyConcept = currentHierarchyElement.getRepresentative();
      if (conceptsProcessed < Math.ceil(totalNumberOfTasks * 0.85)) {
        this.progressMonitor.elementClassified(currentHierarchyConcept);
        conceptsProcessed++;
      }
      if (this.conceptHasBeenProcessedAlready(currentHierarchyConcept)) continue;

      const rootNodeOfModel = this.buildModelForConcept(currentHierarchyConcept);
      if (rootNodeOfModel === null) {
        // Unsatisfiable leaf: propagate upward (explore the parents) and
        // downward (everything below an unsatisfiable concept is unsatisfiable).
        this.makeConceptUnsatisfiable(currentHierarchyConcept);
        unsatHierarchyNodes.add(currentHierarchyElement);
        for (const p of currentHierarchyElement.getParentNodes()) toProcess.push(p);

        const visited = new Set();
        const toVisit = [...currentHierarchyElement.getChildNodes()];
        while (toVisit.length > 0) {
          const current = toVisit.shift();
          if (!visited.has(current) && !unsatHierarchyNodes.has(current)) {
            visited.add(current);
            for (const c of current.getChildNodes()) toVisit.push(c);
            unsatHierarchyNodes.add(current);
            this.makeConceptUnsatisfiable(current.getRepresentative());
            const idx = toProcess.indexOf(current);
            if (idx !== -1) toProcess.splice(idx, 1);
            for (const parentOfRemovedConcept of current.getParentNodes()) {
              if (!this.conceptHasBeenProcessedAlready(parentOfRemovedConcept.getRepresentative())) {
                toProcess.push(parentOfRemovedConcept);
              }
            }
          }
        }
      } else {
        // NOTE: no `getCanonicalNode()` here — readKnownSubsumersFromRootNode
        // does that itself, but only when the node was not merged (or the merge
        // was deterministic).
        this.readKnownSubsumersFromRootNode(currentHierarchyConcept, rootNodeOfModel);
        this.updatePossibleSubsumers();
      }
    }
    return conceptsProcessed;
  }

  conceptHasBeenProcessedAlready(atomicConcept) {
    return this.possibleSubsumptions.getSuccessors(atomicConcept).size > 0
      || this.isUnsatisfiable(atomicConcept);
  }

  /**
   * Build a model for `concept` alone (no ABox — a TBox-only run is cheaper and
   * sufficient here).
   *
   * @returns {object|null} the node representing the fresh individual, or null
   *          when the concept is unsatisfiable
   */
  buildModelForConcept(concept) {
    const freshIndividual = createAnonymousIndividual('fresh-individual');
    const nodesForIndividuals = new Map([[freshIndividual, null]]);
    if (this.tableau.isSatisfiable({
      loadPermanentABox: false,
      perTestPositiveFactsNoDependency: [createAtom(concept, freshIndividual)],
      nodesForIndividuals,
      reasoningTaskDescription: this.getSatTestDescription(concept)
    })) {
      return nodesForIndividuals.get(freshIndividual);
    }
    return null;
  }

  makeConceptUnsatisfiable(concept) {
    this.addKnownSubsumption(concept, this.bottomElement);
    this.possibleSubsumptions.mutableSuccessors(concept).clear();
  }

  isUnsatisfiable(concept) {
    return this.knownSubsumptions.getSuccessors(concept).has(this.bottomElement);
  }

  /**
   * Harvest KNOWN subsumers of `subconcept` from a completed model: every
   * atomic concept asserted on the (canonical) root node under an EMPTY
   * dependency set holds in every branch, so the subsumption is proven.
   */
  readKnownSubsumersFromRootNode(subconcept, checkedNode) {
    if (!checkedNode.getCanonicalNodeDependencySet().isEmpty()) return;
    const canonical = checkedNode.getCanonicalNode();
    const binaryTable = this.tableau.getExtensionManager().getExtensionTable(2);
    for (const entry of binaryTable.retrieve(null, [canonical])) {
      const conceptObject = entry.tuple[0];
      if (conceptObject instanceof AtomicConcept
        && entry.dependencySet.isEmpty()
        && this.elements.has(conceptObject)) {
        this.addKnownSubsumption(subconcept, conceptObject);
      }
    }
  }

  /**
   * Harvest POSSIBLE subsumers from every unblocked node of the current model:
   * if `A` and `B` are both asserted on some unblocked node then `A ⊑ B` is not
   * refuted by this model, so `B` stays a candidate subsumer of `A`.
   */
  updatePossibleSubsumers() {
    const binaryTable = this.tableau.getExtensionManager().getExtensionTable(2);
    for (const entry of binaryTable.getAllEntries()) {
      const conceptObject = entry.tuple[0];
      if (!(conceptObject instanceof AtomicConcept)) continue;
      if (!this.elements.has(conceptObject)) continue;
      const node = entry.tuple[1];
      if (!node.isActive() || node.isBlocked()) continue;
      if (this.possibleSubsumptions.getSuccessors(conceptObject).size === 0) {
        this.readPossibleSubsumersFromNodeLabel(conceptObject, node);
      } else {
        this.prunePossibleSubsumersOfConcept(conceptObject, node);
      }
    }
  }

  /** Drop candidates that this model refutes (node lacks the assertion). */
  prunePossibleSubsumers() {
    const binaryTable = this.tableau.getExtensionManager().getExtensionTable(2);
    for (const entry of binaryTable.getAllEntries()) {
      const conceptObject = entry.tuple[0];
      if (!(conceptObject instanceof AtomicConcept)) continue;
      if (!this.elements.has(conceptObject)) continue;
      const node = entry.tuple[1];
      if (!node.isActive() || node.isBlocked()) continue;
      this.prunePossibleSubsumersOfConcept(conceptObject, node);
    }
  }

  prunePossibleSubsumersOfConcept(atomicConcept, node) {
    const extensionManager = this.tableau.getExtensionManager();
    const possible = this.possibleSubsumptions.mutableSuccessors(atomicConcept);
    for (const candidate of [...possible]) {
      if (!extensionManager.containsConceptAssertion(candidate, node)) possible.delete(candidate);
    }
  }

  readPossibleSubsumersFromNodeLabel(atomicConcept, node) {
    const binaryTable = this.tableau.getExtensionManager().getExtensionTable(2);
    for (const entry of binaryTable.retrieve(null, [node])) {
      const concept = entry.tuple[0];
      if (concept instanceof AtomicConcept && this.elements.has(concept)) {
        this.addPossibleSubsumption(atomicConcept, concept);
      }
    }
  }

  /**
   * Condense a known-subsumption graph into a hierarchy.
   *
   * Every element gets `topElement` and itself among its subsumers; the bottom
   * element is subsumed by everything (so it sinks to the bottom node).
   */
  buildTransitivelyReducedHierarchy(knownSubsumptions, elements) {
    const allSubsumers = new Map();
    for (const element of elements) {
      const extendedSubs = new Set(knownSubsumptions.getSuccessors(element));
      extendedSubs.add(this.topElement);
      extendedSubs.add(element);
      allSubsumers.set(element, new GraphNode(element, extendedSubs));
    }
    allSubsumers.set(this.bottomElement, new GraphNode(this.bottomElement, new Set(elements)));
    return DeterministicClassification.buildHierarchy(
      this.topElement, this.bottomElement, allSubsumers);
  }

  /** Seed the known graph from the syntactic `A(X) :- B(X)` clauses. */
  initialiseKnownSubsumptionsUsingToldSubsumers(dlClauses) {
    const clauses = dlClauses || this.tableau.getPermanentDLOntology().dlClauses;
    for (const dlClause of clauses) {
      if (dlClause.getHeadLength() === 1 && dlClause.getBodyLength() === 1) {
        const headPredicate = dlClause.getHeadAtom(0).dlPredicate;
        const bodyPredicate = dlClause.getBodyAtom(0).dlPredicate;
        if (headPredicate instanceof AtomicConcept && bodyPredicate instanceof AtomicConcept) {
          if (this.elements.has(headPredicate) && this.elements.has(bodyPredicate)) {
            this.addKnownSubsumption(bodyPredicate, headPredicate);
          }
        }
      }
    }
  }

  /**
   * Walk down the small hierarchy of unknown candidates, testing subsumption
   * only where it can still make a difference. A positive answer at a node
   * immediately proves it for the whole equivalence class and lets the search
   * descend; a negative answer prunes the entire subtree.
   */
  checkUnknownSubsumersUsingEnhancedTraversal(hierarchyRelation, startNode, pickedElement) {
    const visited = new Set([startNode]);
    const toProcess = [startNode];
    while (toProcess.length > 0) {
      const current = toProcess.shift();
      for (const subordinateElement of [...current.getChildNodes()]) {
        const element = subordinateElement.getRepresentative();
        if (visited.has(subordinateElement)) continue;
        if (hierarchyRelation.doesSubsume(element, pickedElement)) {
          this.addKnownSubsumption(pickedElement, element);
          this.addKnownSubsumptions(pickedElement, subordinateElement.getEquivalentElements());
          if (!visited.has(subordinateElement)) {
            visited.add(subordinateElement);
            toProcess.push(subordinateElement);
          }
        }
        visited.add(subordinateElement);
      }
    }
  }

  /**
   * Batch test: when only a handful of candidates remain, ask in ONE tableau
   * run whether the element is subsumed by their disjunction. If it is not,
   * none of them is a subsumer and no further tests are needed.
   *
   * @returns {boolean} true iff the batch test proved no candidate subsumes
   */
  isEveryPossibleSubsumerNonSubsumer(unknownPossibleSubsumers, pickedElement, lowerBound, upperBound) {
    const size = unknownPossibleSubsumers.size;
    if (size <= lowerBound || size >= upperBound) return false;

    const freshIndividual = createAnonymousIndividual('fresh-individual');
    const subconceptAssertion = createAtom(pickedElement, freshIndividual);
    const superconceptAssertions = [];
    const superconcepts = [];
    for (const unknownSupNode of unknownPossibleSubsumers) {
      const atom = createAtom(unknownSupNode, freshIndividual);
      superconceptAssertions.push(atom);
      superconcepts.push(atom.dlPredicate);
    }
    const nodesForIndividuals = new Map([[freshIndividual, null]]);
    const isSubsumedBy = !this.tableau.isSatisfiable({
      loadPermanentABox: false,
      perTestPositiveFactsNoDependency: [subconceptAssertion],
      perTestNegativeFactsDummyDependency: superconceptAssertions,
      nodesForIndividuals,
      reasoningTaskDescription:
        this.getSubsumedByListTestDescription(pickedElement, superconcepts)
    });
    if (!isSubsumedBy) {
      this.prunePossibleSubsumers();
    } else {
      this.readKnownSubsumersFromRootNode(pickedElement, nodesForIndividuals.get(freshIndividual));
      const possible = this.possibleSubsumptions.mutableSuccessors(pickedElement);
      for (const k of this.getAllKnownSubsumers(pickedElement)) possible.delete(k);
    }
    return !isSubsumedBy;
  }

  getAllKnownSubsumers(child) {
    return this.knownSubsumptions.getReachableSuccessors(child);
  }

  // ---- Reasoning-task descriptions ----------------------------------------
  //
  // These three are split out as methods (rather than inlined template strings)
  // because `QuasiOrderClassificationForRoles` overrides them to describe the
  // tests in terms of the ROLES being classified instead of the internal proxy
  // concepts. That mirrors HermiT, where the same three are `protected` and the
  // role subclass overrides them to return
  // `ReasoningTaskDescription.isRoleSatisfiable(...)` etc.

  /** Description for the `is C satisfiable?` test. */
  getSatTestDescription(atomicConcept) {
    return `isConceptSatisfiable(${atomicConcept})`;
  }

  /** Description for the `is sub ⊑ super?` test. */
  getSubsumptionTestDescription(subConcept, superConcept) {
    return `isConceptSubsumedBy(${subConcept}, ${superConcept})`;
  }

  /** Description for the batched `is sub ⊑ (super₁ ⊔ … ⊔ superₙ)?` test. */
  getSubsumedByListTestDescription(subConcept, superConcepts) {
    return `isConceptSubsumedByList(${subConcept}, [${superConcepts.join(', ')}])`;
  }

  addKnownSubsumption(subConcept, superConcept) {
    this.knownSubsumptions.addEdge(subConcept, superConcept);
  }

  addKnownSubsumptions(subConcept, superConcepts) {
    this.knownSubsumptions.addEdges(subConcept, superConcepts);
  }

  addPossibleSubsumption(subConcept, superConcept) {
    this.possibleSubsumptions.addEdge(subConcept, superConcept);
  }
}

module.exports = { QuasiOrderClassification };
