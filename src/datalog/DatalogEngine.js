'use strict';

// ---------------------------------------------------------------------------
// datalog/DatalogEngine.js — ABox materialisation for conjunctive query
// answering.
//
// Mirrors org.semanticweb.HermiT.datalog.DatalogEngine.
//
// === Why a separate engine? ==================================================
//
// The hypertableau calculus answers *entailment* questions: it tries to build a
// model of `ontology ∧ ¬query` and reports whether that is possible. It never
// enumerates what is true — it stops at the first model. Conjunctive query
// answering needs the opposite: the complete set of ground facts, so that a
// query can be matched against them.
//
// `materialize()` therefore runs the calculus with an expansion strategy that
// NEVER creates nodes (`NullExistentialExpansionStrategy`). Existential
// expansion is what makes the forest potentially infinite; without it the
// calculus saturates the given individuals under the DL-clauses and stops. The
// result is the "materialised ABox": every ground consequence that mentions
// only the individuals already present.
//
// This is exactly HermiT's approach, and it carries the same restriction: the
// ontology must be Horn. A disjunctive head would need branching, and a
// materialised ABox cannot represent "one of these two holds" — so the
// constructor rejects any clause with more than one head atom.
//
// === What is NOT complete ====================================================
//
// Because existentials are never expanded, a query cannot see witnesses that
// would only exist in an infinite model. `∃R.A(a)` with no ground `R(a,b)`
// asserts that some R-successor of `a` is an A, but materialisation never
// invents it, so `R(X,Y)` returns nothing for it. This is inherent to ABox
// materialisation (HermiT behaves identically), not a bug in this port.
// ---------------------------------------------------------------------------

const { Tableau, InterruptFlag } = require('../tableau/Tableau');

// ===========================================================================
// NullExistentialExpansionStrategy
// ===========================================================================

/**
 * An expansion strategy that never expands anything.
 *
 * Mirrors DatalogEngine.NullExistentialExpansionStrategy. Every callback the
 * Tableau invokes on its strategy is a no-op; `expandExistentials` always
 * returns `false` ("nothing changed"), which is what makes the saturation loop
 * terminate on a finite ABox.
 *
 * Deliberately STATELESS — no field is written by any method — so a single
 * shared instance can serve every engine, exactly as HermiT's `INSTANCE` does.
 */
class NullExistentialExpansionStrategy {
  initialize(_tableau) { /* no blocking strategy to initialise */ }
  additionalDLOntologySet(_additionalDLOntology) {}
  additionalDLOntologyCleared() {}
  clear() {}

  /** The whole point: never expand, so the loop sees "no more work". */
  expandExistentials(_finalChance) { return false; }

  // ---- assertion notifications -------------------------------------------
  assertionAddedConcept(_concept, _node) {}
  assertionAddedRole(_role, _from, _to) {}
  assertionRemovedConcept(_concept, _node) {}
  assertionRemovedRole(_role, _from, _to) {}
  assertionCoreSet() {}

  // ---- node lifecycle -----------------------------------------------------
  nodesMerged(_mergeFrom, _mergeInto) {}
  nodesUnmerged(_mergeFrom, _mergeInto) {}
  nodeStatusChanged(_node) {}
  nodeInitialized(_node) {}
  nodeDestroyed(_node) {}

  // ---- branching ----------------------------------------------------------
  branchingPointPushed() {}
  backtrack() {}
  modelFound() {}

  /**
   * Both flags are `true`, matching HermiT.
   *
   * `isExact() === true` matters: `Tableau.runCalculus` only grants the
   * expansion strategy a "final chance" pass when the strategy is inexact. With
   * an exact strategy that pass is skipped, so the loop ends as soon as rule
   * saturation stops producing new tuples.
   */
  isDeterministic() { return true; }
  isExact() { return true; }
}

/** Shared instance (stateless, so sharing is safe). Mirrors `INSTANCE`. */
const NULL_EXPANSION_STRATEGY = new NullExistentialExpansionStrategy();

// ===========================================================================
// DatalogEngine
// ===========================================================================

class DatalogEngine {
  /**
   * @param {DLOntology} dlOntology a CLAUSIFIED ontology — `reasoner.getDLOntology()`.
   * @throws {Error} if any DL-clause has a disjunctive head (not Horn).
   */
  constructor(dlOntology) {
    if (!dlOntology || !Array.isArray(dlOntology.dlClauses)) {
      throw new Error('DatalogEngine requires a clausified DLOntology '
        + '(reasoner.getDLOntology()).');
    }
    for (const dlClause of dlOntology.dlClauses) {
      if (dlClause.getHeadLength() > 1) {
        throw new Error('The supplied DL ontology contains rules with '
          + 'disjunctive heads.');
      }
    }
    this.interruptFlag = new InterruptFlag(0);
    this.dlOntology = dlOntology;

    /** Term → the node created for it (NOT canonicalised). Filled by the run. */
    this.termsToNodes = new Map();
    /** Inverse of `termsToNodes`. */
    this.nodesToTerms = new Map();
    /** Term → the Set of all terms denoting the same individual. */
    this.termsToEquivalenceClasses = new Map();
    /** Term → the chosen representative term of its equivalence class. */
    this.termsToRepresentatives = new Map();

    /** Non-null once `materialize()` has run; also acts as the cache flag. */
    this.extensionManager = null;
    /** The materialised tableau. `ConjunctiveQuery` matches against it. */
    this.tableau = null;
  }

  /** Ask a running materialisation to abort. */
  interrupt() { this.interruptFlag.interrupt(); }

  getDLOntology() { return this.dlOntology; }

  /**
   * Saturate the ABox. Idempotent: the second call returns the cached answer.
   *
   * @returns {boolean} `false` iff the ontology is inconsistent (a clash was
   *   derived), in which case there are no answers to anything.
   */
  materialize() {
    if (this.extensionManager === null) {
      this.termsToNodes.clear();
      this.nodesToTerms.clear();
      this.termsToEquivalenceClasses.clear();
      this.termsToRepresentatives.clear();

      const tableau = new Tableau({
        interruptFlag: this.interruptFlag,
        tableauMonitor: null,
        existentialExpansionStrategy: NULL_EXPANSION_STRATEGY,
        // Disjunction learning is pointless without disjunctions, and the
        // constructor rejects non-Horn ontologies anyway. HermiT passes false.
        useDisjunctionLearning: false,
        // Without this, `owl:Thing` and `rdfs:Literal` tuples are dropped by
        // `ExtensionTable.addTuple` (they are implied of every node, so the
        // tableau calculus never needs them stored). That is fine for
        // entailment but fatal for query answering: `owl:Thing(X)` is the
        // natural way to ask "which individuals are there?" and would return
        // an empty answer set — silently. HermiT has the same trap.
        materialiseTopPredicates: true,
        permanentDLOntology: this.dlOntology,
        additionalDLOntology: null,
        parameters: {}
      });

      // `loadPermanentABox: true` is essential. Tableau's default only loads the
      // ABox when the ontology has nominals, but query answering must see the
      // individuals of EVERY ontology. HermiT passes `true` explicitly too.
      //
      // Passing our own Map as `termsToNodes` is what lets the term↔node
      // correspondence survive the run: Tableau assigns `this.termsToNodes`
      // from the option rather than allocating a fresh map.
      tableau.isSatisfiable({
        loadPermanentABox: true,
        loadAdditionalABox: false,
        termsToNodes: this.termsToNodes
      });

      for (const [term, node] of this.termsToNodes) this.nodesToTerms.set(node, term);

      this.tableau = tableau;
      this.extensionManager = tableau.getExtensionManager();
      this._computeEquivalenceClasses();
    }
    return !this.extensionManager.containsClash();
  }

  /**
   * Group terms by the individual they denote.
   *
   * Walks the whole node chain — merged nodes stay linked (only *destroyed*
   * nodes are unlinked), so every term is visited. A term's representative is
   * the term of its node's canonical node; all terms sharing a canonical node
   * form one equivalence class.
   */
  _computeEquivalenceClasses() {
    let node = this.tableau.firstTableauNode;
    while (node !== null) {
      const term = this.nodesToTerms.get(node);
      // A node that was not created for a term has nothing to record. That is
      // the fallback NI node Tableau creates when the ABox is empty ("ensure at
      // least one individual exists"); it is never merged into, so skipping it
      // cannot lose a class.
      if (term !== undefined) {
        const canonicalNode = node.getCanonicalNode();
        const canonicalTerm = this.nodesToTerms.get(canonicalNode);
        // Defensive: a canonical node with no term would make the representative
        // unnameable. Fall back to the term itself so `getRepresentative` stays
        // total over every known term.
        const representative = canonicalTerm === undefined ? term : canonicalTerm;

        let equivalenceClass = this.termsToEquivalenceClasses.get(representative);
        if (equivalenceClass === undefined) {
          equivalenceClass = new Set();
          this.termsToEquivalenceClasses.set(representative, equivalenceClass);
        }
        // Every non-representative member also maps straight to the class, so
        // `getEquivalenceClass(x)` works for any member, not just the rep.
        if (term !== representative) this.termsToEquivalenceClasses.set(term, equivalenceClass);
        equivalenceClass.add(term);
        this.termsToRepresentatives.set(term, representative);
      }
      node = node.nextTableauNode;
    }
  }

  /**
   * All terms denoting the same individual as `term`, including `term` itself.
   * @returns {Set<Term>|null} null if `term` is unknown to this engine.
   *   The returned Set is a COPY — mutating it cannot corrupt the engine.
   */
  getEquivalenceClass(term) {
    const cls = this.termsToEquivalenceClasses.get(term);
    return cls === undefined ? null : new Set(cls);
  }

  /**
   * The canonical name for `term`'s individual.
   *
   * Query answers are reported in terms of representatives, because after
   * merging the extension tables only hold canonical nodes. Comparing an answer
   * against an expected individual therefore has to go through this map — which
   * is exactly what HermiT's own tests do.
   *
   * @returns {Term|null} null if `term` is unknown to this engine.
   */
  getRepresentative(term) {
    const rep = this.termsToRepresentatives.get(term);
    return rep === undefined ? null : rep;
  }

  /** The term a node denotes, or null. Used to turn bindings into answers. */
  getTermForNode(node) {
    if (node === null || node === undefined) return null;
    const term = this.nodesToTerms.get(node.getCanonicalNode());
    return term === undefined ? null : term;
  }
}

module.exports = {
  DatalogEngine,
  NullExistentialExpansionStrategy,
  NULL_EXPANSION_STRATEGY
};
