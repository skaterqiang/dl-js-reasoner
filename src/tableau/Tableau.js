'use strict';

// ---------------------------------------------------------------------------
// tableau/Tableau.js — the hypertableau calculus engine.
//
// A faithful JavaScript port of org.semanticweb.HermiT.tableau.Tableau.
//
// The engine owns:
//   • the node forest (intrusive doubly-linked list + a free-node pool),
//   • the extension tables (via ExtensionManager),
//   • the stack of branching points (dependency-directed backjumping),
//   • the list of ground disjunctions still to be branched on,
//   • the managers: hyperresolution, merging, existential expansion, nominal
//     introduction, datatypes, blocking + existential-expansion strategy.
//
// The main loop (runCalculus / doIteration) is HermiT's verbatim:
//
//   repeat
//     1. process queued annotated equalities (NN/NI rules)
//     2. saturate: while the delta-new window is non-empty and there is no
//        clash, rotate the windows and fire
//           hyperresolution → unknown-datatype semantics → datatype constraint
//           checking → annotated equalities
//     3. expand existentials (∃-rule, with blocking)
//     4. branch on the first unsatisfied ground disjunction
//     5. on a clash, backjump to the highest branching point in the clash's
//        dependency set and try the next choice there
//   until nothing changed
//
// Steps 2–5 are mutually exclusive within one iteration, exactly as in HermiT:
// each returns as soon as it did something so the loop restarts from step 1.
// ---------------------------------------------------------------------------

const { DependencySetFactory } = require('./DependencySetFactory');
const { PERMANENT } = require('./DependencySet');
const { Node, NODE_TYPE, nextNodeID } = require('./Node');
const { ExtensionManager } = require('./ExtensionManager');
const { HyperresolutionManager } = require('./HyperresolutionManager');
const { MergingManager } = require('./MergingManager');
const { ExistentialExpansionManager } = require('./ExistentialExpansionManager');
const { NominalIntroductionManager } = require('./NominalIntroductionManager');
const { DatatypeManager } = require('./DatatypeManager');
const { BranchingPoint, DisjunctionBranchingPoint } = require('./BranchingPoint');
const { IndividualReuseStrategy } = require('./ExpansionStrategy');
const { createBlockingStrategy } = require('./BlockingStrategy');

const {
  AtomicConcept,
  AtomicNegationConcept,
  AtLeastConcept,
  AtLeastDataRange,
  LiteralDataRange,
  AtomicNegationDataRange,
  DatatypeRestriction,
  InternalDatatype,
  ConstantEnumeration,
  AtomicRole,
  NegatedAtomicRole,
  Equality,
  Inequality,
  THING,
  INTERNAL_NAMED,
  RDFS_LITERAL,
  BOTTOM_OBJECT_ROLE,
  EQUALITY,
  INEQUALITY,
  internNegatedAtomicRole,
  internConstantEnumeration
} = require('../model/DLPredicate');
const { Individual, Constant } = require('../model/Term');
const { createAtom } = require('../model/Atom');
const { isInternalIRI } = require('../model/DLOntology');

// ===========================================================================
// Interrupt handling
// ===========================================================================

/** Thrown by InterruptFlag.checkInterrupt when a run is cancelled/times out. */
class InterruptedException extends Error {
  constructor(message) {
    super(message || 'Reasoning task interrupted.');
    this.name = 'InterruptedException';
  }
}

/**
 * Mirrors org.semanticweb.HermiT.InterruptFlag. Long loops call checkInterrupt()
 * periodically; an external caller may cancel via interrupt(). An optional
 * timeLimitMs turns wall-clock overrun into an interrupt.
 */
class InterruptFlag {
  constructor(timeLimitMs = 0) {
    this.timeLimitMs = timeLimitMs || 0;
    this._interrupted = false;
    this._depth = 0;
    this._startTime = 0;
  }
  startTask() {
    this._depth++;
    if (this._depth === 1) this._startTime = Date.now();
    this.checkInterrupt();
  }
  endTask() { if (this._depth > 0) this._depth--; }
  interrupt() { this._interrupted = true; }
  clearInterrupt() { this._interrupted = false; }
  isSet() { return this._interrupted; }
  checkInterrupt() {
    if (this._interrupted) {
      this._interrupted = false;
      throw new InterruptedException();
    }
    if (this.timeLimitMs > 0 && this._depth > 0
      && Date.now() - this._startTime > this.timeLimitMs) {
      throw new InterruptedException('Reasoning task exceeded the time limit.');
    }
  }
}

// ===========================================================================
// Predicate classification helpers
// ===========================================================================

/**
 * HermiT's `Concept`: the unary predicates asserted on *abstract* nodes.
 * (Data ranges are a separate hierarchy and get no node-counter bookkeeping.)
 */
function isConceptPredicate(p) {
  return p instanceof AtomicConcept
    || p instanceof AtomicNegationConcept
    || p instanceof AtLeastConcept
    || p instanceof AtLeastDataRange;
}

/** HermiT's `ExistentialConcept`: restrictions that drive ∃-expansion. */
function isExistentialConcept(p) {
  return p instanceof AtLeastConcept || p instanceof AtLeastDataRange;
}

/** HermiT's `DataRange` hierarchy: unary predicates asserted on concrete nodes. */
function isLiteralDataRangePredicate(p) {
  return p instanceof LiteralDataRange
    || p instanceof AtomicNegationDataRange
    || p instanceof DatatypeRestriction
    || p instanceof InternalDatatype
    || p instanceof ConstantEnumeration;
}

/** HermiT's `LiteralConcept`: anything assertable as a ground unary fact. */
function isLiteralConcept(p) {
  return isConceptPredicate(p) || isLiteralDataRangePredicate(p);
}

// ===========================================================================
// Tableau
// ===========================================================================

class Tableau {
  /**
   * @param {object} opts
   * @param {DLOntology} opts.permanentDLOntology  the TBox+RBox (+ABox if it has nominals)
   * @param {DLOntology} [opts.additionalDLOntology] extra clauses loaded per test
   * @param {object} [opts.interruptFlag]
   * @param {object} [opts.tableauMonitor]  optional observer (see TableauMonitor below)
   * @param {object} [opts.existentialExpansionStrategy]
   * @param {boolean} [opts.useDisjunctionLearning]
   * @param {boolean} [opts.materialiseTopPredicates]  store `owl:Thing` /
   *   `rdfs:Literal` tuples even when no DL-clause consumes them. Required by
   *   conjunctive query answering; see `updateFlagsDependentOnAdditionalOntology`.
   * @param {object} [opts.parameters]
   */
  constructor(opts) {
    const options = opts || {};
    this.interruptFlag = options.interruptFlag || new InterruptFlag(options.timeLimitMs);
    this.tableauMonitor = options.tableauMonitor || null;
    this.parameters = options.parameters || {};
    this.useDisjunctionLearning = options.useDisjunctionLearning !== false;
    // Read before `updateFlagsDependentOnAdditionalOntology()` runs below.
    this.materialiseTopPredicates = options.materialiseTopPredicates === true;

    this.permanentDLOntology = options.permanentDLOntology;
    if (!this.permanentDLOntology) throw new Error('Tableau requires a permanentDLOntology.');
    this.additionalDLOntology = options.additionalDLOntology || null;

    this.interruptFlag.startTask();
    try {
      // ---- managers (construction order matters: each reads fields off `this`)
      this.dependencySetFactory = new DependencySetFactory();
      this.extensionManager = new ExtensionManager(this);

      // Extension flags must exist before any tuple is added.
      this.needsThingExtension = false;
      this.needsNamedExtension = false;
      this.needsRDFSLiteralExtension = false;
      this.checkDatatypes = false;
      this.checkUnknownDatatypeRestrictions = false;

      this.permanentHyperresolutionManager =
        new HyperresolutionManager(this, this.permanentDLOntology.dlClauses);
      this.additionalHyperresolutionManager = this.additionalDLOntology
        ? new HyperresolutionManager(this, this.additionalDLOntology.dlClauses)
        : null;

      this.mergingManager = new MergingManager(this);
      this.existentialExpansionManager = new ExistentialExpansionManager(this);
      // HermiT computes the functional-role index in the manager's constructor;
      // this port takes the ontology explicitly so it must be triggered here.
      this.existentialExpansionManager.updateFunctionalRoles(this.permanentDLOntology);
      this.nominalIntroduction = new NominalIntroductionManager(this);
      this.datatypeManager = new DatatypeManager(this);
      // HermiT's DatatypeManager constructor seeds the permanent restrictions
      // and then, if an additional ontology is already attached, calls
      // `additionalDLOntologySet(...)`. Without the second step a tableau built
      // directly with an additional ontology (Reasoner.getTableau falling back
      // to createTableau) would never apply unknown-datatype-restriction
      // semantics to the delta axioms — which is exactly where
      // `internal:unknown-datatype#A` lives during data-property classification.
      this.datatypeManager.setUnknownDatatypeRestrictions(
        this._mergedUnknownDatatypeRestrictions());

      // Description graphs are not produced by this port's clausifier.
      this.hasDescriptionGraphs = false;

      // ---- existential expansion strategy ---------------------------------
      // `Reasoner.createTableau` always supplies an explicit strategy, so this
      // fallback only runs for a directly constructed Tableau. When the caller
      // passes `options.configuration` its blocking options are honoured; with
      // no configuration the defaults resolve to anywhere blocking plus the
      // direct checker implied by `hasInverseRoles`.
      this.existentialExpansionStrategy = options.existentialExpansionStrategy
        || new IndividualReuseStrategy(
          createBlockingStrategy(
            options.configuration || null,
            this.permanentDLOntology.hasInverseRoles,
            this.permanentDLOntology.hasNominals),
          this.isDeterministic());
      this.existentialExpansionStrategy.initialize(this);

      // ---- node forest -----------------------------------------------------
      this.allocatedNodes = 0;
      this.numberOfNodesInTableau = 0;
      this.numberOfMergedOrPrunedNodes = 0;
      this.numberOfNodeCreations = 0;
      this.firstFreeNode = null;
      this.firstTableauNode = null;
      this.lastTableauNode = null;
      this.lastMergedOrPrunedNode = null;

      // ---- ground disjunctions ---------------------------------------------
      this.firstGroundDisjunction = null;
      this.firstUnprocessedGroundDisjunction = null;

      // ---- branching points -------------------------------------------------
      this.branchingPoints = new Array(2).fill(null);
      this.currentBranchingPoint = -1;
      this.nonbacktrackableBranchingPoint = -1;
      this.isCurrentModelDeterministic = true;

// ---- per-run term → node map (used by getNodeForTerm & clause matching).
    // Rebuilt by every isSatisfiable() call; left in place afterwards so the
    // reasoner can read the model off.
      this.termsToNodes = new Map();

      // ---- pool of reusable arrays for the expansion strategy ---------------
      this.existentialConceptsBuffers = [];

      // ---- run statistics ----------------------------------------------------
      this.statistics = {
        iterations: 0,
        nodeCreations: 0,
        backjumps: 0,
        clausesFired: 0,
        startTime: 0,
        elapsedMs: 0
      };

      this.updateFlagsDependentOnAdditionalOntology();
      if (this.tableauMonitor && typeof this.tableauMonitor.setTableau === 'function') {
        this.tableauMonitor.setTableau(this);
      }
    } finally {
      this.interruptFlag.endTask();
    }
  }

  // ---- accessors -------------------------------------------------------------

  getPermanentDLOntology() { return this.permanentDLOntology; }
  getAdditionalDLOntology() { return this.additionalDLOntology; }
  getExtensionManager() { return this.extensionManager; }
  getDependencySetFactory() { return this.dependencySetFactory; }
  getMergingManager() { return this.mergingManager; }
  getExistentialExpansionManager() { return this.existentialExpansionManager; }
  getNominalIntroductionManager() { return this.nominalIntroduction; }
  getPermanentHyperresolutionManager() { return this.permanentHyperresolutionManager; }
  getAdditionalHyperresolutionManager() { return this.additionalHyperresolutionManager; }
  getExistentialExpansionStrategy() { return this.existentialExpansionStrategy; }
  getInterruptFlag() { return this.interruptFlag; }

  /** Alias used by some HermiT call sites. */
  get nominalIntroductionManager() { return this.nominalIntroduction; }

  /**
   * A run is deterministic when no branching can ever be needed: both
   * ontologies are Horn and the expansion strategy introduces no branching
   * points. Deterministic runs never backtrack, so classification can use the
   * much cheaper "model-reuse" path.
   */
  isDeterministic() {
    const permanentHorn = !!this.permanentDLOntology.isHorn;
    const additionalHorn = this.additionalDLOntology === null || !!this.additionalDLOntology.isHorn;
    const strategy = this.existentialExpansionStrategy;
    // During construction the strategy does not exist yet; assume deterministic
    // (IndividualReuseStrategy is built with this very value).
    const strategyDeterministic = strategy ? strategy.isDeterministic() : true;
    return permanentHorn && additionalHorn && strategyDeterministic;
  }

  isCurrentModelDeterministicFlag() { return this.isCurrentModelDeterministic; }

  checkInterrupt() { this.interruptFlag.checkInterrupt(); }

  isInternalIRI(iri) { return isInternalIRI(iri); }

  // ---- additional-ontology support -------------------------------------------

  supportsAdditionalDLOntology(additionalDLOntology) {
    if (!additionalDLOntology) return true;
    const additional = this.additionalDLOntology;
    const hasInverseRoles = this.permanentDLOntology.hasInverseRoles
      || (additional !== null && additional.hasInverseRoles);
    const hasNominals = this.permanentDLOntology.hasNominals
      || (additional !== null && additional.hasNominals);
    const isHorn = this.permanentDLOntology.isHorn
      || (additional !== null && additional.isHorn);
    // NOTE: BOTTOM_OBJECT_ROLE is a module-level constant in this port, not a
    // static on AtomicRole (HermiT's `AtomicRole.BOTTOM_OBJECT_ROLE`).
    const permanentHasBottomObjectProperty =
      this.permanentDLOntology.containsObjectRole
        ? this.permanentDLOntology.containsObjectRole(BOTTOM_OBJECT_ROLE)
        : false;
    const hasBottomObjectProperty = permanentHasBottomObjectProperty
      || (additional !== null && additional.containsObjectRole
        && additional.containsObjectRole(BOTTOM_OBJECT_ROLE));

    if (additionalDLOntology.hasInverseRoles && !hasInverseRoles) return false;
    if (additionalDLOntology.hasNominals && !hasNominals) return false;
    if (!additionalDLOntology.isHorn && isHorn) return false;
    if (hasBottomObjectProperty && !permanentHasBottomObjectProperty) return false;
    for (const clause of additionalDLOntology.dlClauses) {
      if (clause.isAtomicRoleInclusion() || clause.isAtomicRoleInverseInclusion()
        || clause.isFunctionalityAxiom() || clause.isInverseFunctionalityAxiom()) return false;
    }
    return true;
  }

  setAdditionalDLOntology(additionalDLOntology) {
    if (!this.supportsAdditionalDLOntology(additionalDLOntology)) {
      throw new Error('Additional DL-ontology contains features that are incompatible with this tableau.');
    }
    this.additionalDLOntology = additionalDLOntology;
    this.additionalHyperresolutionManager = additionalDLOntology
      ? new HyperresolutionManager(this, additionalDLOntology.dlClauses)
      : null;
    this.datatypeManager.setUnknownDatatypeRestrictions(
      this._mergedUnknownDatatypeRestrictions());
    if (typeof this.existentialExpansionStrategy.additionalDLOntologySet === 'function') {
      this.existentialExpansionStrategy.additionalDLOntologySet(this.additionalDLOntology);
    }
    this.updateFlagsDependentOnAdditionalOntology();
  }

  clearAdditionalDLOntology() {
    this.additionalDLOntology = null;
    this.additionalHyperresolutionManager = null;
    this.datatypeManager.setUnknownDatatypeRestrictions(
      this._mergedUnknownDatatypeRestrictions());
    if (typeof this.existentialExpansionStrategy.additionalDLOntologyCleared === 'function') {
      this.existentialExpansionStrategy.additionalDLOntologyCleared();
    }
    this.updateFlagsDependentOnAdditionalOntology();
  }

  /**
   * The union of the permanent and additional ontologies' unknown datatype
   * restrictions. HermiT keeps them as two separate sets and checks both; a
   * single merged set is equivalent for the membership test the
   * DatatypeManager performs.
   * @returns {Set<import('../model/DLPredicate').DatatypeRestriction>}
   */
  _mergedUnknownDatatypeRestrictions() {
    const merged = new Set(this.permanentDLOntology.allUnknownDatatypeRestrictions);
    const additional = this.additionalDLOntology;
    if (additional !== null && additional.allUnknownDatatypeRestrictions) {
      for (const r of additional.allUnknownDatatypeRestrictions) merged.add(r);
    }
    return merged;
  }

  updateFlagsDependentOnAdditionalOntology() {
    const permanent = this.permanentHyperresolutionManager;
    this.needsThingExtension = permanent.tupleConsumersByDeltaPredicate.has(THING);
    this.needsNamedExtension = permanent.tupleConsumersByDeltaPredicate.has(INTERNAL_NAMED);
    this.needsRDFSLiteralExtension = permanent.tupleConsumersByDeltaPredicate.has(RDFS_LITERAL);
    this.checkDatatypes = !!this.permanentDLOntology.hasDatatypes;
    this.checkUnknownDatatypeRestrictions = !!this.permanentDLOntology.hasUnknownDatatypeRestrictions;
    if (this.additionalHyperresolutionManager !== null) {
      const additional = this.additionalHyperresolutionManager;
      this.needsThingExtension |= additional.tupleConsumersByDeltaPredicate.has(THING);
      this.needsNamedExtension |= additional.tupleConsumersByDeltaPredicate.has(INTERNAL_NAMED);
      this.needsRDFSLiteralExtension |= additional.tupleConsumersByDeltaPredicate.has(RDFS_LITERAL);
    }
    if (this.additionalDLOntology !== null) {
      this.checkDatatypes = this.checkDatatypes || !!this.additionalDLOntology.hasDatatypes;
      this.checkUnknownDatatypeRestrictions = this.checkUnknownDatatypeRestrictions
        || !!this.additionalDLOntology.hasUnknownDatatypeRestrictions;
    }
    // Coerce the bitwise-or results back to booleans.
    this.needsThingExtension = !!this.needsThingExtension;
    this.needsNamedExtension = !!this.needsNamedExtension;
    this.needsRDFSLiteralExtension = !!this.needsRDFSLiteralExtension;

    // `owl:Thing` holds of every abstract node and `rdfs:Literal` of every
    // concrete one, so `ExtensionManager.containsConceptAssertion` answers
    // `true` for them WITHOUT consulting a table and `ExtensionTable.addTuple`
    // drops the tuples as dead weight. That is a pure optimisation for the
    // tableau calculus — but it is a silent trap for conjunctive query
    // answering, where `owl:Thing(X)` is the natural way to ask for "every
    // individual" and would otherwise return an empty answer set.
    //
    // Forcing the extensions is safe: HermiT itself stores `owl:Thing` whenever
    // an unsafe clause needs it (`getSafeVersion(AtomicConcept.THING)`), so
    // blocking and the delta loop already cope with these tuples being present.
    // The cost is one extra tuple per node plus a no-consumer `continue` in
    // `applyDLClauses`.
    if (this.materialiseTopPredicates) {
      this.needsThingExtension = true;
      this.needsRDFSLiteralExtension = true;
    }
  }

  // ---- reset -------------------------------------------------------------------

  clear() {
    this.allocatedNodes = 0;
    this.numberOfNodesInTableau = 0;
    this.numberOfMergedOrPrunedNodes = 0;
    this.numberOfNodeCreations = 0;
    this.firstFreeNode = null;
    this.firstTableauNode = null;
    this.lastTableauNode = null;
    this.lastMergedOrPrunedNode = null;
    this.firstGroundDisjunction = null;
    this.firstUnprocessedGroundDisjunction = null;
    this.branchingPoints = new Array(2).fill(null);
    this.currentBranchingPoint = -1;
    this.nonbacktrackableBranchingPoint = -1;

    this.dependencySetFactory.clear();
    this.extensionManager.clear();
    this.permanentHyperresolutionManager.clear();
    if (this.additionalHyperresolutionManager !== null) this.additionalHyperresolutionManager.clear();
    this.mergingManager.clear();
    this.existentialExpansionManager.clear();
    this.nominalIntroduction.clear();
    this.isCurrentModelDeterministic = true;
    this.existentialExpansionStrategy.clear();
    this.datatypeManager.clear();
    this.existentialConceptsBuffers.length = 0;

    if (this.tableauMonitor && typeof this.tableauMonitor.tableauCleared === 'function') {
      this.tableauMonitor.tableauCleared();
    }
  }

  // ---- the satisfiability test --------------------------------------------------

  /**
   * Run the calculus.
   *
   * @param {object} [opts]
   * @param {boolean} [opts.loadPermanentABox]  default: true iff some ontology has nominals.
   *        HermiT skips the ABox for pure TBox tasks: without nominals (or keys)
   *        the individuals cannot interact with the TBox, so loading them is
   *        wasted work. Pass `true` explicitly for ABox reasoning tasks.
   * @param {boolean} [opts.loadAdditionalABox] default: false
   * @param {Atom[]|Set<Atom>} [opts.perTestPositiveFactsNoDependency]
   * @param {Atom[]|Set<Atom>} [opts.perTestNegativeFactsNoDependency]
   * @param {Atom[]|Set<Atom>} [opts.perTestPositiveFactsDummyDependency]
   * @param {Atom[]|Set<Atom>} [opts.perTestNegativeFactsDummyDependency]
   * @param {Map<Individual,Node>} [opts.nodesForIndividuals] filled in with the nodes
   * @param {string} [opts.reasoningTaskDescription]
   * @returns {boolean} true iff a model was found (no clash remains)
   */
  isSatisfiable(opts) {
    const options = opts || {};
    const additionalHasNominals = this.additionalDLOntology !== null
      && !!this.additionalDLOntology.hasNominals;
    const loadPermanentABox = options.loadPermanentABox !== undefined
      ? options.loadPermanentABox
      : (!!this.permanentDLOntology.hasNominals || additionalHasNominals);
    const loadAdditionalABox = !!options.loadAdditionalABox;

    const perTestPositiveFactsNoDependency = _asArray(options.perTestPositiveFactsNoDependency);
    const perTestNegativeFactsNoDependency = _asArray(options.perTestNegativeFactsNoDependency);
    const perTestPositiveFactsDummyDependency = _asArray(options.perTestPositiveFactsDummyDependency);
    const perTestNegativeFactsDummyDependency = _asArray(options.perTestNegativeFactsDummyDependency);
    const nodesForIndividuals = options.nodesForIndividuals || null;
    const reasoningTaskDescription = options.reasoningTaskDescription || null;

    if (this.tableauMonitor && typeof this.tableauMonitor.isSatisfiableStarted === 'function') {
      this.tableauMonitor.isSatisfiableStarted(reasoningTaskDescription);
    }

    this.interruptFlag.startTask();
    try {
      this.clear();
      this.statistics.startTime = Date.now();
      this.statistics.iterations = 0;
      this.statistics.backjumps = 0;

      // A fresh term→node map per run (HermiT passes `new HashMap<>()`).
      const termsToNodes = options.termsToNodes instanceof Map ? options.termsToNodes : new Map();
      this.termsToNodes = termsToNodes;
      const emptySet = this.dependencySetFactory.emptySet();

      if (loadPermanentABox) {
        for (const atom of this.permanentDLOntology.positiveFacts) {
          this.loadPositiveFact(termsToNodes, atom, emptySet);
        }
        for (const atom of this.permanentDLOntology.negativeFacts) {
          this.loadNegativeFact(termsToNodes, atom, emptySet);
        }
      }
      if (loadAdditionalABox && this.additionalDLOntology !== null) {
        for (const atom of this.additionalDLOntology.positiveFacts) {
          this.loadPositiveFact(termsToNodes, atom, emptySet);
        }
        for (const atom of this.additionalDLOntology.negativeFacts) {
          this.loadNegativeFact(termsToNodes, atom, emptySet);
        }
      }
      for (const atom of perTestPositiveFactsNoDependency) {
        this.loadPositiveFact(termsToNodes, atom, emptySet);
      }
      for (const atom of perTestNegativeFactsNoDependency) {
        this.loadNegativeFact(termsToNodes, atom, emptySet);
      }

      // Facts that may be retracted: they live under a branching point that is
      // never backjumped past (nonbacktrackableBranchingPoint), so a clash that
      // depends only on them makes the whole test fail.
      if (perTestPositiveFactsDummyDependency.length > 0
        || perTestNegativeFactsDummyDependency.length > 0) {
        this.branchingPoints[0] = new BranchingPoint(this);
        this.currentBranchingPoint++;
        this.nonbacktrackableBranchingPoint = this.currentBranchingPoint;
        const dependencySet = this.dependencySetFactory.addBranchingPoint(
          emptySet, this.currentBranchingPoint);
        for (const atom of perTestPositiveFactsDummyDependency) {
          this.loadPositiveFact(termsToNodes, atom, dependencySet);
        }
        for (const atom of perTestNegativeFactsDummyDependency) {
          this.loadNegativeFact(termsToNodes, atom, dependencySet);
        }
      }

      // Make sure every individual the caller cares about has a node, and
      // hand the caller back the node that ended up representing it.
      if (nodesForIndividuals !== null) {
        for (const individual of [...nodesForIndividuals.keys()]) {
          if (!termsToNodes.has(individual)) {
            this.loadPositiveFact(termsToNodes, createAtom(THING, individual), emptySet);
          }
          nodesForIndividuals.set(individual, termsToNodes.get(individual));
        }
      }

      // Ensure that at least one individual exists.
      if (this.firstTableauNode === null) this.createNewNINode(emptySet);

      const result = this.runCalculus();
      this.statistics.elapsedMs = Date.now() - this.statistics.startTime;
      this.statistics.nodeCreations = this.numberOfNodeCreations;

      if (this.tableauMonitor && typeof this.tableauMonitor.isSatisfiableFinished === 'function') {
        this.tableauMonitor.isSatisfiableFinished(reasoningTaskDescription, result);
      }
      return result;
    } finally {
      this.interruptFlag.endTask();
    }
  }

  /** Assert a ground positive fact, creating nodes for its terms as needed. */
  loadPositiveFact(termsToNodes, atom, dependencySet) {
    const dlPredicate = atom.dlPredicate;
    if (isLiteralConcept(dlPredicate)) {
      this.extensionManager.addConceptAssertion(
        dlPredicate,
        this.getNodeForTerm(termsToNodes, atom.getArgument(0), dependencySet),
        dependencySet, true);
    } else if (dlPredicate instanceof AtomicRole
      || dlPredicate instanceof Equality || dlPredicate instanceof Inequality) {
      this.extensionManager.addAssertion(
        dlPredicate,
        this.getNodeForTerm(termsToNodes, atom.getArgument(0), dependencySet),
        this.getNodeForTerm(termsToNodes, atom.getArgument(1), dependencySet),
        dependencySet, true);
    } else {
      throw new Error(`Unsupported type of positive ground atom: ${atom}`);
    }
  }

  /** Assert the negation of a ground fact. */
  loadNegativeFact(termsToNodes, atom, dependencySet) {
    const dlPredicate = atom.dlPredicate;
    if (isLiteralConcept(dlPredicate)) {
      const negation = this.extensionManager.negationOf(dlPredicate);
      if (negation === null) throw new Error(`Cannot negate ${dlPredicate}`);
      this.extensionManager.addConceptAssertion(
        negation,
        this.getNodeForTerm(termsToNodes, atom.getArgument(0), dependencySet),
        dependencySet, true);
    } else if (dlPredicate instanceof AtomicRole) {
      this.extensionManager.addTuple([
        internNegatedAtomicRole(dlPredicate),
        this.getNodeForTerm(termsToNodes, atom.getArgument(0), dependencySet),
        this.getNodeForTerm(termsToNodes, atom.getArgument(1), dependencySet)
      ], dependencySet, true);
    } else if (dlPredicate instanceof Equality) {
      this.extensionManager.addAssertion(
        INEQUALITY,
        this.getNodeForTerm(termsToNodes, atom.getArgument(0), dependencySet),
        this.getNodeForTerm(termsToNodes, atom.getArgument(1), dependencySet),
        dependencySet, true);
    } else if (dlPredicate instanceof Inequality) {
      this.extensionManager.addAssertion(
        EQUALITY,
        this.getNodeForTerm(termsToNodes, atom.getArgument(0), dependencySet),
        this.getNodeForTerm(termsToNodes, atom.getArgument(1), dependencySet),
        dependencySet, true);
    } else {
      throw new Error(`Unsupported type of negative ground atom: ${atom}`);
    }
  }

  /**
   * The node denoting a ground term, creating it on first use.
   *   • named individual   → NAMED_NODE   (keys apply)
   *   • anonymous individual → NI_NODE    (keys do not apply)
   *   • constant           → ROOT_CONSTANT_NODE + a ConstantEnumeration assertion
   * Returns the *canonical* node (merge redirections already applied).
   */
  getNodeForTerm(termsToNodes, term, dependencySet) {
    let node = termsToNodes.get(term);
    if (node === undefined || node === null) {
      if (term instanceof Individual) {
        node = term.isAnonymous()
          ? this.createNewNINode(dependencySet)
          : this.createNewNamedNode(dependencySet);
      } else if (term instanceof Constant) {
        node = this.createNewRootConstantNode(dependencySet);
        // Anonymous constants are not assigned a particular value.
        if (!term.isAnonymous()) {
          this.extensionManager.addAssertion(
            internConstantEnumeration([term]), node, dependencySet, true);
        }
      } else {
        throw new Error(`Unsupported term in a ground atom: ${term}`);
      }
      termsToNodes.set(term, node);
    }
    return node.getCanonicalNode();
  }

  // ---- the calculus -------------------------------------------------------------

  runCalculus() {
    this.interruptFlag.startTask();
    try {
      const existentialsAreExact = this.existentialExpansionStrategy.isExact();
      if (this.tableauMonitor && typeof this.tableauMonitor.saturateStarted === 'function') {
        this.tableauMonitor.saturateStarted();
      }
      let hasMoreWork = true;
      while (hasMoreWork) {
        if (this.tableauMonitor && typeof this.tableauMonitor.iterationStarted === 'function') {
          this.tableauMonitor.iterationStarted();
        }
        hasMoreWork = this.doIteration();
        this.statistics.iterations++;
        if (this.tableauMonitor && typeof this.tableauMonitor.iterationFinished === 'function') {
          this.tableauMonitor.iterationFinished();
        }
        if (!existentialsAreExact && !hasMoreWork && !this.extensionManager.containsClash()) {
          // The blocking strategy may have established invalid blocks; give the
          // expansion one final chance to validate them.
          hasMoreWork = this.existentialExpansionStrategy.expandExistentials(true);
        }
        this.checkInterrupt();
      }
      if (this.tableauMonitor && typeof this.tableauMonitor.saturateFinished === 'function') {
        this.tableauMonitor.saturateFinished(!this.extensionManager.containsClash());
      }
      if (!this.extensionManager.containsClash()) {
        this.existentialExpansionStrategy.modelFound();
        return true;
      }
      return false;
    } finally {
      this.interruptFlag.endTask();
    }
  }

  /**
   * One step of the calculus. Returns true if the tableau changed (so the loop
   * must continue) and false when a final answer has been reached.
   */
  doIteration() {
    const em = this.extensionManager;

    // (1) Rule saturation over the delta windows.
    if (!em.containsClash()) {
      this.nominalIntroduction.processAnnotatedEqualities();
      let hasChange = false;
      while (em.propagateDeltaNew() && !em.containsClash()) {
        if (!em.containsClash()) {
          this.permanentHyperresolutionManager.applyDLClauses();
          this.statistics.clausesFired++;
        }
        if (this.additionalHyperresolutionManager !== null && !em.containsClash()) {
          this.additionalHyperresolutionManager.applyDLClauses();
        }
        if (this.checkUnknownDatatypeRestrictions && !em.containsClash()) {
          this.datatypeManager.applyUnknownDatatypeRestrictionSemantics();
        }
        if (this.checkDatatypes && !em.containsClash()) {
          this.datatypeManager.checkDatatypeConstraints();
        }
        if (!em.containsClash()) {
          this.nominalIntroduction.processAnnotatedEqualities();
        }
        hasChange = true;
      }
      if (hasChange) return true;
    }

    // (2) Existential expansion (with blocking).
    if (!em.containsClash()) {
      if (this.existentialExpansionStrategy.expandExistentials(false)) return true;
    }

    // (3) Branch on the most recently derived, still unsatisfied disjunction.
    if (!em.containsClash()) {
      while (this.firstUnprocessedGroundDisjunction !== null) {
        const groundDisjunction = this.firstUnprocessedGroundDisjunction;
        if (this.tableauMonitor
          && typeof this.tableauMonitor.processGroundDisjunctionStarted === 'function') {
          this.tableauMonitor.processGroundDisjunctionStarted(groundDisjunction);
        }
        this.firstUnprocessedGroundDisjunction = groundDisjunction.previous;
        if (!groundDisjunction.isPruned() && !groundDisjunction.isSatisfied(this)) {
          const sortedDisjunctIndexes = groundDisjunction.getHeader().getSortedDisjunctIndexes();
          let dependencySet = groundDisjunction.getDependencySet();
          if (groundDisjunction.getNumberOfDisjuncts() > 1) {
            const branchingPoint = new DisjunctionBranchingPoint(
              this, groundDisjunction, sortedDisjunctIndexes);
            this.pushBranchingPoint(branchingPoint);
            dependencySet = this.dependencySetFactory.addBranchingPoint(
              dependencySet, branchingPoint.getLevel());
          }
          if (this.tableauMonitor
            && typeof this.tableauMonitor.disjunctProcessingStarted === 'function') {
            this.tableauMonitor.disjunctProcessingStarted(
              groundDisjunction, sortedDisjunctIndexes[0]);
          }
          groundDisjunction.addDisjunctToTableau(this, sortedDisjunctIndexes[0], dependencySet);
          if (this.tableauMonitor
            && typeof this.tableauMonitor.disjunctProcessingFinished === 'function') {
            this.tableauMonitor.disjunctProcessingFinished(
              groundDisjunction, sortedDisjunctIndexes[0]);
            this.tableauMonitor.processGroundDisjunctionFinished(groundDisjunction);
          }
          return true;
        }
        if (this.tableauMonitor
          && typeof this.tableauMonitor.groundDisjunctionSatisfied === 'function') {
          this.tableauMonitor.groundDisjunctionSatisfied(groundDisjunction);
        }
        this.checkInterrupt();
      }
    }

    // (4) Clash: dependency-directed backjump.
    if (em.containsClash()) {
      const clashDependencySet = em.getClashDependencySet();
      const newCurrentBranchingPoint = clashDependencySet.maximum();
      if (newCurrentBranchingPoint <= this.nonbacktrackableBranchingPoint) return false;
      this.backtrackTo(newCurrentBranchingPoint);
      this.statistics.backjumps++;
      const branchingPoint = this.getCurrentBranchingPoint();
      if (this.tableauMonitor
        && typeof this.tableauMonitor.startNextBranchingPointStarted === 'function') {
        this.tableauMonitor.startNextBranchingPointStarted(branchingPoint);
      }
      branchingPoint.startNextChoice(this, clashDependencySet);
      if (this.tableauMonitor
        && typeof this.tableauMonitor.startNextBranchingPointFinished === 'function') {
        this.tableauMonitor.startNextBranchingPointFinished(branchingPoint);
      }
      this.dependencySetFactory.removeUnusedSets();
      return true;
    }

    return false;
  }

  // ---- ground disjunctions -------------------------------------------------------

  /** Prepend a newly derived disjunction to the work list. */
  addGroundDisjunction(groundDisjunction) {
    groundDisjunction.next = this.firstGroundDisjunction;
    groundDisjunction.previous = null;
    if (this.firstGroundDisjunction !== null) {
      this.firstGroundDisjunction.previous = groundDisjunction;
    }
    this.firstGroundDisjunction = groundDisjunction;
    if (this.firstUnprocessedGroundDisjunction === null) {
      this.firstUnprocessedGroundDisjunction = groundDisjunction;
    }
    if (this.tableauMonitor && typeof this.tableauMonitor.groundDisjunctionDerived === 'function') {
      this.tableauMonitor.groundDisjunctionDerived(groundDisjunction);
    }
  }

  getFirstUnprocessedGroundDisjunction() { return this.firstUnprocessedGroundDisjunction; }

  // ---- branching points -----------------------------------------------------------

  getCurrentBranchingPointLevel() { return this.currentBranchingPoint; }

  getCurrentBranchingPoint() { return this.branchingPoints[this.currentBranchingPoint]; }

  /** Record the current state so the calculus can come back to it. */
  pushBranchingPoint(branchingPoint) {
    if (this.currentBranchingPoint + 1 !== branchingPoint.level) {
      throw new Error('Internal error: branching point level mismatch.');
    }
    if (this.tableauMonitor && typeof this.tableauMonitor.pushBranchingPointStarted === 'function') {
      this.tableauMonitor.pushBranchingPointStarted(branchingPoint);
    }
    this.currentBranchingPoint++;
    if (this.currentBranchingPoint >= this.branchingPoints.length) {
      let newSize = Math.max(2, Math.floor(this.branchingPoints.length * 3 / 2));
      while (newSize <= this.currentBranchingPoint) newSize = Math.floor(newSize * 3 / 2) + 1;
      const grown = new Array(newSize).fill(null);
      for (let i = 0; i < this.branchingPoints.length; i++) grown[i] = this.branchingPoints[i];
      this.branchingPoints = grown;
    }
    this.branchingPoints[this.currentBranchingPoint] = branchingPoint;
    this.extensionManager.branchingPointPushed();
    this.existentialExpansionManager.branchingPointPushed();
    this.existentialExpansionStrategy.branchingPointPushed();
    this.nominalIntroduction.branchingPointPushed();
    this.isCurrentModelDeterministic = false;
    if (this.tableauMonitor && typeof this.tableauMonitor.pushBranchingPointFinished === 'function') {
      this.tableauMonitor.pushBranchingPointFinished(branchingPoint);
    }
  }

  /**
   * Undo everything done after branching point `newCurrentBranchingPoint`.
   * The order is the exact reverse of the order things were created in.
   */
  backtrackTo(newCurrentBranchingPoint) {
    const branchingPoint = this.branchingPoints[newCurrentBranchingPoint];
    if (!branchingPoint) throw new Error(`Internal error: no branching point ${newCurrentBranchingPoint}.`);
    if (this.tableauMonitor && typeof this.tableauMonitor.backtrackToStarted === 'function') {
      this.tableauMonitor.backtrackToStarted(branchingPoint);
    }

    // (a) drop the branching points above the target
    for (let index = newCurrentBranchingPoint + 1; index <= this.currentBranchingPoint; index++) {
      this.branchingPoints[index] = null;
    }
    this.currentBranchingPoint = newCurrentBranchingPoint;

    // (b) restore the ground-disjunction work list
    this.firstUnprocessedGroundDisjunction = branchingPoint.firstUnprocessedGroundDisjunction;
    const firstGroundDisjunctionShouldBe = branchingPoint.firstGroundDisjunction;
    while (this.firstGroundDisjunction !== firstGroundDisjunctionShouldBe) {
      const next = this.firstGroundDisjunction.next;
      this.firstGroundDisjunction.destroy(this);
      this.firstGroundDisjunction = next;
    }
    if (this.firstGroundDisjunction !== null) this.firstGroundDisjunction.previous = null;

    // (c) existentials, nominal introduction, extension tables
    this.existentialExpansionStrategy.backtrack();
    this.existentialExpansionManager.backtrack();
    this.nominalIntroduction.backtrack();
    this.extensionManager.backtrack();

    // (d) un-merge / un-prune nodes
    const lastMergedOrPrunedNodeShouldBe = branchingPoint.lastMergedOrPrunedNode;
    while (this.lastMergedOrPrunedNode !== lastMergedOrPrunedNodeShouldBe) {
      this.backtrackLastMergedOrPrunedNode();
    }

    // (e) destroy the nodes created after the branching point
    const lastTableauNodeShouldBe = branchingPoint.lastTableauNode;
    while (lastTableauNodeShouldBe !== this.lastTableauNode) {
      this.destroyLastTableauNode();
    }

    this.extensionManager.clearClash();
    if (this.tableauMonitor && typeof this.tableauMonitor.backtrackToFinished === 'function') {
      this.tableauMonitor.backtrackToFinished(branchingPoint);
    }
  }

  // ---- node creation ---------------------------------------------------------------

  /** A node for an individual named in the input ontology (keys apply). */
  createNewNamedNode(dependencySet) {
    return this.createNewNodeRaw(dependencySet, null, NODE_TYPE.NAMED_NODE, 0);
  }

  /** A nominal node that is *not* named in the input ontology (keys do not apply). */
  createNewNINode(dependencySet) {
    return this.createNewNodeRaw(dependencySet, null, NODE_TYPE.NI_NODE, 0);
  }

  /** An anonymous successor in the model tree. */
  createNewTreeNode(dependencySet, parent) {
    return this.createNewNodeRaw(dependencySet, parent, NODE_TYPE.TREE_NODE, parent.getTreeDepth() + 1);
  }

  /** A data node hanging off `parent`. */
  createNewConcreteNode(dependencySet, parent) {
    return this.createNewNodeRaw(dependencySet, parent, NODE_TYPE.CONCRETE_NODE, parent.getTreeDepth() + 1);
  }

  /** A data constant used as a root (from a ground literal in the ABox). */
  createNewRootConstantNode(dependencySet) {
    return this.createNewNodeRaw(dependencySet, null, NODE_TYPE.ROOT_CONSTANT_NODE, 0);
  }

  createNewNodeRaw(dependencySet, parent, nodeType, treeDepth) {
    let node;
    if (this.firstFreeNode === null) {
      node = new Node(-1, null, null);
      this.allocatedNodes++;
    } else {
      node = this.firstFreeNode;
      this.firstFreeNode = this.firstFreeNode.nextTableauNode;
    }
    // Node IDs are never recycled: the extension tables key tuples by ID, and
    // stale references (in the reuse caches, blocking labels, ...) must not
    // alias a freshly created node.
    node.initialize(nextNodeID(), parent, nodeType, treeDepth);

    this.existentialExpansionStrategy.nodeInitialized(node);

    // Link into the intrusive node list.
    node.previousTableauNode = this.lastTableauNode;
    if (this.lastTableauNode === null) this.firstTableauNode = node;
    else this.lastTableauNode.nextTableauNode = node;
    this.lastTableauNode = node;
    if (parent !== null) parent.children.push(node);

    this.existentialExpansionStrategy.nodeStatusChanged(node);
    this.numberOfNodesInTableau++;
    this.numberOfNodeCreations++;
    if (this.tableauMonitor && typeof this.tableauMonitor.nodeCreated === 'function') {
      this.tableauMonitor.nodeCreated(node);
    }

    // Every node carries its "top" assertion. These are only materialised in
    // the extension tables when some DL-clause actually consumes them.
    const ds = dependencySet || PERMANENT;
    if (node.isAbstract()) {
      this.extensionManager.addConceptAssertion(THING, node, ds, true);
      if (nodeType === NODE_TYPE.NAMED_NODE && this.needsNamedExtension) {
        this.extensionManager.addConceptAssertion(INTERNAL_NAMED, node, ds, true);
      }
    } else {
      this.extensionManager.addDataRangeAssertion(RDFS_LITERAL, node, ds, true);
    }
    return node;
  }

  // ---- merging / pruning -------------------------------------------------------------

  /** Convenience delegate used by ExtensionManager when Equality is asserted. */
  mergeNodes(node0, node1, dependencySet) {
    return this.mergingManager.mergeNodes(node0, node1, dependencySet);
  }

  /**
   * Redirect `node` to `mergeInto`. Concepts and roles must already have been
   * copied over by the MergingManager.
   */
  mergeNode(node, mergeInto, dependencySet) {
    if (!node.isActive()) return;
    node.mergedInto = mergeInto;
    node.mergedIntoDependencySet = this.dependencySetFactory.getPermanent(dependencySet);
    this.dependencySetFactory.addUsage(node.mergedIntoDependencySet);
    node.previousMergedOrPrunedNode = this.lastMergedOrPrunedNode;
    this.lastMergedOrPrunedNode = node;
    this.numberOfMergedOrPrunedNodes++;
    this.existentialExpansionStrategy.nodeStatusChanged(node);
    this.existentialExpansionStrategy.nodesMerged(node, mergeInto);
  }

  /** Mark a node (and hence its subtree) as removed from the model. */
  pruneNode(node) {
    if (!node.isActive()) return;
    node.pruned = true;
    node.previousMergedOrPrunedNode = this.lastMergedOrPrunedNode;
    this.lastMergedOrPrunedNode = node;
    this.numberOfMergedOrPrunedNodes++;
    this.existentialExpansionStrategy.nodeStatusChanged(node);
  }

  backtrackLastMergedOrPrunedNode() {
    const node = this.lastMergedOrPrunedNode;
    if (node === null) return;
    let savedMergedInfo = null;
    if (node.mergedInto !== null) {
      this.dependencySetFactory.removeUsage(node.mergedIntoDependencySet);
      savedMergedInfo = node.mergedInto;
      node.mergedInto = null;
      node.mergedIntoDependencySet = null;
    }
    node.pruned = false;
    this.lastMergedOrPrunedNode = node.previousMergedOrPrunedNode;
    node.previousMergedOrPrunedNode = null;
    this.numberOfMergedOrPrunedNodes--;
    this.existentialExpansionStrategy.nodeStatusChanged(node);
    if (savedMergedInfo !== null) {
      this.existentialExpansionStrategy.nodesUnmerged(node, savedMergedInfo);
    }
  }

  destroyLastTableauNode() {
    const node = this.lastTableauNode;
    if (node === null) return;
    this.existentialExpansionStrategy.nodeDestroyed(node);
    if (node.previousTableauNode === null) this.firstTableauNode = null;
    else node.previousTableauNode.nextTableauNode = null;
    this.lastTableauNode = node.previousTableauNode;
    if (node.parent !== null) {
      const idx = node.parent.children.indexOf(node);
      if (idx >= 0) node.parent.children.splice(idx, 1);
    }
    node.destroy(this);
    node.nextTableauNode = this.firstFreeNode;
    this.firstFreeNode = node;
    this.numberOfNodesInTableau--;
  }

  /** Look a node up by id (linear scan — used by monitors and tests). */
  getNode(nodeID) {
    let node = this.firstTableauNode;
    while (node !== null) {
      if (node.nodeID === nodeID) return node;
      node = node.nextTableauNode;
    }
    return null;
  }

  /** Every active node, in creation order. */
  *nodes() {
    let node = this.firstTableauNode;
    while (node !== null) {
      const next = node.nextTableauNode;
      if (node.isActive()) yield node;
      node = next;
    }
  }

  // ---- dependency-set helpers ---------------------------------------------------------

  /** Weaken `dependencySet` with the merge history of `node`. */
  addCanonicalNodeDependencySet(node, dependencySet) {
    return node.addCanonicalNodeDependencySet(dependencySet);
  }

  // ---- extension-table callbacks (HermiT: ExtensionTable.postAdd / postRemove) --------

  /**
   * Called by ExtensionTable for every genuinely new tuple. Maintains the node
   * counters that clash detection and blocking rely on, notifies the expansion
   * strategy, and finally runs clash detection.
   */
  tupleAdded(table, tuple, dependencySet, isCore) {
    const dlPredicate = tuple[0];
    if (isConceptPredicate(dlPredicate)) {
      const node = tuple[1];
      if (dlPredicate instanceof AtomicConcept) {
        node.numberOfPositiveAtomicConcepts++;
        node.concepts.add(dlPredicate);
      } else if (isExistentialConcept(dlPredicate)) {
        node.addToUnprocessedExistentials(dlPredicate);
      } else if (dlPredicate instanceof AtomicNegationConcept) {
        node.numberOfNegatedAtomicConcepts++;
        node.concepts.add(dlPredicate);
      }
      this.existentialExpansionStrategy.assertionAddedConcept(dlPredicate, node);
    } else if (dlPredicate instanceof AtomicRole) {
      this.existentialExpansionStrategy.assertionAddedRole(dlPredicate, tuple[1], tuple[2]);
    } else if (dlPredicate instanceof NegatedAtomicRole) {
      tuple[1].numberOfNegatedRoleAssertions++;
    }
    if (this.tableauMonitor && typeof this.tableauMonitor.tupleAdded === 'function') {
      this.tableauMonitor.tupleAdded(tuple);
    }
    // ClashManager.tupleAdded
    this.extensionManager.detectClash(table, tuple, dependencySet, isCore);
  }

  /** Called by ExtensionTable for every tuple removed during backtracking. */
  tupleRemoved(table, tuple, entry) {
    const dlPredicate = tuple[0];
    if (isConceptPredicate(dlPredicate)) {
      const node = tuple[1];
      this.existentialExpansionStrategy.assertionRemovedConcept(dlPredicate, node);
      if (dlPredicate instanceof AtomicConcept) {
        node.numberOfPositiveAtomicConcepts--;
        node.concepts.delete(dlPredicate);
      } else if (isExistentialConcept(dlPredicate)) {
        node.removeFromUnprocessedExistentials(dlPredicate);
      } else if (dlPredicate instanceof AtomicNegationConcept) {
        node.numberOfNegatedAtomicConcepts--;
        node.concepts.delete(dlPredicate);
      }
    } else if (dlPredicate instanceof AtomicRole) {
      this.existentialExpansionStrategy.assertionRemovedRole(dlPredicate, tuple[1], tuple[2]);
    } else if (dlPredicate instanceof NegatedAtomicRole) {
      tuple[1].numberOfNegatedRoleAssertions--;
    }
    if (this.tableauMonitor && typeof this.tableauMonitor.tupleRemoved === 'function') {
      this.tableauMonitor.tupleRemoved(tuple);
    }
  }

  /** A tuple's core flag was upgraded (validated blocking only). */
  assertionCoreSet(tuple) {
    const strategy = this.existentialExpansionStrategy;
    if (!strategy || typeof strategy.assertionCoreSet !== 'function') return;
    const dlPredicate = tuple[0];
    if (isConceptPredicate(dlPredicate)) strategy.assertionCoreSet(dlPredicate, tuple[1]);
    else if (dlPredicate instanceof AtomicRole) strategy.assertionCoreSet(dlPredicate, tuple[1], tuple[2]);
  }

  // ---- buffer pooling ----------------------------------------------------------------

  getExistentialConceptsBuffer() {
    return this.existentialConceptsBuffers.length > 0
      ? this.existentialConceptsBuffers.pop()
      : [];
  }

  putExistentialConceptsBuffer(buffer) {
    buffer.length = 0;
    this.existentialConceptsBuffers.push(buffer);
  }

  // ---- integrity checking (debug aid) ---------------------------------------------------

  /** Validate the intrusive node list; throws if it is inconsistent. */
  checkTableauList() {
    let node = this.firstTableauNode;
    let previous = null;
    let count = 0;
    while (node !== null) {
      if (node.previousTableauNode !== previous) {
        throw new Error(`Tableau list corrupted at node ${node.nodeID}.`);
      }
      previous = node;
      count++;
      node = node.nextTableauNode;
    }
    if (previous !== this.lastTableauNode) throw new Error('Tableau list corrupted at the tail.');
    if (count !== this.numberOfNodesInTableau) {
      throw new Error(`Tableau list length ${count} != numberOfNodesInTableau ${this.numberOfNodesInTableau}.`);
    }
    return true;
  }

  /** A readable dump of the current (partial) model — handy for debugging. */
  describeModel() {
    const lines = [];
    for (const node of this.nodes()) {
      const unary = this.extensionManager.binaryTable.retrieve(null, [node])
        .map(e => String(e.tuple[0]));
      const roles = this.extensionManager.ternaryTable.retrieve(null, [node, null])
        .map(e => `${e.tuple[0]} → #${e.tuple[2].nodeID}`);
      lines.push(`#${node.nodeID} ${node.nodeType}${node.isBlocked() ? ' [blocked by #' + node.blocker.nodeID + ']' : ''}`);
      if (unary.length) lines.push(`    concepts: ${unary.join(', ')}`);
      if (roles.length) lines.push(`    roles:    ${roles.join(', ')}`);
    }
    return lines.join('\n');
  }
}

// ---------------------------------------------------------------------------

function _asArray(coll) {
  if (!coll) return [];
  return Array.isArray(coll) ? coll : [...coll];
}

module.exports = {
  Tableau,
  InterruptFlag,
  InterruptedException,
  isConceptPredicate,
  isExistentialConcept,
  isLiteralConcept,
  isLiteralDataRangePredicate
};
