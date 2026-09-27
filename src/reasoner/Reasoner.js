'use strict';

// ---------------------------------------------------------------------------
// reasoner/Reasoner.js — the public façade.
//
// Port of org.semanticweb.HermiT.Reasoner. This is the class users touch: it
// owns the clausification pipeline, the tableau, and the three hierarchies
// (classes, object properties, data properties), and answers the standard OWL
// 2 DL queries — consistency, class-expression satisfiability, subsumption,
// classification, property characteristics, domains/ranges and (via a slower
// fallback path) instance retrieval.
//
// Differences from HermiT, all forced by unported collaborators:
//
//   • `InstanceManager` is not ported. Realisation-style queries (`getTypes`,
//     `getInstances`, `getSameIndividuals`, `getObjectPropertyValues`,
//     `hasObjectPropertyRelationship`) are answered by per-query tableau tests
//     instead of by reading off a single completed model. Slower, same answers.
//   • `ReducedABoxOnlyClausification` IS ported, so `flush()` rebuilds only the
//     ABox when every pending change is an assertion (see
//     `canProcessPendingChangesIncrementally`); anything else full-reloads.
//   • `QuasiOrderClassificationForRoles` IS ported (see
//     `../hierarchy/QuasiOrderClassificationForRoles.js`), so object-property
//     classification seeds from told role inclusions and mirrors subsumptions
//     onto inverse roles.
//   • `HierarchyDumperFSS` / `HierarchyPrinterFSS` ARE ported (see
//     `../hierarchy/`); `dumpHierarchies` / `printHierarchies` below drive them.
//   • `Timer` / `TimerWithPause` / `CountingMonitor` / `TableauMonitorFork` ARE
//     ported (see `../monitor/`); only the interactive `Debugger` is not, so
//     DEBUGGER_* degrades to `CountingMonitor`.
//   • `AncestorBlocking` IS ported, so `BLOCKING_STRATEGY_TYPE` is honoured.
//     The *validated* blocking checkers and `BlockingSignatureCache` are not, so
//     a core-blocking or cached-signature request degrades to `AnywhereBlocking`
//     and warns through `configuration.warningMonitor`.
//   • `getDataFactory()` IS ported (returns the `owl/OWLExpressions` factory
//     module, our `OWLDataFactory` analogue — stateless, so shared). Conjunctive
//     query answering goes through `../datalog/`.
//   • protege-js has no `Node`/`NodeSet`; see `./Node.js`.
// ---------------------------------------------------------------------------

const E = require('../owl/OWLExpressions');
const P = require('../model/DLPredicate');
const { createAtom } = require('../model/Atom');
const { createAnonymousIndividual, createIndividual, createAnonymousConstant } = require('../model/Term');
const {
  Configuration,
  EXISTENTIAL_STRATEGY_TYPE,
  INDIVIDUAL_NODE_SET_POLICY,
  FRESH_ENTITY_POLICY,
  INFERENCE_TYPE,
  TABLEAU_MONITOR_TYPE
} = require('../Configuration');
const { Prefixes } = require('../Prefixes');
const { Tableau, InterruptFlag } = require('../tableau/Tableau');
const { createBlockingStrategy } = require('../tableau/BlockingStrategy');
const { CreationOrderStrategy, IndividualReuseStrategy } = require('../tableau/ExpansionStrategy');
const { CountingMonitor } = require('../monitor/CountingMonitor');
const { Timer } = require('../monitor/Timer');
const { TimerWithPause } = require('../monitor/TimerWithPause');
const { TableauMonitorFork } = require('../monitor/TableauMonitorFork');
const { Hierarchy, HierarchyNode } = require('../hierarchy/Hierarchy');
const { getAncestorNodes } = require('../hierarchy/HierarchyNode');
const { HierarchyDumperFSS } = require('../hierarchy/HierarchyDumperFSS');
const { HierarchyPrinterFSS } = require('../hierarchy/HierarchyPrinterFSS');
// `EntailmentChecker` requires nothing itself, so this top-level require is
// cycle-free. It is re-exported below so that
// `require('./reasoner/Reasoner').EntailmentChecker` works the same way
// `require('dl-js-reasoner').EntailmentChecker` does.
const { EntailmentChecker } = require('./EntailmentChecker');
const HierarchySearch = require('../hierarchy/HierarchySearch');
const { DeterministicClassification } = require('../hierarchy/DeterministicClassification');
const { QuasiOrderClassification } = require('../hierarchy/QuasiOrderClassification');
const { QuasiOrderClassificationForRoles } = require('../hierarchy/QuasiOrderClassificationForRoles');
const { OWLClausification } = require('../structural/OWLClausification');
const { DLOntology } = require('../model/DLOntology');
const {
  ReducedABoxOnlyClausification,
  INDIVIDUAL_AXIOM_TYPES,
  INCREMENTAL_CLASS_EXPRESSION_TYPES
} = require('../structural/ReducedABoxOnlyClausification');
const { OWLNormalization } = require('../structural/OWLNormalization');
const { OWLAxioms } = require('../structural/OWLAxioms');
const { OWLAxiomsExpressivity } = require('../structural/OWLAxiomsExpressivity');
const { BuiltInPropertyManager } = require('../structural/BuiltInPropertyManager');
const { DatalogEngine } = require('../datalog/DatalogEngine');
const { ConjunctiveQuery, CollectingQueryResultCollector } = require('../datalog/ConjunctiveQuery');
const { buildQuerySpec } = require('../datalog/QuerySpec');
const { Node, NodeSet, entityKey } = require('./Node');

const T = E.ClassExpressionType;

/**
 * The axiom type string, tolerating both plain objects and OWL API objects, and
 * detecting protege-js `SWRLRule` objects (which carry NO `axiomType`)
 * structurally. Shared with `EntailmentChecker.axiomTypeOf`.
 */
function axiomTypeOf(axiom) {
  if (axiom === null || axiom === undefined) return null;
  if (Array.isArray(axiom.body) && Array.isArray(axiom.head)) return 'SWRLRule';
  return axiom.axiomType
    || (typeof axiom.getAxiomType === 'function' ? axiom.getAxiomType() : null);
}

// ---- internal IRIs used by the reasoning tasks ------------------------------

const IRI_QUERY_CONCEPT = 'internal:query-concept';
const IRI_PSEUDO_NOMINAL = 'internal:pseudo-nominal';
const IRI_FRESH_CONCEPT = 'internal:fresh-concept';
const IRI_NEGATED_SUPERPROPERTY = 'internal:negated-superproperty';
const IRI_UNKNOWN_DATATYPE_A = 'internal:unknown-datatype#A';
const IRI_ANONYMOUS_CONSTANTS = 'internal:anonymous-constants';
const IRI_FRESH_CONSTANT = 'internal:fresh-constant';
const IRI_DELTA_KB = 'uri:urn:internal-kb';

const REASONER_NAME = 'DL-JS-REASONER';

/**
 * The version is read from `package.json` so that it has exactly ONE source of
 * truth and can never drift from the published package metadata.
 *
 * This mirrors HermiT, whose `Reasoner.getReasonerVersion()` reads
 * `Reasoner.class.getPackage().getImplementationVersion()` out of the JAR
 * manifest rather than hardcoding a string (Reasoner.java:301-317). HermiT
 * tolerates a missing manifest entry by filling the version components with
 * zeros; the `catch` below is the equivalent fallback for a layout where
 * `package.json` is not reachable (e.g. a bundler that inlines this file).
 */
const REASONER_VERSION = (() => {
  try {
    const pkg = require('../../package.json');
    return typeof pkg.version === 'string' && pkg.version !== '' ? pkg.version : '0.0.0';
  } catch (_e) {
    return '0.0.0';
  }
})();

// ===========================================================================
// OWL → HermiT term conversion (HermiT's overloaded `H(...)`)
// ===========================================================================

/** OWLClass → AtomicConcept */
function H_class(owlClass) {
  return P.internAtomicConcept(E.iriString(owlClass));
}

/** OWLObjectProperty → AtomicRole (object) */
function H_objectProperty(objectProperty) {
  return P.internAtomicRole(E.iriString(objectProperty), false);
}

/**
 * OWLObjectPropertyExpression → Role. An inverse expression becomes the
 * `InverseRole` of its named property.
 */
function H_role(objectPropertyExpression) {
  if (E.isAnonymousProperty(objectPropertyExpression)) {
    return H_objectProperty(E.namedPropertyOf(objectPropertyExpression)).getInverse();
  }
  return H_objectProperty(objectPropertyExpression);
}

/** OWLDataProperty → AtomicRole (data) */
function H_dataProperty(dataProperty) {
  return P.internAtomicRole(E.iriString(dataProperty), true);
}

/** OWLIndividual (named or anonymous) → Individual */
function H_individual(individual) {
  if (typeof individual === 'string') return createIndividual(individual);
  const isAnon = typeof individual.isAnonymous === 'function'
    ? individual.isAnonymous()
    : individual.nodeId !== undefined;
  if (isAnon) {
    const id = individual.nodeId !== undefined
      ? individual.nodeId
      : String((individual.getID && individual.getID()) || individual);
    return createAnonymousIndividual(id);
  }
  return createIndividual(E.iriString(individual));
}

/**
 * `role.getRoleAssertion(from, to)`.
 *
 * HermiT's `Role` has this method; the JS `AtomicRole`/`InverseRole` do not.
 * `InverseRole.getRoleAssertion(a, b)` is `Atom.create(inverseOf, b, a)` — the
 * arguments are swapped, which is the whole point of an inverse role.
 */
function roleAssertion(role, from, to) {
  if (role instanceof P.InverseRole) return createAtom(role.inverseRole, to, from);
  return createAtom(role, from, to);
}

/** Unwrap an `InverseRole` to the `AtomicRole` it inverts. */
function atomicRoleOf(role) {
  return role instanceof P.InverseRole ? role.inverseRole : role;
}

/** A `Constant` term → the OWLLiteral it came from. */
function constantToLiteral(constant) {
  const datatypeIRI = constant.datatypeIRI;
  if (datatypeIRI === E.IRI_RDF_PLAIN_LITERAL) {
    const lex = constant.lexicalValue;
    const at = lex.lastIndexOf('@');
    if (at >= 0) return E.literal(lex.substring(0, at), null, lex.substring(at + 1));
  }
  return E.literal(constant.lexicalValue, datatypeIRI);
}

// ===========================================================================
// Errors
// ===========================================================================

class InconsistentOntologyException extends Error {
  constructor(message) {
    super(message || 'Inconsistent ontology.');
    this.name = 'InconsistentOntologyException';
  }
}

class FreshEntitiesException extends Error {
  constructor(entities) {
    const list = [...entities].map(String).join(', ');
    super(`Some of the entities in the query are not present in the ontology: ${list}`);
    this.name = 'FreshEntitiesException';
    this.entities = new Set(entities);
  }
}

// ===========================================================================
// Entity signature walker (duck-typed; works on protege-js objects too)
// ===========================================================================

const _ENTITY_FIELDS = [
  'operands', 'classExpressions', 'individuals', 'properties', 'propertyExpressions',
  'propertyChain', 'subObjectProperties'
];
const _SINGLE_FIELDS = [
  'property', 'filler', 'dataRange', 'operand', 'subClass', 'superClass',
  'subProperty', 'superProperty', 'domain', 'range', 'individual', 'subject',
  'object', 'value', 'datatype', 'owlClass', 'superObjectProperty', 'superProperty',
  'property1', 'property2', 'entity', 'literal'
];

/**
 * Collect every OWL entity mentioned by `x` (an entity, expression, axiom,
 * individual, or an array/iterable of any of those).
 *
 * @param {*} x
 * @param {{classes:Set, objectProperties:Set, dataProperties:Set, individuals:Set, datatypes:Set}} out
 */
function collectEntities(x, out) {
  if (x === null || x === undefined) return;
  if (typeof x === 'string') return;
  if (Array.isArray(x) || x instanceof Set || x instanceof Map) {
    for (const item of x) collectEntities(item, out);
    return;
  }
  if (typeof x !== 'object') return;

  // A literal is not an entity.
  if (x.lexicalValue !== undefined && x.entityType === undefined) return;

  // Anonymous individuals are not entities either.
  if (x.nodeId !== undefined) return;

  if (x.entityType !== undefined) {
    const iri = E.iriString(x.iri || (x.getIRI && x.getIRI()));
    switch (x.entityType) {
      case E.EntityType.CLASS: out.classes.add(E.owlClass(iri)); return;
      case E.EntityType.OBJECT_PROPERTY: out.objectProperties.add(E.objectProperty(iri)); return;
      case E.EntityType.DATA_PROPERTY: out.dataProperties.add(E.dataProperty(iri)); return;
      case E.EntityType.NAMED_INDIVIDUAL: out.individuals.add(E.namedIndividual(iri)); return;
      case E.EntityType.DATATYPE: out.datatypes.add(E.datatype(iri)); return;
      default: return;
    }
  }

  for (const field of _ENTITY_FIELDS) {
    if (Array.isArray(x[field])) collectEntities(x[field], out);
  }
  for (const field of _SINGLE_FIELDS) {
    if (x[field] !== undefined) collectEntities(x[field], out);
  }
  // `subObjectProperties` on a ComplexObjectPropertyInclusion is already covered.
  if (x.subObjectProperties !== undefined) collectEntities(x.subObjectProperties, out);
}

/** A fresh, empty entity bucket. */
function _emptyEntitySets() {
  return {
    classes: new Set(),
    objectProperties: new Set(),
    dataProperties: new Set(),
    individuals: new Set(),
    datatypes: new Set()
  };
}

// ===========================================================================
// Reasoner
// ===========================================================================

class Reasoner {
  /**
   * @param {object|object[]} rootOntology a protege-js OWLOntology, an array of
   *        axioms, or an array of ontologies
   * @param {Configuration} [configuration]
   */
  constructor(rootOntology, configuration) {
    this.configuration = configuration instanceof Configuration ? configuration : new Configuration(configuration || {});
    this.rootOntology = rootOntology;
    this.descriptionGraphs = new Set();

    /** @type {Array<{axiom:object, isAdd:boolean}>} */
    this.pendingChanges = [];

    this.interruptFlag = new InterruptFlag(this.configuration.individualTaskTimeout);

    this.objectPropertyInclusionManager = null;
    this.dlOntology = null;
    this.prefixes = null;
    this.tableau = null;

    /** @type {boolean|null} tri-state cache */
    this.isConsistentCache = null;
    this.atomicConceptHierarchy = null;
    this.objectRoleHierarchy = null;
    this.dataRoleHierarchy = null;

    this.directObjectRoleDomains = new Map();
    this.directObjectRoleRanges = new Map();
    this.directDataRoleDomains = new Map();
    /** @type {Map<HierarchyNode, Set<HierarchyNode>>} */
    this.directDisjointClasses = new Map();

    /**
     * Memoised `getDirectSuperConceptNodes` results, keyed by `Individual.iri`.
     *
     * This is the single most expensive query in the port: without
     * `InstanceManager`, computing one individual's direct types costs one
     * tableau satisfiability test per candidate hierarchy node, and
     * `getInstances(C, true)` recomputes that for EVERY individual, once per
     * class queried. Measured on `iao.owl` (20 individuals): 5 `getInstances`
     * calls cost 2200 tableau runs, whereas all 20 individuals' direct types
     * cost only 440 — a 5x redundancy that grows with the number of classes
     * asked about. Caching removes it.
     *
     * Soundness rests on two verified properties (see
     * `scripts/smoke-incremental.js` and the probe that established them):
     *   - `getDirectSuperConceptNodes` is IDEMPOTENT — repeated calls agree, so
     *     the `isSatisfiable` tests leave no residue in the permanent tables;
     *   - every mutation path (`clearState`, `flush`, incremental ABox update)
     *     calls `clearInferenceCaches()`, which drops this map.
     *
     * @type {Map<string, Set<HierarchyNode>>}
     */
    this.directSuperConceptNodesCache = new Map();

    /**
     * Completion flags for the three precompute entry points, plus the
     * same-as equivalence-class cache they populate.
     *
     * These mirror HermiT's `m_isRealisedCurrently` / `m_instanceManager`. They
     * are consulted by `isPrecomputed(...)` and by `getSameIndividuals`, so they
     * MUST be reset whenever the answers they vouch for can change — i.e. in
     * `clearInferenceCaches()`. Before this was fixed they were only ever SET,
     * never cleared, so after an incremental ABox flush `isPrecomputed` kept
     * reporting `true` over a stale cache and `getSameIndividuals` returned the
     * pre-flush equivalence classes (proved reachable: retracting
     * `DifferentIndividuals(a b)` and asserting `SameIndividual(a b)`, the
     * flushed reasoner still answered `{a}` where a fresh one answers `{a, b}`).
     *
     * @type {boolean}
     */
    this._realisationCompleted = false;
    /** @type {boolean} */
    this._propertyRealisationCompleted = false;
    /** @type {boolean} */
    this._sameAsComputed = false;
    /** @type {Map<string, NodeSet>|null} */
    this._sameAsEquivalenceClasses = null;

    /** Lazily built by {@link Reasoner#getDatalogEngine}. */
    this.datalogEngine = null;

    this.loadOntology();
  }

  // ---- lifecycle ------------------------------------------------------------

  /** Clausify the root ontology and build the permanent tableau. */
  loadOntology() {
    this.clearState();
    // `warningMonitor` / `ignoreUnsupportedDatatypes` are read off the
    // Configuration by OWLClausification itself; `preprocessAndClausify` only
    // accepts `ontologyIRI` / `firstReplacementIndex` here.
    const clausifier = new OWLClausification(this.configuration);
    const result = clausifier.preprocessAndClausify(this.rootOntology);
    this.objectPropertyInclusionManager = result.objectPropertyInclusionManager;
    this.dlOntology = result.dlOntology;
    this.createPrefixes();
    this.tableau = Reasoner.createTableau(
      this.interruptFlag, this.configuration, this.dlOntology, null, this.prefixes);
  }

  /** Reset every cached inference result. */
  clearState() {
    this.pendingChanges.length = 0;
    this.objectPropertyInclusionManager = null;
    this.dlOntology = null;
    this.prefixes = null;
    this.tableau = null;
    // The materialised ABox belongs to the DLOntology that is being thrown away.
    this.datalogEngine = null;
    this.clearInferenceCaches();
  }

  /**
   * Drop every cached ANSWER while keeping the clausified ontology, the tableau
   * and the prefix map. Called after an incremental ABox update, which leaves the
   * TBox/RBox clauses untouched but can change consistency (and therefore every
   * hierarchy).
   *
   * Divergence from HermiT: its incremental `flush()` nulls only
   * `m_instanceManager` and `m_isConsistent`, leaving `m_atomicConceptHierarchy`
   * and the role hierarchies cached. Those go stale the moment an ABox change
   * makes the ontology inconsistent (every class must then collapse to ⊥), so
   * this port clears them all.
   */
  clearInferenceCaches() {
    this.isConsistentCache = null;
    this.atomicConceptHierarchy = null;
    this.objectRoleHierarchy = null;
    this.dataRoleHierarchy = null;
    this.directObjectRoleDomains = new Map();
    this.directObjectRoleRanges = new Map();
    this.directDataRoleDomains = new Map();
    this.directDisjointClasses = new Map();
    // Per-individual type answers go stale with the hierarchy they were computed
    // against — and an ABox change can make the ontology inconsistent, in which
    // case every individual's types collapse to the top node.
    //
    // PROVEN LOAD-BEARING: with this line disabled, section 19 of
    // `scripts/smoke-incremental.js` reports 11 stale answers (e.g. after
    // retracting `A(a)`, `getTypes(a,true)` still yields `[A]`).
    this.directSuperConceptNodesCache = new Map();
    // The precompute completion flags and the same-as equivalence-class cache
    // vouch for answers about the CURRENT ABox, so they go stale on any change.
    //
    // ROOT CAUSE of the bug this fixes: in HermiT all of this state lives INSIDE
    // `InstanceManager`, and `flush()` simply does `m_instanceManager = null`
    // (Reasoner.java:408), so dropping the manager drops the cache with it. This
    // port has no `InstanceManager`, so the fields were hoisted onto `Reasoner`
    // directly — and orphaned from the reset that used to cover them. Any future
    // field hoisted the same way must be added here too.
    //
    // PROVEN LOAD-BEARING: with these lines disabled, retracting
    // `DifferentIndividuals(a b)` and asserting `SameIndividual(a b)` leaves the
    // flushed reasoner answering `getSameIndividuals(a) === {a}` where a fresh
    // reasoner over the mutated ontology answers `{a, b}`, and
    // `isPrecomputed(SAME_INDIVIDUAL)` / `isPrecomputed(CLASS_ASSERTIONS)` keep
    // reporting `true` over the stale cache. See `test/same-as-cache.test.js`.
    this._realisationCompleted = false;
    this._propertyRealisationCompleted = false;
    this._sameAsComputed = false;
    this._sameAsEquivalenceClasses = null;
    // An incremental ABox flush keeps `dlOntology` alive but changes its ground
    // facts, so a previously materialised ABox is stale. Dropping the engine (not
    // just its cache) forces a fresh materialisation on next use.
    this.datalogEngine = null;
  }

  /** Release resources. (The JS `InterruptFlag` has no `dispose()`.) */
  dispose() {
    this.clearState();
  }

  /** Ask a running reasoning task to abort. */
  interrupt() {
    this.interruptFlag.interrupt();
  }

  /**
   * Build the prefix map used when printing IRIs. Mirrors HermiT's
   * `createPrefixes()`: semantic-web prefixes first, then one internal prefix
   * per individual IRI, then the ontology IRI as the default prefix, then
   * whatever the source document declared.
   */
  createPrefixes() {
    const prefixes = new Prefixes();
    prefixes.declareSemanticWebPrefixes();

    const individualIRIs = new Set();
    const anonIndividualIRIs = new Set();
    for (const individual of this.dlOntology.allIndividuals) {
      Reasoner._addIRI(individual.iri, individual.isAnonymous() ? anonIndividualIRIs : individualIRIs);
    }
    prefixes.declareInternalPrefixes(individualIRIs, anonIndividualIRIs);
    prefixes.declareDefaultPrefix(`${this.dlOntology.ontologyIRI || 'urn:hermit:kb'}#`);

    // Document-format prefixes, if the source ontology carries any.
    const declared = this._documentPrefixes();
    for (const [prefixName, prefixIRI] of declared) {
      if (prefixes.getPrefixName(prefixIRI) !== undefined) continue;
      try {
        prefixes.declarePrefix(prefixName, prefixIRI);
      } catch (err) {
        // A conflicting or malformed prefix is not worth failing over.
      }
    }

    this.prefixes = prefixes;
    return prefixes;
  }

  /** `uri` → the namespace ending at its last `#`, unless it is internal. */
  static _addIRI(uri, prefixIRIs) {
    if (!Prefixes.isInternalIRI(uri)) {
      const lastHash = uri.lastIndexOf('#');
      if (lastHash !== -1) prefixIRIs.add(uri.substring(0, lastHash + 1));
    }
  }

  _documentPrefixes() {
    const out = new Map();
    const sources = [];
    const ontology = this.rootOntology;
    if (Array.isArray(ontology)) {
      for (const o of ontology) if (o && typeof o === 'object') sources.push(o);
    } else if (ontology && typeof ontology === 'object') {
      sources.push(ontology);
    }
    for (const o of sources) {
      const candidates = [
        o.prefixes,
        o._prefixes,
        typeof o.getPrefixes === 'function' ? o.getPrefixes() : null,
        o.documentFormat && o.documentFormat.prefixes,
        o.manager && o.manager.documentFormats
      ];
      for (const c of candidates) {
        if (!c) continue;
        const entries = c instanceof Map ? c.entries() : Object.entries(c);
        for (const [name, iri] of entries) {
          if (typeof iri !== 'string') continue;
          const prefixName = name.endsWith(':') ? name : `${name}:`;
          if (!out.has(prefixName)) out.set(prefixName, iri);
        }
      }
    }
    return out;
  }

  // ---- accessors ------------------------------------------------------------

  getReasonerName() { return REASONER_NAME; }
  getReasonerVersion() { return REASONER_VERSION; }
  getRootOntology() { return this.rootOntology; }
  /**
   * The factory used to build entities, class expressions and axioms. HermiT's
   * `Reasoner.getDataFactory()` returns the OWL API's `OWLDataFactory`; the
   * closest analogue here is our own expression/axiom factory module
   * (`owl/OWLExpressions`, also exported as `E` / `OWLExpressions`). It is a
   * stateless module (not tied to a `m_rootOntology`), so the same instance is
   * returned for every call and every reasoner.
   */
  getDataFactory() { return E; }
  getTimeOut() { return this.configuration.individualTaskTimeout; }
  getIndividualNodeSetPolicy() { return this.configuration.individualNodeSetPolicy; }
  getFreshEntityPolicy() { return this.configuration.freshEntityPolicy; }
  getPrefixes() { return this.prefixes; }
  getDLOntology() { return this.dlOntology; }
  getTableauStatistics() { return this.tableau ? this.tableau.statistics : null; }
  getConfiguration() { return this.configuration.clone(); }
  getBufferingMode() { return this.configuration.bufferChanges ? 'BUFFERING' : 'NON_BUFFERING'; }

  // ---- conjunctive query answering ------------------------------------------

  /**
   * The {@link DatalogEngine} over the clausified ontology, built on first use.
   *
   * Building it does NOT materialise anything — `DatalogEngine.materialize()` is
   * called lazily by the first `ConjunctiveQuery`. The engine is dropped by
   * `clearState()` and `clearInferenceCaches()`, so it can never outlive the
   * `DLOntology` it was built from.
   *
   * @returns {DatalogEngine}
   * @throws {Error} if the ontology contains a clause with a disjunctive head
   *   (query answering requires a Horn ontology).
   */
  getDatalogEngine() {
    if (this.datalogEngine === null) {
      if (this.dlOntology === null) this.loadOntology();
      this.datalogEngine = new DatalogEngine(this.dlOntology);
    }
    return this.datalogEngine;
  }

  /**
   * Build a conjunctive query `q(answerTerms) ← queryAtoms[0] ∧ … ∧ queryAtoms[n]`.
   *
   * The atoms are DL-layer atoms (`createAtom(internAtomicConcept(iri), …)`),
   * not OWL objects — see `../model/Atom.js`. Constructing the query
   * materialises the ABox, so an inconsistent ontology throws here.
   *
   * @param {Atom[]} queryAtoms the body conjunction
   * @param {Term[]} answerTerms one per answer column
   * @returns {ConjunctiveQuery}
   */
  createConjunctiveQuery(queryAtoms, answerTerms) {
    return new ConjunctiveQuery(this.getDatalogEngine(), queryAtoms, answerTerms);
  }

  /**
   * Convenience: build the query and return its distinct answers.
   *
   * @param {Atom[]} queryAtoms
   * @param {Term[]} answerTerms
   * @returns {Term[][]} one array of Terms per answer
   */
  answerQuery(queryAtoms, answerTerms) {
    const collector = new CollectingQueryResultCollector();
    this.createConjunctiveQuery(queryAtoms, answerTerms).evaluate(collector);
    return collector.results;
  }

  /**
   * As {@link Reasoner#answerQuery}, but answers are rendered as IRI / literal
   * strings — the shape that is easy to assert on and to serialise.
   *
   * @param {Atom[]} queryAtoms
   * @param {Term[]} answerTerms
   * @returns {string[][]}
   */
  answerQueryAsStrings(queryAtoms, answerTerms) {
    const collector = new CollectingQueryResultCollector();
    this.createConjunctiveQuery(queryAtoms, answerTerms).evaluate(collector);
    return collector.toArrayOfStrings();
  }

  /**
   * Build a query from a readable spec instead of hand-assembled atoms.
   *
   *   reasoner.createQuery({
   *     select: ['?X'],
   *     where: [{ objectProperty: EX + 'R', subject: '?X', object: EX + 'a' }]
   *   })
   *
   * See `../datalog/QuerySpec.js` for the full spec grammar. `select` is
   * optional and defaults to every body variable in first-appearance order.
   *
   * @param {{select?: Array, where: Array}} spec
   * @returns {ConjunctiveQuery}
   */
  createQuery(spec) {
    const { queryAtoms, answerTerms } = buildQuerySpec(spec);
    return this.createConjunctiveQuery(queryAtoms, answerTerms);
  }

  /**
   * Convenience: build a query from a spec and return its distinct answers as
   * arrays of IRI / literal strings.
   *
   * @param {{select?: Array, where: Array}} spec
   * @returns {string[][]}
   */
  query(spec) {
    const collector = new CollectingQueryResultCollector();
    this.createQuery(spec).evaluate(collector);
    return collector.toArrayOfStrings();
  }

  // ---- incremental changes --------------------------------------------------

  getPendingAxiomAdditions() {
    return this.pendingChanges.filter((c) => c.isAdd).map((c) => c.axiom);
  }

  getPendingAxiomRemovals() {
    return this.pendingChanges.filter((c) => !c.isAdd).map((c) => c.axiom);
  }

  getPendingChanges() { return this.pendingChanges.slice(); }

  /**
   * Record an ontology change. Accepts `{axiom, isAdd}`, protege-js-style
   * `{type:'AddAxiom'|'RemoveAxiom', axiom}`, or a bare axiom (treated as an
   * addition).
   */
  applyChange(change) {
    if (change === null || change === undefined) return this;
    if (change.axiomType !== undefined && change.axiom === undefined) {
      this.pendingChanges.push({ axiom: change, isAdd: true });
      return this;
    }
    const isAdd = change.isAdd !== undefined
      ? !!change.isAdd
      : change.type !== 'RemoveAxiom' && change.type !== 'RemoveOntology';
    this.pendingChanges.push({ axiom: change.axiom, isAdd });
    return this;
  }

  applyChanges(changes) {
    for (const change of changes || []) this.applyChange(change);
    return this;
  }

  /**
   * Recompute everything if there are pending changes.
   *
   * When every pending change is an ABox assertion over entities that already
   * exist (`canProcessPendingChangesIncrementally`), only the ground facts are
   * re-clausified and spliced into the existing `DLOntology` via
   * `ReducedABoxOnlyClausification`; the TBox/RBox clauses and the tableau's
   * compiled clause index are reused. Otherwise the whole ontology is rebuilt.
   */
  flush() {
    if (this.pendingChanges.length === 0) return;
    if (this.canProcessPendingChangesIncrementally()) this._flushIncrementally();
    else this.loadOntology();
    this.pendingChanges.length = 0;
  }

  /**
   * Whether the pending changes can be applied by re-clausifying only the ABox.
   *
   * Port of HermiT's `Reasoner.canProcessPendingChangesIncrementally`. Returns
   * true when every change is either a declaration of an entity that already
   * occurs in the loaded ontology, or an individual axiom (assertion) whose
   * classes/properties/individuals all already occur. Nominals disqualify the
   * fast path: with nominals the ABox is woven into the TBox clauses during
   * clausification, so a fact change can alter the clause set.
   *
   * @returns {boolean}
   */
  canProcessPendingChangesIncrementally() {
    if (this.dlOntology === null) return false;
    if (this.dlOntology.hasNominals) return false;

    for (const change of this.pendingChanges) {
      const axiom = change.axiom;
      if (axiom === null || axiom === undefined) return false;

      const type = axiomTypeOf(axiom);
      // A SWRL rule (or any non-axiom change) can introduce arbitrary clauses.
      if (type === null || type === 'SWRLRule') return false;

      if (!E.NON_LOGICAL_AXIOM_TYPES.has(type)) {
        // Logical axiom: must be an individual axiom, and every entity it names
        // must already be in the signature.
        if (!INDIVIDUAL_AXIOM_TYPES.has(type)) return false;
        if (!this._assertionEntitiesDefined(axiom)) return false;
      } else if (type === E.AxiomType.DECLARATION) {
        // Declaring an entity that already exists is a no-op for the clauses;
        // declaring a NEW one would need a signature entry classification reads.
        const entity = axiom.entity;
        if (!this.isDefined(entity) && !Prefixes.isInternalIRI(E.iriString(entity))) return false;
      }
      // Other non-logical axioms (annotations) carry no DL semantics.
    }
    return true;
  }

  /**
   * Whether every class/property/individual an ABox assertion mentions already
   * occurs in the loaded ontology. Mirrors the per-shape `isDefined` checks in
   * HermiT's gate, but expressed over the shapes `ReducedABoxOnlyClausification`
   * can actually translate — so the gate and the translator cannot disagree.
   */
  _assertionEntitiesDefined(axiom) {
    const type = axiomTypeOf(axiom);

    // Individuals named directly by the assertion.
    const individuals = [];
    if (type === E.AxiomType.SAME_INDIVIDUAL || type === E.AxiomType.DIFFERENT_INDIVIDUALS) {
      individuals.push(...(E.operandsOf(axiom).length > 0 ? E.operandsOf(axiom) : axiom.individuals));
    } else if (type === E.AxiomType.CLASS_ASSERTION) {
      individuals.push(axiom.individual);
    } else {
      individuals.push(axiom.subject, axiom.object);
    }
    for (const ind of individuals) {
      if (ind === undefined || ind === null) continue;
      // A literal object (data property assertion) is not an individual.
      if (ind.lexicalValue !== undefined && ind.entityType === undefined) continue;
      if (!this.isDefined(ind)) return false;
    }

    // The property of a (data/object) property assertion.
    if (axiom.property !== undefined) {
      if (!this._propertyDefined(axiom.property)) return false;
    }

    // The class expression of a class assertion: must be a shape the reduced
    // clausifier handles, and every entity inside it must already exist.
    if (type === E.AxiomType.CLASS_ASSERTION) {
      return this._classAssertionIncremental(axiom.classExpression);
    }
    return true;
  }

  /** Whether a (possibly inverse) object property or a data property is defined. */
  _propertyDefined(propertyExpression) {
    if (propertyExpression === undefined || propertyExpression === null) return true;
    if (E.isAnonymousProperty(propertyExpression)) {
      return this.isDefined(E.namedPropertyOf(propertyExpression));
    }
    return this.isDefined(propertyExpression);
  }

  /**
   * Whether `ClassAssertion(D, …)` with class expression `D` is translatable to
   * a single ground fact over already-defined entities. Recurses through one
   * level of complement, matching `_classAssertionAtom`.
   */
  _classAssertionIncremental(description) {
    if (description === undefined || description === null) return false;
    let t = E.exprType(description);
    if (t === T.OBJECT_COMPLEMENT_OF) {
      description = E.operandOf(description);
      t = E.exprType(description);
    }
    if (!INCREMENTAL_CLASS_EXPRESSION_TYPES.has(t)) return false;

    if (t === T.OWL_CLASS) return this.isDefined(description) || Prefixes.isInternalIRI(E.iriString(description));
    if (t === T.OBJECT_HAS_SELF) return this._propertyDefined(description.property);
    if (t === T.OBJECT_HAS_VALUE) {
      return this._propertyDefined(description.property) && this.isDefined(description.filler);
    }
    if (t === T.DATA_HAS_VALUE) return this._propertyDefined(description.property);
    if (t === T.DATA_SOME_VALUES_FROM) {
      const filler = description.filler;
      if (E.exprType(filler) !== T.DATA_ONE_OF || E.operandsOf(filler).length !== 1) return false;
      return this._propertyDefined(description.property);
    }
    return false;
  }

  /**
   * Apply the pending changes by re-clausifying only the ABox. Rebuilds the
   * `DLOntology`'s fact sets and individuals, then rebuilds the tableau on the
   * SAME clauses (so the compiled hyperresolution index is cheap to recreate)
   * and drops every cached answer.
   */
  _flushIncrementally() {
    const original = this.dlOntology;

    const clausifier = new ReducedABoxOnlyClausification({
      allAtomicConcepts: original.allAtomicConcepts,
      allAtomicObjectRoles: original.allAtomicObjectRoles,
      allAtomicDataRoles: original.allAtomicDataRoles,
      definedDatatypeIRIs: original.definedDatatypesIRIs,
      allUnknownDatatypeRestrictions: original.allUnknownDatatypeRestrictions,
      ignoreUnsupportedDatatypes: this.configuration.ignoreUnsupportedDatatypes,
      warningMonitor: this.configuration.warningMonitor
    });

    // Start from the CURRENT facts, then add/remove each change's facts.
    const positiveFacts = new Set(original.positiveFacts);
    const negativeFacts = new Set(original.negativeFacts);
    const allIndividuals = new Set(original.allIndividuals);

    for (const change of this.pendingChanges) {
      const axiom = change.axiom;
      // Declarations of existing entities change nothing at the fact level.
      if (axiomTypeOf(axiom) === E.AxiomType.DECLARATION) continue;

      clausifier.clausify([axiom]);
      for (const fact of clausifier.getPositiveFacts()) {
        if (change.isAdd) positiveFacts.add(fact);
        else positiveFacts.delete(fact);
      }
      for (const fact of clausifier.getNegativeFacts()) {
        if (change.isAdd) negativeFacts.add(fact);
        else negativeFacts.delete(fact);
      }
    }

    // Individuals: the union of those still referenced by a surviving fact plus
    // the ones the reduced clausifier saw. (Removals leave the individual in the
    // signature, which is harmless — an unreferenced individual simply has no
    // facts, exactly as a declaration-only individual does.)
    for (const ind of clausifier.getAllIndividuals()) allIndividuals.add(ind);

    this.dlOntology = new DLOntology({
      ontologyIRI: original.ontologyIRI,
      dlClauses: original.dlClauses,
      positiveFacts: [...positiveFacts],
      negativeFacts: [...negativeFacts],
      atomicConcepts: original.allAtomicConcepts,
      atomicObjectRoles: original.allAtomicObjectRoles,
      complexObjectRoles: original.complexObjectRoles,
      atomicDataRoles: original.allAtomicDataRoles,
      allUnknownDatatypeRestrictions: original.allUnknownDatatypeRestrictions,
      hasUnknownDatatypeRestrictions: original.hasUnknownDatatypeRestrictions,
      definedDatatypesIRIs: original.definedDatatypesIRIs,
      individuals: allIndividuals,
      hasInverseRoles: original.hasInverseRoles,
      hasAtMostRestrictions: original.hasAtMostRestrictions,
      hasNominals: original.hasNominals,
      hasDatatypes: original.hasDatatypes
    });

    // Rebuild the tableau on the same clauses but the new facts, reusing the
    // monitor and expansion strategy HermiT reuses.
    this.tableau = Reasoner.createTableau(
      this.interruptFlag, this.configuration, this.dlOntology, null, this.prefixes);

    this.clearInferenceCaches();
  }

  flushChangesIfRequired() {
    if (!this.configuration.bufferChanges && this.pendingChanges.length > 0) this.flush();
  }

  // ---- preconditions --------------------------------------------------------

  /**
   * HermiT's `checkPreConditions(...)`: flush, reject fresh entities when the
   * policy says so, and reject an inconsistent ontology when configured to.
   */
  checkPreConditions(...objects) {
    this.flushChangesIfRequired();
    if (objects.length > 0) this.throwFreshEntityExceptionIfNecessary(objects);
    this.throwInconsistentOntologyExceptionIfNecessary();
  }

  throwInconsistentOntologyExceptionIfNecessary() {
    if (!this.isConsistent() && this.configuration.throwInconsistentOntologyException) {
      throw new InconsistentOntologyException();
    }
  }

  throwFreshEntityExceptionIfNecessary(objects) {
    if (this.configuration.freshEntityPolicy !== FRESH_ENTITY_POLICY.DISALLOW) return;
    const undeclared = new Set();
    for (const entity of this._undeclaredEntities(objects)) undeclared.add(entity);
    if (undeclared.size > 0) throw new FreshEntitiesException(undeclared);
  }

  /**
   * Whether any of `objects` mentions an entity that does not occur in the
   * clausified ontology. Mirrors HermiT's `containsFreshEntities`.
   */
  containsFreshEntities(...objects) {
    for (const entity of this._undeclaredEntities(objects)) {
      void entity;
      return true;
    }
    return false;
  }

  _undeclaredEntities(objects) {
    const found = [];
    for (const object of objects) {
      if (object === null || object === undefined) continue;
      const sets = _emptyEntitySets();
      collectEntities(object, sets);
      for (const c of sets.classes) {
        if (!this.isDefined(c) && !Prefixes.isInternalIRI(E.iriString(c))) found.push(c);
      }
      for (const p of sets.objectProperties) {
        if (!this.isDefined(p) && !Prefixes.isInternalIRI(E.iriString(p))) found.push(p);
      }
      for (const p of sets.dataProperties) {
        if (!this.isDefined(p) && !Prefixes.isInternalIRI(E.iriString(p))) found.push(p);
      }
      for (const i of sets.individuals) {
        if (!this.isDefined(i) && !Prefixes.isInternalIRI(E.iriString(i))) found.push(i);
      }
    }
    return found;
  }

  /**
   * Whether `entity` occurs in the clausified ontology. Duck-typed replacement
   * for HermiT's four `isDefined` overloads.
   */
  isDefined(entity) {
    if (entity === null || entity === undefined) return false;
    if (typeof entity === 'string') return false;
    const entityType = entity.entityType
      || (typeof entity.getEntityType === 'function' ? entity.getEntityType() : null);
    switch (entityType) {
      case E.EntityType.CLASS: {
        const concept = H_class(entity);
        return this.dlOntology.containsAtomicConcept(concept)
          || concept === P.THING || concept === P.NOTHING;
      }
      case E.EntityType.OBJECT_PROPERTY: {
        const role = H_objectProperty(entity);
        return this.dlOntology.containsObjectRole(role)
          || role === P.TOP_OBJECT_ROLE || role === P.BOTTOM_OBJECT_ROLE;
      }
      case E.EntityType.DATA_PROPERTY: {
        const role = H_dataProperty(entity);
        return this.dlOntology.containsDataRole(role)
          || role === P.TOP_DATA_ROLE || role === P.BOTTOM_DATA_ROLE;
      }
      case E.EntityType.NAMED_INDIVIDUAL:
        return this.dlOntology.containsIndividual(H_individual(entity));
      case E.EntityType.DATATYPE:
        return true;
      default:
        // Not an entity (a class expression, an axiom, …) — nothing to check.
        return true;
    }
  }

  // ---- precomputation -------------------------------------------------------

  getPrecomputableInferenceTypes() {
    return [
      INFERENCE_TYPE.CLASS_HIERARCHY,
      INFERENCE_TYPE.OBJECT_PROPERTY_HIERARCHY,
      INFERENCE_TYPE.DATA_PROPERTY_HIERARCHY,
      INFERENCE_TYPE.CLASS_ASSERTIONS,
      INFERENCE_TYPE.OBJECT_PROPERTY_ASSERTIONS,
      INFERENCE_TYPE.SAME_INDIVIDUAL
    ];
  }

  isPrecomputed(inferenceType) {
    switch (inferenceType) {
      case INFERENCE_TYPE.CLASS_HIERARCHY: return this.atomicConceptHierarchy !== null;
      case INFERENCE_TYPE.OBJECT_PROPERTY_HIERARCHY: return this.objectRoleHierarchy !== null;
      case INFERENCE_TYPE.DATA_PROPERTY_HIERARCHY: return this.dataRoleHierarchy !== null;
      case INFERENCE_TYPE.CLASS_ASSERTIONS: return this._realisationCompleted;
      case INFERENCE_TYPE.OBJECT_PROPERTY_ASSERTIONS: return this._propertyRealisationCompleted;
      case INFERENCE_TYPE.SAME_INDIVIDUAL: return this._sameAsComputed;
      default: return false;
    }
  }

  precomputeInferences(...inferenceTypes) {
    this.checkPreConditions();
    const prepare = this.configuration.prepareReasonerInferences;
    const doAll = prepare === null || prepare === undefined;
    const wanted = new Set(inferenceTypes);
    const needs = (type, flag) => wanted.has(type) && (doAll || prepare[flag]);

    if (needs(INFERENCE_TYPE.CLASS_HIERARCHY, 'classClassificationRequired')) this.classifyClasses();
    if (needs(INFERENCE_TYPE.OBJECT_PROPERTY_HIERARCHY, 'objectPropertyClassificationRequired')) this.classifyObjectProperties();
    if (needs(INFERENCE_TYPE.DATA_PROPERTY_HIERARCHY, 'dataPropertyClassificationRequired')) this.classifyDataProperties();
    if (needs(INFERENCE_TYPE.CLASS_ASSERTIONS, 'realisationRequired')
      || (this.configuration.individualNodeSetPolicy === INDIVIDUAL_NODE_SET_POLICY.BY_SAME_AS
        && wanted.has(INFERENCE_TYPE.CLASS_ASSERTIONS))) {
      this.precomputeSameAsEquivalenceClasses();
    }
    if (needs(INFERENCE_TYPE.OBJECT_PROPERTY_ASSERTIONS, 'objectPropertyRealisationRequired')) this.realiseObjectProperties();
    return this.getPrecomputableInferenceTypes();
  }

  // ---- consistency ----------------------------------------------------------

  /** Whether the whole ontology (TBox + ABox) has a model. Cached. */
  isConsistent() {
    this.flushChangesIfRequired();
    if (this.isConsistentCache === null) {
      this.isConsistentCache = this.getTableau().isSatisfiable({
        loadPermanentABox: true,
        loadAdditionalABox: true,
        reasoningTaskDescription: 'isABoxSatisfiable()'
      });
    }
    return this.isConsistentCache;
  }

  // ---- entailment -----------------------------------------------------------

  isEntailmentCheckingSupported(_axiomType) { return true; }

  /**
   * Whether `axiom` (or every axiom in a set/array of them) follows from the
   * ontology. An inconsistent ontology entails everything.
   */
  isEntailed(axiom) {
    const axioms = (axiom instanceof Set || Array.isArray(axiom)) ? [...axiom] : [axiom];
    this.checkPreConditions(...axioms);
    if (!this.isConsistent()) return true;
    return new EntailmentChecker(this, E).entails(axioms.length === 1 && !Array.isArray(axiom) && !(axiom instanceof Set)
      ? axioms[0] : axioms);
  }

  // ---- class inferences -----------------------------------------------------

  /** @deprecated use {@link Reasoner#classifyClasses} */
  classify() { this.classifyClasses(); }

  /**
   * Build (and cache) the class hierarchy over every non-internal atomic
   * concept plus owl:Thing and owl:Nothing.
   */
  classifyClasses() {
    this.checkPreConditions();
    if (this.atomicConceptHierarchy !== null) return this.atomicConceptHierarchy;

    const relevantAtomicConcepts = new Set([P.THING, P.NOTHING]);
    for (const atomicConcept of this.dlOntology.allAtomicConcepts) {
      if (!Prefixes.isInternalIRI(atomicConcept.iri)) relevantAtomicConcepts.add(atomicConcept);
    }

    if (!this.isConsistent()) {
      this.atomicConceptHierarchy = Hierarchy.emptyHierarchy(relevantAtomicConcepts, P.THING, P.NOTHING);
      return this.atomicConceptHierarchy;
    }

    const total = relevantAtomicConcepts.size;
    this.atomicConceptHierarchy = this._withProgress('Building the class hierarchy...', total,
      (progressMonitor) => Reasoner.classifyAtomicConcepts(
        this.getTableau(), progressMonitor, P.THING, P.NOTHING,
        relevantAtomicConcepts, this.configuration.forceQuasiOrderClassification));
    return this.atomicConceptHierarchy;
  }

  getTopClassNode() {
    this.classifyClasses();
    return this._conceptNodeToNode(this.atomicConceptHierarchy.getTopNode());
  }

  getBottomClassNode() {
    this.classifyClasses();
    return this._conceptNodeToNode(this.atomicConceptHierarchy.getBottomNode());
  }

  /** Whether `classExpression` can have an instance. */
  isSatisfiable(classExpression) {
    this.checkPreConditions(classExpression);
    if (!this.isConsistent()) return false;
    if (E.isNamedClass(classExpression) && this.atomicConceptHierarchy !== null) {
      const concept = H_class(classExpression);
      return this.atomicConceptHierarchy.getNodeForElement(concept)
        !== this.atomicConceptHierarchy.getBottomNode();
    }
    const freshIndividual = E.anonymousIndividual('fresh-individual');
    const assertClassExpression = E.classAssertion(classExpression, freshIndividual);
    const tableau = this.getTableau(assertClassExpression);
    return tableau.isSatisfiable({
      loadAdditionalABox: true,
      reasoningTaskDescription: `isConceptSatisfiable(${classExpression})`
    });
  }

  /** Whether `subClassExpression ⊑ superClassExpression` holds. */
  isSubClassOf(subClassExpression, superClassExpression) {
    this.checkPreConditions(subClassExpression, superClassExpression);
    if (!this.isConsistent()
      || E.isOWLNothing(subClassExpression)
      || E.isOWLThing(superClassExpression)) {
      return true;
    }

    if (E.isNamedClass(subClassExpression) && E.isNamedClass(superClassExpression)) {
      const subconcept = H_class(subClassExpression);
      const superconcept = H_class(superClassExpression);
      if (this.atomicConceptHierarchy !== null
        && !this.containsFreshEntities(subClassExpression, superClassExpression)) {
        const subconceptNode = this.atomicConceptHierarchy.getNodeForElement(subconcept);
        if (subconceptNode !== undefined) {
          return subconceptNode.isEquivalentElement(superconcept)
            || subconceptNode.isAncestorElement(superconcept);
        }
      }
      const tableau = this.getTableau();
      const freshIndividual = createAnonymousIndividual('fresh-individual');
      return !tableau.isSatisfiable({
        loadAdditionalABox: true,
        perTestPositiveFactsNoDependency: [createAtom(subconcept, freshIndividual)],
        perTestNegativeFactsNoDependency: [createAtom(superconcept, freshIndividual)],
        reasoningTaskDescription: `isConceptSubsumedBy(${subconcept}, ${superconcept})`
      });
    }

    const freshIndividual = E.anonymousIndividual('fresh-individual');
    const assertSub = E.classAssertion(subClassExpression, freshIndividual);
    const assertNotSuper = E.classAssertion(
      E.objectComplementOf(superClassExpression), freshIndividual);
    const tableau = this.getTableau(assertSub, assertNotSuper);
    const result = tableau.isSatisfiable({
      loadAdditionalABox: true,
      reasoningTaskDescription: `isConceptSubsumedBy(${subClassExpression}, ${superClassExpression})`
    });
    tableau.clearAdditionalDLOntology();
    return !result;
  }

  getEquivalentClasses(classExpression) {
    return this._conceptNodeToNode(this.getHierarchyNode(classExpression));
  }

  getSuperClasses(classExpression, direct) {
    const node = this.getHierarchyNode(classExpression);
    let result;
    if (direct) {
      result = new Set(node.getParentNodes());
    } else {
      result = new Set(node.getAncestorNodes());
      result.delete(node);
    }
    return this._conceptNodesToNodeSet(result);
  }

  getSubClasses(classExpression, direct) {
    const node = this.getHierarchyNode(classExpression);
    let result;
    if (direct) {
      result = new Set(node.getChildNodes());
    } else {
      result = new Set(node.getDescendantNodes());
      result.delete(node);
    }
    return this._conceptNodesToNodeSet(result);
  }

  /** Every unsatisfiable class, as the single bottom node. */
  getUnsatisfiableClasses() {
    this.classifyClasses();
    return this._conceptNodeToNode(this.atomicConceptHierarchy.getBottomNode());
  }

  getDisjointClasses(classExpression) {
    this.checkPreConditions(classExpression);
    this.classifyClasses();

    if (E.isOWLNothing(classExpression) || !this.isConsistent()) {
      const node = this.atomicConceptHierarchy.getBottomNode();
      return this._conceptNodesToNodeSet(node.getAncestorNodes());
    }
    if (E.isOWLThing(classExpression)) {
      return this._conceptNodesToNodeSet([this.atomicConceptHierarchy.getBottomNode()]);
    }
    if (E.isNamedClass(classExpression)) {
      const node = this.getHierarchyNode(classExpression);
      if (node === null || node === undefined || node === this.atomicConceptHierarchy.getTopNode()) {
        // A fresh concept: only owl:Nothing is disjoint from it.
        return new NodeSet(new Node(E.owlNothing()));
      }
      if (node === this.atomicConceptHierarchy.getBottomNode()) {
        return this._conceptNodesToNodeSet(node.getAncestorNodes());
      }
      const result = new Set();
      for (const directDisjoint of this.getDisjointConceptNodes(node)) {
        for (const descendant of directDisjoint.getDescendantNodes()) result.add(descendant);
      }
      return this._conceptNodesToNodeSet(result);
    }
    const complement = E.objectComplementOf(classExpression);
    const equivalentToComplement = this.getEquivalentClasses(complement);
    const subsDisjoint = this.getSubClasses(complement, false);
    const result = new NodeSet();
    if (!equivalentToComplement.isEmpty()) result.addNode(equivalentToComplement);
    for (const node of subsDisjoint.getNodes()) result.addNode(node);
    return result;
  }

  /**
   * The nodes directly disjoint from `node`. Cached, because the answer needs a
   * full `getHierarchyNode(¬C)` computation.
   */
  getDisjointConceptNodes(node) {
    const cached = this.directDisjointClasses.get(node);
    if (cached !== undefined) return cached;

    const negated = E.objectComplementOf(E.owlClass(node.getRepresentative().iri));
    const equivalentToComplement = this.getHierarchyNode(negated);
    let result;
    for (const equiv of equivalentToComplement.getEquivalentElements()) {
      if (!Prefixes.isInternalIRI(equiv.iri)) {
        result = new Set([this.atomicConceptHierarchy.getNodeForElement(equiv)]);
        this.directDisjointClasses.set(node, result);
        return result;
      }
    }
    result = equivalentToComplement.getChildNodes();
    this.directDisjointClasses.set(node, result);
    return result;
  }

  precomputeDisjointClasses() {
    this.checkPreConditions();
    if (!this.isConsistent()) return;
    this.classifyClasses();
    if (this.directDisjointClasses.size >= this.atomicConceptHierarchy.getAllNodesSet().size - 2) return;

    const nodes = new Set(this.atomicConceptHierarchy.getAllNodesSet());
    nodes.delete(this.atomicConceptHierarchy.getTopNode());
    nodes.delete(this.atomicConceptHierarchy.getBottomNode());
    for (const key of this.directDisjointClasses.keys()) nodes.delete(key);

    this._withProgress('Compute disjoint classes', nodes.size, () => {
      for (const node of nodes) this.getDisjointConceptNodes(node);
    });
  }

  /**
   * Where `classExpression` sits in the class hierarchy. A complex expression is
   * positioned by introducing `internal:query-concept ≡ ce` as an additional
   * ontology and searching for its parents/children.
   *
   * @returns {HierarchyNode}
   */
  getHierarchyNode(classExpression) {
    this.checkPreConditions(classExpression);
    this.classifyClasses();
    if (!this.isConsistent()) return this.atomicConceptHierarchy.getBottomNode();

    if (E.isNamedClass(classExpression)) {
      const atomicConcept = H_class(classExpression);
      let node = this.atomicConceptHierarchy.getNodeForElement(atomicConcept);
      if (node === undefined) {
        node = new HierarchyNode(
          atomicConcept,
          new Set([atomicConcept]),
          new Set([this.atomicConceptHierarchy.getTopNode()]),
          new Set([this.atomicConceptHierarchy.getBottomNode()]));
      }
      return node;
    }

    const queryConcept = E.owlClass(IRI_QUERY_CONCEPT);
    const queryAtomicConcept = P.internAtomicConcept(IRI_QUERY_CONCEPT);
    const classDefinitionAxiom = E.equivalentClasses([queryConcept, classExpression]);
    const tableau = this.getTableau(classDefinitionAxiom);
    const hierarchyRelation = {
      doesSubsume: (parent, child) => {
        const freshIndividual = createAnonymousIndividual('fresh-individual');
        return !tableau.isSatisfiable({
          loadAdditionalABox: true,
          perTestPositiveFactsNoDependency: [createAtom(child, freshIndividual)],
          perTestNegativeFactsDummyDependency: [createAtom(parent, freshIndividual)],
          reasoningTaskDescription: `isConceptSubsumedBy(${child}, ${parent})`
        });
      }
    };
    const extendedHierarchy = HierarchySearch.findPosition(
      hierarchyRelation, queryAtomicConcept,
      this.atomicConceptHierarchy.getTopNode(),
      this.atomicConceptHierarchy.getBottomNode());
    tableau.clearAdditionalDLOntology();
    return extendedHierarchy;
  }

  // ---- object property inferences -------------------------------------------

  classifyObjectProperties() {
    this.checkPreConditions();
    if (this.objectRoleHierarchy !== null) return this.objectRoleHierarchy;

    const relevantObjectRoles = new Set();
    for (const atomicRole of this.dlOntology.allAtomicObjectRoles) {
      if (atomicRole !== P.TOP_OBJECT_ROLE && atomicRole !== P.BOTTOM_OBJECT_ROLE) {
        relevantObjectRoles.add(atomicRole);
        if (this.dlOntology.hasInverseRoles) relevantObjectRoles.add(atomicRole.getInverse());
      }
    }

    if (!this.isConsistent()) {
      relevantObjectRoles.add(P.TOP_OBJECT_ROLE);
      relevantObjectRoles.add(P.BOTTOM_OBJECT_ROLE);
      this.objectRoleHierarchy = Hierarchy.emptyHierarchy(
        relevantObjectRoles, P.TOP_OBJECT_ROLE, P.BOTTOM_OBJECT_ROLE);
      return this.objectRoleHierarchy;
    }

    // Each role R is represented by a fresh concept `internal:prop#R ≡ ∃R.F`,
    // so role subsumption becomes concept subsumption.
    const conceptsForRoles = new Map();
    const rolesForConcepts = new Map();
    const additionalAxioms = [];
    const freshConcept = E.owlClass(IRI_FRESH_CONCEPT);

    for (const objectRole of relevantObjectRoles) {
      let conceptForRole;
      let objectPropertyExpression;
      if (objectRole instanceof P.AtomicRole) {
        conceptForRole = P.internAtomicConcept(`internal:prop#${objectRole.iri}`);
        objectPropertyExpression = E.objectProperty(objectRole.iri);
      } else {
        conceptForRole = P.internAtomicConcept(`internal:prop#inv#${objectRole.inverseRole.iri}`);
        objectPropertyExpression = E.objectInverseOf(E.objectProperty(objectRole.inverseRole.iri));
      }
      additionalAxioms.push(E.equivalentClasses([
        E.owlClass(conceptForRole.iri),
        E.objectSomeValuesFrom(objectPropertyExpression, freshConcept)
      ]));
      conceptsForRoles.set(objectRole, conceptForRole);
      rolesForConcepts.set(conceptForRole, objectRole);
    }

    conceptsForRoles.set(P.TOP_OBJECT_ROLE, P.THING);
    rolesForConcepts.set(P.THING, P.TOP_OBJECT_ROLE);
    conceptsForRoles.set(P.BOTTOM_OBJECT_ROLE, P.NOTHING);
    rolesForConcepts.set(P.NOTHING, P.BOTTOM_OBJECT_ROLE);

    additionalAxioms.push(E.classAssertion(freshConcept, E.anonymousIndividual('fresh-individual')));

    const tableau = this.getTableau(additionalAxioms);
    try {
      const atomicConceptHierarchyForRoles = this._withProgress(
        'Classifying object properties...', relevantObjectRoles.size,
        (progressMonitor) => Reasoner.classifyAtomicConceptsForRoles(
          tableau, progressMonitor,
          conceptsForRoles.get(P.TOP_OBJECT_ROLE),
          conceptsForRoles.get(P.BOTTOM_OBJECT_ROLE),
          new Set(rolesForConcepts.keys()),
          this.dlOntology.hasInverseRoles,
          conceptsForRoles, rolesForConcepts,
          this.configuration.forceQuasiOrderClassification));

      const transformer = {
        transform: (atomicConcept) => rolesForConcepts.get(atomicConcept),
        determineRepresentative: (oldRepresentative) => rolesForConcepts.get(oldRepresentative)
      };
      this.objectRoleHierarchy = atomicConceptHierarchyForRoles.transform(transformer, null);
    } finally {
      tableau.clearAdditionalDLOntology();
    }
    return this.objectRoleHierarchy;
  }

  getTopObjectPropertyNode() {
    this.classifyObjectProperties();
    return this._objectPropertyNodeToNode(this.objectRoleHierarchy.getTopNode());
  }

  getBottomObjectPropertyNode() {
    this.classifyObjectProperties();
    return this._objectPropertyNodeToNode(this.objectRoleHierarchy.getBottomNode());
  }

  isSubObjectPropertyExpressionOf(subPropertyExpression, superPropertyExpression) {
    // The chain variant.
    if (Array.isArray(subPropertyExpression)) {
      return this._isSubPropertyChainOf(subPropertyExpression, superPropertyExpression);
    }

    this.checkPreConditions(subPropertyExpression, superPropertyExpression);
    if (!this.isConsistent()
      || E.isBottomObjectProperty(E.namedPropertyOf(subPropertyExpression))
      || E.isTopObjectProperty(E.namedPropertyOf(superPropertyExpression))) {
      return true;
    }
    const subrole = H_role(subPropertyExpression);
    const superrole = H_role(superPropertyExpression);
    if (this.objectRoleHierarchy !== null
      && !this.containsFreshEntities(subPropertyExpression, superPropertyExpression)) {
      const subroleNode = this.objectRoleHierarchy.getNodeForElement(subrole);
      if (subroleNode !== undefined) {
        return subroleNode.isEquivalentElement(superrole) || subroleNode.isAncestorElement(superrole);
      }
    }

    // Pseudo-nominal trick: R ⊑ S iff {R(a,b), b:P, a:∀S.¬P} is unsatisfiable.
    const pseudoNominal = E.owlClass(IRI_PSEUDO_NOMINAL);
    const allSuperNotPseudoNominal = E.objectAllValuesFrom(
      superPropertyExpression, E.objectComplementOf(pseudoNominal));
    const freshIndividualA = E.anonymousIndividual('fresh-individual-A');
    const freshIndividualB = E.anonymousIndividual('fresh-individual-B');
    const tableau = this.getTableau(
      E.objectPropertyAssertion(subPropertyExpression, freshIndividualA, freshIndividualB),
      E.classAssertion(pseudoNominal, freshIndividualB),
      E.classAssertion(allSuperNotPseudoNominal, freshIndividualA));
    const result = tableau.isSatisfiable({
      loadAdditionalABox: true,
      reasoningTaskDescription: `isRoleSubsumedBy(${subrole}, ${superrole}, true)`
    });
    tableau.clearAdditionalDLOntology();
    return !result;
  }

  /** `R1∘…∘Rn ⊑ S`. */
  _isSubPropertyChainOf(subPropertyChain, superPropertyExpression) {
    this.checkPreConditions(...subPropertyChain, superPropertyExpression);
    if (!this.isConsistent() || E.isTopObjectProperty(E.namedPropertyOf(superPropertyExpression))) {
      return true;
    }
    const pseudoNominal = E.owlClass(IRI_PSEUDO_NOMINAL);
    const allSuperNotPseudoNominal = E.objectAllValuesFrom(
      superPropertyExpression, E.objectComplementOf(pseudoNominal));
    const additionalAxioms = [];
    let axiomIndex = 0;
    for (const sub of subPropertyChain) {
      const first = E.anonymousIndividual(`fresh-individual-${axiomIndex}`);
      const second = E.anonymousIndividual(`fresh-individual-${axiomIndex + 1}`);
      additionalAxioms.push(E.objectPropertyAssertion(sub, first, second));
      axiomIndex++;
    }
    const freshIndividual0 = E.anonymousIndividual('fresh-individual-0');
    const freshIndividualN = E.anonymousIndividual(`fresh-individual-${subPropertyChain.length}`);
    additionalAxioms.push(E.classAssertion(pseudoNominal, freshIndividualN));
    additionalAxioms.push(E.classAssertion(allSuperNotPseudoNominal, freshIndividual0));
    const tableau = this.getTableau(additionalAxioms);
    const result = tableau.isSatisfiable({
      loadAdditionalABox: true,
      reasoningTaskDescription: 'subproperty chain subsumption'
    });
    tableau.clearAdditionalDLOntology();
    return !result;
  }

  getSuperObjectProperties(propertyExpression, direct) {
    const node = this.getObjectPropertyHierarchyNode(propertyExpression);
    let result;
    if (direct) {
      result = new Set(node.getParentNodes());
    } else {
      result = new Set(node.getAncestorNodes());
      result.delete(node);
    }
    return this._objectPropertyNodesToNodeSet(result);
  }

  getSubObjectProperties(propertyExpression, direct) {
    const node = this.getObjectPropertyHierarchyNode(propertyExpression);
    let result;
    if (direct) {
      result = new Set(node.getChildNodes());
    } else {
      result = new Set(node.getDescendantNodes());
      result.delete(node);
    }
    return this._objectPropertyNodesToNodeSet(result);
  }

  getEquivalentObjectProperties(propertyExpression) {
    return this._objectPropertyNodeToNode(this.getObjectPropertyHierarchyNode(propertyExpression));
  }

  getInverseObjectProperties(propertyExpression) {
    return this.getEquivalentObjectProperties(E.inversePropertyOf(propertyExpression));
  }

  getObjectPropertyDomains(propertyExpression, direct) {
    this.checkPreConditions(propertyExpression);
    this.classifyClasses();
    if (!this.isConsistent()) return new NodeSet(this.getBottomClassNode());

    const role = H_role(propertyExpression);
    let nodes = this.directObjectRoleDomains.get(role);
    if (nodes === undefined) {
      const freshIndividualA = createAnonymousIndividual('fresh-individual-A');
      const freshIndividualB = createAnonymousIndividual('fresh-individual-B');
      const assertion = roleAssertion(role, freshIndividualA, freshIndividualB);
      const tableau = this.getTableau();
      nodes = HierarchySearch.search({
        getSuccessorElements: (u) => u.getChildNodes(),
        getPredecessorElements: (u) => u.getParentNodes(),
        trueOf: (u) => {
          const potentialDomainConcept = u.getRepresentative();
          return !tableau.isSatisfiable({
            perTestPositiveFactsNoDependency: [assertion],
            perTestNegativeFactsNoDependency: [createAtom(potentialDomainConcept, freshIndividualA)],
            reasoningTaskDescription: `isDomainOf(${potentialDomainConcept}, ${role})`
          });
        }
      }, new Set([this.atomicConceptHierarchy.getTopNode()]), null);
      this.directObjectRoleDomains.set(role, nodes);
    }
    if (!direct) nodes = getAncestorNodes(nodes);
    return this._conceptNodesToNodeSet(nodes);
  }

  getObjectPropertyRanges(propertyExpression, direct) {
    this.checkPreConditions(propertyExpression);
    this.classifyClasses();
    if (!this.isConsistent()) return new NodeSet(this.getBottomClassNode());

    const role = H_role(propertyExpression);
    let nodes = this.directObjectRoleRanges.get(role);
    if (nodes === undefined) {
      const freshIndividualA = createAnonymousIndividual('fresh-individual-A');
      const freshIndividualB = createAnonymousIndividual('fresh-individual-B');
      const assertion = roleAssertion(role, freshIndividualA, freshIndividualB);
      const tableau = this.getTableau();
      nodes = HierarchySearch.search({
        getSuccessorElements: (u) => u.getChildNodes(),
        getPredecessorElements: (u) => u.getParentNodes(),
        trueOf: (u) => {
          const potentialRangeConcept = u.getRepresentative();
          return !tableau.isSatisfiable({
            perTestPositiveFactsNoDependency: [assertion],
            perTestNegativeFactsNoDependency: [createAtom(potentialRangeConcept, freshIndividualB)],
            reasoningTaskDescription: `isRangeOf(${potentialRangeConcept}, ${role})`
          });
        }
      }, new Set([this.atomicConceptHierarchy.getTopNode()]), null);
      this.directObjectRoleRanges.set(role, nodes);
    }
    if (!direct) nodes = getAncestorNodes(nodes);
    return this._conceptNodesToNodeSet(nodes);
  }

  getDisjointObjectProperties(propertyExpression) {
    this.checkPreConditions(propertyExpression);
    if (!this.isConsistent()) return new NodeSet();
    this.classifyObjectProperties();

    if (E.isTopObjectProperty(E.namedPropertyOf(propertyExpression))) {
      return this._objectPropertyNodesToNodeSet([this.objectRoleHierarchy.getBottomNode()]);
    }
    if (E.isBottomObjectProperty(E.namedPropertyOf(propertyExpression))) {
      const node = this.objectRoleHierarchy.getTopNode();
      const result = new Set([node]);
      for (const descendant of node.getDescendantNodes()) result.add(descendant);
      return this._objectPropertyNodesToNodeSet(result);
    }

    const role = H_role(propertyExpression);
    const freshIndividualA = createAnonymousIndividual('fresh-individual-A');
    const freshIndividualB = createAnonymousIndividual('fresh-individual-B');
    const assertion = roleAssertion(role, freshIndividualA, freshIndividualB);
    const tableau = this.getTableau();

    const result = new Set();
    const nodesToTest = new Set(this.objectRoleHierarchy.getTopNode().getChildNodes());
    while (nodesToTest.size > 0) {
      const nodeToTest = nodesToTest.values().next().value;
      nodesToTest.delete(nodeToTest);
      const roleToTest = nodeToTest.getRepresentative();
      const disjoint = !tableau.isSatisfiable({
        perTestPositiveFactsNoDependency: [assertion, roleAssertion(roleToTest, freshIndividualA, freshIndividualB)],
        reasoningTaskDescription: `disjointness of ${role} and ${roleToTest}`
      });
      if (disjoint) {
        for (const descendant of nodeToTest.getDescendantNodes()) result.add(descendant);
      } else {
        for (const child of nodeToTest.getChildNodes()) nodesToTest.add(child);
      }
    }
    if (result.size === 0) result.add(this.objectRoleHierarchy.getBottomNode());
    return this._objectPropertyNodesToNodeSet(result);
  }

  isDisjointObjectProperty(propertyExpression1, propertyExpression2) {
    this.checkPreConditions(propertyExpression1, propertyExpression2);
    if (!this.isConsistent()) return true;
    const role1 = H_role(propertyExpression1);
    const role2 = H_role(propertyExpression2);
    const freshIndividualA = createAnonymousIndividual('fresh-individual-A');
    const freshIndividualB = createAnonymousIndividual('fresh-individual-B');
    return !this.getTableau().isSatisfiable({
      perTestPositiveFactsNoDependency: [
        roleAssertion(role1, freshIndividualA, freshIndividualB),
        roleAssertion(role2, freshIndividualA, freshIndividualB)
      ],
      reasoningTaskDescription: `disjointness of ${role1} and ${role2}`
    });
  }

  /**
   * Whether `p1` and `p2` are disjoint data properties, i.e. whether no
   * individual can have both with the SAME value.
   *
   * This is the data-property counterpart of {@link Reasoner#isDisjointObjectProperty}.
   * HermiT has no such method: its `EntailmentChecker.visit(OWLDisjointDataPropertiesAxiom)`
   * spells the test out as `∃p1.⊤ ⊓ ∃p2.⊤ ⊓ (≤1 owl:topDataProperty)` and asks
   * `isSatisfiable`. That cannot work — `OWLNormalization` rejects
   * `owl:topDataProperty` in a cardinality restriction ("in OWL 2 DL,
   * owl:topDataProperty is only allowed to occur in the super property position
   * of SubDataPropertyOf axioms"), so HermiT throws on every
   * `DisjointDataProperties` entailment query. Sharing one fresh constant
   * between the two role assertions expresses exactly the same constraint
   * (the `≤1` restriction is what forces the two values to coincide) without
   * mentioning `owl:topDataProperty`.
   */
  isDisjointDataProperty(propertyExpression1, propertyExpression2) {
    this.checkPreConditions(propertyExpression1, propertyExpression2);
    if (!this.isConsistent()) return true;
    const role1 = H_dataProperty(propertyExpression1);
    const role2 = H_dataProperty(propertyExpression2);
    const freshIndividual = createAnonymousIndividual('fresh-individual');
    const freshConstant = createAnonymousConstant('fresh-constant');
    return !this.getTableau().isSatisfiable({
      perTestPositiveFactsNoDependency: [
        roleAssertion(role1, freshIndividual, freshConstant),
        roleAssertion(role2, freshIndividual, freshConstant)
      ],
      reasoningTaskDescription: `disjointness of ${role1} and ${role2}`
    });
  }

  /** Functional / inverse-functional / … — dispatches on the property kind. */
  isFunctional(propertyExpression) {
    return E.isDataProperty(propertyExpression)
      ? this.isFunctionalDataProperty(propertyExpression)
      : this.isFunctionalObjectProperty(propertyExpression);
  }

  isFunctionalObjectProperty(propertyExpression) {
    this.checkPreConditions(propertyExpression);
    if (!this.isConsistent()) return true;
    const role = H_role(propertyExpression);
    const freshIndividual = createAnonymousIndividual('fresh-individual');
    const freshIndividualA = createAnonymousIndividual('fresh-individual-A');
    const freshIndividualB = createAnonymousIndividual('fresh-individual-B');
    return !this.getTableau().isSatisfiable({
      perTestPositiveFactsNoDependency: [
        roleAssertion(role, freshIndividual, freshIndividualA),
        roleAssertion(role, freshIndividual, freshIndividualB),
        createAtom(P.INEQUALITY, freshIndividualA, freshIndividualB)
      ],
      reasoningTaskDescription: `functionality of ${role}`
    });
  }

  isInverseFunctional(propertyExpression) {
    this.checkPreConditions(propertyExpression);
    if (!this.isConsistent()) return true;
    const role = H_role(propertyExpression);
    const freshIndividual = createAnonymousIndividual('fresh-individual');
    const freshIndividualA = createAnonymousIndividual('fresh-individual-A');
    const freshIndividualB = createAnonymousIndividual('fresh-individual-B');
    return !this.getTableau().isSatisfiable({
      perTestPositiveFactsNoDependency: [
        roleAssertion(role, freshIndividualA, freshIndividual),
        roleAssertion(role, freshIndividualB, freshIndividual),
        createAtom(P.INEQUALITY, freshIndividualA, freshIndividualB)
      ],
      reasoningTaskDescription: `inverse-functionality of ${role}`
    });
  }

  isIrreflexive(propertyExpression) {
    this.checkPreConditions(propertyExpression);
    if (!this.isConsistent()) return true;
    const role = H_role(propertyExpression);
    const freshIndividual = createAnonymousIndividual('fresh-individual');
    return !this.getTableau().isSatisfiable({
      perTestPositiveFactsNoDependency: [roleAssertion(role, freshIndividual, freshIndividual)],
      reasoningTaskDescription: `irreflexivity of ${role}`
    });
  }

  isReflexive(propertyExpression) {
    this.checkPreConditions(propertyExpression);
    if (!this.isConsistent()) return true;
    const pseudoNominal = E.owlClass(IRI_PSEUDO_NOMINAL);
    const allNotPseudoNominal = E.objectAllValuesFrom(
      propertyExpression, E.objectComplementOf(pseudoNominal));
    const freshIndividual = E.anonymousIndividual('fresh-individual');
    const tableau = this.getTableau(
      E.classAssertion(pseudoNominal, freshIndividual),
      E.classAssertion(allNotPseudoNominal, freshIndividual));
    const result = tableau.isSatisfiable({
      loadAdditionalABox: true,
      reasoningTaskDescription: `reflexivity of ${H_role(propertyExpression)}`
    });
    tableau.clearAdditionalDLOntology();
    return !result;
  }

  isAsymmetric(propertyExpression) {
    this.checkPreConditions(propertyExpression);
    if (!this.isConsistent()) return true;
    const freshIndividualA = E.anonymousIndividual('fresh-individual-A');
    const freshIndividualB = E.anonymousIndividual('fresh-individual-B');
    const tableau = this.getTableau(
      E.objectPropertyAssertion(propertyExpression, freshIndividualA, freshIndividualB),
      E.objectPropertyAssertion(E.inversePropertyOf(propertyExpression), freshIndividualA, freshIndividualB));
    const result = tableau.isSatisfiable({
      loadAdditionalABox: true,
      reasoningTaskDescription: `asymmetry of ${H_role(propertyExpression)}`
    });
    tableau.clearAdditionalDLOntology();
    return !result;
  }

  isSymmetric(propertyExpression) {
    this.checkPreConditions(propertyExpression);
    if (!this.isConsistent() || E.isTopObjectProperty(E.namedPropertyOf(propertyExpression))) return true;
    const pseudoNominal = E.owlClass(IRI_PSEUDO_NOMINAL);
    const allNotPseudoNominal = E.objectAllValuesFrom(
      propertyExpression, E.objectComplementOf(pseudoNominal));
    const freshIndividualA = E.anonymousIndividual('fresh-individual-A');
    const freshIndividualB = E.anonymousIndividual('fresh-individual-B');
    const tableau = this.getTableau(
      E.objectPropertyAssertion(propertyExpression, freshIndividualA, freshIndividualB),
      E.classAssertion(allNotPseudoNominal, freshIndividualB),
      E.classAssertion(pseudoNominal, freshIndividualA));
    const result = tableau.isSatisfiable({
      loadAdditionalABox: true,
      reasoningTaskDescription: `symmetry of ${propertyExpression}`
    });
    tableau.clearAdditionalDLOntology();
    return !result;
  }

  isTransitive(propertyExpression) {
    this.checkPreConditions(propertyExpression);
    if (!this.isConsistent()) return true;
    const pseudoNominal = E.owlClass(IRI_PSEUDO_NOMINAL);
    const allNotPseudoNominal = E.objectAllValuesFrom(
      propertyExpression, E.objectComplementOf(pseudoNominal));
    const a = E.anonymousIndividual('fresh-individual-A');
    const b = E.anonymousIndividual('fresh-individual-B');
    const c = E.anonymousIndividual('fresh-individual-C');
    const tableau = this.getTableau(
      E.objectPropertyAssertion(propertyExpression, a, b),
      E.objectPropertyAssertion(propertyExpression, b, c),
      E.classAssertion(allNotPseudoNominal, a),
      E.classAssertion(pseudoNominal, c));
    const result = tableau.isSatisfiable({
      loadAdditionalABox: true,
      reasoningTaskDescription: `transitivity of ${H_role(propertyExpression)}`
    });
    tableau.clearAdditionalDLOntology();
    return !result;
  }

  /** @returns {HierarchyNode} the node of the object-role hierarchy */
  getObjectPropertyHierarchyNode(propertyExpression) {
    this.checkPreConditions(propertyExpression);
    this.classifyObjectProperties();
    if (!this.isConsistent()) return this.objectRoleHierarchy.getBottomNode();
    const role = H_role(propertyExpression);
    let node = this.objectRoleHierarchy.getNodeForElement(role);
    if (node === undefined) {
      node = new HierarchyNode(
        role, new Set([role]),
        new Set([this.objectRoleHierarchy.getTopNode()]),
        new Set([this.objectRoleHierarchy.getBottomNode()]));
    }
    return node;
  }

  // ---- data property inferences ---------------------------------------------

  classifyDataProperties() {
    this.checkPreConditions();
    if (this.dataRoleHierarchy !== null) return this.dataRoleHierarchy;

    const relevantDataRoles = new Set([P.TOP_DATA_ROLE, P.BOTTOM_DATA_ROLE]);
    for (const role of this.dlOntology.allAtomicDataRoles) relevantDataRoles.add(role);

    if (!this.isConsistent()) {
      this.dataRoleHierarchy = Hierarchy.emptyHierarchy(
        relevantDataRoles, P.TOP_DATA_ROLE, P.BOTTOM_DATA_ROLE);
      return this.dataRoleHierarchy;
    }

    if (!this.dlOntology.hasDatatypes) {
      this.dataRoleHierarchy = Hierarchy.trivialHierarchy(P.TOP_DATA_ROLE, P.BOTTOM_DATA_ROLE);
      return this.dataRoleHierarchy;
    }

    const conceptsForRoles = new Map();
    const rolesForConcepts = new Map();
    const additionalAxioms = [];
    const unknownDatatypeA = E.datatype(IRI_UNKNOWN_DATATYPE_A);

    for (const dataRole of relevantDataRoles) {
      let conceptForRole;
      if (dataRole === P.TOP_DATA_ROLE) {
        conceptForRole = P.THING;
      } else if (dataRole === P.BOTTOM_DATA_ROLE) {
        conceptForRole = P.NOTHING;
      } else {
        conceptForRole = P.internAtomicConcept(`internal:prop#${dataRole.iri}`);
        additionalAxioms.push(E.equivalentClasses([
          E.owlClass(conceptForRole.iri),
          E.dataSomeValuesFrom(E.dataProperty(dataRole.iri), unknownDatatypeA)
        ]));
      }
      conceptsForRoles.set(dataRole, conceptForRole);
      rolesForConcepts.set(conceptForRole, dataRole);
    }

    const tableau = this.getTableau(additionalAxioms);
    try {
      const atomicConceptHierarchyForRoles = this._withProgress(
        'Classifying data properties...', relevantDataRoles.size,
        (progressMonitor) => Reasoner.classifyAtomicConcepts(
          tableau, progressMonitor,
          conceptsForRoles.get(P.TOP_DATA_ROLE),
          conceptsForRoles.get(P.BOTTOM_DATA_ROLE),
          new Set(rolesForConcepts.keys()),
          this.configuration.forceQuasiOrderClassification));

      const transformer = {
        transform: (atomicConcept) => rolesForConcepts.get(atomicConcept),
        determineRepresentative: (oldRepresentative) => rolesForConcepts.get(oldRepresentative)
      };
      this.dataRoleHierarchy = atomicConceptHierarchyForRoles.transform(transformer, null);
    } finally {
      tableau.clearAdditionalDLOntology();
    }
    return this.dataRoleHierarchy;
  }

  getTopDataPropertyNode() {
    this.classifyDataProperties();
    return this._dataPropertyNodeToNode(this.dataRoleHierarchy.getTopNode());
  }

  getBottomDataPropertyNode() {
    this.classifyDataProperties();
    return this._dataPropertyNodeToNode(this.dataRoleHierarchy.getBottomNode());
  }

  isSubDataPropertyOf(subDataProperty, superDataProperty) {
    this.checkPreConditions(subDataProperty, superDataProperty);
    if (!this.isConsistent()
      || E.isBottomDataProperty(subDataProperty)
      || E.isTopDataProperty(superDataProperty)) {
      return true;
    }
    const subrole = H_dataProperty(subDataProperty);
    const superrole = H_dataProperty(superDataProperty);
    if (this.dataRoleHierarchy !== null
      && !this.containsFreshEntities(subDataProperty, superDataProperty)) {
      const subroleNode = this.dataRoleHierarchy.getNodeForElement(subrole);
      if (subroleNode !== undefined) {
        return subroleNode.isEquivalentElement(superrole) || subroleNode.isAncestorElement(superrole);
      }
    }

    // dp ⊑ dq iff {dp(i,c), dnq(i,c), DisjointDataProperties(dq, dnq)} is unsat.
    const individual = E.anonymousIndividual('fresh-individual');
    const freshConstant = E.literal(IRI_FRESH_CONSTANT, E.datatype(IRI_ANONYMOUS_CONSTANTS));
    const negatedSuperDataProperty = E.dataProperty(IRI_NEGATED_SUPERPROPERTY);
    const tableau = this.getTableau(
      E.dataPropertyAssertion(subDataProperty, individual, freshConstant),
      E.dataPropertyAssertion(negatedSuperDataProperty, individual, freshConstant),
      // `E` has no `disjointDataProperties` factory; build the axiom directly.
      { axiomType: E.AxiomType.DISJOINT_DATA_PROPERTIES,
        properties: [superDataProperty, negatedSuperDataProperty] });
    const result = tableau.isSatisfiable({
      loadAdditionalABox: true,
      reasoningTaskDescription: `isRoleSubsumedBy(${subrole}, ${superrole}, false)`
    });
    tableau.clearAdditionalDLOntology();
    return !result;
  }

  getSuperDataProperties(property, direct) {
    const node = this.getDataPropertyHierarchyNode(property);
    let result;
    if (direct) {
      result = new Set(node.getParentNodes());
    } else {
      result = new Set(node.getAncestorNodes());
      result.delete(node);
    }
    return this._dataPropertyNodesToNodeSet(result);
  }

  getSubDataProperties(property, direct) {
    const node = this.getDataPropertyHierarchyNode(property);
    let result;
    if (direct) {
      result = new Set(node.getChildNodes());
    } else {
      result = new Set(node.getDescendantNodes());
      result.delete(node);
    }
    return this._dataPropertyNodesToNodeSet(result);
  }

  getEquivalentDataProperties(property) {
    return this._dataPropertyNodeToNode(this.getDataPropertyHierarchyNode(property));
  }

  getDataPropertyDomains(property, direct) {
    this.checkPreConditions(property);
    this.classifyClasses();
    if (!this.isConsistent()) return new NodeSet(this.getBottomClassNode());

    const atomicRole = H_dataProperty(property);
    let nodes = this.directDataRoleDomains.get(atomicRole);
    if (nodes === undefined) {
      const freshIndividual = createAnonymousIndividual('fresh-individual');
      const freshConstant = createAnonymousConstant('fresh-constant');
      const assertion = roleAssertion(atomicRole, freshIndividual, freshConstant);
      const tableau = this.getTableau();
      nodes = HierarchySearch.search({
        getSuccessorElements: (u) => u.getChildNodes(),
        getPredecessorElements: (u) => u.getParentNodes(),
        trueOf: (u) => {
          const potentialDomainConcept = u.getRepresentative();
          return !tableau.isSatisfiable({
            perTestPositiveFactsNoDependency: [assertion],
            perTestNegativeFactsNoDependency: [createAtom(potentialDomainConcept, freshIndividual)],
            reasoningTaskDescription: `isDomainOf(${potentialDomainConcept}, ${atomicRole})`
          });
        }
      }, new Set([this.atomicConceptHierarchy.getTopNode()]), null);
      this.directDataRoleDomains.set(atomicRole, nodes);
    }
    if (!direct) nodes = getAncestorNodes(nodes);
    return this._conceptNodesToNodeSet(nodes);
  }

  getDisjointDataProperties(propertyExpression) {
    this.checkPreConditions(propertyExpression);
    if (!this.dlOntology.hasDatatypes) {
      if (E.isTopDataProperty(propertyExpression) && this.isConsistent()) {
        return new NodeSet(new Node(E.bottomDataProperty()));
      }
      if (E.isBottomDataProperty(propertyExpression) && this.isConsistent()) {
        return new NodeSet(new Node(E.topDataProperty()));
      }
      return new NodeSet();
    }

    this.classifyDataProperties();
    if (!this.isConsistent()) return new NodeSet();

    if (E.isTopDataProperty(propertyExpression)) {
      return this._dataPropertyNodesToNodeSet([this.dataRoleHierarchy.getBottomNode()]);
    }
    if (E.isBottomDataProperty(propertyExpression)) {
      const node = this.dataRoleHierarchy.getTopNode();
      const result = new Set([node]);
      for (const descendant of node.getDescendantNodes()) result.add(descendant);
      return this._dataPropertyNodesToNodeSet(result);
    }

    const atomicRole = H_dataProperty(propertyExpression);
    // NOTE: HermiT uses a *named* fresh individual here (Individual.create, not
    // createAnonymous) — kept faithfully.
    const freshIndividual = createIndividual('fresh-individual');
    const freshConstant = createAnonymousConstant('fresh-constant');
    const assertion = roleAssertion(atomicRole, freshIndividual, freshConstant);
    const tableau = this.getTableau();

    const result = new Set();
    const nodesToTest = new Set(this.dataRoleHierarchy.getTopNode().getChildNodes());
    while (nodesToTest.size > 0) {
      const nodeToTest = nodesToTest.values().next().value;
      nodesToTest.delete(nodeToTest);
      const atomicRoleToTest = nodeToTest.getRepresentative();
      const disjoint = !tableau.isSatisfiable({
        perTestPositiveFactsNoDependency: [
          assertion,
          roleAssertion(atomicRoleToTest, freshIndividual, freshConstant)
        ],
        reasoningTaskDescription: `disjointness of ${atomicRole} and ${atomicRoleToTest}`
      });
      if (disjoint) {
        for (const descendant of nodeToTest.getDescendantNodes()) result.add(descendant);
      } else {
        for (const child of nodeToTest.getChildNodes()) nodesToTest.add(child);
      }
    }
    if (result.size === 0) result.add(this.dataRoleHierarchy.getBottomNode());
    return this._dataPropertyNodesToNodeSet(result);
  }

  isFunctionalDataProperty(property) {
    this.checkPreConditions(property);
    if (!this.isConsistent()) return true;
    const atomicRole = H_dataProperty(property);
    const freshIndividual = createAnonymousIndividual('fresh-individual');
    const freshConstantA = createAnonymousConstant('fresh-constant-A');
    const freshConstantB = createAnonymousConstant('fresh-constant-B');
    return !this.getTableau().isSatisfiable({
      perTestPositiveFactsNoDependency: [
        roleAssertion(atomicRole, freshIndividual, freshConstantA),
        roleAssertion(atomicRole, freshIndividual, freshConstantB),
        createAtom(P.INEQUALITY, freshConstantA, freshConstantB)
      ],
      reasoningTaskDescription: `functionality of ${atomicRole}`
    });
  }

  /** @returns {HierarchyNode} the node of the data-role hierarchy */
  getDataPropertyHierarchyNode(property) {
    this.checkPreConditions(property);
    this.classifyDataProperties();
    if (!this.isConsistent()) return this.dataRoleHierarchy.getBottomNode();
    const atomicRole = H_dataProperty(property);
    let node = this.dataRoleHierarchy.getNodeForElement(atomicRole);
    if (node === undefined) {
      node = new HierarchyNode(
        atomicRole, new Set([atomicRole]),
        new Set([this.dataRoleHierarchy.getTopNode()]),
        new Set([this.dataRoleHierarchy.getBottomNode()]));
    }
    return node;
  }

  // ---- individual inferences ------------------------------------------------
  //
  // HermiT answers these from a completed `InstanceManager` model. That class is
  // not ported, so each query below is answered by a direct tableau test. The
  // answers are the same; only the asymptotics differ (O(#individuals) tableau
  // runs instead of one).

  /**
   * Realisation. Without `InstanceManager` this only needs to make sure the
   * class hierarchy exists; every type query is then answered on demand.
   */
  realise() {
    this.checkPreConditions();
    this.classifyClasses();
    this._realisationCompleted = true;
    return true;
  }

  realiseObjectProperties() {
    this.checkPreConditions();
    this.classifyObjectProperties();
    this._propertyRealisationCompleted = true;
    return true;
  }

  /**
   * Compute every individual's `owl:sameAs` equivalence class in one pass.
   *
   * This is just a loop over {@link Reasoner#getSameIndividuals}, which does all
   * the work: it memoises each class it computes (for every member of it) and
   * skips candidates whose class is already known. So the first call costs N-1
   * tableau tests and caches its whole class, and every later call either hits
   * the cache outright or skips the already-classified candidates without a test.
   * The net effect is the union-find sweep — N(N-1)/2 tests instead of N(N-1) —
   * but expressed once, in the query method, so a caller who reaches for
   * `getSameIndividuals` directly gets the same benefit.
   *
   * Measured on the real ontologies (where every individual is its own class,
   * i.e. the WORST case for the shortcut) this is exactly 2x — `ogms.owl`
   * 306 → 153 tableau runs, `iao.owl` 380 → 190 — and 4x on a synthetic ontology
   * with real merges (56 → 14), with the resulting equivalence classes verified
   * IDENTICAL in both. Repeating a single `getSameIndividuals` query 10x drops
   * from 170 runs to 0.
   *
   * Entries a previous cold query left in the cache are reused, not recomputed;
   * they were computed against the CURRENT ABox (every mutation path calls
   * `clearInferenceCaches()`), so they are still the right classes.
   */
  precomputeSameAsEquivalenceClasses() {
    this.checkPreConditions();
    if (this.dlOntology.allIndividuals.size === 0) return;
    if (!this.isConsistent()) {
      // In an inconsistent ontology every individual is "the same as" every other
      // (ex falso), and `getSameIndividuals` answers that directly without
      // consulting the cache. Drop any entries memoised while the ontology was
      // still consistent so a later consistency-restoring change cannot
      // resurrect them — `clearInferenceCaches()` already does this, but this
      // method can be called again without one.
      this._sameAsEquivalenceClasses = new Map();
    } else {
      // `getSameIndividuals` memoises each class it computes and skips members of
      // classes already known, so this plain loop IS the union-find sweep: the
      // first call costs N-1 tests and caches its whole class, and every later
      // call either hits the cache or skips the already-classified candidates.
      // Entries a previous cold query left behind are reused, not recomputed.
      for (const individual of this.getAllNamedIndividuals()) {
        this.getSameIndividuals(individual);
      }
    }
    this._sameAsComputed = true;
  }

  /**
   * The named classes `individual` is an instance of.
   *
   * @param {*} individual
   * @param {boolean} direct only the most specific ones
   * @returns {NodeSet}
   */
  getTypes(individual, direct) {
    this.checkPreConditions(individual);
    if (!this.isDefined(individual)) {
      this.classifyClasses();
      return this._conceptNodesToNodeSet([this.atomicConceptHierarchy.getTopNode()]);
    }
    if (direct) {
      return this._conceptNodesToNodeSet(this.getDirectSuperConceptNodes(H_individual(individual)));
    }
    const ancestors = new Set();
    for (const node of this.getDirectSuperConceptNodes(H_individual(individual))) {
      for (const ancestor of node.getAncestorNodes()) ancestors.add(ancestor);
    }
    return this._conceptNodesToNodeSet(ancestors);
  }

  /**
   * Whether `individual` is an instance of `type`.
   *
   * @param {*} individual
   * @param {*} type a class expression
   * @param {boolean} direct
   */
  hasType(individual, type, direct) {
    this.checkPreConditions(individual, type);
    if (!this.isConsistent()) return true;
    if (!this.isDefined(individual)) {
      return this.getEquivalentClasses(type).contains(E.owlThing());
    }

    if (direct && E.isNamedClass(type)) {
      const concept = H_class(type);
      for (const node of this.getDirectSuperConceptNodes(H_individual(individual))) {
        if (node.isEquivalentElement(concept)) return true;
      }
      return false;
    }

    if (E.isNamedClass(type)) {
      // KB ⊨ C(i) iff KB ∪ {¬C(i)} has no model.
      return !this.getTableau().isSatisfiable({
        loadPermanentABox: true,
        loadAdditionalABox: true,
        perTestNegativeFactsNoDependency: [createAtom(H_class(type), H_individual(individual))],
        reasoningTaskDescription: `isInstanceOf(${individual}, ${type})`
      });
    }

    const negatedAssertionAxiom = E.classAssertion(E.objectComplementOf(type), individual);
    const tableau = this.getTableau(negatedAssertionAxiom);
    const result = tableau.isSatisfiable({
      loadPermanentABox: true,
      loadAdditionalABox: true,
      reasoningTaskDescription: `isInstanceOf(${individual}, ${type})`
    });
    tableau.clearAdditionalDLOntology();
    return !result;
  }

  /**
   * The named individuals that are instances of `classExpression`.
   *
   * @param {*} classExpression
   * @param {boolean} direct
   * @returns {NodeSet}
   */
  getInstances(classExpression, direct) {
    if (this.dlOntology.allIndividuals.size === 0) return new NodeSet();
    this.checkPreConditions(classExpression);
    if (!this.isConsistent()) return new NodeSet(new Node(this.getAllNamedIndividuals()));

    const result = [];
    for (const individual of this.getAllNamedIndividuals()) {
      if (this.hasType(individual, classExpression, direct)) result.push(H_individual(individual));
    }
    return this.sortBySameAsIfNecessary(result);
  }

  isSameIndividual(individual1, individual2) {
    if (!this.isConsistent()) return true;
    if (this.dlOntology.allIndividuals.size === 0) return false;
    const i1 = H_individual(individual1);
    const i2 = H_individual(individual2);
    if (i1 === i2) return true;
    return !this.getTableau().isSatisfiable({
      loadPermanentABox: true,
      loadAdditionalABox: true,
      perTestNegativeFactsNoDependency: [createAtom(P.EQUALITY, i1, i2)],
      reasoningTaskDescription: `isSameIndividual(${i1}, ${i2})`
    });
  }

  getSameIndividuals(individual) {
    if (!this.isConsistent()) return new NodeSet(new Node(this.getAllNamedIndividuals()));
    if (this.dlOntology.allIndividuals.size === 0 || !this.isDefined(individual)) {
      return new NodeSet(new Node(individual));
    }
    // The cache is `null` until something first populates it, and a Map MISS
    // means "compute this one". The old
    // `this._sameAsEquivalenceClasses && ...get(key)` guard conflated the two:
    // it evaluated to `null`, and `null !== undefined`, so it fell through the
    // check below and returned `null` to the caller instead of computing. That
    // was only accidentally correct while the field happened to be `undefined`.
    if (this._sameAsEquivalenceClasses === null) this._sameAsEquivalenceClasses = new Map();
    const key = entityKey(individual);
    const cached = this._sameAsEquivalenceClasses.get(key);
    if (cached !== undefined) return cached;

    // Compute this individual's class, then memoise it for EVERY member —
    // `owl:sameAs` is an equivalence relation, so they all have exactly this
    // class. Without memoising, asking for the same individual twice re-runs the
    // whole sweep: measured on `ogms.owl`, 10 repeat queries of one individual
    // cost 170 tableau runs, and 0 afterwards.
    //
    // The inner loop skips any individual already in the cache. That is sound,
    // and it is what turns an N(N-1) sweep into N(N-1)/2: a cached class was
    // computed COMPLETELY (every candidate was either tested or itself skipped by
    // this same argument), and it does not contain `individual` — if it did, the
    // lookup above would have hit. So `individual` and that cached member are
    // different, by symmetry of equality, with no tableau test needed.
    const node = new Node(individual);
    for (const other of this.getAllNamedIndividuals()) {
      const otherKey = entityKey(other);
      if (otherKey === key) continue;
      if (this._sameAsEquivalenceClasses.has(otherKey)) continue;
      if (this.isSameIndividual(individual, other)) node.add(other);
    }

    // Every member shares ONE NodeSet instance. Safe because both callers
    // (`getObjectPropertyValues`, `sortBySameAsIfNecessary`) only read it through
    // `getFlattened()`, which builds a fresh Set.
    const nodeSet = new NodeSet(node);
    for (const member of node.getEntities()) {
      this._sameAsEquivalenceClasses.set(entityKey(member), nodeSet);
    }
    return nodeSet;
  }

  getDifferentIndividuals(namedIndividual) {
    this.checkPreConditions(namedIndividual);
    if (!this.isConsistent()) return new NodeSet(new Node(this.getAllNamedIndividuals()));

    const individual = H_individual(namedIndividual);
    const tableau = this.getTableau();
    const result = [];
    for (const potentiallyDifferent of this.dlOntology.allIndividuals) {
      if (!Reasoner.isResultRelevantIndividual(potentiallyDifferent)) continue;
      if (potentiallyDifferent === individual) continue;
      const entailed = !tableau.isSatisfiable({
        loadPermanentABox: true,
        loadAdditionalABox: true,
        perTestPositiveFactsNoDependency: [createAtom(P.EQUALITY, individual, potentiallyDifferent)],
        reasoningTaskDescription: `isDifferentFrom(${individual}, ${potentiallyDifferent})`
      });
      if (entailed) result.push(potentiallyDifferent);
    }
    return this.sortBySameAsIfNecessary(result);
  }

  getObjectPropertyValues(individual, propertyExpression) {
    if (!this.isConsistent()) return new NodeSet(new Node(this.getAllNamedIndividuals()));
    const role = H_role(propertyExpression);
    if (!this.dlOntology.containsObjectRole(atomicRoleOf(role))) return new NodeSet();

    const subject = H_individual(individual);
    const tableau = this.getTableau();
    const result = [];
    for (const candidate of this.getAllNamedIndividuals()) {
      const object = H_individual(candidate);
      // `pe⁻(s,o)` is `pe(o,s)`.
      const assertion = E.isAnonymousProperty(propertyExpression)
        ? roleAssertion(role, object, subject)
        : roleAssertion(role, subject, object);
      const entailed = !tableau.isSatisfiable({
        loadPermanentABox: true,
        loadAdditionalABox: true,
        perTestNegativeFactsNoDependency: [assertion],
        reasoningTaskDescription: `hasObjectPropertyRelationship(${role}, ${subject}, ${object})`
      });
      if (entailed) result.push(object);
    }
    return this.sortBySameAsIfNecessary(result);
  }

  /** @returns {Map<*, Set<*>>} subject → objects */
  getObjectPropertyInstances(property) {
    const result = new Map();
    if (!this.isConsistent()) {
      const all = this.getAllNamedIndividuals();
      for (const individual of all) result.set(individual, new Set(all));
      return result;
    }
    const role = H_role(property);
    if (!this.dlOntology.containsObjectRole(atomicRoleOf(role))) return result;
    for (const subject of this.getAllNamedIndividuals()) {
      const values = this.getObjectPropertyValues(subject, property).getFlattened();
      if (values.size > 0) result.set(subject, values);
    }
    return result;
  }

  hasObjectPropertyRelationship(subject, propertyExpression, object) {
    if (!this.isConsistent()) return true;
    const role = H_role(propertyExpression);
    const s = H_individual(subject);
    const o = H_individual(object);
    const assertion = E.isAnonymousProperty(propertyExpression)
      ? roleAssertion(role, o, s)
      : roleAssertion(role, s, o);
    return !this.getTableau().isSatisfiable({
      loadPermanentABox: true,
      loadAdditionalABox: true,
      perTestNegativeFactsNoDependency: [assertion],
      reasoningTaskDescription: `hasObjectRoleRelationship(${role}, ${s}, ${o})`
    });
  }

  /**
   * The data values `individual` is known to have for `dataProperty` (or any of
   * its sub-properties). Read straight off the clausified ABox, exactly as
   * HermiT does.
   *
   * @returns {NodeSet} one node per literal
   */
  getDataPropertyValues(individual, dataProperty) {
    if (!this.dlOntology.hasDatatypes) return new NodeSet();
    const relevantDataProperties = this.getSubDataProperties(dataProperty, false).getFlattened();
    relevantDataProperties.add(dataProperty);
    const relevantIndividuals = this.getSameIndividuals(individual).getFlattened();

    const result = new NodeSet();
    for (const dp of relevantDataProperties) {
      if (E.isBottomDataProperty(dp)) continue;
      const atomicRole = H_dataProperty(dp);
      const byIndividual = this.dlOntology.dataPropertyAssertions.get(atomicRole);
      if (byIndividual === undefined) continue;
      for (const ind of relevantIndividuals) {
        const constants = byIndividual.get(H_individual(ind));
        if (constants === undefined) continue;
        for (const constant of constants) result.addNode(new Node(constantToLiteral(constant)));
      }
    }
    return result;
  }

  hasDataPropertyRelationship(subject, dataProperty, object) {
    this.checkPreConditions(subject, dataProperty);
    if (!this.isConsistent()) return true;
    const notAssertion = E.negativeDataPropertyAssertion(dataProperty, subject, object);
    const tableau = this.getTableau(notAssertion);
    const result = tableau.isSatisfiable({
      loadPermanentABox: true,
      loadAdditionalABox: true,
      reasoningTaskDescription: `hasDataPropertyRelationship(${subject}, ${dataProperty}, ${object})`
    });
    tableau.clearAdditionalDLOntology();
    return !result;
  }

  /**
   * The most specific class-hierarchy nodes `individual` belongs to. HermiT's
   * `getDirectSuperConceptNodes` — the workhorse behind `getTypes(_, true)`.
   *
   * MEMOISED per individual, because this is the port's most expensive query and
   * several callers ask about the same individual repeatedly — most importantly
   * `getInstances(C, true)`, which walks EVERY individual once per class queried.
   * See `directSuperConceptNodesCache` for the soundness argument.
   *
   * The cached `Set` is shared with callers, so it must be treated as immutable.
   * Every current caller only iterates it (`_conceptNodesToNodeSet`, the
   * `getTypes`/`hasType` loops); do not add to or delete from it.
   *
   * @param {import('../model/Term').Individual} individual
   * @returns {Set<HierarchyNode>}
   */
  getDirectSuperConceptNodes(individual) {
    this.classifyClasses();
    const key = individual.iri;
    const cached = this.directSuperConceptNodesCache.get(key);
    if (cached !== undefined) return cached;

    const tableau = this.getTableau();
    const result = HierarchySearch.search({
      getSuccessorElements: (u) => u.getChildNodes(),
      getPredecessorElements: (u) => u.getParentNodes(),
      trueOf: (u) => {
        const concept = u.getRepresentative();
        return concept === P.THING || !tableau.isSatisfiable({
          loadPermanentABox: true,
          loadAdditionalABox: true,
          perTestNegativeFactsNoDependency: [createAtom(concept, individual)],
          reasoningTaskDescription: `isInstanceOf(${concept}, ${individual})`
        });
      }
    }, new Set([this.atomicConceptHierarchy.getTopNode()]), null);

    this.directSuperConceptNodesCache.set(key, result);
    return result;
  }

  /**
   * Group `individuals` into nodes according to `individualNodeSetPolicy`:
   * BY_SAME_AS puts same-as individuals in one node, BY_NAME gives each its own.
   *
   * @param {Iterable<import('../model/Term').Individual>} individuals
   * @returns {NodeSet}
   */
  sortBySameAsIfNecessary(individuals) {
    const result = new NodeSet();
    if (this.configuration.individualNodeSetPolicy === INDIVIDUAL_NODE_SET_POLICY.BY_SAME_AS) {
      const assigned = new Set();
      for (const individual of individuals) {
        const key = individual.iri;
        if (assigned.has(key)) continue;
        const sameNamedIndividuals = new Set();
        for (const other of this.getSameIndividuals(E.namedIndividual(individual.iri)).getFlattened()) {
          const otherKey = E.iriString(other);
          assigned.add(otherKey);
          sameNamedIndividuals.add(E.namedIndividual(otherKey));
        }
        if (sameNamedIndividuals.size === 0) sameNamedIndividuals.add(E.namedIndividual(key));
        result.addNode(new Node(sameNamedIndividuals));
      }
      return result;
    }
    for (const individual of individuals) result.addNode(new Node(E.namedIndividual(individual.iri)));
    return result;
  }

  /** Every named, non-internal individual in the ontology. */
  getAllNamedIndividuals() {
    const result = new Set();
    for (const individual of this.dlOntology.allIndividuals) {
      if (Reasoner.isResultRelevantIndividual(individual)) result.add(E.namedIndividual(individual.iri));
    }
    return result;
  }

  /** Named and not one of HermiT's `internal:` bookkeeping individuals. */
  static isResultRelevantIndividual(individual) {
    return !individual.isAnonymous() && !Prefixes.isInternalIRI(individual.iri);
  }

  // ---- tableau plumbing -----------------------------------------------------

  /** The permanent tableau, with any additional ontology removed. */
  getTableau(...additionalAxioms) {
    if (additionalAxioms.length === 1 && Array.isArray(additionalAxioms[0])) {
      return this.getTableau(...additionalAxioms[0]);
    }
    if (additionalAxioms.length === 0) {
      this.tableau.clearAdditionalDLOntology();
      return this.tableau;
    }
    const deltaDLOntology = this.createDeltaDLOntology(additionalAxioms);
    if (this.tableau.supportsAdditionalDLOntology(deltaDLOntology)) {
      this.tableau.setAdditionalDLOntology(deltaDLOntology);
      return this.tableau;
    }
    return Reasoner.createTableau(
      this.interruptFlag, this.configuration, this.dlOntology, deltaDLOntology, this.prefixes);
  }

  /**
   * Build a tableau from a configuration.
   *
   * Monitor selection follows HermiT: `tableauMonitorType` picks a well-known
   * monitor, and when `configuration.monitor` is ALSO set the two are combined
   * with a `TableauMonitorFork`.
   *
   * Blocking selection is delegated to `createBlockingStrategy`, which mirrors
   * the three switches in HermiT's `createTableau`. `directBlockingType` and
   * `blockingStrategyType` are honoured for every value except the two
   * approximate core strategies, and `blockingSignatureCacheType` is not
   * implemented; both degrade with a `configuration.warningMonitor` warning
   * rather than silently ignoring the request.
   */
  static createTableau(interruptFlag, configuration, permanentDLOntology, additionalDLOntology, _prefixes) {
    const hasInverseRoles = permanentDLOntology.hasInverseRoles
      || (additionalDLOntology !== null && additionalDLOntology !== undefined
        && additionalDLOntology.hasInverseRoles);
    // HermiT Reasoner.java:1937 — caching is unsound with nominals, so the
    // signature-cache decision needs this too.
    const hasNominals = permanentDLOntology.hasNominals
      || (additionalDLOntology !== null && additionalDLOntology !== undefined
        && additionalDLOntology.hasNominals);

    // Monitor selection — HermiT `Reasoner.createTableau` lines 1939-1966:
    // pick the well-known monitor named by `tableauMonitorType`, then combine it
    // with a user-supplied `configuration.monitor` via a fork when both exist.
    //
    // DEBUGGER_* are not ported (HermiT's `Debugger` is an interactive console
    // requiring a full command language), so they degrade to `CountingMonitor` —
    // the closest non-interactive equivalent — rather than silently doing
    // nothing, which is what an exported-but-inert enum value would mean.
    let wellKnownTableauMonitor = null;
    switch (configuration.tableauMonitorType) {
      case TABLEAU_MONITOR_TYPE.NONE:
        wellKnownTableauMonitor = null;
        break;
      case TABLEAU_MONITOR_TYPE.TIMING:
        wellKnownTableauMonitor = new Timer(configuration.monitorOptions || {});
        break;
      case TABLEAU_MONITOR_TYPE.TIMING_WITH_PAUSE:
        // HermiT's `TimerWithPause` IS ported: `Timer` plus a blocking stdin
        // read after each report (fs.readSync(0), which degrades to no-pause on
        // a non-TTY stdin). `monitorOptions.wait` / `.pause` control it.
        wellKnownTableauMonitor = new TimerWithPause(configuration.monitorOptions || {});
        break;
      case TABLEAU_MONITOR_TYPE.DEBUGGER_NO_HISTORY:
      case TABLEAU_MONITOR_TYPE.DEBUGGER_HISTORY_ON:
        wellKnownTableauMonitor = new CountingMonitor();
        break;
      default:
        throw new Error(`Unknown monitor type: ${configuration.tableauMonitorType}`);
    }

    let tableauMonitor;
    if (configuration.monitor === null || configuration.monitor === undefined) {
      tableauMonitor = wellKnownTableauMonitor;
    } else if (wellKnownTableauMonitor === null) {
      tableauMonitor = configuration.monitor;
    } else {
      tableauMonitor = new TableauMonitorFork(wellKnownTableauMonitor, configuration.monitor);
    }

    const blockingStrategy = createBlockingStrategy(configuration, hasInverseRoles, hasNominals);

    let existentialExpansionStrategy;
    switch (configuration.existentialStrategyType) {
      case EXISTENTIAL_STRATEGY_TYPE.CREATION_ORDER:
        existentialExpansionStrategy = new CreationOrderStrategy(blockingStrategy);
        break;
      case EXISTENTIAL_STRATEGY_TYPE.EL:
        existentialExpansionStrategy = new IndividualReuseStrategy(blockingStrategy, true);
        break;
      case EXISTENTIAL_STRATEGY_TYPE.INDIVIDUAL_REUSE:
        existentialExpansionStrategy = new IndividualReuseStrategy(blockingStrategy, false);
        break;
      default:
        throw new Error(`Unknown expansion strategy type: ${configuration.existentialStrategyType}`);
    }

    return new Tableau({
      interruptFlag,
      tableauMonitor,
      existentialExpansionStrategy,
      useDisjunctionLearning: configuration.useDisjunctionLearning,
      permanentDLOntology,
      additionalDLOntology: additionalDLOntology || null,
      parameters: configuration.parameters
    });
  }

  /**
   * Clausify a handful of extra axioms on top of the permanent ontology, so a
   * single query does not have to rebuild everything.
   *
   * @param {Iterable<object>} additionalAxioms
   * @returns {import('../model/DLOntology').DLOntology}
   */
  createDeltaDLOntology(additionalAxioms) {
    const original = this.dlOntology;
    const set = new Set();
    for (const axiom of additionalAxioms) {
      if (Reasoner.isUnsupportedExtensionAxiom(axiom)) {
        throw new Error('Internal error: unsupported extension axiom type.');
      }
      set.add(axiom);
    }

    const axioms = new OWLAxioms();
    for (const iri of original.definedDatatypesIRIs) axioms.definedDatatypesIRIs.add(iri);

    new OWLNormalization(axioms, original.allAtomicConcepts.size).processAxioms(set);

    new BuiltInPropertyManager().axiomatizeBuiltInPropertiesAsNeeded(axioms, {
      skipTopObjectProperty: original.allAtomicObjectRoles.has(P.TOP_OBJECT_ROLE),
      skipBottomObjectProperty: original.allAtomicObjectRoles.has(P.BOTTOM_OBJECT_ROLE),
      skipTopDataProperty: original.allAtomicDataRoles.has(P.TOP_DATA_ROLE),
      skipBottomDataProperty: original.allAtomicDataRoles.has(P.BOTTOM_DATA_ROLE)
    });

    const replacementIndex = this.objectPropertyInclusionManager
      .rewriteNegativeObjectPropertyAssertions(null, axioms, original.allAtomicConcepts.size);
    this.objectPropertyInclusionManager.rewriteAxioms(null, axioms, replacementIndex);

    const expressivity = new OWLAxiomsExpressivity(axioms);
    expressivity.hasAtMostRestrictions = expressivity.hasAtMostRestrictions || original.hasAtMostRestrictions;
    expressivity.hasInverseRoles = expressivity.hasInverseRoles || original.hasInverseRoles;
    expressivity.hasNominals = expressivity.hasNominals || original.hasNominals;
    expressivity.hasDatatypes = expressivity.hasDatatypes || original.hasDatatypes;

    return new OWLClausification(this.configuration)
      .clausify(IRI_DELTA_KB, axioms, expressivity);
  }

  /**
   * Axiom types that must never appear in a delta ontology, because their
   * clauses would change the role hierarchy the permanent tableau was built
   * with.
   */
  static isUnsupportedExtensionAxiom(axiom) {
    if (axiom === null || axiom === undefined) return false;
    // protege-js SWRL rules carry no `axiomType`; detect them structurally, as
    // `OWLNormalization._visitAxiom` does. A rule can introduce arbitrary role
    // inclusions, so letting one into a delta ontology would silently change
    // the role hierarchy the permanent tableau was built with.
    if (Array.isArray(axiom.body) && Array.isArray(axiom.head)) return true;
    const type = axiom.axiomType || (typeof axiom.getAxiomType === 'function' ? axiom.getAxiomType() : null);
    return type === E.AxiomType.SUB_OBJECT_PROPERTY_OF
      || type === E.AxiomType.TRANSITIVE_OBJECT_PROPERTY
      || type === E.AxiomType.SUB_PROPERTY_CHAIN_OF
      || type === E.AxiomType.FUNCTIONAL_OBJECT_PROPERTY
      || type === E.AxiomType.INVERSE_FUNCTIONAL_OBJECT_PROPERTY
      || type === 'SWRLRule';
  }

  // ---- classification drivers -----------------------------------------------

  /**
   * Horn ontologies get the cheap deterministic algorithm (one tableau run per
   * concept, subsumers read off the single model); everything else needs the
   * quasi-order algorithm.
   */
  static classifyAtomicConcepts(tableau, progressMonitor, topElement, bottomElement, elements,
    forceQuasiOrderClassification) {
    if (tableau.isDeterministic() && !forceQuasiOrderClassification) {
      return new DeterministicClassification(
        tableau, progressMonitor, topElement, bottomElement, elements).classify();
    }
    return new QuasiOrderClassification(
      tableau, progressMonitor, topElement, bottomElement, elements).classify();
  }

  /**
   * Role classification. Port of `Reasoner.classifyAtomicConceptsForRoles`.
   *
   * The deterministic case is identical to concept classification. The
   * non-deterministic case uses `QuasiOrderClassificationForRoles`, which seeds
   * the known-subsumption graph from the told ROLE inclusions and mirrors every
   * subsumption onto the inverse roles (`R ⊑ S⁻` ⟺ `R⁻ ⊑ S`) — the plain
   * quasi-order algorithm does neither, because its seeder only recognises
   * clauses whose predicates are `AtomicConcept`s.
   *
   * Note this is used for OBJECT properties only. Data properties go through
   * `classifyAtomicConcepts`, matching HermiT: OWL 2 has no inverse data
   * properties, so there is nothing for the mirroring to exploit.
   */
  static classifyAtomicConceptsForRoles(tableau, progressMonitor, topElement, bottomElement, elements,
    hasInverseRoles, conceptsForRoles, rolesForConcepts, forceQuasiOrderClassification) {
    if (tableau.isDeterministic() && !forceQuasiOrderClassification) {
      return new DeterministicClassification(
        tableau, progressMonitor, topElement, bottomElement, elements).classify();
    }
    return new QuasiOrderClassificationForRoles(
      tableau, progressMonitor, topElement, bottomElement, elements,
      hasInverseRoles, conceptsForRoles, rolesForConcepts).classify();
  }

  /**
   * Run `fn` with a `{elementClassified}` progress monitor wired to
   * `configuration.reasonerProgressMonitor`, guaranteeing the task is stopped.
   */
  _withProgress(taskName, totalSteps, fn) {
    const monitor = this.configuration.reasonerProgressMonitor;
    if (!monitor) return fn({ elementClassified() {} });
    let processed = 0;
    if (typeof monitor.reasonerTaskStarted === 'function') monitor.reasonerTaskStarted(taskName);
    try {
      return fn({
        elementClassified: () => {
          processed++;
          if (typeof monitor.reasonerTaskProgressChanged === 'function') {
            monitor.reasonerTaskProgressChanged(processed, totalSteps);
          }
        }
      });
    } finally {
      if (typeof monitor.reasonerTaskStopped === 'function') monitor.reasonerTaskStopped();
    }
  }

  // ---- HierarchyNode → Node / NodeSet conversion ----------------------------

  /** AtomicConcept node → OWLClass node, dropping HermiT's internal concepts. */
  _conceptNodeToNode(hierarchyNode) {
    const result = new Node();
    for (const concept of hierarchyNode.getEquivalentElements()) {
      if (!Prefixes.isInternalIRI(concept.iri)) result.add(E.owlClass(concept.iri));
    }
    return result;
  }

  _conceptNodesToNodeSet(hierarchyNodes) {
    const result = new NodeSet();
    for (const hierarchyNode of hierarchyNodes) {
      const node = this._conceptNodeToNode(hierarchyNode);
      if (node.getSize() !== 0) result.addNode(node);
    }
    return result;
  }

  /** Role node → object property expression node (inverses stay inverses). */
  _objectPropertyNodeToNode(hierarchyNode) {
    const result = new Node();
    for (const role of hierarchyNode.getEquivalentElements()) {
      if (role instanceof P.AtomicRole) {
        result.add(E.objectProperty(role.iri));
      } else {
        result.add(E.objectInverseOf(E.objectProperty(role.inverseRole.iri)));
      }
    }
    return result;
  }

  _objectPropertyNodesToNodeSet(hierarchyNodes) {
    const result = new NodeSet();
    for (const hierarchyNode of hierarchyNodes) {
      result.addNode(this._objectPropertyNodeToNode(hierarchyNode));
    }
    return result;
  }

  _dataPropertyNodeToNode(hierarchyNode) {
    const result = new Node();
    for (const atomicRole of hierarchyNode.getEquivalentElements()) {
      result.add(E.dataProperty(atomicRole.iri));
    }
    return result;
  }

  _dataPropertyNodesToNodeSet(hierarchyNodes) {
    const result = new NodeSet();
    for (const hierarchyNode of hierarchyNodes) {
      result.addNode(this._dataPropertyNodeToNode(hierarchyNode));
    }
    return result;
  }

  // ---- printing -------------------------------------------------------------

  /**
   * Dump the hierarchies as flat functional-syntax axioms.
   *
   * Port of `Reasoner.dumpHierarchies(PrintWriter, boolean, boolean, boolean)`.
   *
   * OVERLOADED for backwards compatibility with the no-argument form this port
   * shipped first: called with no `out`, it classifies all three hierarchies and
   * RETURNS a human-readable string (the `Hierarchy.toString()` indented form).
   * Called with a writer, it emits `SubClassOf` / `EquivalentClasses` (and the
   * role analogues) via {@link HierarchyDumperFSS} and returns `undefined`.
   *
   * @param {{print: function(string): void, println: function(string=): void}} [out]
   * @param {boolean} [classes=true]            print the class hierarchy
   * @param {boolean} [objectProperties=true]   print the object property hierarchy
   * @param {boolean} [dataProperties=true]     print the data property hierarchy
   * @returns {string|undefined} a string only in the no-argument form
   */
  dumpHierarchies(out, classes = true, objectProperties = true, dataProperties = true) {
    if (out === undefined || out === null) {
      const parts = [];
      this.classifyClasses();
      parts.push(`Class hierarchy:\n${this.atomicConceptHierarchy.toString()}`);
      this.classifyObjectProperties();
      parts.push(`Object property hierarchy:\n${this.objectRoleHierarchy.toString()}`);
      this.classifyDataProperties();
      parts.push(`Data property hierarchy:\n${this.dataRoleHierarchy.toString()}`);
      return parts.join('\n');
    }
    const printer = new HierarchyDumperFSS(out);
    if (classes) {
      this.classifyClasses();
      printer.printAtomicConceptHierarchy(this.atomicConceptHierarchy);
    }
    if (objectProperties) {
      this.classifyObjectProperties();
      printer.printObjectPropertyHierarchy(this.objectRoleHierarchy);
    }
    if (dataProperties) {
      this.classifyDataProperties();
      printer.printDataPropertyHierarchy(this.dataRoleHierarchy);
    }
    return undefined;
  }

  /**
   * Print the hierarchies into a functional-syntax `Ontology( ... )` frame,
   * sorted and prefix-abbreviated.
   *
   * Port of `Reasoner.printHierarchies(PrintWriter, boolean, boolean, boolean)`;
   * this port previously had no equivalent.
   *
   * @param {{print: function(string): void, println: function(string=): void}} out
   * @param {boolean} [classes=true]
   * @param {boolean} [objectProperties=true]
   * @param {boolean} [dataProperties=true]
   */
  printHierarchies(out, classes = true, objectProperties = true, dataProperties = true) {
    const dlOntology = this.getDLOntology();
    const printer = new HierarchyPrinterFSS(out, `${dlOntology.getOntologyIRI() || ''}#`);
    if (classes) {
      this.classifyClasses();
      printer.loadAtomicConceptPrefixIRIs(this.atomicConceptHierarchy.getAllElements());
    }
    if (objectProperties) {
      this.classifyObjectProperties();
      printer.loadAtomicRolePrefixIRIs(dlOntology.getAllAtomicObjectRoles());
    }
    if (dataProperties) {
      this.classifyDataProperties();
      printer.loadAtomicRolePrefixIRIs(dlOntology.getAllAtomicDataRoles());
    }
    printer.startPrinting();
    let atLF = true;
    if (classes && !this.atomicConceptHierarchy.isEmpty()) {
      printer.printAtomicConceptHierarchy(this.atomicConceptHierarchy);
      atLF = false;
    }
    if (objectProperties && !this.objectRoleHierarchy.isEmpty()) {
      if (!atLF) out.println();
      printer.printRoleHierarchy(this.objectRoleHierarchy, true);
      atLF = false;
    }
    if (dataProperties && !this.dataRoleHierarchy.isEmpty()) {
      if (!atLF) out.println();
      printer.printRoleHierarchy(this.dataRoleHierarchy, false);
      atLF = false;
    }
    printer.endPrinting();
  }

  toString() {
    return `${REASONER_NAME} ${REASONER_VERSION}`;
  }
}

// ---- factory ----------------------------------------------------------------

/**
 * Convenience factory mirroring HermiT's `ReasonerFactory`.
 *
 * @param {object|object[]} ontology
 * @param {Configuration|object} [configuration]
 * @param {{bufferChanges?:boolean}} [options]
 */
function createReasoner(ontology, configuration, options = {}) {
  const config = configuration instanceof Configuration
    ? configuration.clone()
    : new Configuration(configuration || {});
  if (options.bufferChanges !== undefined) config.bufferChanges = options.bufferChanges;
  return new Reasoner(ontology, config);
}

/** A non-buffering reasoner: every `applyChange` takes effect immediately. */
function createNonBufferingReasoner(ontology, configuration) {
  return createReasoner(ontology, configuration, { bufferChanges: false });
}

module.exports = {
  Reasoner,
  createReasoner,
  createNonBufferingReasoner,
  Node,
  NodeSet,
  InconsistentOntologyException,
  FreshEntitiesException,
  EntailmentChecker,
  // conversion helpers, exported for the entailment checker and for tests
  H_class,
  H_objectProperty,
  H_role,
  H_dataProperty,
  H_individual,
  roleAssertion,
  atomicRoleOf,
  constantToLiteral,
  collectEntities,
  // internal IRIs
  IRI_QUERY_CONCEPT,
  IRI_PSEUDO_NOMINAL,
  IRI_FRESH_CONCEPT,
  IRI_NEGATED_SUPERPROPERTY,
  IRI_UNKNOWN_DATATYPE_A,
  IRI_ANONYMOUS_CONSTANTS,
  IRI_FRESH_CONSTANT,
  REASONER_NAME,
  REASONER_VERSION
};
