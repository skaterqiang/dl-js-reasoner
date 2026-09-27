'use strict';
/**
 * Reasoner configuration.
 *
 * Port of `org.semanticweb.HermiT.Configuration`.
 *
 * HermiT's Configuration is a mutable bag of public fields plus a handful of
 * enums. This port keeps the same shape but uses frozen string-constant objects
 * for the enums so that `Configuration.BLOCKING_STRATEGY.ANYWHERE` reads
 * naturally and `===` comparison works.
 *
 * Only the options this port actually honours are wired through to the tableau;
 * the rest are kept for API fidelity and are documented as such.
 */

/** Tableau monitor selection. Only NONE is implemented in this port. */
const TABLEAU_MONITOR_TYPE = Object.freeze({
  NONE: 'NONE',
  TIMING: 'TIMING',
  TIMING_WITH_PAUSE: 'TIMING_WITH_PAUSE',
  DEBUGGER_NO_HISTORY: 'DEBUGGER_NO_HISTORY',
  DEBUGGER_HISTORY_ON: 'DEBUGGER_HISTORY_ON'
});

/**
 * Which direct-blocking checker to use. All three values are honoured.
 *
 * HermiT substitutes its *Validated* checkers when a core blocking strategy is
 * requested; those are not ported, and core strategies degrade to `ANYWHERE`,
 * so the plain checkers are always used here.
 */
const DIRECT_BLOCKING_TYPE = Object.freeze({
  /**
   * Single blocking even when the ontology has inverse roles. As in HermiT this
   * is a deliberate override and is not generally sound for such ontologies.
   */
  SINGLE: 'SINGLE',
  /** Pairwise blocking even when the ontology has no inverse roles. */
  PAIR_WISE: 'PAIR_WISE',
  /** single when the ontology has no inverse roles, pairwise otherwise. */
  OPTIMAL: 'OPTIMAL'
});

/** Which nodes are considered as candidate blockers. */
const BLOCKING_STRATEGY_TYPE = Object.freeze({
  /** A blocker may be any earlier unblocked tree node. Implemented. */
  ANYWHERE: 'ANYWHERE',
  /** A blocker must be one of the node's own ancestors. Implemented. */
  ANCESTOR: 'ANCESTOR',
  /**
   * Approximate core blocking. NOT implemented — degrades to `ANYWHERE` with a
   * `warningMonitor` warning. Results are unaffected (both are exact); only the
   * size of the constructed model differs.
   */
  COMPLEX_CORE: 'COMPLEX_CORE',
  /** Approximate core blocking. NOT implemented — see `COMPLEX_CORE`. */
  SIMPLE_CORE: 'SIMPLE_CORE',
  /**
   * HermiT picks SIMPLE_CORE for ontologies with nominals and ANYWHERE
   * otherwise. SIMPLE_CORE is not ported, so this port always resolves OPTIMAL
   * to ANYWHERE — which is also HermiT's choice in the no-nominals case.
   */
  OPTIMAL: 'OPTIMAL'
});

/**
 * Blocker caching. `CACHED` enables the ported `blocking/BlockingSignatureCache`:
 * blocker shapes are remembered across models so a later node can be blocked by
 * a remembered signature instead of by a live node. Pure performance — reasoning
 * results are unchanged. The default is `CACHED`, matching HermiT.
 */
const BLOCKING_SIGNATURE_CACHE_TYPE = Object.freeze({
  /** Cache blocker signatures across models (HermiT's default). */
  CACHED: 'CACHED',
  /** Run without a blocking signature cache. */
  NOT_CACHED: 'NOT_CACHED'
});

/** How existentials are expanded. */
const EXISTENTIAL_STRATEGY_TYPE = Object.freeze({
  /** Breadth-first-ish; deterministic. HermiT's default. */
  CREATION_ORDER: 'CREATION_ORDER',
  /** Reuse existing individuals first; smaller models, more non-determinism. */
  INDIVIDUAL_REUSE: 'INDIVIDUAL_REUSE',
  /** Deterministic individual reuse for EL ontologies. */
  EL: 'EL'
});

/** How realisation groups individuals into nodes. */
const INDIVIDUAL_NODE_SET_POLICY = Object.freeze({
  BY_NAME: 'BY_NAME',
  BY_SAME_AS: 'BY_SAME_AS'
});

/** What to do when a query mentions an entity absent from the signature. */
const FRESH_ENTITY_POLICY = Object.freeze({
  ALLOW: 'ALLOW',
  DISALLOW: 'DISALLOW'
});

/** Which inference types `precomputeInferences` should run. */
const INFERENCE_TYPE = Object.freeze({
  CLASS_HIERARCHY: 'CLASS_HIERARCHY',
  OBJECT_PROPERTY_HIERARCHY: 'OBJECT_PROPERTY_HIERARCHY',
  DATA_PROPERTY_HIERARCHY: 'DATA_PROPERTY_HIERARCHY',
  CLASS_ASSERTIONS: 'CLASS_ASSERTIONS',
  OBJECT_PROPERTY_ASSERTIONS: 'OBJECT_PROPERTY_ASSERTIONS',
  DATA_PROPERTY_ASSERTIONS: 'DATA_PROPERTY_ASSERTIONS',
  SAME_INDIVIDUAL: 'SAME_INDIVIDUAL',
  DIFFERENT_INDIVIDUALS: 'DIFFERENT_INDIVIDUALS',
  DISJOINT_CLASSES: 'DISJOINT_CLASSES'
});

class PrepareReasonerInferences {
  constructor(overrides = {}) {
    this.classClassificationRequired = true;
    this.objectPropertyClassificationRequired = true;
    this.dataPropertyClassificationRequired = true;
    this.objectPropertyDomainsRequired = true;
    this.objectPropertyRangesRequired = true;
    this.realisationRequired = true;
    this.objectPropertyRealisationRequired = true;
    this.dataPropertyRealisationRequired = true;
    this.sameAs = true;
    Object.assign(this, overrides);
  }
}

class Configuration {
  /**
   * @param {object} [overrides] any public field below may be overridden
   */
  constructor(overrides = {}) {
    /**
     * Sink for non-fatal degradations: unsupported datatypes skipped during
     * clausification, and configuration options this port cannot honour (core
     * blocking, the blocking signature cache). Called as a plain function with
     * a single message string; when null, degradations are silent.
     * @type {?(function(string): void)}
     */
    this.warningMonitor = null;
    /**
     * Progress reporting. Duck-typed; the reasoner calls
     * `reasonerTaskStarted(description)`, `reasonerTaskProgressChanged(step, total)`
     * and `reasonerTaskStopped()` when present.
     * @type {?object}
     */
    this.reasonerProgressMonitor = null;

    this.tableauMonitorType = TABLEAU_MONITOR_TYPE.NONE;
    this.directBlockingType = DIRECT_BLOCKING_TYPE.OPTIMAL;
    this.blockingStrategyType = BLOCKING_STRATEGY_TYPE.OPTIMAL;
    // Matches HermiT's default. The signature cache IS ported (see
    // blocking/BlockingSignatureCache.js), so a stock Configuration caches.
    this.blockingSignatureCacheType = BLOCKING_SIGNATURE_CACHE_TYPE.CACHED;
    this.existentialStrategyType = EXISTENTIAL_STRATEGY_TYPE.CREATION_ORDER;

    /** Ignore axioms mentioning datatypes this port cannot handle. */
    this.ignoreUnsupportedDatatypes = false;

    /** Custom tableau monitor (duck-typed). */
    this.monitor = null;

    /**
     * Options for the well-known monitor selected by `tableauMonitorType`.
     * For `TIMING` this is passed to `new Timer(options)` and for
     * `TIMING_WITH_PAUSE` to `new TimerWithPause(options)`; both accept
     * `{out, write, writeLine}` — supply `write`/`writeLine` to capture the
     * report instead of printing it to stdout. `TimerWithPause` additionally
     * accepts `{pause, wait}`: `pause: false` disables the after-report stdin
     * pause, and `wait` replaces the blocking read entirely (used by tests).
     * @type {?object}
     */
    this.monitorOptions = null;

    /** Passed straight through to the Tableau; currently unused. */
    this.parameters = new Map();

    /**
     * Abort any single reasoning task after this many milliseconds.
     * `-1` means "no limit".
     */
    this.individualTaskTimeout = -1;

    this.individualNodeSetPolicy = INDIVIDUAL_NODE_SET_POLICY.BY_NAME;
    this.freshEntityPolicy = FRESH_ENTITY_POLICY.ALLOW;

    /**
     * Prefer disjuncts that have caused fewer clashes. On by default in HermiT.
     */
    this.useDisjunctionLearning = true;

    /** Buffer ontology changes until `flush()`. */
    this.bufferChanges = true;

    /** Throw when a query is issued against an inconsistent ontology. */
    this.throwInconsistentOntologyException = true;

    /** @type {?PrepareReasonerInferences} */
    this.prepareReasonerInferences = null;

    /**
     * Use `QuasiOrderClassification` even for Horn (deterministic) ontologies.
     * Slower in the common case but occasionally more robust.
     */
    this.forceQuasiOrderClassification = false;

    Object.assign(this, overrides);
  }

  /** HermiT calls this `getTimeOut()`. */
  getTimeOut() {
    return this.individualTaskTimeout;
  }

  getIndividualNodeSetPolicy() {
    return this.individualNodeSetPolicy;
  }

  getProgressMonitor() {
    return this.reasonerProgressMonitor;
  }

  getFreshEntityPolicy() {
    return this.freshEntityPolicy;
  }

  /** Shallow copy with a fresh `parameters` map (mirrors `Configuration.clone`). */
  clone() {
    const result = new Configuration();
    Object.assign(result, this);
    result.parameters = new Map(this.parameters);
    return result;
  }
}

Configuration.TABLEAU_MONITOR_TYPE = TABLEAU_MONITOR_TYPE;
Configuration.DIRECT_BLOCKING_TYPE = DIRECT_BLOCKING_TYPE;
Configuration.BLOCKING_STRATEGY_TYPE = BLOCKING_STRATEGY_TYPE;
Configuration.BLOCKING_SIGNATURE_CACHE_TYPE = BLOCKING_SIGNATURE_CACHE_TYPE;
Configuration.EXISTENTIAL_STRATEGY_TYPE = EXISTENTIAL_STRATEGY_TYPE;
Configuration.INDIVIDUAL_NODE_SET_POLICY = INDIVIDUAL_NODE_SET_POLICY;
Configuration.FRESH_ENTITY_POLICY = FRESH_ENTITY_POLICY;
Configuration.INFERENCE_TYPE = INFERENCE_TYPE;
Configuration.PrepareReasonerInferences = PrepareReasonerInferences;

module.exports = {
  Configuration,
  PrepareReasonerInferences,
  TABLEAU_MONITOR_TYPE,
  DIRECT_BLOCKING_TYPE,
  BLOCKING_STRATEGY_TYPE,
  BLOCKING_SIGNATURE_CACHE_TYPE,
  EXISTENTIAL_STRATEGY_TYPE,
  INDIVIDUAL_NODE_SET_POLICY,
  FRESH_ENTITY_POLICY,
  INFERENCE_TYPE
};
