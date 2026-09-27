'use strict';

// ---------------------------------------------------------------------------
// test/blocking-configuration.test.js
//
// `createBlockingStrategy` used to take a single boolean and ignore all three
// blocking enums, so `DIRECT_BLOCKING_TYPE`, `BLOCKING_STRATEGY_TYPE` and
// `BLOCKING_SIGNATURE_CACHE_TYPE` were exported-but-inert: setting them changed
// nothing and told the caller nothing. These tests pin the now-honest mapping
// (a port of the three switches in HermiT's `Reasoner.createTableau`) and, just
// as importantly, pin the DEGRADATIONS — an option this port cannot honour must
// say so through `warningMonitor` rather than silently doing something else.
// ---------------------------------------------------------------------------

const test = require('node:test');
const assert = require('node:assert');

const {
  createBlockingStrategy,
  AnywhereBlocking,
  AncestorBlocking,
  SingleDirectBlockingChecker,
  PairWiseDirectBlockingChecker,
  isCoreBlockingStrategy
} = require('../src/tableau/BlockingStrategy');
const {
  DIRECT_BLOCKING_TYPE,
  BLOCKING_STRATEGY_TYPE,
  BLOCKING_SIGNATURE_CACHE_TYPE,
  EXISTENTIAL_STRATEGY_TYPE
} = require('../src/Configuration');
const { CountingMonitor } = require('../src/monitor/CountingMonitor');

const { ontology, cls, op, ind, declaration, createR } = require('./helpers');
const E = require('../src/owl/OWLExpressions');

const EX = 'http://example.org/test#';
const A = cls('A');
const B = cls('B');
const C = cls('C');
const R = op('R');
const a = ind('a');

/** Collect warnings instead of printing them. */
function collector() {
  const messages = [];
  return { messages, warningMonitor: (m) => messages.push(m) };
}

/** `createBlockingStrategy` plus a warning collector, returning both. */
function build(config, hasInverseRoles = false, hasNominals = false) {
  const w = collector();
  const strategy = createBlockingStrategy(
    Object.assign({}, config, { warningMonitor: w.warningMonitor }),
    hasInverseRoles, hasNominals);
  return { strategy, warnings: w.messages };
}

// ===========================================================================
// DIRECT_BLOCKING_TYPE
// ===========================================================================

test('DIRECT_BLOCKING_TYPE.OPTIMAL picks the checker implied by hasInverseRoles', () => {
  assert.ok(build({ directBlockingType: DIRECT_BLOCKING_TYPE.OPTIMAL }).strategy.checker
    instanceof SingleDirectBlockingChecker, 'no inverses -> single');
  assert.ok(build({ directBlockingType: DIRECT_BLOCKING_TYPE.OPTIMAL }, true).strategy.checker
    instanceof PairWiseDirectBlockingChecker, 'inverses -> pairwise');
});

test('DIRECT_BLOCKING_TYPE.SINGLE forces single blocking even with inverse roles', () => {
  const { strategy, warnings } = build({ directBlockingType: DIRECT_BLOCKING_TYPE.SINGLE }, true);
  assert.ok(strategy.checker instanceof SingleDirectBlockingChecker);
  // HermiT documents this override as not generally sound; it must not warn,
  // because the user asked for exactly what they got.
  assert.deepEqual(warnings, []);
});

test('DIRECT_BLOCKING_TYPE.PAIR_WISE forces pairwise blocking without inverses', () => {
  const { strategy, warnings } = build({ directBlockingType: DIRECT_BLOCKING_TYPE.PAIR_WISE }, false);
  assert.ok(strategy.checker instanceof PairWiseDirectBlockingChecker);
  assert.deepEqual(warnings, []);
});

test('an unknown direct blocking type throws', () => {
  assert.throws(() => build({ directBlockingType: 'TRIANGLE' }),
    /Unknown direct blocking type: TRIANGLE/);
});

// ===========================================================================
// BLOCKING_STRATEGY_TYPE
// ===========================================================================

test('ANYWHERE and OPTIMAL both build AnywhereBlocking', () => {
  for (const t of [BLOCKING_STRATEGY_TYPE.ANYWHERE, BLOCKING_STRATEGY_TYPE.OPTIMAL]) {
    const { strategy, warnings } = build({ blockingStrategyType: t });
    assert.ok(strategy instanceof AnywhereBlocking, `${t} -> AnywhereBlocking`);
    assert.deepEqual(warnings, [], `${t} is fully implemented and must not warn`);
  }
});

test('ANCESTOR builds AncestorBlocking, not AnywhereBlocking', () => {
  const { strategy, warnings } = build({ blockingStrategyType: BLOCKING_STRATEGY_TYPE.ANCESTOR });
  assert.ok(strategy instanceof AncestorBlocking);
  assert.ok(!(strategy instanceof AnywhereBlocking),
    'AncestorBlocking must not be a subclass of AnywhereBlocking');
  assert.deepEqual(warnings, [], 'ancestor blocking is fully implemented');
});

test('the two core strategies degrade to ANYWHERE and warn', () => {
  for (const t of [BLOCKING_STRATEGY_TYPE.SIMPLE_CORE, BLOCKING_STRATEGY_TYPE.COMPLEX_CORE]) {
    const { strategy, warnings } = build({ blockingStrategyType: t });
    assert.ok(strategy instanceof AnywhereBlocking, `${t} degrades to AnywhereBlocking`);
    assert.equal(warnings.length, 1, `${t} must warn exactly once`);
    assert.match(warnings[0], new RegExp(t), 'the warning names the requested strategy');
    assert.match(warnings[0], /ANYWHERE/, 'the warning names the fallback');
  }
});

test('an unknown blocking strategy type throws', () => {
  assert.throws(() => build({ blockingStrategyType: 'SIDEWAYS' }),
    /Unknown blocking strategy type: SIDEWAYS/);
});

test('a core strategy still honours an explicit direct blocking type', () => {
  // HermiT would substitute a *Validated* checker here; those are not ported,
  // so the plain checker named by directBlockingType must be used.
  const { strategy } = build({
    blockingStrategyType: BLOCKING_STRATEGY_TYPE.SIMPLE_CORE,
    directBlockingType: DIRECT_BLOCKING_TYPE.PAIR_WISE
  });
  assert.ok(strategy.checker instanceof PairWiseDirectBlockingChecker);
});

test('isCoreBlockingStrategy classifies exactly the two core values', () => {
  assert.equal(isCoreBlockingStrategy(BLOCKING_STRATEGY_TYPE.SIMPLE_CORE), true);
  assert.equal(isCoreBlockingStrategy(BLOCKING_STRATEGY_TYPE.COMPLEX_CORE), true);
  assert.equal(isCoreBlockingStrategy(BLOCKING_STRATEGY_TYPE.ANYWHERE), false);
  assert.equal(isCoreBlockingStrategy(BLOCKING_STRATEGY_TYPE.ANCESTOR), false);
  assert.equal(isCoreBlockingStrategy(BLOCKING_STRATEGY_TYPE.OPTIMAL), false);
});

// ===========================================================================
// BLOCKING_SIGNATURE_CACHE_TYPE
// ===========================================================================

test('CACHED installs a cache; NOT_CACHED leaves the strategy uncached', () => {
  const cached = build({ blockingSignatureCacheType: BLOCKING_SIGNATURE_CACHE_TYPE.CACHED });
  assert.ok(cached.strategy.blockingSignatureCache !== null, 'CACHED installs a cache');
  assert.deepEqual(cached.warnings, []);

  const uncached = build({ blockingSignatureCacheType: BLOCKING_SIGNATURE_CACHE_TYPE.NOT_CACHED });
  assert.equal(uncached.strategy.blockingSignatureCache, null, 'NOT_CACHED runs uncached');
  assert.deepEqual(uncached.warnings, []);
});

test('a stock Configuration produces no warnings at all', () => {
  // The default blockingSignatureCacheType is CACHED (matching HermiT). The
  // cache is fully implemented, so a stock configuration installs it silently.
  const { Configuration } = require('../src/Configuration');
  const w = collector();
  const cfg = new Configuration();
  cfg.warningMonitor = w.warningMonitor;
  const strategy = createBlockingStrategy(cfg, false, false);
  assert.ok(strategy.blockingSignatureCache !== null, 'stock Configuration caches');
  assert.deepEqual(w.messages, []);
});

test('nominals suppress the cache, as in HermiT', () => {
  // HermiT skips the cache switch entirely when the ontology has nominals,
  // because caching is unsound there. Asking for CACHED is then a no-op rather
  // than a broken promise, so no cache is installed and nothing warns.
  const { strategy, warnings } = build(
    { blockingSignatureCacheType: BLOCKING_SIGNATURE_CACHE_TYPE.CACHED }, false, true);
  assert.equal(strategy.blockingSignatureCache, null, 'nominals disable the cache');
  assert.deepEqual(warnings, []);
});

test('a core strategy still installs the cache on its ANYWHERE fallback', () => {
  // A core request degrades to ANYWHERE (one warning), and for ANYWHERE HermiT
  // honours CACHED — so the cache is installed. Only the core degradation warns.
  const { strategy, warnings } = build({
    blockingStrategyType: BLOCKING_STRATEGY_TYPE.COMPLEX_CORE,
    blockingSignatureCacheType: BLOCKING_SIGNATURE_CACHE_TYPE.CACHED
  });
  assert.ok(strategy instanceof AnywhereBlocking);
  assert.ok(strategy.blockingSignatureCache !== null, 'the fallback honours CACHED');
  assert.equal(warnings.length, 1, `got: ${JSON.stringify(warnings)}`);
  assert.match(warnings[0], /COMPLEX_CORE/, 'the core-strategy warning fires');
});

test('an unknown cache type throws even when the cache would be skipped', () => {
  // Validated unconditionally so a typo is caught rather than swallowed.
  assert.throws(() => build({ blockingSignatureCacheType: 'MAYBE' }, false, true),
    /Unknown blocking signature cache type: MAYBE/);
});

// ===========================================================================
// AncestorBlocking specifics
// ===========================================================================

test('AncestorBlocking.computeIsBlocked throws, as in HermiT', () => {
  const { strategy } = build({ blockingStrategyType: BLOCKING_STRATEGY_TYPE.ANCESTOR });
  assert.throws(() => strategy.computeIsBlocked(null),
    /ancestor blocking cannot be used with a lazy expansion strategy/);
});

test('both ported strategies report themselves exact', () => {
  for (const t of [BLOCKING_STRATEGY_TYPE.ANYWHERE, BLOCKING_STRATEGY_TYPE.ANCESTOR]) {
    const { strategy } = build({ blockingStrategyType: t });
    assert.equal(strategy.isExact(), true, `${t} is exact`);
    assert.equal(strategy.isPermanentAssertion(A, null), true);
  }
});

// ===========================================================================
// End to end: the option really reaches the tableau
// ===========================================================================

/** A ⊑ ∃R.A forces an infinite chain, so blocking decides when it stops. */
function chainAxioms() {
  return [
    declaration(A), declaration(R), declaration(B), declaration(C),
    E.subclassOf(A, E.objectSomeValuesFrom(R, A)),
    E.subclassOf(A, E.objectUnionOf([B, C])),
    E.subclassOf(B, E.objectComplementOf(C)),
    E.classAssertion(A, a)
  ];
}

/** The blocking strategy a reasoner actually ended up using. */
function strategyOf(r) {
  return r.getTableau().existentialExpansionStrategy.blockingStrategy;
}

test('blockingStrategyType reaches the tableau built by the reasoner', () => {
  const cases = [
    [BLOCKING_STRATEGY_TYPE.ANYWHERE, AnywhereBlocking],
    [BLOCKING_STRATEGY_TYPE.OPTIMAL, AnywhereBlocking],
    [BLOCKING_STRATEGY_TYPE.ANCESTOR, AncestorBlocking],
    // The degraded core strategies must still land on a working AnywhereBlocking.
    [BLOCKING_STRATEGY_TYPE.SIMPLE_CORE, AnywhereBlocking],
    [BLOCKING_STRATEGY_TYPE.COMPLEX_CORE, AnywhereBlocking]
  ];
  for (const [type, expected] of cases) {
    const r = createR(ontology(chainAxioms()), { blockingStrategyType: type });
    try {
      assert.equal(r.isConsistent(), true, `${type}: consistent`);
      assert.ok(strategyOf(r) instanceof expected, `${type} -> ${expected.name}`);
    } finally { r.dispose(); }
  }
});

test('directBlockingType reaches the tableau built by the reasoner', () => {
  const cases = [
    [DIRECT_BLOCKING_TYPE.SINGLE, SingleDirectBlockingChecker],
    [DIRECT_BLOCKING_TYPE.PAIR_WISE, PairWiseDirectBlockingChecker],
    [DIRECT_BLOCKING_TYPE.OPTIMAL, SingleDirectBlockingChecker] // no inverses here
  ];
  for (const [type, expected] of cases) {
    const r = createR(ontology(chainAxioms()), { directBlockingType: type });
    try {
      assert.equal(r.isConsistent(), true, `${type}: consistent`);
      assert.ok(strategyOf(r).checker instanceof expected, `${type} -> ${expected.name}`);
    } finally { r.dispose(); }
  }
});

test('every direct blocking type agrees on an ontology WITH inverse roles', () => {
  // PAIR_WISE is the sound choice here; SINGLE is a deliberate override that
  // HermiT also permits. All three must at least agree on consistency and
  // satisfiability for this small ontology.
  const axioms = [
    declaration(A), declaration(B), declaration(C), declaration(R),
    E.subclassOf(A, E.objectSomeValuesFrom(R, B)),
    E.subclassOf(B, E.objectSomeValuesFrom(E.objectInverseOf(R), C)),
    E.subclassOf(A, E.objectUnionOf([B, C])),
    E.subclassOf(B, E.objectComplementOf(C)),
    E.classAssertion(A, a)
  ];
  let previous = null;
  for (const type of Object.values(DIRECT_BLOCKING_TYPE)) {
    const r = createR(ontology(axioms), { directBlockingType: type });
    try {
      const result = {
        consistent: r.isConsistent(),
        satA: r.isSatisfiable(A),
        satB: r.isSatisfiable(B),
        satC: r.isSatisfiable(C)
      };
      if (previous !== null) assert.deepEqual(result, previous, `${type} disagrees`);
      previous = result;
    } finally { r.dispose(); }
  }
  assert.equal(previous.consistent, true);
  assert.equal(previous.satB, true);
});

test('degradation warnings surface through the reasoner configuration', () => {
  const w = collector();
  const r = createR(ontology(chainAxioms()), {
    blockingStrategyType: BLOCKING_STRATEGY_TYPE.SIMPLE_CORE,
    blockingSignatureCacheType: BLOCKING_SIGNATURE_CACHE_TYPE.CACHED,
    warningMonitor: w.warningMonitor
  });
  try {
    r.isConsistent();
    // Only the core strategy degrades (to ANYWHERE); CACHED is honoured on the
    // fallback, so exactly one warning fires.
    assert.equal(w.messages.length, 1, `got: ${JSON.stringify(w.messages)}`);
    assert.match(w.messages[0], /SIMPLE_CORE/);
    assert.ok(strategyOf(r).blockingSignatureCache !== null, 'the fallback caches');
  } finally { r.dispose(); }
});

test('ancestor blocking builds at least as many nodes as anywhere blocking', () => {
  // Anywhere blocking may use a non-ancestor as a blocker, so it can only ever
  // prune more. This is the observable difference that proves ANCESTOR is wired
  // up rather than silently aliasing ANYWHERE.
  function nodesFor(type) {
    const r = createR(ontology(chainAxioms()), { blockingStrategyType: type });
    try {
      r.isConsistent();
      return r.getTableau().numberOfNodeCreations;
    } finally { r.dispose(); }
  }
  const anywhere = nodesFor(BLOCKING_STRATEGY_TYPE.ANYWHERE);
  const ancestor = nodesFor(BLOCKING_STRATEGY_TYPE.ANCESTOR);
  assert.ok(anywhere > 0, 'the chain ontology must create nodes');
  assert.ok(ancestor >= anywhere,
    `ancestor (${ancestor}) should create >= anywhere (${anywhere}) nodes`);
});

test('all five strategies agree on an ontology where blocking actually fires', () => {
  // `A ⊑ ∃R.A` makes the tree grow forever, so termination depends entirely on
  // blocking — this is what makes the comparison meaningful. (The non-Horn
  // ontology in reasoner-backjump.test.js has only a finite chain, where
  // blocking may never trigger at all.)
  //
  // Before the configuration was wired up this comparison was vacuous: every
  // value produced the same AnywhereBlocking. ANCESTOR now really differs.
  const axioms = [
    declaration(A), declaration(B), declaration(C), declaration(R),
    E.subclassOf(A, E.objectSomeValuesFrom(R, A)),
    E.subclassOf(A, E.objectUnionOf([B, C])),
    E.subclassOf(B, E.objectComplementOf(C)),
    E.subclassOf(B, E.objectSomeValuesFrom(R, C)),
    E.classAssertion(A, a)
  ];

  let previous = null;
  const seen = new Set();
  let maxBlocked = 0;
  for (const strategyType of Object.values(BLOCKING_STRATEGY_TYPE)) {
    for (const directBlockingType of Object.values(DIRECT_BLOCKING_TYPE)) {
      const r = createR(ontology(axioms),
        { blockingStrategyType: strategyType, directBlockingType });
      try {
        const result = {
          consistent: r.isConsistent(),
          satA: r.isSatisfiable(A),
          satB: r.isSatisfiable(B),
          satC: r.isSatisfiable(C),
          superOfB: [...r.getSuperClasses(B, true).getFlattened()]
            .map((x) => E.iriString(x)).sort()
        };
        const key = `${strategyType}/${directBlockingType}`;
        seen.add(strategyOf(r).constructor.name);
        // Prove the machinery under test actually ran: without blocking the
        // `A ⊑ ∃R.A` chain would never terminate, so a completed run with a
        // blocked node is the evidence that this comparison is meaningful.
        const tableau = r.getTableau();
        let blocked = 0;
        for (let n = tableau.firstTableauNode; n !== null; n = n.nextTableauNode) {
          if (n.isBlocked()) blocked++;
        }
        if (blocked > maxBlocked) maxBlocked = blocked;
        if (previous !== null) {
          assert.deepEqual(result, previous, `${key} disagrees`);
        }
        previous = result;
      } finally { r.dispose(); }
    }
  }
  assert.ok(maxBlocked > 0,
    'blocking must actually fire, otherwise this comparison proves nothing');
  assert.equal(previous.consistent, true);
  assert.equal(previous.satA, true);
  assert.equal(previous.satB, true);
  assert.equal(previous.satC, true);
  // Both strategies must have been exercised, not just AnywhereBlocking.
  assert.deepEqual([...seen].sort(), ['AncestorBlocking', 'AnywhereBlocking']);
});

test('all 45 strategy x checker x existential combos agree, with blocking firing', () => {
  // The previous test fixes the DEFAULT existential strategy (CREATION_ORDER).
  // Under INDIVIDUAL_REUSE / EL a linear chain `A ⊑ ∃R.A` gets collapsed onto
  // the individual `a`, so blocking never fires and the comparison is vacuous.
  // `A ⊑ ≥2 R.A` demands TWO distinct successors per node — reuse cannot
  // satisfy that — so the forest grows under EVERY existential strategy and
  // blocking provably fires in all of them.
  //
  // Measured via CountingMonitor, which ACCUMULATES across a run. Reading
  // `tableau.firstTableauNode` after the last query only sees that query's
  // leftover state (often a single node), which is why the monitor is used here.
  const axioms = [
    declaration(A), declaration(B), declaration(C), declaration(R),
    E.subclassOf(A, E.objectMinCardinality(2, R, A)),
    E.subclassOf(A, E.objectUnionOf([B, C])),
    E.subclassOf(B, E.objectComplementOf(C)),
    E.classAssertion(A, a)
  ];

  let previous = null;
  const seen = new Set();
  let totalBlocked = 0;
  let runs = 0;
  for (const existentialStrategyType of Object.values(EXISTENTIAL_STRATEGY_TYPE)) {
    for (const strategyType of Object.values(BLOCKING_STRATEGY_TYPE)) {
      for (const directBlockingType of Object.values(DIRECT_BLOCKING_TYPE)) {
        const monitor = new CountingMonitor();
        const r = createR(ontology(axioms), {
          existentialStrategyType,
          blockingStrategyType: strategyType,
          directBlockingType,
          monitor
        });
        try {
          const result = {
            consistent: r.isConsistent(),
            satA: r.isSatisfiable(A),
            satB: r.isSatisfiable(B),
            satC: r.isSatisfiable(C)
          };
          const key = `${existentialStrategyType}/${strategyType}/${directBlockingType}`;
          seen.add(strategyOf(r).constructor.name);
          const summary = monitor.getSummary();
          totalBlocked += summary.blockedNodes || 0;
          runs++;
          if (previous !== null) {
            assert.deepEqual(result, previous, `${key} disagrees`);
          }
          previous = result;
        } finally { r.dispose(); }
      }
    }
  }
  assert.equal(runs, 45, 'every combination must run');
  assert.ok(totalBlocked > 0,
    'blocking must fire in at least one run, or the comparison proves nothing');
  assert.equal(previous.consistent, true);
  assert.equal(previous.satA, true);
  // Both blocking implementations must have been exercised.
  assert.deepEqual([...seen].sort(), ['AncestorBlocking', 'AnywhereBlocking']);
});
