'use strict';

// ---------------------------------------------------------------------------
// test/same-as-cache.test.js — invalidation of the same-as / realisation state.
//
// `Reasoner` keeps four pieces of derived state that vouch for answers about the
// CURRENT ABox:
//
//   _sameAsEquivalenceClasses   Map<iri, NodeSet> of owl:sameAs classes
//   _sameAsComputed             flag reported by isPrecomputed(SAME_INDIVIDUAL)
//   _realisationCompleted       flag reported by isPrecomputed(CLASS_ASSERTIONS)
//   _propertyRealisationCompleted  ... by isPrecomputed(OBJECT_PROPERTY_ASSERTIONS)
//
// All four were SET and never RESET. `clearInferenceCaches()` nulled the three
// hierarchies and the per-individual type cache, but not these — even though
// same-as classes are MORE sensitive to an ABox change than the TBox hierarchies
// are. The result was a reachable soundness bug: retract
// `DifferentIndividuals(a b)`, assert `SameIndividual(a b)`, flush, and the
// reasoner still answered `getSameIndividuals(a) === {a}` where a fresh reasoner
// over the mutated ontology answers `{a, b}`. `isPrecomputed` also kept
// reporting `true` over the stale cache.
//
// Unlike the type-cache tests (which pin an OPTIMISATION by counting work), these
// tests pin CORRECTNESS: every assertion here fails against the pre-fix code
// with a genuinely wrong answer, not merely with extra tableau runs.
//
// A fresh reasoner is used as the oracle throughout, because the whole point is
// that the mutated reasoner must agree with one that never saw the old facts.
// ---------------------------------------------------------------------------

const test = require('node:test');
const assert = require('node:assert');

const { E, cls, ind, declaration, ontology, createR, iris } = require('./helpers');
const { Tableau } = require('../src/tableau/Tableau');

const A = cls('A');
const a = ind('a'), b = ind('b'), c = ind('c');

/** The configuration the same-as cache is actually populated under. */
const BY_SAME_AS = {
  throwInconsistentOntologyException: false,
  bufferChanges: true,
  individualNodeSetPolicy: 'BY_SAME_AS'
};

/**
 * Base ontology in which `a` and `b` are DISTINCT.
 *
 * The `DifferentIndividuals` axiom is returned alongside the list so a test can
 * retract the very same object — axioms are not interned, so a structurally
 * equal but distinct object would not be found by `removeAxiom`.
 */
function base() {
  const distinct = E.differentIndividuals([a, b]);
  const axioms = [
    declaration(A), declaration(a), declaration(b), declaration(c),
    distinct,
    E.classAssertion(A, a)
  ];
  return { axioms, distinct };
}

/** Mutate the ontology FIRST, then tell the reasoner — OWL API ordering. */
function change(ont, r, axiom, isAdd) {
  if (isAdd) ont.addAxiom(axiom);
  else ont.removeAxiom(axiom);
  r.applyChange({ axiom, isAdd });
}

/** Count `Tableau.isSatisfiable` calls made while `fn` runs. */
function countTableauRuns(fn) {
  const original = Tableau.prototype.isSatisfiable;
  let runs = 0;
  Tableau.prototype.isSatisfiable = function (...args) {
    runs++;
    return original.apply(this, args);
  };
  try { fn(); } finally { Tableau.prototype.isSatisfiable = original; }
  return runs;
}

// ---------------------------------------------------------------------------
test('baseline: distinct individuals are not the same as each other', () => {
  const { axioms } = base();
  const r = createR(ontology(axioms), BY_SAME_AS);
  try {
    assert.strictEqual(r.isConsistent(), true);
    assert.deepStrictEqual(iris(r.getSameIndividuals(a)), [E.iriString(a)]);
    assert.strictEqual(r.isSameIndividual(a, b), false);
  } finally { r.dispose(); }
});

test('getSameIndividuals on a reasoner that never precomputed returns a NodeSet', () => {
  // Guards the null-vs-undefined distinction: `_sameAsEquivalenceClasses` is
  // initialised to null, and `null !== undefined`, so a `map && map.get(k)`
  // guard would return null straight to the caller instead of computing.
  const { axioms } = base();
  const r = createR(ontology(axioms), BY_SAME_AS);
  try {
    assert.strictEqual(r._sameAsEquivalenceClasses, null);
    const result = r.getSameIndividuals(a);
    assert.notStrictEqual(result, null);
    assert.strictEqual(typeof result.getFlattened, 'function');
    assert.deepStrictEqual(iris(result), [E.iriString(a)]);
  } finally { r.dispose(); }
});

test('BUG REGRESSION: merging two individuals across a flush is visible', () => {
  const { axioms, distinct } = base();
  const ont = ontology(axioms);
  const r = createR(ont, BY_SAME_AS);
  try {
    // Prime the cache while a and b are still distinct.
    r.precomputeSameAsEquivalenceClasses();
    assert.strictEqual(r._sameAsComputed, true);
    assert.strictEqual(r.isPrecomputed('SAME_INDIVIDUAL'), true);
    assert.deepStrictEqual(iris(r.getSameIndividuals(a)), [E.iriString(a)]);

    // Now merge them: retract DifferentIndividuals, assert SameIndividual.
    const merged = E.sameIndividual([a, b]);
    change(ont, r, distinct, false);
    change(ont, r, merged, true);
    r.flush();

    // The oracle: a reasoner that only ever saw the merged ontology.
    const fresh = createR(ontology([
      declaration(A), declaration(a), declaration(b), declaration(c),
      merged, E.classAssertion(A, a)
    ]), BY_SAME_AS);
    let expected;
    try { expected = iris(fresh.getSameIndividuals(a)); } finally { fresh.dispose(); }

    assert.deepStrictEqual(expected, [E.iriString(a), E.iriString(b)]);
    // THE BUG: pre-fix this returned [a] — the stale cached class.
    assert.deepStrictEqual(iris(r.getSameIndividuals(a)), expected);
    assert.strictEqual(r.isSameIndividual(a, b), true);
  } finally { r.dispose(); }
});

test('BUG REGRESSION: splitting two individuals across a flush is visible', () => {
  // The opposite direction, so the fix cannot be a one-way "always recompute
  // bigger classes" accident.
  const { axioms, distinct } = base();
  const merged = E.sameIndividual([a, b]);
  const ont = ontology([...axioms.filter((x) => x !== distinct), merged]);
  const r = createR(ont, BY_SAME_AS);
  try {
    r.precomputeSameAsEquivalenceClasses();
    assert.deepStrictEqual(
      iris(r.getSameIndividuals(a)), [E.iriString(a), E.iriString(b)]);

    change(ont, r, merged, false);
    r.flush();

    const fresh = createR(ontology([
      declaration(A), declaration(a), declaration(b), declaration(c),
      E.classAssertion(A, a)
    ]), BY_SAME_AS);
    let expected;
    try { expected = iris(fresh.getSameIndividuals(a)); } finally { fresh.dispose(); }

    assert.deepStrictEqual(expected, [E.iriString(a)]);
    assert.deepStrictEqual(iris(r.getSameIndividuals(a)), expected);
    assert.strictEqual(r.isSameIndividual(a, b), false);
  } finally { r.dispose(); }
});

test('BUG REGRESSION: isPrecomputed stops claiming stale work is done', () => {
  const { axioms } = base();
  const ont = ontology(axioms);
  const r = createR(ont, BY_SAME_AS);
  try {
    r.realise();
    r.realiseObjectProperties();
    r.precomputeSameAsEquivalenceClasses();

    assert.strictEqual(r.isPrecomputed('CLASS_ASSERTIONS'), true);
    assert.strictEqual(r.isPrecomputed('OBJECT_PROPERTY_ASSERTIONS'), true);
    assert.strictEqual(r.isPrecomputed('SAME_INDIVIDUAL'), true);

    change(ont, r, E.classAssertion(cls('B'), c), true);
    r.flush();

    // All three flags must fall, or a caller that checks isPrecomputed before
    // deciding whether to precompute will silently skip the work.
    assert.strictEqual(r._realisationCompleted, false);
    assert.strictEqual(r._propertyRealisationCompleted, false);
    assert.strictEqual(r._sameAsComputed, false);
    assert.strictEqual(r.isPrecomputed('CLASS_ASSERTIONS'), false);
    assert.strictEqual(r.isPrecomputed('OBJECT_PROPERTY_ASSERTIONS'), false);
    assert.strictEqual(r.isPrecomputed('SAME_INDIVIDUAL'), false);
  } finally { r.dispose(); }
});

test('clearInferenceCaches drops the same-as cache map itself', () => {
  const { axioms } = base();
  const r = createR(ontology(axioms), BY_SAME_AS);
  try {
    r.precomputeSameAsEquivalenceClasses();
    const primed = r._sameAsEquivalenceClasses;
    assert.notStrictEqual(primed, null);
    assert.ok(primed.size > 0);

    r.clearInferenceCaches();

    assert.strictEqual(r._sameAsEquivalenceClasses, null);
    assert.strictEqual(r._sameAsComputed, false);
    // Not merely nulled — recomputed correctly on demand.
    assert.deepStrictEqual(iris(r.getSameIndividuals(a)), [E.iriString(a)]);
  } finally { r.dispose(); }
});

test('the cache still works when primed: a warm sweep costs nothing', () => {
  // Pinning the invalidation must not be read as licence to delete the cache.
  const { axioms } = base();
  const r = createR(ontology(axioms), BY_SAME_AS);
  try {
    const cold = countTableauRuns(() => r.precomputeSameAsEquivalenceClasses());
    assert.ok(cold > 0, 'precompute must do real work');

    const warm = countTableauRuns(() => {
      for (const i of r.getAllNamedIndividuals()) r.getSameIndividuals(i);
    });
    assert.strictEqual(warm, 0);
  } finally { r.dispose(); }
});

// ---------------------------------------------------------------------------
// The union-find sweep. `owl:sameAs` is an equivalence relation, so a class
// found once need not be recomputed per member, and a pair already decided
// different need not be re-tested from the other side. These tests pin the win
// by COUNTING WORK — the answers are asserted identical separately, so a
// result-comparison test alone would pass with or without the shortcut.
// ---------------------------------------------------------------------------

/** 8 individuals in 4 same-as classes of sizes 3, 2, 1, 2. */
function mergedAxioms() {
  const names = ['i1', 'i2', 'i3', 'i4', 'i5', 'i6', 'i7', 'i8'];
  const inds = names.map((n) => ind(n));
  const groups = [[0, 1, 2], [3, 4], [5], [6, 7]];
  const axioms = [declaration(A), ...inds.map(declaration)];
  for (const g of groups) {
    if (g.length > 1) axioms.push(E.sameIndividual(g.map((k) => inds[k])));
  }
  // One representative per group, pairwise distinct, keeps the groups apart.
  axioms.push(E.differentIndividuals(groups.map((g) => inds[g[0]])));
  return { axioms, inds, groups };
}

test('PERFORMANCE: precompute costs N(N-1)/2, not N(N-1), when all are distinct', () => {
  const { axioms } = base();
  const r = createR(ontology(axioms), BY_SAME_AS);
  try {
    // `precomputeSameAsEquivalenceClasses` calls `isConsistent()` first, which is
    // itself one tableau run. Warm it so the count measures the SWEEP alone —
    // otherwise the assertion is off by one and stops being exact.
    assert.strictEqual(r.isConsistent(), true);

    const n = r.getAllNamedIndividuals().size;
    const runs = countTableauRuns(() => r.precomputeSameAsEquivalenceClasses());
    // Non-vacuity: the sweep must actually test something.
    assert.ok(runs > 0, 'precompute must run tableau tests');
    assert.strictEqual(runs, (n * (n - 1)) / 2);
    assert.ok(runs < n * (n - 1), 'must beat the all-pairs cost');
  } finally { r.dispose(); }
});

test('PERFORMANCE: merged classes are computed once, not once per member', () => {
  const { axioms, inds } = mergedAxioms();
  const r = createR(ontology(axioms), BY_SAME_AS);
  try {
    assert.strictEqual(r.isConsistent(), true); // warm, as above

    const n = inds.length;
    const runs = countTableauRuns(() => r.precomputeSameAsEquivalenceClasses());
    // 8 individuals, all-pairs would be 56 and the no-merges shortcut 28. With
    // real merges the sweep needs far less than either: every member of an
    // already-found class is skipped as a representative AND as a candidate.
    // Measured: 14. Asserted as a bound so the exact figure can drift with the
    // hierarchy without the test becoming brittle.
    assert.ok(runs > 0, 'precompute must run tableau tests');
    assert.ok(runs < (n * (n - 1)) / 2,
      `expected < ${n * (n - 1) / 2} runs (merges must help), got ${runs}`);
  } finally { r.dispose(); }
});

test('the union-find sweep produces the correct equivalence classes', () => {
  const { axioms, inds, groups } = mergedAxioms();
  const r = createR(ontology(axioms), BY_SAME_AS);
  try {
    r.precomputeSameAsEquivalenceClasses();
    groups.forEach((g, gi) => {
      const expected = g.map((k) => E.iriString(inds[k])).sort();
      for (const k of g) {
        assert.deepStrictEqual(
          iris(r.getSameIndividuals(inds[k])), expected,
          `individual ${E.iriString(inds[k])} should sit in group ${gi}`);
      }
    });
    // And the classes really are disjoint.
    assert.strictEqual(r.isSameIndividual(inds[0], inds[3]), false);
    assert.strictEqual(r.isSameIndividual(inds[1], inds[2]), true);
  } finally { r.dispose(); }
});

test('every member of a class shares one NodeSet, and reading it does not mutate it', () => {
  const { axioms, inds } = mergedAxioms();
  const r = createR(ontology(axioms), BY_SAME_AS);
  try {
    r.precomputeSameAsEquivalenceClasses();
    const first = r.getSameIndividuals(inds[0]);
    // i1, i2, i3 are one class: the cache hands back the SAME instance.
    assert.strictEqual(r.getSameIndividuals(inds[1]), first);
    assert.strictEqual(r.getSameIndividuals(inds[2]), first);

    const sizeBefore = first.getFlattened().size;
    const contentsBefore = iris(first);
    // Both real callers read through getFlattened(); make sure that is a copy
    // and that repeated reads leave the shared instance alone.
    for (const i of inds) {
      const flattened = r.getSameIndividuals(i).getFlattened();
      flattened.clear(); // mutating the COPY must not touch the cached NodeSet
    }
    assert.strictEqual(first.getFlattened().size, sizeBefore);
    assert.deepStrictEqual(iris(first), contentsBefore);
  } finally { r.dispose(); }
});

test('the same-as bug is reachable under the DEFAULT node-set policy too', () => {
  // `getSameIndividuals` is public API; a caller need not opt into BY_SAME_AS to
  // hit the stale map, and `precomputeInferences(CLASS_ASSERTIONS)` populates it
  // under BY_NAME as well.
  const { axioms, distinct } = base();
  const ont = ontology(axioms);
  const r = createR(ont, {
    throwInconsistentOntologyException: false,
    bufferChanges: true
  });
  try {
    assert.strictEqual(r.configuration.individualNodeSetPolicy, 'BY_NAME');
    r.precomputeSameAsEquivalenceClasses();
    assert.deepStrictEqual(iris(r.getSameIndividuals(a)), [E.iriString(a)]);

    const merged = E.sameIndividual([a, b]);
    change(ont, r, distinct, false);
    change(ont, r, merged, true);
    r.flush();

    assert.deepStrictEqual(
      iris(r.getSameIndividuals(a)), [E.iriString(a), E.iriString(b)]);
  } finally { r.dispose(); }
});

// ---------------------------------------------------------------------------
// The COLD path. The memoisation lives in `getSameIndividuals` itself, not only
// in `precomputeSameAsEquivalenceClasses`, so a caller who never precomputes
// still benefits. This was the second measurement: before the refactor, ten
// repeat queries of one individual on `ogms.owl` cost 170 tableau runs and threw
// every one of them away. These tests pin that the cold path now caches.
// ---------------------------------------------------------------------------

test('COLD PATH: repeating one query costs one sweep, not ten', () => {
  const { axioms } = base();
  const r = createR(ontology(axioms), BY_SAME_AS);
  try {
    assert.strictEqual(r.isConsistent(), true); // warm: isConsistent is itself a run

    const first = countTableauRuns(() => r.getSameIndividuals(a));
    assert.ok(first > 0, 'the first query must do real work');

    const repeats = countTableauRuns(() => {
      for (let k = 0; k < 10; k++) r.getSameIndividuals(a);
    });
    assert.strictEqual(repeats, 0,
      `a repeated query must be free, cost ${repeats} runs`);
  } finally { r.dispose(); }
});

test('COLD PATH: a sweep without precompute still costs N(N-1)/2', () => {
  // The cached-candidate skip must work outside `precompute` too: after `a` is
  // known, querying `b` skips `a` without a tableau test.
  const { axioms } = base();
  const r = createR(ontology(axioms), BY_SAME_AS);
  try {
    assert.strictEqual(r.isConsistent(), true);
    assert.strictEqual(r._sameAsComputed, false, 'nothing precomputed yet');

    const n = r.getAllNamedIndividuals().size;
    const runs = countTableauRuns(() => {
      for (const i of r.getAllNamedIndividuals()) r.getSameIndividuals(i);
    });
    assert.strictEqual(runs, (n * (n - 1)) / 2);
    assert.ok(runs < n * (n - 1), 'must beat the all-pairs cost');
  } finally { r.dispose(); }
});

test('COLD PATH: a partially filled cache does NOT claim to be complete', () => {
  // `_sameAsComputed` means "EVERY individual's class is known", and
  // `isPrecomputed(SAME_INDIVIDUAL)` reports it. One cold query fills in one
  // class, so the flag must stay false — otherwise a caller would skip the
  // precompute it still needs.
  const { axioms } = base();
  const r = createR(ontology(axioms), BY_SAME_AS);
  try {
    assert.strictEqual(r.isConsistent(), true);
    assert.strictEqual(r.isPrecomputed('SAME_INDIVIDUAL'), false);

    r.getSameIndividuals(a);

    assert.ok(r._sameAsEquivalenceClasses.size > 0, 'the query did cache something');
    assert.strictEqual(r._sameAsComputed, false);
    assert.strictEqual(r.isPrecomputed('SAME_INDIVIDUAL'), false);

    r.precomputeSameAsEquivalenceClasses();
    assert.strictEqual(r.isPrecomputed('SAME_INDIVIDUAL'), true);
  } finally { r.dispose(); }
});

test('COLD PATH: precompute reuses what a cold query already cached', () => {
  const { axioms } = base();
  const fromScratch = createR(ontology(axioms), BY_SAME_AS);
  const afterCold = createR(ontology(axioms), BY_SAME_AS);
  try {
    assert.strictEqual(fromScratch.isConsistent(), true);
    assert.strictEqual(afterCold.isConsistent(), true);

    const full = countTableauRuns(() => fromScratch.precomputeSameAsEquivalenceClasses());
    assert.ok(full > 0);

    // Ask about `a` first; that caches a's class, so the later sweep has less to
    // do. If the cold path cached nothing, both counts would be equal.
    countTableauRuns(() => afterCold.getSameIndividuals(a));
    const partial = countTableauRuns(() => afterCold.precomputeSameAsEquivalenceClasses());

    assert.ok(partial < full,
      `precompute after a cold query should cost less than ${full}, got ${partial}`);
    // And the answers must still agree.
    assert.deepStrictEqual(
      iris(afterCold.getSameIndividuals(a)), iris(fromScratch.getSameIndividuals(a)));
  } finally { fromScratch.dispose(); afterCold.dispose(); }
});
