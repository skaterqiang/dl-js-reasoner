'use strict';

// ---------------------------------------------------------------------------
// test/realisation-cache.test.js — the memoised per-individual type cache.
//
// `Reasoner.getDirectSuperConceptNodes` is the workhorse behind
// `getTypes(_, true)` and the innermost loop of `getInstances(C, true)`. Without
// `InstanceManager` it costs one tableau satisfiability test per candidate
// hierarchy node, and `getInstances(C, true)` recomputes it for EVERY individual
// once per class queried — an N-fold redundancy, since there are only as many
// distinct individuals as there are.
//
// The cache removes that. These tests pin it by COUNTING WORK, not by comparing
// answers: the answers were already correct, so a result-comparison test would
// pass with or without the cache and prove nothing. Two things are asserted:
//
//   1. the win — querying k classes costs no more than querying one;
//   2. the answers are unchanged by it.
//
// Cache INVALIDATION (the soundness half) is covered by section 19 of
// `scripts/smoke-incremental.js`, which primes the cache, mutates the ontology,
// flushes, and re-queries in both directions.
// ---------------------------------------------------------------------------

const test = require('node:test');
const assert = require('node:assert');

const { E, cls, ind, declaration, ontology, createR, iris } = require('./helpers');
const { Tableau } = require('../src/tableau/Tableau');

const A = cls('A'), B = cls('B'), C = cls('C'), D = cls('D');
const a1 = ind('a1'), a2 = ind('a2'), a3 = ind('a3'), a4 = ind('a4');

/** A ⊑ B ⊑ C, plus an unrelated D, with one individual per class. */
function axioms() {
  return [
    declaration(A), declaration(B), declaration(C), declaration(D),
    declaration(a1), declaration(a2), declaration(a3), declaration(a4),
    E.subclassOf(A, B),
    E.subclassOf(B, C),
    E.classAssertion(A, a1),
    E.classAssertion(B, a2),
    E.classAssertion(C, a3),
    E.classAssertion(D, a4)
  ];
}

/**
 * Count `Tableau.isSatisfiable` calls made by `fn`.
 *
 * Patching the PROTOTYPE is safe here: `Reasoner` calls
 * `tableau.isSatisfiable(...)` as an ordinary instance method, so the lookup is
 * dynamic. (Contrast a DESTRUCTURED import, which a prototype patch cannot
 * reach.) Always restored, so the count cannot leak into other test files.
 */
function countTableauRuns(fn) {
  const original = Tableau.prototype.isSatisfiable;
  let runs = 0;
  Tableau.prototype.isSatisfiable = function (...args) {
    runs++;
    return original.apply(this, args);
  };
  try {
    fn();
  } finally {
    Tableau.prototype.isSatisfiable = original;
  }
  return runs;
}

/**
 * A reasoner whose shared, expensive preconditions are already done, so the
 * counts below measure ONLY the individual queries.
 *
 * `isConsistent()` and `classifyClasses()` both cache, and neither is what the
 * per-individual memoisation replaces — including them would drown the signal.
 */
function warmed() {
  const r = createR(ontology(axioms()));
  r.isConsistent();
  r.classifyClasses();
  return r;
}

test('the four individuals have the expected direct types', () => {
  const r = warmed();
  try {
    assert.deepStrictEqual(iris(r.getTypes(a1, true)), [E.iriString(A)]);
    assert.deepStrictEqual(iris(r.getTypes(a2, true)), [E.iriString(B)]);
    assert.deepStrictEqual(iris(r.getTypes(a3, true)), [E.iriString(C)]);
    assert.deepStrictEqual(iris(r.getTypes(a4, true)), [E.iriString(D)]);
    // A ⊑ B ⊑ C, so the non-direct answer accumulates the ancestors.
    assert.deepStrictEqual(iris(r.getTypes(a1, false)),
      [E.iriString(A), E.iriString(B), E.iriString(C), E.iriString(E.owlThing())].sort());
  } finally { r.dispose(); }
});

test('getInstances answers are correct for every class', () => {
  const r = warmed();
  try {
    assert.deepStrictEqual(iris(r.getInstances(A, true)), [E.iriString(a1)]);
    assert.deepStrictEqual(iris(r.getInstances(B, true)), [E.iriString(a2)]);
    assert.deepStrictEqual(iris(r.getInstances(C, true)), [E.iriString(a3)]);
    assert.deepStrictEqual(iris(r.getInstances(D, true)), [E.iriString(a4)]);
    // Non-direct: a1 is an A, hence also a B and a C.
    assert.deepStrictEqual(iris(r.getInstances(C, false)),
      [E.iriString(a1), E.iriString(a2), E.iriString(a3)].sort());
  } finally { r.dispose(); }
});

test('PERFORMANCE: querying k classes costs no more than querying one', () => {
  const classes = [A, B, C, D];

  // One class on a cold cache: this is the baseline per-class cost, and it must
  // be non-zero or the rest of the test would pass vacuously.
  const r1 = warmed();
  let costOne;
  try {
    costOne = countTableauRuns(() => r1.getInstances(A, true));
  } finally { r1.dispose(); }
  assert.ok(costOne > 0, 'the first query must actually run the tableau');

  // All four classes on a cold cache. Every individual's direct types are
  // computed during the first query and then REUSED, so the total must equal
  // the cost of that single query rather than four times it.
  const r2 = warmed();
  let costAll;
  try {
    costAll = countTableauRuns(() => {
      for (const c of classes) r2.getInstances(c, true);
    });
  } finally { r2.dispose(); }
  assert.strictEqual(costAll, costOne,
    'four getInstances queries must cost the same as one');
});

test('PERFORMANCE: without the cache the cost is multiplicative in the classes', () => {
  const classes = [A, B, C, D];

  const cached = warmed();
  let costCached;
  try {
    costCached = countTableauRuns(() => {
      for (const c of classes) cached.getInstances(c, true);
    });
  } finally { cached.dispose(); }

  // Simulate the pre-memoisation behaviour by dropping the cache between
  // classes, so each query recomputes every individual's direct types.
  const uncached = warmed();
  let costUncached;
  try {
    costUncached = countTableauRuns(() => {
      for (const c of classes) {
        uncached.directSuperConceptNodesCache.clear();
        uncached.getInstances(c, true);
      }
    });
  } finally { uncached.dispose(); }

  // `>=` rather than `===` so the assertion states the property that matters
  // (the cache saves at least a factor of the number of classes) without
  // hard-coding the exact hierarchy-search cost. It is DISCRIMINATING: if the
  // cache did nothing the two costs would be equal and this would fail.
  assert.ok(costUncached >= classes.length * costCached,
    `clearing the cache between queries must cost at least ${classes.length}x more ` +
    `(cached=${costCached}, uncached=${costUncached})`);
});

test('PERFORMANCE: repeated getTypes for one individual is free after the first', () => {
  const r = warmed();
  try {
    const first = countTableauRuns(() => r.getTypes(a1, true));
    assert.ok(first > 0, 'the first getTypes must actually run the tableau');

    // Everything derived from the direct-type nodes is served from the cache.
    const again = countTableauRuns(() => {
      r.getTypes(a1, true);
      r.getTypes(a1, false);
      r.hasType(a1, A, true);
    });
    assert.strictEqual(again, 0,
      'getTypes and the DIRECT hasType branch must be served from the cache');

    // The NON-DIRECT hasType branch is deliberately NOT cached: it runs one
    // tableau test per call, because rewriting it to walk the cached ancestors
    // would make a single-class query several times SLOWER (see the README's
    // "What is deliberately NOT cached"). Asserting the cost here pins that
    // decision, so an accidental change in either direction is caught.
    const nonDirect = countTableauRuns(() => r.hasType(a1, C, false));
    assert.strictEqual(nonDirect, 1,
      'hasType(_, _, false) must still cost exactly one tableau test');
  } finally { r.dispose(); }
});

test('the cache is keyed per individual, not shared across them', () => {
  const r = warmed();
  try {
    countTableauRuns(() => r.getTypes(a1, true));
    assert.strictEqual(r.directSuperConceptNodesCache.size, 1);

    countTableauRuns(() => r.getTypes(a2, true));
    assert.strictEqual(r.directSuperConceptNodesCache.size, 2,
      'a different individual must not be served a1\'s entry');

    // And the answers really are that individual's own.
    assert.deepStrictEqual(iris(r.getTypes(a2, true)), [E.iriString(B)]);
  } finally { r.dispose(); }
});

test('the cached node set is not mutated by the queries that read it', () => {
  const r = warmed();
  try {
    r.getTypes(a1, true);
    const key = E.iriString(a1);
    const cached = r.directSuperConceptNodesCache.get(key);
    assert.ok(cached instanceof Set, 'the cache holds a Set of hierarchy nodes');
    const sizeBefore = cached.size;
    const contentsBefore = [...cached].map((n) => n.getRepresentative().iri).sort().join('|');

    // Every reader must treat the cached Set as immutable — it is shared.
    r.getTypes(a1, true);
    r.getTypes(a1, false);
    r.getInstances(A, true);
    r.getInstances(C, false);
    r.hasType(a1, B, false);

    assert.strictEqual(r.directSuperConceptNodesCache.get(key), cached,
      'the same Set instance must still be cached');
    assert.strictEqual(cached.size, sizeBefore);
    assert.strictEqual(
      [...cached].map((n) => n.getRepresentative().iri).sort().join('|'),
      contentsBefore);
  } finally { r.dispose(); }
});

test('clearInferenceCaches drops the per-individual type cache', () => {
  const r = warmed();
  try {
    r.getTypes(a1, true);
    assert.ok(r.directSuperConceptNodesCache.size > 0);

    r.clearInferenceCaches();
    assert.strictEqual(r.directSuperConceptNodesCache.size, 0,
      'an ontology change must invalidate every cached type answer');

    // And the answers are recomputed, still correctly.
    const runs = countTableauRuns(() => r.getTypes(a1, true));
    assert.ok(runs > 0, 'the answer must be recomputed after invalidation');
    assert.deepStrictEqual(iris(r.getTypes(a1, true)), [E.iriString(A)]);
  } finally { r.dispose(); }
});
