'use strict';

// ---------------------------------------------------------------------------
// test/edge-cases.test.js — degenerate-input regression guards.
//
// These are the boundary shapes an exhaustive smoke chain tends to skip: a
// completely empty ontology, singleton and self-contradictory individual
// axioms, a self-referential role under functionality, querying after
// `dispose()`, and the exact contents of `getSubClasses(⊤, false)` when
// nothing is declared. Each was first confirmed CORRECT by a throwaway probe
// (no defect found), then pinned here so a future change cannot silently
// regress it. The answers match the documented semantics — see the README
// "Public API" notes on `getSubClasses(⊤, false)` including the inferred
// `owl:Nothing`, and on `getTypes` of an untyped individual.
// ---------------------------------------------------------------------------

const test = require('node:test');
const assert = require('node:assert/strict');

const {
  E, AT, EX, cls, op, dp, ind, declaration, ontology, createR, iris
} = require('./helpers');

const THING = E.owlThing();
const NOTHING = E.owlNothing();
const sub = (a, b) => E.subclassOf(a, b);

test('a completely empty ontology is consistent and answers empty queries', () => {
  const r = createR(ontology([]));
  try {
    assert.equal(r.isConsistent(), true);
    // getSubClasses(⊤, false) INCLUDES the inferred owl:Nothing and EXCLUDES
    // ⊤, so with nothing declared the answer is exactly {owl:Nothing}.
    assert.deepEqual(iris(r.getSubClasses(THING, false)), [E.IRI_NOTHING]);
    // No individuals exist, so there are no instances of ⊤ either.
    assert.deepEqual(iris(r.getInstances(THING, false)), []);
  } finally { r.dispose(); }
});

test('a declaration-only ontology is consistent', () => {
  const r = createR(ontology([
    declaration(cls('A')), declaration(op('R')), declaration(dp('d')), declaration(ind('a'))
  ]));
  try { assert.equal(r.isConsistent(), true); } finally { r.dispose(); }
});

test('trivial subsumptions hold and ⊤ ⊑ ⊥ is inconsistent', () => {
  const A = cls('A');
  const r = createR(ontology([declaration(A)]));
  try {
    assert.equal(r.isEntailed(sub(A, A)), true);        // reflexive
    assert.equal(r.isEntailed(sub(A, THING)), true);     // everything ⊑ ⊤
    assert.equal(r.isEntailed(sub(NOTHING, A)), true);   // ⊥ ⊑ everything
  } finally { r.dispose(); }

  const bad = createR(ontology([sub(THING, NOTHING)]));
  try { assert.equal(bad.isConsistent(), false); } finally { bad.dispose(); }
});

test('duplicate subclass axioms do not disturb classification', () => {
  const A = cls('D1'), B = cls('D2');
  const ax = sub(A, B);
  const r = createR(ontology([declaration(A), declaration(B), ax, ax, ax]));
  try {
    assert.deepEqual(iris(r.getSuperClasses(A, true)), [EX + 'D2']);
  } finally { r.dispose(); }
});

test('singleton sameIndividual / differentIndividuals are consistent', () => {
  const a = ind('s1');
  const r1 = createR(ontology([declaration(a), E.sameIndividual([a])]));
  try { assert.equal(r1.isConsistent(), true); } finally { r1.dispose(); }

  const b = ind('s2');
  const r2 = createR(ontology([declaration(b), E.differentIndividuals([b])]));
  try { assert.equal(r2.isConsistent(), true); } finally { r2.dispose(); }
});

test('an individual declared different from itself is inconsistent', () => {
  const a = ind('s3');
  const r = createR(ontology([declaration(a), E.differentIndividuals([a, a])]));
  try { assert.equal(r.isConsistent(), false); } finally { r.dispose(); }
});

test('a self-referential role assertion is consistent under functionality', () => {
  const R = op('Rf'), a = ind('rf1');
  const r = createR(ontology([
    declaration(R), declaration(a),
    E.objectPropertyAssertion(R, a, a),
    { axiomType: AT.FUNCTIONAL_OBJECT_PROPERTY, property: R }
  ]));
  try { assert.equal(r.isConsistent(), true); } finally { r.dispose(); }
});

test('a functional role forces its two distinct fillers to clash', () => {
  const R = op('Rf2'), a = ind('fa'), b = ind('fb'), c = ind('fc');
  const r = createR(ontology([
    declaration(R), declaration(a), declaration(b), declaration(c),
    E.objectPropertyAssertion(R, a, b), E.objectPropertyAssertion(R, a, c),
    E.differentIndividuals([b, c]),
    { axiomType: AT.FUNCTIONAL_OBJECT_PROPERTY, property: R }
  ]));
  try { assert.equal(r.isConsistent(), false); } finally { r.dispose(); }
});

test('an inverse-functional role forces two distinct subjects to clash', () => {
  const R = op('Rif'), a = ind('ia'), b = ind('ib'), c = ind('ic');
  const r = createR(ontology([
    declaration(R), declaration(a), declaration(b), declaration(c),
    E.objectPropertyAssertion(R, b, a), E.objectPropertyAssertion(R, c, a),
    E.differentIndividuals([b, c]),
    { axiomType: AT.INVERSE_FUNCTIONAL_OBJECT_PROPERTY, property: R }
  ]));
  try { assert.equal(r.isConsistent(), false); } finally { r.dispose(); }
});

test('a 20-deep subclass chain classifies with ⊤ among the ancestors', () => {
  const cs = Array.from({ length: 20 }, (_, i) => cls(`C${i}`));
  const axioms = cs.map(declaration);
  for (let i = 0; i < 19; i++) axioms.push(sub(cs[i], cs[i + 1]));
  const r = createR(ontology(axioms));
  try {
    const anc = iris(r.getSuperClasses(cs[0], false));
    // C1..C19 (19) plus owl:Thing (1) = 20 ancestors of C0.
    assert.equal(anc.length, 20);
    assert.ok(anc.includes(EX + 'C19'));
    assert.ok(anc.includes(E.IRI_THING));
  } finally { r.dispose(); }
});

test('getTypes separates direct types from ancestors', () => {
  const A = cls('TA'), B = cls('TB'), a = ind('ta');
  const r = createR(ontology([
    declaration(A), declaration(B), declaration(a),
    sub(A, B), E.classAssertion(A, a)
  ]));
  try {
    const direct = iris(r.getTypes(a, true));
    const all = iris(r.getTypes(a, false));
    assert.ok(direct.includes(EX + 'TA'));
    assert.ok(!direct.includes(EX + 'TB'));  // B is an ancestor, not a direct type
    assert.ok(all.includes(EX + 'TB'));
  } finally { r.dispose(); }
});

test('an empty-string literal assertion is consistent', () => {
  const d = dp('dE'), a = ind('aE');
  const r = createR(ontology([
    declaration(d), declaration(a),
    E.dataPropertyAssertion(d, a, E.literal('', E.IRI_XSD_STRING))
  ]));
  try { assert.equal(r.isConsistent(), true); } finally { r.dispose(); }
});

test('querying a disposed reasoner throws rather than returning a stale answer', () => {
  const A = cls('Z');
  const r = createR(ontology([declaration(A)]));
  r.dispose();
  // Any throw is acceptable; a silent (possibly wrong) answer is not.
  assert.throws(() => r.isConsistent());
});
