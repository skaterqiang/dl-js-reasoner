'use strict';

// ---------------------------------------------------------------------------
// test/facade.test.js — the small `OWLReasoner`-style accessors.
//
// `getDataFactory()` mirrors HermiT's `Reasoner.getDataFactory()`, which returns
// the OWL API's `OWLDataFactory`. The port's analogue is the expression/axiom
// factory module `owl/OWLExpressions` (exported publicly as `E` / `OWLExpressions`).
// These tests pin that the method exists, returns that exact module (stateless,
// so shared across calls and reasoners), and yields working factories.
// ---------------------------------------------------------------------------

const test = require('node:test');
const assert = require('node:assert');

const { E, cls, ind, declaration, ontology, createR } = require('./helpers');

test('getDataFactory returns the OWLExpressions factory module', () => {
  const r = createR(ontology([declaration(cls('A')), declaration(ind('a'))]));
  assert.strictEqual(r.getDataFactory(), E);
});

test('getDataFactory is stable across calls and reasoners', () => {
  const r1 = createR(ontology([declaration(cls('A'))]));
  const r2 = createR(ontology([declaration(cls('B'))]));
  assert.strictEqual(r1.getDataFactory(), r1.getDataFactory());
  assert.strictEqual(r1.getDataFactory(), r2.getDataFactory());
});

test('the returned factory builds working expressions and axioms', () => {
  const r = createR(ontology([declaration(cls('A'))]));
  const F = r.getDataFactory();
  const A = F.owlClass('http://example.org/test#A');
  const ax = F.subclassOf(A, F.owlThing());
  assert.strictEqual(ax.axiomType, F.AxiomType.SUBCLASS_OF);
  assert.ok(F.isNamedClass(A));
});

test('getRootOntology returns the ontology passed to the constructor', () => {
  const ont = ontology([declaration(cls('A'))]);
  const r = createR(ont);
  assert.strictEqual(r.getRootOntology(), ont);
});
