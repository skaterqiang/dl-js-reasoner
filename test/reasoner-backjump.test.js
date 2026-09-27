'use strict';

// ---------------------------------------------------------------------------
// test/reasoner-backjump.test.js — end-to-end non-Horn reasoning.
//
// All four real sample ontologies under protege-js/sample/ontologies are Horn,
// so `smoke-reasoner-real.js` exercises NO backtracking at all. These tests
// build deliberately non-Horn axioms so that DisjunctionBranchingPoint,
// dependency-directed backjumping and clash handling actually run.
// ---------------------------------------------------------------------------

const test = require('node:test');
const assert = require('node:assert/strict');

const { createReasoner } = require('../src/reasoner/Reasoner');
const { E, EX, cls, op, ind, declaration, ontology, recordingReasoner, iris } = require('./helpers');

const A = cls('A'), B = cls('B'), C = cls('C');
const B1 = cls('B1'), C1 = cls('C1'), B2 = cls('B2'), C2 = cls('C2'), B3 = cls('B3'), C3 = cls('C3');
const X = cls('X');
const R = op('R');
const a = ind('a'), b = ind('b'), c = ind('c');

test('a Horn ontology pushes no branching points and never backtracks', () => {
  const { r, rec } = recordingReasoner([
    declaration(A), declaration(B), declaration(a),
    E.subclassOf(A, B),
    E.classAssertion(A, a)
  ]);
  try {
    assert.equal(r.isConsistent(), true);
    // `direct=false`: B is an *indirect* type of a (A is the direct one), so
    // `hasType(a, B, true)` is legitimately false.
    assert.equal(r.hasType(a, B, false), true);
    assert.equal(r.hasType(a, B, true), false);
    assert.equal(r.isEntailed(E.classAssertion(B, a)), true);
    assert.equal(rec.branchingPointsPushed, 0);
    assert.equal(rec.backtracks.length, 0);
  } finally { r.dispose(); }
});

test('a disjunction ladder backtracks but stays consistent', () => {
  // A ⊑ B1⊔C1, B1 ⊑ B2⊔C2, B2 ⊑ B3⊔C3, and every Ci is unsatisfiable. The
  // reasoner must explore the ladder, clash on each Ci, and still find a model.
  //
  // NOTE: `isConsistent`/`isSatisfiable` alone push branching points but never
  // backtrack here — the first disjunct already yields a model. It is
  // `isEntailed`, which adds the negation of the query and so forces the wrong
  // choices to clash, that produces the backtracks (and a level-skipping one:
  // from 2 down to 1).
  const { r, rec } = recordingReasoner([
    declaration(A), declaration(B1), declaration(C1),
    declaration(B2), declaration(C2), declaration(B3), declaration(C3),
    E.subclassOf(A, E.objectUnionOf([B1, C1])),
    E.subclassOf(B1, E.objectUnionOf([B2, C2])),
    E.subclassOf(B2, E.objectUnionOf([B3, C3])),
    E.subclassOf(C1, E.owlNothing()),
    E.subclassOf(C2, E.owlNothing()),
    E.subclassOf(C3, E.owlNothing())
  ]);
  try {
    assert.equal(r.isConsistent(), true);
    assert.equal(r.isSatisfiable(A), true);
    assert.ok(rec.branchingPointsPushed >= 3, 'expected branching points');
    assert.equal(rec.backtracks.length, 0, 'no backtrack needed to find a model');

    assert.equal(r.isEntailed(E.subclassOf(A, B3)), true);
    assert.equal(r.isEntailed(E.subclassOf(A, C1)), false);
    assert.ok(rec.backtracks.length > 0, 'expected backtracks from isEntailed');
    assert.ok(rec.maxSkipped >= 1, 'expected at least one level-skipping backjump');
  } finally { r.dispose(); }
});

test('both disjuncts clashing makes the class unsatisfiable', () => {
  // A ⊑ B⊔C, A ⊑ X, B ⊑ ¬X, C ⊑ ¬X. Neither choice survives, so A ≡ ⊥.
  const r = createReasoner(ontology([
    declaration(A), declaration(B), declaration(C), declaration(X),
    E.subclassOf(A, E.objectUnionOf([B, C])),
    E.subclassOf(A, X),
    E.subclassOf(B, E.objectComplementOf(X)),
    E.subclassOf(C, E.objectComplementOf(X))
  ]));
  try {
    assert.equal(r.isConsistent(), true);
    assert.equal(r.isSatisfiable(A), false);
    assert.equal(r.isSatisfiable(B), true);
  } finally { r.dispose(); }
});

test('classification under non-Horn axioms yields the expected hierarchy', () => {
  const Top = cls('Top'), L = cls('L'), Rt = cls('Rt'), Leaf = cls('Leaf'), Bad = cls('Bad');
  const r = createReasoner(ontology([
    declaration(Top), declaration(L), declaration(Rt), declaration(Leaf), declaration(Bad),
    E.subclassOf(Top, E.objectUnionOf([L, Rt])),
    E.subclassOf(L, Leaf),
    E.subclassOf(Rt, Leaf),
    E.subclassOf(Bad, E.owlNothing())
  ]));
  try {
    r.classifyClasses();
    const bottom = r.getBottomClassNode();
    assert.ok([...bottom.getEntities()].some((x) => E.isOWLNothing(x)),
      'the bottom node must contain owl:Nothing');
    const unsat = iris(r.getUnsatisfiableClasses());
    assert.deepEqual(unsat, [EX + 'Bad', E.IRI_NOTHING]);
  } finally { r.dispose(); }
});

test('all five blocking strategies agree on a non-Horn ontology', () => {
  const { BLOCKING_STRATEGY_TYPE } = require('../src/Configuration');
  const axioms = [
    declaration(A), declaration(B), declaration(C), declaration(R),
    E.subclassOf(A, E.objectSomeValuesFrom(R, B)),
    E.subclassOf(B, E.objectSomeValuesFrom(R, C)),
    E.subclassOf(A, E.objectUnionOf([B, C])),
    E.subclassOf(B, E.objectComplementOf(C)),
    E.classAssertion(A, a)
  ];

  let previous = null;
  for (const strategy of Object.values(BLOCKING_STRATEGY_TYPE)) {
    const r = createReasoner(ontology(axioms), { blockingStrategyType: strategy });
    try {
      const result = {
        consistent: r.isConsistent(),
        satA: r.isSatisfiable(A),
        satB: r.isSatisfiable(B),
        satC: r.isSatisfiable(C)
      };
      if (previous !== null) {
        assert.deepEqual(result, previous, `strategy ${strategy} disagrees`);
      }
      previous = result;
    } finally { r.dispose(); }
  }
  assert.equal(previous.consistent, true);
});

test('disjunction learning on and off agree', () => {
  const axioms = [
    declaration(A), declaration(B1), declaration(C1),
    declaration(B2), declaration(C2), declaration(B3), declaration(C3),
    E.subclassOf(A, E.objectUnionOf([B1, C1])),
    E.subclassOf(B1, E.objectUnionOf([B2, C2])),
    E.subclassOf(B2, E.objectUnionOf([B3, C3])),
    E.subclassOf(C1, E.owlNothing()),
    E.subclassOf(C2, E.owlNothing()),
    E.subclassOf(C3, E.owlNothing()),
    E.classAssertion(A, a)
  ];

  let previous = null;
  for (const learn of [true, false]) {
    const { r, rec } = recordingReasoner(axioms, { useDisjunctionLearning: learn });
    try {
      const result = { consistent: r.isConsistent(), satA: r.isSatisfiable(A) };
      if (previous !== null) {
        assert.deepEqual(result, previous, `useDisjunctionLearning=${learn} disagrees`);
      }
      previous = result;
      assert.ok(rec.branchingPointsPushed > 0);
    } finally { r.dispose(); }
  }
});

test('a functional role with two distinct fillers clashes only when they differ', () => {
  // ⊤ ⊑ ≤1 R.⊤ with R(a,b) and R(a,c). Consistent iff b and c may be the same
  // individual; DifferentIndividuals([b,c]) forces a clash.
  const plain = createReasoner(ontology([
    declaration(R), declaration(a), declaration(b), declaration(c),
    E.subclassOf(E.owlThing(), E.objectMaxCardinality(1, R)),
    E.objectPropertyAssertion(R, a, b),
    E.objectPropertyAssertion(R, a, c)
  ]));
  try { assert.equal(plain.isConsistent(), true); } finally { plain.dispose(); }

  const distinct = createReasoner(ontology([
    declaration(R), declaration(a), declaration(b), declaration(c),
    E.subclassOf(E.owlThing(), E.objectMaxCardinality(1, R)),
    E.objectPropertyAssertion(R, a, b),
    E.objectPropertyAssertion(R, a, c),
    E.differentIndividuals([b, c])
  ]));
  try { assert.equal(distinct.isConsistent(), false); } finally { distinct.dispose(); }
});
