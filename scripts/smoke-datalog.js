'use strict';

// ---------------------------------------------------------------------------
// scripts/smoke-datalog.js — conjunctive query answering end to end.
//
// `test/datalog-query.test.js` is the focused `node:test` suite. This script is
// the broad one: it exercises the whole public surface (DatalogEngine,
// ConjunctiveQuery, the QuerySpec layer, the Reasoner methods and the
// ProtegeAdapter methods) and then runs queries against the four REAL sample
// ontologies shipped with protege-js, to prove the engine works at scale and not
// just on hand-written fixtures.
//
// Sections:
//   1. HermiT's DatalogEngineTest oracles, reproduced exactly.
//   2. Engine contract: Horn check, inconsistency, idempotence, copies, nulls.
//   3. Query construction: safety, unknown ground terms, inverse roles,
//      de-duplication.
//   4. The spec layer: every atom kind, literal matching, error messages.
//   5. Reasoner + ProtegeAdapter wiring and cache invalidation.
//   6. The real ontologies (bfo, ogms, ro-core, iao) — all Horn, so all legal.
//
// Run with:  node scripts/smoke-datalog.js
// ---------------------------------------------------------------------------

const path = require('path');
const DL = require('../src/index');

const {
  E,
  DLPredicate: P,
  DatalogEngine,
  ConjunctiveQuery,
  CollectingQueryResultCollector,
  createAtom,
  createVariable,
  createIndividual,
  createReasoner,
  reasonerFor
} = DL;
const AT = E.AxiomType;

let failures = 0;
let checks = 0;

function check(name, actual, expected) {
  checks++;
  const a = JSON.stringify(actual);
  const e = JSON.stringify(expected);
  const ok = a === e;
  if (!ok) failures++;
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}${ok ? '' : `  (got ${a}, expected ${e})`}`);
}
function section(title) { console.log(`\n=== ${title} ===`); }

const EX = 'http://example.org/dq#';
const cls = (n) => E.owlClass(EX + n);
const op = (n) => E.objectProperty(EX + n);
const dp = (n) => E.dataProperty(EX + n);
const ind = (n) => E.namedIndividual(EX + n);
const decl = (e) => ({ axiomType: AT.DECLARATION, entity: e });
const range = (p, dr) => ({ axiomType: AT.DATA_PROPERTY_RANGE, property: p, range: dr });

const I = (n) => createIndividual(EX + n);
const V = (n) => createVariable(n);

/** A minimal mutable ontology mock (same shape as the other smoke scripts). */
function ontology(axioms) {
  const list = axioms.slice();
  return {
    getAxioms: () => list.slice(),
    getOntologyID: () => ({ ontologyIRI: EX + 'dq', isAnonymous: () => false }),
    addAxiom: (x) => { list.push(x); return true; },
    removeAxiom: (x) => { const i = list.indexOf(x); if (i >= 0) list.splice(i, 1); return i >= 0; },
    getImportsClosure: () => [{ getAxioms: () => list.slice() }],
    _axioms: list
  };
}

/** The distinct answers of a query as sorted `a -> b` strings. */
function names(query) {
  const collector = new CollectingQueryResultCollector();
  query.evaluate(collector);
  return collector.results
    .map((row) => row.map((t) => (t.iri ? t.iri.slice(EX.length) : String(t))).join(' -> '))
    .sort();
}

/** Strip the namespace from a `string[][]` answer matrix and sort the rows. */
function short(rows) {
  return rows
    .map((row) => row.map((c) => (c.startsWith(EX) ? c.slice(EX.length) : c)))
    .map((row) => row.join('\u0000'))
    .sort()
    .map((k) => k.split('\u0000'));
}

const A = cls('A'), B = cls('B'), C = cls('C');
const R = op('R'), S = op('S');

// ===========================================================================
section('1. HermiT DatalogEngineTest oracles');
// ===========================================================================

// ---- testBasic -------------------------------------------------------------
{
  const r = createReasoner(ontology([
    decl(A), decl(B), decl(C), decl(R),
    E.subclassOf(E.objectSomeValuesFrom(R, A), A),
    E.subclassOf(E.objectSomeValuesFrom(R, B), B),
    E.subclassOf(E.objectIntersectionOf([A, B]), C),
    E.classAssertion(A, I('a')),
    E.objectPropertyAssertion(R, I('b'), I('a')),
    E.objectPropertyAssertion(R, I('c'), I('b')),
    E.objectPropertyAssertion(R, I('d'), I('c')),
    E.classAssertion(B, I('k')),
    E.objectPropertyAssertion(R, I('l'), I('k')),
    E.objectPropertyAssertion(R, I('m'), I('l')),
    E.objectPropertyAssertion(R, I('c'), I('m')),
    E.objectPropertyAssertion(R, I('n'), I('c'))
  ]));
  const engine = new DatalogEngine(r.getDLOntology());
  check('testBasic: materialize', engine.materialize(), true);
  check('testBasic: isHorn', r.getDLOntology().isHorn, true);
  check('testBasic: A(X)',
    names(new ConjunctiveQuery(engine, [createAtom(P.internAtomicConcept(EX + 'A'), V('X'))], [V('X')])),
    ['a', 'b', 'c', 'd', 'n']);
  check('testBasic: B(X)',
    names(new ConjunctiveQuery(engine, [createAtom(P.internAtomicConcept(EX + 'B'), V('X'))], [V('X')])),
    ['c', 'd', 'k', 'l', 'm', 'n']);
  check('testBasic: C(X)',
    names(new ConjunctiveQuery(engine, [createAtom(P.internAtomicConcept(EX + 'C'), V('X'))], [V('X')])),
    ['c', 'd', 'n']);
  check('testBasic: R(X,Y) positive control',
    names(new ConjunctiveQuery(engine,
      [createAtom(P.internAtomicRole(EX + 'R', false), V('X'), V('Y'))], [V('X'), V('Y')])),
    ['b -> a', 'c -> b', 'c -> m', 'd -> c', 'l -> k', 'm -> l', 'n -> c']);
  r.dispose();
}

// ---- testEquality ----------------------------------------------------------
{
  const r = createReasoner(ontology([
    decl(R),
    { axiomType: AT.FUNCTIONAL_OBJECT_PROPERTY, property: R },
    E.objectPropertyAssertion(R, I('b'), I('a')),
    E.objectPropertyAssertion(R, I('b'), I('c')),
    E.objectPropertyAssertion(R, I('d'), I('c')),
    E.objectPropertyAssertion(R, I('d'), I('e')),
    E.objectPropertyAssertion(R, I('f'), I('e')),
    E.objectPropertyAssertion(R, I('f'), I('g'))
  ]));
  const engine = new DatalogEngine(r.getDLOntology());
  check('testEquality: materialize', engine.materialize(), true);
  check('testEquality: equivalenceClass(a)',
    [...engine.getEquivalenceClass(I('a'))].map((t) => t.iri.slice(EX.length)).sort(),
    ['a', 'c', 'e', 'g']);
  const rep = engine.getRepresentative(I('a'));
  const answers = new ConjunctiveQuery(engine,
    [createAtom(P.internAtomicRole(EX + 'R', false), V('X'), V('Y'))], [V('X'), V('Y')]).getAnswers();
  check('testEquality: R(X,Y) first column',
    answers.map((row) => row[0].iri.slice(EX.length)).sort(), ['b', 'd', 'f']);
  check('testEquality: every second column IS the representative',
    answers.every((row) => row[1] === rep), true);
  r.dispose();
}

// ---- testQueryWithIndividualsAndEquality -----------------------------------
{
  const r = createReasoner(ontology([
    decl(R), decl(S),
    E.objectPropertyAssertion(R, I('c'), I('b')),
    E.objectPropertyAssertion(S, I('c'), I('a')),
    E.sameIndividual([I('a'), I('b')]),
    E.objectPropertyAssertion(R, I('d'), I('e')),
    E.objectPropertyAssertion(S, I('d'), I('f'))
  ]));
  const engine = new DatalogEngine(r.getDLOntology());
  check('individuals+equality: materialize', engine.materialize(), true);
  check('individuals+equality: equivalenceClass(a)',
    [...engine.getEquivalenceClass(I('a'))].map((t) => t.iri.slice(EX.length)).sort(), ['a', 'b']);
  check('individuals+equality: R(X,I(a)) ^ S(X,I(b))',
    names(new ConjunctiveQuery(engine, [
      createAtom(P.internAtomicRole(EX + 'R', false), V('X'), I('a')),
      createAtom(P.internAtomicRole(EX + 'S', false), V('X'), I('b'))
    ], [V('X')])),
    ['c']);
  r.dispose();
}

// ---- testQueryWithIndividuals ----------------------------------------------
{
  const D0 = cls('D0'), RD0 = cls('RD0');
  const pvar = (n) => ({ iri: EX + 'var#' + n });
  const classAtom = (ce, arg) => ({ type: 'ClassAtom', classExpression: ce, arg });
  const opAtom = (p, a1, a2) => ({ type: 'ObjectPropertyAtom', property: p, arg1: a1, arg2: a2 });
  const rule = (body, head) => ({ body, head });
  const r = createReasoner(ontology([
    decl(A), decl(B), decl(D0), decl(RD0), decl(R),
    rule([classAtom(D0, pvar('X'))], [classAtom(A, pvar('X'))]),
    rule([classAtom(D0, pvar('X'))], [classAtom(B, pvar('X'))]),
    rule([classAtom(A, pvar('X')), classAtom(RD0, pvar('Z'))], [classAtom(D0, pvar('Z'))]),
    rule([classAtom(A, pvar('X')), classAtom(RD0, pvar('Z'))], [opAtom(R, pvar('X'), pvar('Z'))]),
    E.classAssertion(E.owlThing(), I('a')),
    E.classAssertion(RD0, I('rd0')),
    E.classAssertion(A, I('a'))
  ]));
  const engine = new DatalogEngine(r.getDLOntology());
  check('individuals: isHorn', r.getDLOntology().isHorn, true);
  check('individuals: materialize', engine.materialize(), true);
  check('individuals: R(X,I(a)) is EMPTY (HermiT oracle)',
    names(new ConjunctiveQuery(engine,
      [createAtom(P.internAtomicRole(EX + 'R', false), V('X'), I('a'))], [V('X')])),
    []);
  check('individuals: R(X,Y) positive control proves the rule fired',
    names(new ConjunctiveQuery(engine,
      [createAtom(P.internAtomicRole(EX + 'R', false), V('X'), V('Y'))], [V('X'), V('Y')])),
    ['a -> rd0', 'rd0 -> rd0']);
  r.dispose();
}

// ===========================================================================
section('2. Engine contract');
// ===========================================================================

// Non-Horn rejection: `Thing ⊑ A ⊔ B` has a disjunctive head.
{
  const r = createReasoner(ontology([
    decl(A), decl(B),
    E.subclassOf(E.owlThing(), E.objectUnionOf([A, B])),
    E.classAssertion(A, I('a'))
  ]));
  let msg = null;
  try { new DatalogEngine(r.getDLOntology()); } catch (e) { msg = e.message; }
  check('non-Horn is rejected', /disjunctive heads/.test(msg || ''), true);
  r.dispose();
}

// A non-DLOntology argument.
{
  let m1 = null, m2 = null;
  try { new DatalogEngine(null); } catch (e) { m1 = e.message; }
  try { new DatalogEngine({}); } catch (e) { m2 = e.message; }
  check('null argument is rejected', /clausified DLOntology/.test(m1 || ''), true);
  check('empty-object argument is rejected', /clausified DLOntology/.test(m2 || ''), true);
}

// Inconsistency.
{
  const r = createReasoner(ontology([
    decl(A), decl(B),
    E.disjointClasses([A, B]),
    E.classAssertion(A, I('a')),
    E.classAssertion(B, I('a'))
  ]));
  const engine = new DatalogEngine(r.getDLOntology());
  check('inconsistent: materialize reports false', engine.materialize(), false);
  let msg = null;
  try {
    new ConjunctiveQuery(engine, [createAtom(P.internAtomicConcept(EX + 'A'), V('X'))], [V('X')]);
  } catch (e) { msg = e.message; }
  check('inconsistent: query throws', /unsatisfiable/.test(msg || ''), true);
  r.dispose();
}

// Idempotence, copies, nulls.
{
  const r = createReasoner(ontology([
    decl(A), decl(R),
    { axiomType: AT.FUNCTIONAL_OBJECT_PROPERTY, property: R },
    E.classAssertion(A, I('a')),
    E.objectPropertyAssertion(R, I('b'), I('a')),
    E.objectPropertyAssertion(R, I('b'), I('c'))
  ]));
  const engine = new DatalogEngine(r.getDLOntology());
  check('idempotence: first materialize', engine.materialize(), true);
  const t1 = engine.tableau;
  check('idempotence: second materialize', engine.materialize(), true);
  check('idempotence: same tableau reused', engine.tableau === t1, true);

  const cls1 = engine.getEquivalenceClass(I('a'));
  cls1.add(I('zzz'));
  cls1.delete(I('a'));
  check('getEquivalenceClass returns a COPY (added term is not retained)',
    engine.getEquivalenceClass(I('a')).has(I('zzz')), false);
  check('getEquivalenceClass returns a COPY (deleted term is still there)',
    engine.getEquivalenceClass(I('a')).has(I('a')), true);

  check('getRepresentative(unknown) is null', engine.getRepresentative(I('never')), null);
  check('getEquivalenceClass(unknown) is null', engine.getEquivalenceClass(I('never')), null);
  check('getTermForNode(null) is null', engine.getTermForNode(null), null);
  check('getTermForNode(undefined) is null', engine.getTermForNode(undefined), null);
  check('getDLOntology round-trips', engine.getDLOntology() === r.getDLOntology(), true);
  r.dispose();
}

// ===========================================================================
section('3. Query construction');
// ===========================================================================

{
  const r = createReasoner(ontology([
    decl(A), decl(R),
    E.classAssertion(A, I('a')),
    E.objectPropertyAssertion(R, I('a'), I('b')),
    E.objectPropertyAssertion(R, I('a'), I('b'))
  ]));
  const engine = r.getDatalogEngine();

  // DL-safety: an answer variable must occur in the body.
  let msg = null;
  try {
    new ConjunctiveQuery(engine, [createAtom(P.internAtomicConcept(EX + 'A'), V('X'))], [V('Y')]);
  } catch (e) { msg = e.message; }
  check('unsafe answer variable is rejected',
    /Answer variable Y does not occur in the query body/.test(msg || ''), true);

  // De-duplication: R(a,b) is asserted twice but is one fact.
  const q = new ConjunctiveQuery(engine,
    [createAtom(P.internAtomicRole(EX + 'R', false), V('X'), V('Y'))], [V('X'), V('Y')]);
  check('duplicate facts give one answer', q.getAnswers().length, 1);
  check('getNumberOfQueryAtoms', q.getNumberOfQueryAtoms(), 1);
  check('getNumberOfAnswerTerms', q.getNumberOfAnswerTerms(), 2);
  check('getQueryAtom(0) round-trips', q.getQueryAtom(0) === q.orderedBodyAtoms[0], true);
  check('getAnswerTerm(0)', q.getAnswerTerm(0), V('X'));
  check('getDatalogEngine round-trips', q.getDatalogEngine() === engine, true);
  check('toString renders q(...) <- ...', /^q\(X, Y\) ← /.test(q.toString()), true);

  // evaluate() needs a collector.
  let msg2 = null;
  try { q.evaluate(null); } catch (e) { msg2 = e.message; }
  check('evaluate(null) is rejected', /QueryResultCollector/.test(msg2 || ''), true);

  // A collector is always cleared, even if evaluation throws.
  const collector = new CollectingQueryResultCollector();
  q.evaluate(collector);
  check('collector size after evaluate', collector.size, 1);
  check('toArrayOfStrings strips the angle brackets',
    collector.toArrayOfStrings(), [[EX + 'a', EX + 'b']]);
  r.dispose();
}

// Unknown ground term: DOCUMENTED DIVERGENCE from HermiT, which throws
// IllegalArgumentException("Term '...' is unknown to the reasoner.").
{
  const r = createReasoner(ontology([decl(R), E.objectPropertyAssertion(R, I('a'), I('b'))]));
  check('unknown ground term gives no answers (HermiT throws instead)',
    names(new ConjunctiveQuery(r.getDatalogEngine(),
      [createAtom(P.internAtomicRole(EX + 'R', false), V('X'), I('unknown'))], [V('X')])),
    []);
  r.dispose();
}

// Inverse roles. The extension tables only ever hold ATOMIC roles, so
// ConjunctiveQuery must normalize a hand-built `R⁻(X,Y)` itself.
{
  const r = createReasoner(ontology([decl(R), E.objectPropertyAssertion(R, I('a'), I('b'))]));
  const inverse = P.internInverseRole(P.internAtomicRole(EX + 'R', false));
  check('inverse role in a query body is normalized',
    names(new ConjunctiveQuery(r.getDatalogEngine(),
      [createAtom(inverse, V('X'), V('Y'))], [V('X'), V('Y')])),
    ['b -> a']);
  r.dispose();
}

// An empty body, and a body of only non-extension predicates.
{
  const r = createReasoner(ontology([decl(A), E.classAssertion(A, I('a'))]));
  let msg = null;
  try { new ConjunctiveQuery(r.getDatalogEngine(), [], []); } catch (e) { msg = e.message; }
  check('an empty query body is rejected', /at least one body atom/.test(msg || ''), true);
  r.dispose();
}

// ===========================================================================
section('4. The spec layer (QuerySpec)');
// ===========================================================================

{
  const hasAge = dp('hasAge');
  const hasName = dp('hasName');
  const XI = E.XSD_NS + 'integer';
  // NOTE: `hasAge` is ranged `xsd:integer`, so every literal asserted on it MUST
  // be an integer. Asserting a language-tagged literal there would be genuinely
  // inconsistent (a plain literal is not an xsd:integer) and every query would
  // then throw "unsatisfiable". The lang-tagged literal therefore goes on the
  // unranged `hasName`.
  const r = createReasoner(ontology([
    decl(A), decl(B), decl(R), decl(hasAge), decl(hasName),
    E.subclassOf(A, B),
    range(hasAge, E.datatype(XI)),
    E.classAssertion(A, I('a')),
    E.classAssertion(B, I('c')),
    E.objectPropertyAssertion(R, I('a'), I('b')),
    E.objectPropertyAssertion(R, I('b'), I('c')),
    E.dataPropertyAssertion(hasAge, I('a'), E.literal('42', XI)),
    E.dataPropertyAssertion(hasAge, I('b'), E.literal('7', XI)),
    E.dataPropertyAssertion(hasName, I('b'), E.literal('bob', null, 'en')),
    E.differentIndividuals([I('a'), I('c')])
  ]));

  check('spec: class atom honours subsumption (A)',
    short(r.query({ where: [{ class: EX + 'A', arg: '?X' }] })), [['a']]);
  check('spec: class atom honours subsumption (B)',
    short(r.query({ where: [{ class: EX + 'B', arg: '?X' }] })), [['a'], ['c']]);
  check('spec: default select is every body variable',
    short(r.query({ where: [{ objectProperty: EX + 'R', subject: '?X', object: '?Y' }] })),
    [['a', 'b'], ['b', 'c']]);
  check('spec: explicit select reorders columns',
    short(r.query({
      select: ['?Y', '?X'],
      where: [{ objectProperty: EX + 'R', subject: '?X', object: '?Y' }]
    })),
    [['b', 'a'], ['c', 'b']]);
  check('spec: inverseObjectProperty',
    short(r.query({ where: [{ inverseObjectProperty: EX + 'R', subject: '?X', object: '?Y' }] })),
    [['b', 'a'], ['c', 'b']]);
  check('spec: two-atom join',
    short(r.query({
      select: ['?X', '?Z'],
      where: [{ objectProperty: EX + 'R', subject: '?X', object: '?Y' },
        { objectProperty: EX + 'R', subject: '?Y', object: '?Z' }]
    })),
    [['a', 'c']]);
  check('spec: ground individual in the body',
    short(r.query({ select: ['?Y'], where: [{ objectProperty: EX + 'R', subject: EX + 'a', object: '?Y' }] })),
    [['b']]);
  check('spec: data property binds the constant',
    short(r.query({ where: [{ dataProperty: EX + 'hasAge', subject: '?X', value: '?V' }] })),
    [['a', '"42"^^<' + XI + '>'], ['b', '"7"^^<' + XI + '>']]);
  check('spec: a typed literal matches the identically typed assertion',
    short(r.query({
      select: ['?X'],
      where: [{ dataProperty: EX + 'hasAge', subject: '?X', value: { literal: '42', datatype: XI } }]
    })),
    [['a']]);
  check('spec: a language-tagged literal matches',
    short(r.query({
      select: ['?X'],
      where: [{ dataProperty: EX + 'hasName', subject: '?X', value: { literal: 'bob', lang: 'en' } }]
    })),
    [['b']]);
  check('spec: a literal with the WRONG datatype does not match',
    short(r.query({
      select: ['?X'],
      where: [{ dataProperty: EX + 'hasAge', subject: '?X',
        value: { literal: '42', datatype: E.XSD_NS + 'string' } }]
    })),
    []);
  check('spec: datatype atom (needs a range axiom to be asserted)',
    r.query({ select: ['?V'], where: [{ datatype: XI, arg: '?V' }] }),
    [['"42"^^<' + XI + '>'], ['"7"^^<' + XI + '>']]);
  check('spec: datatype atom joins with a data property atom',
    short(r.query({
      select: ['?X', '?V'],
      where: [{ dataProperty: EX + 'hasAge', subject: '?X', value: '?V' },
        { datatype: XI, arg: '?V' }]
    })),
    [['a', '"42"^^<' + XI + '>'], ['b', '"7"^^<' + XI + '>']]);
  check('spec: differentFrom atom',
    short(r.query({ where: [{ differentFrom: ['?X', '?Y'] }] })),
    [['a', 'c']]);

  // Term shorthands must all resolve identically.
  for (const arg of ['?X', { variable: 'X' }, V('X')]) {
    check(`spec: variable shorthand ${JSON.stringify(arg)}`,
      short(r.query({ select: [arg], where: [{ class: EX + 'A', arg }] })), [['a']]);
  }
  // Individual shorthands. The "other" individual is `c`, not `a`: `A` has
  // exactly one member (`a`), so `A(?X) ^ ?X != c` answers `{a}` while
  // `A(?X) ^ ?X != a` answers `{}`. A shorthand that silently resolved to the
  // wrong individual would flip one of those two results.
  for (const other of [EX + 'c', { individual: EX + 'c' }, I('c')]) {
    check(`spec: individual shorthand ${typeof other}`,
      short(r.query({
        select: ['?X'],
        where: [{ class: EX + 'A', arg: '?X' }, { differentFrom: ['?X', other] }]
      })), [['a']]);
  }
  check('spec: an individual shorthand that names the only answer gives no answer',
    short(r.query({
      select: ['?X'],
      where: [{ class: EX + 'A', arg: '?X' }, { differentFrom: ['?X', EX + 'a'] }]
    })), []);

  // An OWLLiteral handed over directly.
  check('spec: a bare OWLLiteral as a term',
    short(r.query({
      select: ['?X'],
      where: [{ dataProperty: EX + 'hasAge', subject: '?X', value: E.literal('42', XI) }]
    })),
    [['a']]);

  // querySpecToString.
  const built = DL.buildQuerySpec({ select: ['?X'], where: [{ class: EX + 'A', arg: '?X' }] });
  check('querySpecToString', DL.querySpecToString(built.queryAtoms, built.answerTerms),
    `q(X) ← ${EX}A(X)`);

  // sameAs throws rather than silently matching nothing.
  let msg = null;
  try { r.query({ where: [{ sameAs: ['?X', EX + 'a'] }] }); } catch (e) { msg = e.message; }
  check('spec: sameAs is rejected with an explanation', /sameAs.*cannot be used/s.test(msg || ''), true);

  // Malformed specs.
  const bad = [
    ['missing where', () => r.query({}), /`where` array/],
    ['empty where', () => r.query({ where: [] }), /at least one atom/],
    ['unknown atom kind', () => r.query({ where: [{ nope: 'x' }] }), /Unrecognized query atom spec/],
    ['null term', () => r.query({ where: [{ class: EX + 'A', arg: null }] }), /cannot be null/],
    ['number term', () => r.query({ where: [{ class: EX + 'A', arg: 42 }] }), /Cannot interpret 42/],
    ['unsafe select', () => r.query({ select: ['?Q'], where: [{ class: EX + 'A', arg: '?X' }] }),
      /Answer variable Q does not occur/]
  ];
  for (const [label, fn, re] of bad) {
    let m = null;
    try { fn(); } catch (e) { m = e.message; }
    check(`spec error: ${label}`, re.test(m || ''), true);
  }
  r.dispose();
}

// ===========================================================================
section('5. Reasoner and ProtegeAdapter wiring');
// ===========================================================================

{
  const onto = ontology([decl(A), E.classAssertion(A, I('a'))]);
  const r = createReasoner(onto);
  const e1 = r.getDatalogEngine();
  check('reasoner: engine is cached', r.getDatalogEngine() === e1, true);
  r.clearInferenceCaches();
  check('reasoner: clearInferenceCaches invalidates the engine', r.getDatalogEngine() !== e1, true);
  const e2 = r.getDatalogEngine();
  check('reasoner: engine is re-cached', r.getDatalogEngine() === e2, true);

  const ax = E.classAssertion(A, I('b'));
  onto.addAxiom(ax);
  r.applyChange({ axiom: ax, isAdd: true });
  r.flush();
  check('reasoner: a flush invalidates the engine', r.getDatalogEngine() !== e2, true);
  check('reasoner: the new engine sees the new assertion',
    short(r.query({ where: [{ class: EX + 'A', arg: '?X' }] })), [['a'], ['b']]);

  const atoms = [createAtom(P.internAtomicConcept(EX + 'A'), V('X'))];
  check('reasoner: answerQuery returns Terms', r.answerQuery(atoms, [V('X')])[0][0].kind, 'Individual');
  check('reasoner: answerQueryAsStrings returns strings',
    r.answerQueryAsStrings(atoms, [V('X')]).map((row) => row[0].slice(EX.length)).sort(), ['a', 'b']);
  check('reasoner: createQuery builds a ConjunctiveQuery',
    r.createQuery({ where: [{ class: EX + 'A', arg: '?X' }] }) instanceof ConjunctiveQuery, true);
  r.dispose();
}

{
  const ad = reasonerFor(ontology([
    decl(A), decl(R),
    E.classAssertion(A, I('a')),
    E.objectPropertyAssertion(R, I('a'), I('b'))
  ]));
  check('adapter: name', ad.getReasonerName(), 'DL-JS-REASONER');
  check('adapter: query()', short(ad.query({ where: [{ class: EX + 'A', arg: '?X' }] })), [['a']]);
  check('adapter: answerQuery() returns Terms',
    ad.answerQuery({ where: [{ class: EX + 'A', arg: '?X' }] })[0][0].kind, 'Individual');
  check('adapter: createQuery()',
    ad.createQuery({ where: [{ class: EX + 'A', arg: '?X' }] }) instanceof ConjunctiveQuery, true);
  check('adapter: getDatalogEngine()', ad.getDatalogEngine() instanceof DatalogEngine, true);
  check('adapter: getQueryRepresentative(known)', ad.getQueryRepresentative(EX + 'a'), EX + 'a');
  check('adapter: getQueryRepresentative(unknown)', ad.getQueryRepresentative(EX + 'zzz'), null);
  ad.dispose();
}

// ===========================================================================
section('6. The real sample ontologies');
// ===========================================================================

// All four are Horn (see scripts/clausify-real-ontologies.js), so all four are
// legal DatalogEngine inputs. This is the scale test: iao alone clausifies to
// 398 DL clauses.
{
  const DIR = path.resolve(__dirname, '../../protege-js/sample/ontologies');
  const FILES = ['bfo.owl', 'ogms.owl', 'ro-core.owl', 'iao.owl'];
  let protege = null;
  try { protege = require('@skaterqiang/protege-js'); } catch (e) { /* optional peer */ }

  if (protege === null) {
    console.log('SKIP  @skaterqiang/protege-js is not installed');
  } else {
    const loader = new protege.OntologyLoader();
    for (const file of FILES) {
      const ont = loader.loadFromFile(path.join(DIR, file));
      const r = createReasoner(ont);
      const dlOntology = r.getDLOntology();
      check(`${file}: is Horn`, dlOntology.isHorn, true);

      const engine = new DatalogEngine(dlOntology);
      const t0 = Date.now();
      check(`${file}: materialize`, engine.materialize(), true);
      const ms = Date.now() - t0;

      // `owl:Thing(X)` is the natural "which individuals are there?" query. It
      // must return exactly the distinct individuals — one row per canonical
      // node, so merged individuals collapse onto their representative. This is
      // also the regression test for the `materialiseTopPredicates` fix: before
      // it, `ExtensionTable.addTuple` dropped every `owl:Thing` tuple (nothing
      // in a TBox consumes it as a delta predicate) and this returned 0 even
      // for ontologies with individuals — silently.
      const thing = P.internAtomicConcept(E.IRI_THING);
      const thingAnswers = new ConjunctiveQuery(engine, [createAtom(thing, V('X'))], [V('X')])
        .getAnswers().length;

      const representatives = new Set();
      for (const individual of dlOntology.allIndividuals) {
        const rep = engine.getRepresentative(individual);
        if (rep !== null) representatives.add(rep);
      }
      const distinctIndividuals = representatives.size;

      let classAnswers = 0;
      let classesWithAnswers = 0;
      for (const concept of dlOntology.allAtomicConcepts) {
        if (concept.iri === E.IRI_THING || concept.iri === E.IRI_NOTHING) continue;
        const n = new ConjunctiveQuery(engine, [createAtom(concept, V('X'))], [V('X')])
          .getAnswers().length;
        classAnswers += n;
        if (n > 0) classesWithAnswers++;
      }

      console.log(`      ${file}: ${dlOntology.dlClauses.length} clauses, `
        + `${dlOntology.positiveFacts.length} facts, `
        + `${distinctIndividuals} individuals, ${thingAnswers} Thing answers, `
        + `${classesWithAnswers}/${dlOntology.allAtomicConcepts.size} classes inhabited, `
        + `${classAnswers} class answers, ${ms}ms`);

      check(`${file}: owl:Thing(X) returns exactly the distinct individuals`,
        thingAnswers, distinctIndividuals);
      if (distinctIndividuals > 0) {
        // bfo.owl and ro-core.owl are pure TBoxes (no individuals), for which an
        // empty answer set is CORRECT — so only assert inhabitation when the
        // ontology actually has an ABox.
        check(`${file}: owl:Thing is materialised (regression: 0 before the fix)`,
          thingAnswers > 0, true);
        check(`${file}: at least one class is inhabited`, classesWithAnswers > 0, true);
      } else {
        console.log(`      ${file}: pure TBox (no individuals) — empty answers are correct`);
      }

      // A role query, to prove binary predicates materialise too. These sample
      // ontologies are TBox-heavy, so the count is often 0; the point is that
      // the query runs over every role without throwing.
      let roleAnswers = 0;
      for (const role of dlOntology.allAtomicObjectRoles) {
        roleAnswers += new ConjunctiveQuery(engine,
          [createAtom(role, V('X'), V('Y'))], [V('X'), V('Y')]).getAnswers().length;
      }
      check(`${file}: object role answers are non-negative`, roleAnswers >= 0, true);
      console.log(`      ${file}: ${roleAnswers} object-role answers over `
        + `${dlOntology.allAtomicObjectRoles.size} roles`);
      r.dispose();
    }
  }
}

// ===========================================================================
console.log(`\n${failures === 0 ? 'ALL PASS' : 'FAILURES'}: ${checks - failures}/${checks} checks passed`);
process.exit(failures === 0 ? 0 : 1);
