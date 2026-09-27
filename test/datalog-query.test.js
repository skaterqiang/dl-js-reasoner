'use strict';

// ---------------------------------------------------------------------------
// test/datalog-query.test.js — conjunctive query answering.
//
// The first four tests are a DIRECT PORT of HermiT's
// `org.semanticweb.HermiT.reasoner.DatalogEngineTest`, same ontologies, same
// expected answer sets. HermiT asserts with `assertContainsAll`, which passes
// if the expected tuples are a SUBSET of the answers; these tests assert exact
// set equality, which is strictly stronger and would also catch a query that
// over-answers.
//
// Two HermiT behaviours are subtle enough to be worth calling out, because both
// look like a bug in our port until you know they are intended:
//
//  • `testEquality` expects every answer's second column to be
//    `getRepresentative(I('a'))`, NOT `I('a')`. After merging, the extension
//    tables only hold canonical nodes, so answers are necessarily reported in
//    terms of the equivalence-class representative.
//
//  • `testQueryWithIndividuals` expects ZERO answers for `R(X, I(a))` even
//    though a rule derives `R(?X, ?Z)`. That is correct, not a silent failure:
//    the derived `R` facts relate `a` to `rd0` and `rd0` to itself, never
//    anything to `a`. The test therefore also runs the positive control
//    `R(X, Y)`, which proves the rule machinery actually fired.
//
// The remaining tests cover what HermiT's suite does not: the `QuerySpec`
// layer, inverse-role normalization in query bodies, the engine's cache
// lifecycle inside `Reasoner`, and the documented divergences.
// ---------------------------------------------------------------------------

const test = require('node:test');
const assert = require('node:assert/strict');

const {
  createReasoner,
  DatalogEngine,
  ConjunctiveQuery,
  CollectingQueryResultCollector,
  createAtom,
  createVariable,
  createIndividual,
  DLPredicate: P
} = require('../src/index');
const { E, EX, AT, cls, op, dp, ind, declaration, dataPropertyRange, ontology } = require('./helpers');

const NS = EX; // HermiT's `NS`, so `I('a')` reads the same in both suites.

const A = cls('A'), B = cls('B'), C = cls('C');
const R = op('R'), S = op('S');

const I = (localName) => createIndividual(NS + localName);
const V = (name) => createVariable(name);

/**
 * The distinct answers of a query, as sorted `string[]`, so an answer set can
 * be compared with `assert.deepEqual` regardless of evaluation order.
 */
function answersOf(query) {
  const collector = new CollectingQueryResultCollector();
  query.evaluate(collector);
  return collector.results
    .map((row) => row.map((t) => (t === null ? 'null' : String(t))))
    .map((row) => row.join(' -> '))
    .sort();
}

/** Same, but with individuals rendered as their bare local name. */
function namesOf(query) {
  const collector = new CollectingQueryResultCollector();
  query.evaluate(collector);
  return collector.results
    .map((row) => row.map((t) => (t.iri ? t.iri.slice(NS.length) : String(t))).join(' -> '))
    .sort();
}

/**
 * Strip the test namespace from every cell of a `string[][]` answer matrix, so
 * the spec-layer expectations below read like HermiT's `I("a")`.
 *
 * Rows are SORTED, because an answer set has no defined order: `Reasoner.query`
 * returns answers in whatever order the join evaluation produced them, which
 * depends on `BodyAtomsSwapper`'s selectivity heuristic. Sorting makes these
 * assertions about the SET of answers, which is what is actually specified.
 */
function short(rows) {
  return rows
    .map((row) => row.map((cell) => (cell.startsWith(NS) ? cell.slice(NS.length) : cell)))
    .map((row) => row.join('\u0000'))
    .sort()
    .map((key) => key.split('\u0000'));
}

// ===========================================================================
// HermiT DatalogEngineTest, ported
// ===========================================================================

test('testBasic: recursive rules saturate A, B and C', () => {
  // ∃R.A ⊑ A ; ∃R.B ⊑ B ; A ⊓ B ⊑ C
  // plus an R-chain that makes the rules fire repeatedly.
  const r = createReasoner(ontology([
    declaration(A), declaration(B), declaration(C), declaration(R),
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
  try {
    const engine = new DatalogEngine(r.getDLOntology());
    assert.equal(engine.materialize(), true);

    // Exact set equality, not HermiT's `assertContainsAll`.
    assert.deepEqual(
      namesOf(new ConjunctiveQuery(engine, [createAtom(P.internAtomicConcept(NS + 'A'), V('X'))], [V('X')])),
      ['a', 'b', 'c', 'd', 'n']);
    assert.deepEqual(
      namesOf(new ConjunctiveQuery(engine, [createAtom(P.internAtomicConcept(NS + 'B'), V('X'))], [V('X')])),
      ['c', 'd', 'k', 'l', 'm', 'n']);
    assert.deepEqual(
      namesOf(new ConjunctiveQuery(engine, [createAtom(P.internAtomicConcept(NS + 'C'), V('X'))], [V('X')])),
      ['c', 'd', 'n']);

    // The R-chain itself, as a positive control that the ABox was loaded at all.
    assert.deepEqual(
      namesOf(new ConjunctiveQuery(engine,
        [createAtom(P.internAtomicRole(NS + 'R', false), V('X'), V('Y'))], [V('X'), V('Y')])),
      ['b -> a', 'c -> b', 'c -> m', 'd -> c', 'l -> k', 'm -> l', 'n -> c']);
  } finally { r.dispose(); }
});

test('testEquality: a functional property merges, and answers use the representative', () => {
  // FunctionalObjectProperty(R) plus R(b,a), R(b,c), R(d,c), R(d,e), R(f,e),
  // R(f,g) forces a, c, e and g into one equivalence class.
  const r = createReasoner(ontology([
    declaration(R),
    { axiomType: E.AxiomType.FUNCTIONAL_OBJECT_PROPERTY, property: R },
    E.objectPropertyAssertion(R, I('b'), I('a')),
    E.objectPropertyAssertion(R, I('b'), I('c')),
    E.objectPropertyAssertion(R, I('d'), I('c')),
    E.objectPropertyAssertion(R, I('d'), I('e')),
    E.objectPropertyAssertion(R, I('f'), I('e')),
    E.objectPropertyAssertion(R, I('f'), I('g'))
  ]));
  try {
    const engine = new DatalogEngine(r.getDLOntology());
    assert.equal(engine.materialize(), true);

    const eqClass = engine.getEquivalenceClass(I('a'));
    assert.deepEqual([...eqClass].map((t) => t.iri).sort(),
      [NS + 'a', NS + 'c', NS + 'e', NS + 'g'].sort());

    const rep = engine.getRepresentative(I('a'));
    // Every surviving R fact must point AT the representative, never at a
    // merged-away node — this is the whole reason answers go through
    // `getRepresentative`.
    const answers = new ConjunctiveQuery(engine,
      [createAtom(P.internAtomicRole(NS + 'R', false), V('X'), V('Y'))], [V('X'), V('Y')])
      .getAnswers();
    assert.deepEqual(answers.map((row) => row[0].iri.slice(NS.length)).sort(), ['b', 'd', 'f']);
    for (const row of answers) assert.equal(row[1], rep, 'second column is the representative');
  } finally { r.dispose(); }
});

test('testQueryWithIndividualsAndEquality: ground individuals and merging', () => {
  const r = createReasoner(ontology([
    declaration(R), declaration(S),
    E.objectPropertyAssertion(R, I('c'), I('b')),
    E.objectPropertyAssertion(S, I('c'), I('a')),
    E.sameIndividual([I('a'), I('b')]),

    E.objectPropertyAssertion(R, I('d'), I('e')),
    E.objectPropertyAssertion(S, I('d'), I('f'))
  ]));
  try {
    const engine = new DatalogEngine(r.getDLOntology());
    assert.equal(engine.materialize(), true);

    assert.deepEqual([...engine.getEquivalenceClass(I('a'))].map((t) => t.iri).sort(),
      [NS + 'a', NS + 'b'].sort());

    // R(X, I(a)) ∧ S(X, I(b)) — the two ground individuals denote the SAME
    // node, so `c` matches both atoms.
    const q = new ConjunctiveQuery(engine, [
      createAtom(P.internAtomicRole(NS + 'R', false), V('X'), I('a')),
      createAtom(P.internAtomicRole(NS + 'S', false), V('X'), I('b'))
    ], [V('X')]);
    assert.deepEqual(namesOf(q), ['c']);
  } finally { r.dispose(); }
});

test('testQueryWithIndividuals: a rule-derived fact can legitimately give no answer', () => {
  // HermiT's four DLSafeRules, hand-built (there is no `swrlRule` factory).
  const D0 = cls('D0'), RD0 = cls('RD0');
  const pvar = (name) => ({ iri: NS + 'var#' + name });
  const classAtom = (ce, arg) => ({ type: 'ClassAtom', classExpression: ce, arg });
  const objectPropertyAtom = (property, arg1, arg2) =>
    ({ type: 'ObjectPropertyAtom', property, arg1, arg2 });
  const rule = (body, head) => ({ body, head });

  const r = createReasoner(ontology([
    declaration(A), declaration(B), declaration(D0), declaration(RD0), declaration(R),
    rule([classAtom(D0, pvar('X'))], [classAtom(A, pvar('X'))]),
    rule([classAtom(D0, pvar('X'))], [classAtom(B, pvar('X'))]),
    rule([classAtom(A, pvar('X')), classAtom(RD0, pvar('Z'))], [classAtom(D0, pvar('Z'))]),
    rule([classAtom(A, pvar('X')), classAtom(RD0, pvar('Z'))],
      [objectPropertyAtom(R, pvar('X'), pvar('Z'))]),
    E.classAssertion(E.owlThing(), I('a')),
    E.classAssertion(RD0, I('rd0')),
    E.classAssertion(A, I('a'))
  ]));
  try {
    const dlOntology = r.getDLOntology();
    assert.equal(dlOntology.isHorn, true, 'the four rules are Horn');
    const engine = new DatalogEngine(dlOntology);
    assert.equal(engine.materialize(), true);

    // The oracle: R(X, I(a)) has NO answer.
    const q = new ConjunctiveQuery(engine,
      [createAtom(P.internAtomicRole(NS + 'R', false), V('X'), I('a'))], [V('X')]);
    assert.deepEqual(namesOf(q), []);

    // The positive control that makes the empty answer meaningful: the rule DID
    // fire, it just never produced an R fact pointing at `a`.
    assert.deepEqual(
      namesOf(new ConjunctiveQuery(engine,
        [createAtom(P.internAtomicRole(NS + 'R', false), V('X'), V('Y'))], [V('X'), V('Y')])),
      ['a -> rd0', 'rd0 -> rd0']);
  } finally { r.dispose(); }
});

// ===========================================================================
// Engine contract
// ===========================================================================

test('the engine rejects a non-Horn ontology', () => {
  // A ⊔ B is a disjunctive head: no materialised ABox can represent "one of
  // these, but we do not know which".
  const r = createReasoner(ontology([
    declaration(A), declaration(B),
    E.subclassOf(E.owlThing(), E.objectUnionOf([A, B])),
    E.classAssertion(A, I('a'))
  ]));
  try {
    assert.throws(() => new DatalogEngine(r.getDLOntology()),
      /disjunctive heads/);
  } finally { r.dispose(); }
});

test('the engine rejects a non-DLOntology argument', () => {
  assert.throws(() => new DatalogEngine(null), /clausified DLOntology/);
  assert.throws(() => new DatalogEngine({}), /clausified DLOntology/);
});

test('a query over an inconsistent ontology throws', () => {
  const r = createReasoner(ontology([
    declaration(A),
    E.disjointClasses([A, B]),
    E.classAssertion(A, I('a')),
    E.classAssertion(B, I('a'))
  ]));
  try {
    const engine = new DatalogEngine(r.getDLOntology());
    assert.equal(engine.materialize(), false, 'materialize reports the clash');
    assert.throws(() => new ConjunctiveQuery(engine,
      [createAtom(P.internAtomicConcept(NS + 'A'), V('X'))], [V('X')]),
    /unsatisfiable/);
  } finally { r.dispose(); }
});

test('materialize() is idempotent and keeps one tableau', () => {
  const r = createReasoner(ontology([declaration(A), E.classAssertion(A, I('a'))]));
  try {
    const engine = new DatalogEngine(r.getDLOntology());
    assert.equal(engine.materialize(), true);
    const first = engine.tableau;
    assert.equal(engine.materialize(), true);
    assert.equal(engine.tableau, first, 'the second call is a cache hit');
  } finally { r.dispose(); }
});

test('getEquivalenceClass returns a copy, so callers cannot corrupt the engine', () => {
  const r = createReasoner(ontology([
    declaration(R),
    { axiomType: E.AxiomType.FUNCTIONAL_OBJECT_PROPERTY, property: R },
    E.objectPropertyAssertion(R, I('b'), I('a')),
    E.objectPropertyAssertion(R, I('b'), I('c'))
  ]));
  try {
    const engine = new DatalogEngine(r.getDLOntology());
    engine.materialize();
    const cls1 = engine.getEquivalenceClass(I('a'));
    cls1.add(I('zzz'));
    cls1.delete(I('a'));
    assert.equal(engine.getEquivalenceClass(I('a')).has(I('zzz')), false);
    assert.equal(engine.getEquivalenceClass(I('a')).has(I('a')), true);
  } finally { r.dispose(); }
});

test('unknown terms and null nodes are handled without throwing', () => {
  const r = createReasoner(ontology([declaration(A), E.classAssertion(A, I('a'))]));
  try {
    const engine = new DatalogEngine(r.getDLOntology());
    engine.materialize();
    assert.equal(engine.getRepresentative(I('never-asserted')), null);
    assert.equal(engine.getEquivalenceClass(I('never-asserted')), null);
    assert.equal(engine.getTermForNode(null), null);
    assert.equal(engine.getTermForNode(undefined), null);
  } finally { r.dispose(); }
});

test('existentials are NOT expanded: no witness means no answer', () => {
  // The documented limitation of ABox materialisation. `A ⊑ ∃R.B` with `A(a)`
  // entails that `a` has SOME `R`-successor in `B`, but the DatalogEngine's
  // `NullExistentialExpansionStrategy` never creates that successor node, so
  // there is no ground `R(a, ?)` fact to answer with. `A(X)` still answers `a`
  // (it is asserted), but `R(X,Y)` is empty. This is inherent to query
  // answering over a materialised ABox and HermiT behaves identically — it is
  // NOT a bug. A positive control proves the machinery ran at all.
  const r = createReasoner(ontology([
    declaration(A), declaration(B), declaration(R),
    E.subclassOf(A, E.objectSomeValuesFrom(R, B)),
    E.classAssertion(A, I('a'))
  ]));
  try {
    const engine = new DatalogEngine(r.getDLOntology());
    assert.equal(engine.materialize(), true);
    // A(X) answers `a` — the asserted class member.
    assert.deepEqual(namesOf(new ConjunctiveQuery(engine,
      [createAtom(P.internAtomicConcept(NS + 'A'), V('X'))], [V('X')])), ['a']);
    // R(X,Y) is EMPTY: the existential witness was never created.
    assert.deepEqual(namesOf(new ConjunctiveQuery(engine,
      [createAtom(P.internAtomicRole(NS + 'R', false), V('X'), V('Y'))], [V('X'), V('Y')])), []);
    // Load-bearing cross-check: the SAME ontology through the full reasoner
    // (which uses a real expansion strategy) does create the witness node, so
    // the empty answer above is caused by the null strategy and not by the
    // ontology being unable to derive it. `isConsistent()` is what actually
    // runs the tableau; `getTableau()` alone just hands back the object.
    assert.equal(r.isConsistent(), true);
    assert.ok(r.getTableau().numberOfNodeCreations > engine.tableau.numberOfNodeCreations,
      'the full tableau expands the existential; the datalog engine does not');
  } finally { r.dispose(); }
});

// ===========================================================================
// Query construction
// ===========================================================================

test('an unsafe answer variable is rejected', () => {
  const r = createReasoner(ontology([declaration(A), E.classAssertion(A, I('a'))]));
  try {
    assert.throws(() => new ConjunctiveQuery(r.getDatalogEngine(),
      [createAtom(P.internAtomicConcept(NS + 'A'), V('X'))], [V('Y')]),
    /Answer variable Y does not occur in the query body/);
  } finally { r.dispose(); }
});

test('a ground term unknown to the reasoner yields no answers', () => {
  // DOCUMENTED DIVERGENCE from HermiT. HermiT's `ValuesBufferManager` throws
  // `IllegalArgumentException("Term '...' is unknown to the reasoner.")`. Our
  // matcher early-returns instead, because `_match` already has to handle an
  // unresolvable ground term when evaluating ordinary DL clauses. The result is
  // the same answer set HermiT would have produced had it not thrown.
  const r = createReasoner(ontology([
    declaration(R),
    E.objectPropertyAssertion(R, I('a'), I('b'))
  ]));
  try {
    const q = new ConjunctiveQuery(r.getDatalogEngine(),
      [createAtom(P.internAtomicRole(NS + 'R', false), V('X'), I('unknown'))], [V('X')]);
    assert.deepEqual(namesOf(q), []);
  } finally { r.dispose(); }
});

test('an inverse role in a query body is normalized before matching', () => {
  // The extension tables only ever hold ATOMIC roles: `ExtensionManager._addTuple`
  // rewrites `R⁻(a,b)` into `R(b,a)`. Clause bodies get that from the
  // clausifier's `getRoleAtom`, but a query body is hand-built, so
  // `ConjunctiveQuery` normalizes it itself. Without that step the atom below
  // would match nothing — silently.
  const r = createReasoner(ontology([
    declaration(R),
    E.objectPropertyAssertion(R, I('a'), I('b'))
  ]));
  try {
    const inverse = P.internInverseRole(P.internAtomicRole(NS + 'R', false));
    const q = new ConjunctiveQuery(r.getDatalogEngine(),
      [createAtom(inverse, V('X'), V('Y'))], [V('X'), V('Y')]);
    assert.deepEqual(namesOf(q), ['b -> a']);
  } finally { r.dispose(); }
});

test('owl:Thing(X) enumerates every individual (materialiseTopPredicates)', () => {
  // `owl:Thing` holds of every abstract node, so `ExtensionManager` answers
  // `containsConceptAssertion(THING, …)` without a table and `ExtensionTable`
  // drops the tuple as dead weight — unless the tableau is told to materialise
  // it. `DatalogEngine` sets `materialiseTopPredicates: true` for exactly this
  // reason. Before that flag, `owl:Thing(X)` — the most natural "which
  // individuals are there?" query — returned [] silently, because no clause in
  // a TBox consumes `owl:Thing` as a delta predicate. HermiT has the same trap.
  const r = createReasoner(ontology([
    declaration(A), declaration(R),
    E.classAssertion(A, I('a')),
    E.objectPropertyAssertion(R, I('a'), I('b')),
    E.objectPropertyAssertion(R, I('c'), I('d'))
  ]));
  try {
    const thing = P.internAtomicConcept(E.IRI_THING);
    const q = new ConjunctiveQuery(r.getDatalogEngine(),
      [createAtom(thing, V('X'))], [V('X')]);
    // a, b, c, d — every individual that got a node, whether or not it is
    // otherwise classified.
    assert.deepEqual(namesOf(q), ['a', 'b', 'c', 'd']);
  } finally { r.dispose(); }
});

test('owl:Thing(X) collapses merged individuals onto their representative', () => {
  // A functional property merges b's two fillers, so `owl:Thing` must report the
  // canonical node once, not once per pre-merge term.
  const r = createReasoner(ontology([
    declaration(R),
    { axiomType: AT.FUNCTIONAL_OBJECT_PROPERTY, property: R },
    E.objectPropertyAssertion(R, I('b'), I('a')),
    E.objectPropertyAssertion(R, I('b'), I('c'))
  ]));
  try {
    const thing = P.internAtomicConcept(E.IRI_THING);
    const q = new ConjunctiveQuery(r.getDatalogEngine(),
      [createAtom(thing, V('X'))], [V('X')]);
    // b and the merged {a,c} representative — exactly two distinct individuals.
    assert.equal(q.getAnswers().length, 2);
  } finally { r.dispose(); }
});

test('answers are de-duplicated and toString renders the query', () => {
  const r = createReasoner(ontology([
    declaration(A), declaration(R),
    E.classAssertion(A, I('a')),
    E.objectPropertyAssertion(R, I('a'), I('b')),
    E.objectPropertyAssertion(R, I('a'), I('b'))
  ]));
  try {
    const q = r.createConjunctiveQuery(
      [createAtom(P.internAtomicRole(NS + 'R', false), V('X'), V('Y'))], [V('X'), V('Y')]);
    assert.equal(q.getAnswers().length, 1, 'the collector de-duplicates');
    assert.equal(q.getNumberOfQueryAtoms(), 1);
    assert.equal(q.getNumberOfAnswerTerms(), 2);
    assert.equal(q.getDatalogEngine(), r.getDatalogEngine());
    assert.match(q.toString(), /^q\(X, Y\) ← /);
  } finally { r.dispose(); }
});

test('evaluate requires a collector', () => {
  const r = createReasoner(ontology([declaration(A), E.classAssertion(A, I('a'))]));
  try {
    const q = r.createConjunctiveQuery(
      [createAtom(P.internAtomicConcept(NS + 'A'), V('X'))], [V('X')]);
    assert.throws(() => q.evaluate(null), /QueryResultCollector/);
  } finally { r.dispose(); }
});

// ===========================================================================
// The spec layer (`QuerySpec.js`) — no HermiT counterpart
// ===========================================================================

test('query(): class, object property and inverse atoms', () => {
  const r = createReasoner(ontology([
    declaration(A), declaration(B), declaration(R),
    E.subclassOf(A, B),
    E.classAssertion(A, I('a')),
    E.classAssertion(B, I('c')),
    E.objectPropertyAssertion(R, I('a'), I('b')),
    E.objectPropertyAssertion(R, I('b'), I('c'))
  ]));
  try {
    // Subsumption is honoured: `a` is an A, hence a B.
    assert.deepEqual(short(r.query({ where: [{ class: NS + 'A', arg: '?X' }] })), [['a']]);
    assert.deepEqual(short(r.query({ where: [{ class: NS + 'B', arg: '?X' }] })), [['a'], ['c']]);

    // `select` reorders the answer columns.
    assert.deepEqual(
      short(r.query({ where: [{ objectProperty: NS + 'R', subject: '?X', object: '?Y' }] })),
      [['a', 'b'], ['b', 'c']]);
    assert.deepEqual(
      short(r.query({
        select: ['?Y', '?X'],
        where: [{ objectProperty: NS + 'R', subject: '?X', object: '?Y' }]
      })),
      [['b', 'a'], ['c', 'b']]);

    // Inverse form, written the readable way.
    assert.deepEqual(
      short(r.query({ where: [{ inverseObjectProperty: NS + 'R', subject: '?X', object: '?Y' }] })),
      [['b', 'a'], ['c', 'b']]);

    // A two-atom join: R(X,Y) ∧ R(Y,Z) ⇒ the transitive step a→c.
    assert.deepEqual(
      short(r.query({
        select: ['?X', '?Z'],
        where: [{ objectProperty: NS + 'R', subject: '?X', object: '?Y' },
          { objectProperty: NS + 'R', subject: '?Y', object: '?Z' }]
      })),
      [['a', 'c']]);

    // A ground individual in the body.
    assert.deepEqual(
      short(r.query({ select: ['?Y'], where: [{ objectProperty: NS + 'R', subject: NS + 'a', object: '?Y' }] })),
      [['b']]);
  } finally { r.dispose(); }
});

test('query(): data property atoms and literal matching', () => {
  const hasAge = dp('hasAge');
  const XI = E.XSD_NS + 'integer';
  const r = createReasoner(ontology([
    declaration(hasAge),
    E.dataPropertyAssertion(hasAge, I('a'), E.literal('42', XI)),
    E.dataPropertyAssertion(hasAge, I('b'), E.literal('bob', null, 'en'))
  ]));
  try {
    // A variable in the value position binds the CONSTANT, rendered the way
    // `Constant.toString` renders it.
    assert.deepEqual(
      short(r.query({ where: [{ dataProperty: NS + 'hasAge', subject: '?X', value: '?V' }] })),
      [['a', '"42"^^<' + XI + '>'],
        ['b', '"bob@en"^^<' + E.IRI_RDF_PLAIN_LITERAL + '>']]);

    // A typed literal in the query matches the identically typed assertion.
    // This is the assertion that `QuerySpec.literalToTerm` and
    // `OWLClausification.convertLiteral` agree — if they drifted, this would
    // return [] with no error.
    assert.deepEqual(
      short(r.query({
        select: ['?X'],
        where: [{ dataProperty: NS + 'hasAge', subject: '?X',
          value: { literal: '42', datatype: XI } }]
      })),
      [['a']]);

    // ... and so does a language-tagged one.
    assert.deepEqual(
      short(r.query({
        select: ['?X'],
        where: [{ dataProperty: NS + 'hasAge', subject: '?X',
          value: { literal: 'bob', lang: 'en' } }]
      })),
      [['b']]);

    // A literal with the wrong datatype must NOT match.
    assert.deepEqual(
      short(r.query({
        select: ['?X'],
        where: [{ dataProperty: NS + 'hasAge', subject: '?X',
          value: { literal: '42', datatype: E.XSD_NS + 'string' } }]
      })),
      []);
  } finally { r.dispose(); }
});

test('query(): datatype and differentFrom atoms', () => {
  const hasAge = dp('hasAge');
  const XI = E.XSD_NS + 'integer';
  const r = createReasoner(ontology([
    declaration(A), declaration(hasAge),
    dataPropertyRange(hasAge, E.datatype(XI)),
    E.dataPropertyAssertion(hasAge, I('a'), E.literal('42', XI)),
    E.classAssertion(A, I('a')),
    E.classAssertion(A, I('b')),
    E.differentIndividuals([I('a'), I('b')])
  ]));
  try {
    // `{ datatype }` must build the SAME predicate the clausifier builds for a
    // datatype IRI — a `DatatypeRestriction` with no facets, not a
    // `LiteralDataRange`. Building the wrong one matches nothing, silently.
    assert.deepEqual(
      r.query({ select: ['?V'], where: [{ datatype: XI, arg: '?V' }] }),
      [['"42"^^<' + XI + '>']]);

    // A datatype atom joins against a data property atom.
    assert.deepEqual(
      short(r.query({
        select: ['?X', '?V'],
        where: [{ dataProperty: NS + 'hasAge', subject: '?X', value: '?V' },
          { datatype: XI, arg: '?V' }]
      })),
      [['a', '"42"^^<' + XI + '>']]);

    // `DifferentIndividuals` is stored as an `!=` tuple, so it does match.
    assert.deepEqual(
      short(r.query({ where: [{ differentFrom: ['?X', '?Y'] }] })),
      [['a', 'b']]);
  } finally { r.dispose(); }
});

test('query(): a sameAs atom throws instead of silently matching nothing', () => {
  const r = createReasoner(ontology([declaration(A), E.classAssertion(A, I('a'))]));
  try {
    assert.throws(
      () => r.query({ where: [{ class: NS + 'A', arg: '?X' }, { sameAs: ['?X', NS + 'a'] }] }),
      /sameAs.*cannot be used/s);
  } finally { r.dispose(); }
});

test('query(): malformed specs are rejected with a useful message', () => {
  const r = createReasoner(ontology([declaration(A), E.classAssertion(A, I('a'))]));
  try {
    assert.throws(() => r.query({}), /`where` array/);
    assert.throws(() => r.query({ where: [] }), /at least one atom/);
    assert.throws(() => r.query({ where: [{ nope: 'x' }] }), /Unrecognized query atom spec/);
    assert.throws(() => r.query({ where: [{ class: NS + 'A', arg: null }] }), /cannot be null/);
    assert.throws(() => r.query({ where: [{ class: NS + 'A', arg: 42 }] }), /Cannot interpret 42/);
    // `select` naming a variable absent from the body is the DL-safety check.
    assert.throws(() => r.query({ select: ['?Q'], where: [{ class: NS + 'A', arg: '?X' }] }),
      /Answer variable Q does not occur/);
  } finally { r.dispose(); }
});

test('query(): term shorthands all resolve to the same term', () => {
  const r = createReasoner(ontology([declaration(A), E.classAssertion(A, I('a'))]));
  try {
    const expected = [['a']];
    // `?X` string, `{ variable }` wrapper and a pre-built Term.
    for (const arg of ['?X', { variable: 'X' }, V('X')]) {
      assert.deepEqual(short(r.query({ select: [arg], where: [{ class: NS + 'A', arg }] })), expected);
    }
    // A bare IRI string, an `{ individual }` wrapper and a pre-built Individual.
    for (const subj of [NS + 'a', { individual: NS + 'a' }, I('a')]) {
      assert.deepEqual(short(r.query({ select: ['?X'], where: [{ class: NS + 'A', arg: '?X' },
        { differentFrom: ['?X', subj] }] })), []);
    }
  } finally { r.dispose(); }
});

// ===========================================================================
// Reasoner wiring and cache lifecycle
// ===========================================================================

test('Reasoner caches the datalog engine and invalidates it on flush', () => {
  const onto = ontology([declaration(A), E.classAssertion(A, I('a'))]);
  const r = createReasoner(onto);
  try {
    const first = r.getDatalogEngine();
    assert.equal(r.getDatalogEngine(), first, 'cached across calls');
    assert.equal(first.getDLOntology(), r.getDLOntology());

    // An incremental flush keeps `dlOntology` alive but changes its ground
    // facts, so a materialised ABox would be stale.
    r.clearInferenceCaches();
    assert.notEqual(r.getDatalogEngine(), first, 'invalidated');
    const second = r.getDatalogEngine();
    assert.equal(r.getDatalogEngine(), second, 're-cached');

    // And the new engine sees the new assertion.
    const ax = E.classAssertion(A, I('b'));
    onto.addAxiom(ax);
    r.applyChange({ axiom: ax, isAdd: true });
    r.flush();
    assert.notEqual(r.getDatalogEngine(), second, 'a flush invalidates too');
    assert.deepEqual(short(r.query({ where: [{ class: NS + 'A', arg: '?X' }] })), [['a'], ['b']]);
  } finally { r.dispose(); }
});

test('answerQuery returns Terms, answerQueryAsStrings returns strings', () => {
  const r = createReasoner(ontology([declaration(A), E.classAssertion(A, I('a'))]));
  try {
    const atoms = [createAtom(P.internAtomicConcept(NS + 'A'), V('X'))];
    const terms = r.answerQuery(atoms, [V('X')]);
    assert.equal(terms[0][0].kind, 'Individual');
    assert.equal(terms[0][0].iri, NS + 'a');
    assert.deepEqual(r.answerQueryAsStrings(atoms, [V('X')]), [[NS + 'a']]);
  } finally { r.dispose(); }
});

test('a custom QueryResultCollector sees every answer', () => {
  const r = createReasoner(ontology([
    declaration(R),
    E.objectPropertyAssertion(R, I('a'), I('b')),
    E.objectPropertyAssertion(R, I('c'), I('d'))
  ]));
  try {
    const seen = [];
    const collector = {
      processResult(_query, result) { seen.push(result.map(String).join('->')); }
    };
    r.createConjunctiveQuery(
      [createAtom(P.internAtomicRole(NS + 'R', false), V('X'), V('Y'))], [V('X'), V('Y')])
      .evaluate(collector);
    // `Individual.toString()` renders `<iri>`, unlike the collector's
    // `toArrayOfStrings()`, which deliberately strips the brackets.
    assert.deepEqual(seen.sort(), [`<${NS}a>-><${NS}b>`, `<${NS}c>-><${NS}d>`]);
  } finally { r.dispose(); }
});
