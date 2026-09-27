'use strict';

// ---------------------------------------------------------------------------
// test/hermit-oracles-3.test.js — differential testing against HermiT's JUnit
// corpus, third instalment: SWRL / DLSafeRule.
//
//   * org.semanticweb.HermiT.reasoner.RulesTest — 24 oracles
//
// `RulesTest` does NOT appear in HermiT's `known-test-failures.txt` (that file
// has no `org.semanticweb.HermiT.reasoner.*` entries at all), so every
// assertion below is a clean oracle: HermiT's own build is expected to pass it.
//
// ---------------------------------------------------------------------------
// WHY THIS CLASS IS INTERESTING
//
// `hermit-oracles.test.js` and `hermit-oracles-2.test.js` exercise the DL side
// of the reasoner. This one exercises the RULE side, which is a completely
// separate pipeline:
//
//   SWRLRule → OWLNormalization._visitSWRLRule
//            → RuleNormalizer (Lloyd-Topor split, sameAs canonicalisation,
//              ground individuals → `ObjectOneOf({ind})` body atoms,
//              data-range variables, DL-safety checking)
//            → OWLClausification.RuleConverter (atoms → DL predicates)
//            → DLClause.getSafeVersion (guarding atoms for unsafe head vars)
//            → HyperresolutionManager
//
// Nothing else in the suite covers Lloyd-Topor splitting, empty-body rules,
// ground individuals in body/head positions, `SameAsAtom` / `DifferentFromAtom`
// in either position, or `DataRangeAtom` polarity handling.
//
// ---------------------------------------------------------------------------
// ENCODING NOTE
//
// HermiT's tests feed the reasoner a FUNCTIONAL-SYNTAX STRING which the OWL API
// parses into `SWRLRule` objects. This port has no functional-syntax parser, so
// the rules are built directly out of `src/structural/RuleNormalizer`'s atom
// factories — the same shapes protege-js' `src/model/SWRL.js` produces. Using
// the factories rather than hand-rolled object literals means a rename of
// `SWRLAtomType` breaks this file loudly instead of silently.
//
// Two name mappings are worth stating explicitly, because the OWL API and
// protege-js disagree:
//
//   OWL API / HermiT functional syntax   this port (`SWRLAtomType`)
//   ----------------------------------   -------------------------
//   SameIndividualAtom                   SameAsAtom
//   DifferentIndividualsAtom             DifferentFromAtom
//   Variable(:x)                         new SWRLVariable('x')
//
// A rule is detected structurally, not by `axiomType`: `OWLNormalization`
// tests `Array.isArray(axiom.body) && Array.isArray(axiom.head)` because
// protege-js' `SWRLRule` carries no `axiomType` at all.
//
// ---------------------------------------------------------------------------
// DECLARATIONS
//
// Every entity is explicitly declared. That is faithful, not belt-and-braces:
// the OWL API AUTO-DECLARES every entity in a parsed axiom's signature, so
// `ClassAssertion(:A :a)` declares both `:A` and `:a`, and a `SWRLRule`
// declares every class, property and individual occurring in its atoms.
// `Reasoner.getAllNamedIndividuals()` ranges over the declared individuals, so
// omitting a declaration would silently shrink the answer sets that
// `getInstances` is asked about.
//
// ---------------------------------------------------------------------------
// UPSTREAM ODDITIES, PRESERVED DELIBERATELY
//
// 1. `testRuleNonSimple` — HermiT asserts only
//      `hasObjectPropertyRelationship(a, t, b)`.
//    The `s` assertion is COMMENTED OUT upstream with the note *"The following
//    fails because transitive properties in rules do not work correctly"*. The
//    oracle is therefore only about `t`; porting the commented line would be
//    porting a known bug.
//
// 2. `testNegativeBodyDataRange` — the local variable `C` is bound to
//      `getOWLClass(IRI.create(NS + "B"))`, i.e. to class **B**, not C. Both
//    assertions are consequently about `B`. That is an upstream typo, but it is
//    what the oracle actually asserts, so it is what is ported — with the rule
//    head still naming `C`, exactly as upstream.
//
// 3. `testRuleWithConstants2` — upstream writes
//      `assertTrue(result.isSingleton()&result.containsEntity(b))`
//    with a single (non-short-circuiting) `&` for the `sb` case. Semantically
//    identical to `&&` here; not reproduced.
//
// 4. `testDiffrentFrom2` — the method name is misspelled upstream. The
//    misspelling is kept so the test name still greps back to the Java source.
// ---------------------------------------------------------------------------

const test = require('node:test');
const assert = require('node:assert/strict');

const E = require('../src/owl/OWLExpressions');
const { createReasoner } = require('../src/reasoner/Reasoner');
const RN = require('../src/structural/RuleNormalizer');
const { ontology } = require('./helpers');

const AT = E.AxiomType;

/** HermiT's `AbstractOntologyTest.ONTOLOGY_IRI` / `.NS`. */
const ONTOLOGY_IRI = 'file:/c/test.owl';
const NS = ONTOLOGY_IRI + '#';
const XSD = 'http://www.w3.org/2001/XMLSchema#';

// ---- entity shorthand (HermiT's `IRI.create(NS + …)`) ----------------------

const c = (n) => E.owlClass(NS + n);
const op = (n) => E.objectProperty(NS + n);
const dpn = (n) => E.dataProperty(NS + n);
const ni = (n) => E.namedIndividual(NS + n);
const declaration = (entity) => ({ axiomType: AT.DECLARATION, entity });

/** Declare every entity in one flat call, mirroring OWL API auto-declaration. */
const decls = (...entities) => entities.map(declaration);

// ---- literals and data ranges (HermiT's `TL` / `DR`) -----------------------

/** `"lex"^^xsd:dt`. */
const TL = (lex, dt) => E.literal(lex, XSD + dt);
const minInc = (lex, dt) => ({ facet: XSD + 'minInclusive', value: TL(lex, dt) });
const maxInc = (lex, dt) => ({ facet: XSD + 'maxInclusive', value: TL(lex, dt) });
/** HermiT's `DR(datatype, restrictions...)`: bare datatype when there are none. */
const DR = (dt, ...facets) =>
  (facets.length === 0 ? E.datatype(XSD + dt) : E.datatypeRestriction(E.datatype(XSD + dt), facets));

// ---- SWRL atoms ------------------------------------------------------------

const V = (name) => new RN.SWRLVariable(name);
const CA = RN.classAtom;
const OPA = RN.objectPropertyAtom;
const DPA = RN.dataPropertyAtom;
const SA = RN.sameAsAtom;
const DFA = RN.differentFromAtom;
const DRA = RN.dataRangeAtom;
/** A `DLSafeRule`. Detected structurally by `body`/`head` being arrays. */
const rule = (body, head) => ({ body: body.slice(), head: head.slice() });

// Property-characteristic axioms have no factory in OWLExpressions, so they are
// hand-built in the exact shape `OWLNormalization` reads.
const transitive = (x) => ({ axiomType: AT.TRANSITIVE_OBJECT_PROPERTY, property: x });
const func = (x) => ({ axiomType: AT.FUNCTIONAL_OBJECT_PROPERTY, property: x });

// ---- reasoner construction -------------------------------------------------

/**
 * HermiT's `loadOntologyWithAxioms(s); createReasoner();`.
 *
 * `throwInconsistentOntologyException` is FALSE because
 * `AbstractReasonerTest.getConfiguration()` sets it that way for the whole
 * corpus — this port's `Configuration` defaults it to TRUE, so the five oracles
 * below that assert an INCONSISTENT ABox would otherwise throw instead of
 * answering. (`testSimpleRule2` uses `createOWLReasoner`, i.e. the DEFAULT
 * configuration, upstream; its ontology is consistent so the flag is moot, and
 * one helper for the whole file keeps the encoding uniform.)
 */
function reasonerFor(axioms) {
  return createReasoner(ontology(axioms, ONTOLOGY_IRI),
    { throwInconsistentOntologyException: false });
}

/** Run `body(r)` and always dispose — a leaked tableau pins its clause index. */
function withReasoner(axioms, body) {
  const r = reasonerFor(axioms);
  try {
    return body(r);
  } finally {
    r.dispose();
  }
}

// ---- HermiT's assertions, ported one-for-one -------------------------------

/** `assertABoxSatisfiable(b)` → `assertEquals(b, m_reasoner.isConsistent())`. */
function assertABoxSatisfiable(r, expected) {
  assert.equal(r.isConsistent(), expected);
}

/** `m_reasoner.getInstances(C, false)` as a Set of IRI strings. */
function instances(r, klass) {
  return new Set([...r.getInstances(klass, false).getFlattened()].map((x) => E.iriString(x)));
}

/** `m_reasoner.getObjectPropertyValues(i, p)` as a Set of IRI strings. */
function objectPropertyValues(r, individual, property) {
  return new Set([...r.getObjectPropertyValues(individual, property).getFlattened()]
    .map((x) => E.iriString(x)));
}

/**
 * `assertTrue(m_reasoner.getInstances(C,false).containsEntity(i))` and its
 * negation. `NodeSet.containsEntity` compares by IRI, so comparing IRI strings
 * against the flattened set is exactly equivalent — and the failure message
 * names the whole answer set instead of just saying "false !== true".
 */
function assertInstance(r, klass, individual, expected) {
  const got = instances(r, klass);
  assert.equal(got.has(E.iriString(individual)), expected,
    `getInstances(${klass}, false) = {${[...got].sort().join(', ')}}`
    + ` — expected ${E.iriString(individual)} ${expected ? 'present' : 'absent'}`);
}

/** `assertTrue(result.isSingleton() && result.containsEntity(i))`. */
function assertSingletonValues(r, individual, property, expected) {
  const nodeSet = r.getObjectPropertyValues(individual, property);
  assert.equal(nodeSet.isSingleton(), true, `getObjectPropertyValues(${individual}, ${property}) is not a singleton`);
  assert.equal(nodeSet.containsEntity(expected), true,
    `getObjectPropertyValues(${individual}, ${property}) = {${[...objectPropertyValues(r, individual, property)].sort().join(', ')}}`
    + ` — expected ${E.iriString(expected)}`);
}

// ===========================================================================
// 1. sameAs atoms in the BODY
//
// `RuleNormalizer.normalize` processes body `SameAsAtom`s FIRST and uses them to
// canonicalise variables (`variableRepresentative`), so `x1 = x2 ∧ x1 = x3`
// collapses all three to one variable. The two oracles differ only in whether
// the three role assertions actually share a subject.
// ===========================================================================

test('RulesTest.testSameAsInBody1 — three roles off one subject force u(a)', () => {
  const [r, s, t] = [op('r'), op('s'), op('t')];
  const u = c('u');
  const [a, b, cc, d] = [ni('a'), ni('b'), ni('c'), ni('d')];
  // r(x1,y1) ∧ s(x2,y2) ∧ t(x3,y3) ∧ x1=x2 ∧ x1=x3 → u(x3)
  const rl = rule(
    [OPA(r, V('x1'), V('y1')), OPA(s, V('x2'), V('y2')), OPA(t, V('x3'), V('y3')),
     SA(V('x1'), V('x2')), SA(V('x1'), V('x3'))],
    [CA(u, V('x3'))]);
  withReasoner([
    ...decls(r, s, t, u, a, b, cc, d),
    E.objectPropertyAssertion(r, a, b),
    E.objectPropertyAssertion(s, a, cc),
    E.objectPropertyAssertion(t, a, d),
    E.classAssertion(E.objectComplementOf(u), a),
    rl
  ], (rsn) => {
    // u(a) is derived, and ¬u(a) is asserted.
    assertABoxSatisfiable(rsn, false);
  });
});

test('RulesTest.testSameAsInBody2 — three distinct subjects leave the rule unfired', () => {
  const [r, s, t] = [op('r'), op('s'), op('t')];
  const u = c('u');
  const [a1, a2, a3, b, cc, d] = [ni('a1'), ni('a2'), ni('a3'), ni('b'), ni('c'), ni('d')];
  const rl = rule(
    [OPA(r, V('x1'), V('y1')), OPA(s, V('x2'), V('y2')), OPA(t, V('x3'), V('y3')),
     SA(V('x1'), V('x2')), SA(V('x1'), V('x3'))],
    [CA(u, V('x3'))]);
  withReasoner([
    ...decls(r, s, t, u, a1, a2, a3, b, cc, d),
    E.objectPropertyAssertion(r, a1, b),
    E.objectPropertyAssertion(s, a2, cc),
    E.objectPropertyAssertion(t, a3, d),
    E.classAssertion(E.objectComplementOf(u), a1),
    rl
  ], (rsn) => {
    assertABoxSatisfiable(rsn, true);
  });
});

// ===========================================================================
// 2. data properties in the body
//
// `testSameAsInBodyWithDataProperties` binds the two data variables together
// with an explicit `SameAsAtom`; `testDataPropertiesInBody` shares ONE variable
// between the two atoms, which `RuleNormalizer` rewrites (per HermiT) into a
// fresh variable plus a `DifferentFromAtom` in the head — the encoding of "at
// most one value per data property atom in the body".
// ===========================================================================

/** The shared ABox of the two data-property oracles. */
function dataPropertyABox() {
  const [r, s] = [dpn('r'), dpn('s')];
  const u = c('u');
  const a = ni('a');
  return {
    r, s, u, a,
    common: [
      ...decls(r, s, u, a),
      E.dataPropertyAssertion(r, a, TL('2', 'integer')),
      // ∃s.[xsd:integer ≥ 2 ∧ ≤ 2] — a one-element value space.
      E.classAssertion(E.dataSomeValuesFrom(s, DR('integer', minInc('2', 'integer'), maxInc('2', 'integer'))), a),
      E.classAssertion(E.objectComplementOf(u), a)
    ]
  };
}

test('RulesTest.testSameAsInBodyWithDataProperties — y1=y2 unifies the two data values', () => {
  const { r, s, u, common } = dataPropertyABox();
  const rl = rule(
    [DPA(r, V('x'), V('y1')), DPA(s, V('x'), V('y2')), SA(V('y1'), V('y2'))],
    [CA(u, V('x'))]);
  withReasoner([...common, rl], (rsn) => assertABoxSatisfiable(rsn, false));
});

test('RulesTest.testDataPropertiesInBody — one shared data variable means the same value', () => {
  const { r, s, u, common } = dataPropertyABox();
  const rl = rule(
    [DPA(r, V('x'), V('y')), DPA(s, V('x'), V('y'))],
    [CA(u, V('x'))]);
  withReasoner([...common, rl], (rsn) => assertABoxSatisfiable(rsn, false));
});

// ===========================================================================
// 3. ground individuals in body and head positions
//
// `RuleNormalizer._getVariableFor` replaces a non-variable argument with a FRESH
// variable plus a `ClassAtom(ObjectOneOf({ind}), fresh)` body atom. So `c(a)` in
// a body becomes `∃v. {a}(v) ∧ c(v)`, and `d(b)` in a head becomes
// `∃v. {b}(v) → d(v)`.
// ===========================================================================

test('RulesTest.testIndividualsInRules — a fully ground rule is a conditional fact', () => {
  const [cd, dd] = [c('c'), c('d')];
  const [a, b] = [ni('a'), ni('b')];
  // c(a) → d(b)
  const rl = rule([CA(cd, a)], [CA(dd, b)]);
  withReasoner([
    ...decls(a, b, cd, dd),
    E.classAssertion(cd, a),
    E.classAssertion(E.objectComplementOf(dd), b),
    rl
  ], (rsn) => {
    assertABoxSatisfiable(rsn, false);
  });
});

test('RulesTest.testRuleWithConstants — a ground head individual is asserted once the body fires', () => {
  const [A, B, C, D] = [c('A'), c('B'), c('C'), c('D')];
  const [a, b] = [ni('a'), ni('b')];
  // B(x) → C(a)
  const rl = rule([CA(B, V('x'))], [CA(C, a)]);
  withReasoner([
    ...decls(A, B, C, D, a, b),
    E.subclassOf(A, B),
    E.classAssertion(A, a),
    E.classAssertion(D, b),
    rl
  ], (rsn) => {
    assertInstance(rsn, C, a, true);
    assertInstance(rsn, C, b, false);
  });
});

test('RulesTest.testRuleWithConstants2 — ground arguments in every position', () => {
  const [r, s, sa, sb, q] = [op('r'), op('s'), op('sa'), op('sb'), op('q')];
  const [a, b] = [ni('a'), ni('b')];
  withReasoner([
    ...decls(r, s, sa, sb, q, a, b),
    E.classAssertion(E.objectSomeValuesFrom(r, E.owlThing()), a),
    E.objectPropertyAssertion(r, a, b),
    // r(x,y) → s(x,y)
    rule([OPA(r, V('x'), V('y'))], [OPA(s, V('x'), V('y'))]),
    // r(x,b) → sb(x,b)
    rule([OPA(r, V('x'), b)], [OPA(sb, V('x'), b)]),
    // s(a,x) → sa(a,b)
    rule([OPA(s, a, V('x'))], [OPA(sa, a, b)]),
    // r(a,b) → q(a,b)
    rule([OPA(r, a, b)], [OPA(q, a, b)])
  ], (rsn) => {
    for (const property of [r, s, sa, sb, q]) {
      assertSingletonValues(rsn, a, property, b);
    }
  });
});

test('RulesTest.testSeveralVars — six variables, a ground body atom and a ground head atom', () => {
  const [A, B, C, D, Ecls, Ap, Bp, Cp, Dp, Ep] =
    [c('A'), c('B'), c('C'), c('D'), c('E'), c('Ap'), c('Bp'), c('Cp'), c('Dp'), c('Ep')];
  const [rab, rac, rcd, rae] = [op('rab'), op('rac'), op('rcd'), op('rae')];
  const [a, b, cc, d, e] = [ni('a'), ni('b'), ni('c'), ni('d'), ni('e')];
  // A(xa) ∧ B(b) ∧ rab(xa,xb) ∧ rac(xa,xc) ∧ rcd(xc,xd) ∧ E(xe)
  //   → Ap(xa) ∧ Bp(xb) ∧ Cp(c) ∧ Dp(xd) ∧ Ep(xe) ∧ rae(xa,xe)
  const rl = rule(
    [CA(A, V('xa')), CA(B, b),
     OPA(rab, V('xa'), V('xb')), OPA(rac, V('xa'), V('xc')), OPA(rcd, V('xc'), V('xd')),
     CA(Ecls, V('xe'))],
    [CA(Ap, V('xa')), CA(Bp, V('xb')), CA(Cp, cc), CA(Dp, V('xd')), CA(Ep, V('xe')),
     OPA(rae, V('xa'), V('xe'))]);
  withReasoner([
    ...decls(A, B, C, D, Ecls, Ap, Bp, Cp, Dp, Ep, rab, rac, rcd, rae, a, b, cc, d, e),
    E.classAssertion(A, a), E.classAssertion(B, b), E.classAssertion(C, cc),
    E.classAssertion(D, d), E.classAssertion(Ecls, e),
    E.objectPropertyAssertion(rab, a, b),
    E.objectPropertyAssertion(rac, a, cc),
    E.objectPropertyAssertion(rcd, cc, d),
    rl
  ], (rsn) => {
    assertInstance(rsn, Ap, a, true);
    assertInstance(rsn, Bp, b, true);
    assertInstance(rsn, Cp, cc, true);
    assertInstance(rsn, Dp, d, true);
    assertInstance(rsn, Ep, e, true);
    assertInstance(rsn, A, a, true);
    assertInstance(rsn, B, b, true);
    assertInstance(rsn, Ecls, e, true);
    assert.equal(rsn.getObjectPropertyValues(cc, rcd).containsEntity(d), true);
    assertSingletonValues(rsn, a, rae, e);
  });
});

// ===========================================================================
// 4. rules are NOT axioms
// ===========================================================================

test('RulesTest.testRuleNotAxiom — A(x)→B(x) does not make A a subclass of B', () => {
  const [A, B] = [c('A'), c('B')];
  const [a, b] = [ni('a'), ni('b')];
  const rl = rule([CA(A, V('x'))], [CA(B, V('x'))]);
  withReasoner([
    ...decls(A, B, a, b),
    E.classAssertion(A, a),
    E.classAssertion(A, b),
    rl
  ], (rsn) => {
    // A DL-safe rule ranges over the ABox only; it is not a TBox inclusion.
    assert.equal(rsn.isEntailed(E.subclassOf(A, B)), false);
    assertInstance(rsn, A, a, true);
    assertInstance(rsn, A, b, true);
    assertInstance(rsn, B, a, true);
    assertInstance(rsn, B, b, true);
  });
});

test('RulesTest.testSimpleRule — a rule chains off a TBox inclusion', () => {
  const [A, B, C, D] = [c('A'), c('B'), c('C'), c('D')];
  const [a, b] = [ni('a'), ni('b')];
  // B(x) → C(x)
  const rl = rule([CA(B, V('x'))], [CA(C, V('x'))]);
  withReasoner([
    ...decls(A, B, C, D, a, b),
    E.subclassOf(A, B),
    E.classAssertion(A, a),
    E.classAssertion(D, b),
    rl
  ], (rsn) => {
    assertInstance(rsn, C, a, true);
    assertInstance(rsn, C, b, false);
  });
});

test('RulesTest.testSimpleRule2 — a five-atom body derives a role assertion', () => {
  const [BluetoothDevice, BluetoothSensor, Location] =
    [c('BluetoothDevice'), c('BluetoothSensor'), c('Location')];
  const [hasLocation, detects] = [op('hasLocation'), op('detects')];
  const [pda, sensor, kitchen] = [ni('pda'), ni('sensor'), ni('kitchen')];
  // BluetoothDevice(vbd) ∧ BluetoothSensor(vbs) ∧ Location(vl)
  //   ∧ detects(vbs,vbd) ∧ hasLocation(vbs,vl) → hasLocation(vbd,vl)
  const rl = rule(
    [CA(BluetoothDevice, V('vbd')), CA(BluetoothSensor, V('vbs')), CA(Location, V('vl')),
     OPA(detects, V('vbs'), V('vbd')), OPA(hasLocation, V('vbs'), V('vl'))],
    [OPA(hasLocation, V('vbd'), V('vl'))]);
  withReasoner([
    ...decls(BluetoothDevice, BluetoothSensor, Location, hasLocation, detects, pda, sensor, kitchen),
    E.classAssertion(BluetoothDevice, pda),
    E.classAssertion(BluetoothSensor, sensor),
    E.classAssertion(Location, kitchen),
    E.objectPropertyAssertion(detects, sensor, pda),
    E.objectPropertyAssertion(hasLocation, sensor, kitchen),
    rl
  ], (rsn) => {
    assert.equal(rsn.getObjectPropertyValues(pda, hasLocation).containsEntity(kitchen), true);
  });
});

// ===========================================================================
// 5. non-simple properties
// ===========================================================================

test('RulesTest.testRuleNonSimple — a transitive property still answers role queries', () => {
  const [t, s] = [op('t'), op('s')];
  const [a, b] = [ni('a'), ni('b')];
  // t(x,y) → s(x,y)
  const rl = rule([OPA(t, V('x'), V('y'))], [OPA(s, V('x'), V('y'))]);
  withReasoner([
    ...decls(t, s, a, b),
    transitive(t),
    E.classAssertion(E.objectSomeValuesFrom(t, E.objectSomeValuesFrom(t, E.objectOneOf([b]))), a),
    rl
  ], (rsn) => {
    assert.equal(rsn.hasObjectPropertyRelationship(a, t, b), true);
    // UPSTREAM: the corresponding `s` assertion is COMMENTED OUT in HermiT with
    // the note "The following fails because transitive properties in rules do
    // not work correctly". It is deliberately not ported — see the file header.
  });
});

// ===========================================================================
// 6. datatype literals in rule atoms
// ===========================================================================

test('RulesTest.testRuleWithDatatypes — "18"^^xsd:short matches "18"^^xsd:integer', () => {
  const dp = dpn('dp');
  const C = c('C');
  const [a, b] = [ni('a'), ni('b')];
  // dp(x, "18"^^xsd:integer) → C(x)
  const rl = rule([DPA(dp, V('x'), TL('18', 'integer'))], [CA(C, V('x'))]);
  withReasoner([
    ...decls(dp, C, a, b),
    E.dataPropertyAssertion(dp, a, TL('18', 'short')),
    E.dataPropertyAssertion(dp, b, TL('17', 'short')),
    rl
  ], (rsn) => {
    // Cross-datatype NUMERIC equality: `constantsEqual` compares parsed values
    // within the numeric group, so "18"^^xsd:short ≡ "18"^^xsd:integer.
    assertInstance(rsn, C, a, true);
    assertInstance(rsn, C, b, false);
  });
});

test('RulesTest.testRuleWithDatatypes2 — a DataRangeAtom splits the individuals by value', () => {
  const dp = dpn('dp');
  const [C, D] = [c('C'), c('D')];
  const [a, b, cc] = [ni('a'), ni('b'), ni('c')];
  const atLeast15 = DR('int', minInc('15', 'int'));
  // dp(x,y) ∧ [xsd:int ≥ 15](y) → C(x)
  const rl1 = rule([DPA(dp, V('x'), V('y')), DRA(atLeast15, V('y'))], [CA(C, V('x'))]);
  // dp(x,y) ∧ ¬[xsd:int ≥ 15](y) → D(x)
  const rl2 = rule([DPA(dp, V('x'), V('y')), DRA(E.dataComplementOf(atLeast15), V('y'))], [CA(D, V('x'))]);
  withReasoner([
    ...decls(dp, C, D, a, b, cc),
    E.classAssertion(E.dataSomeValuesFrom(dp, DR('integer', minInc('10', 'integer'))), a),
    E.dataPropertyAssertion(dp, b, TL('10', 'short')),
    E.dataPropertyAssertion(dp, cc, TL('25', 'integer')),
    E.classAssertion(E.objectComplementOf(C), a),
    rl1, rl2
  ], (rsn) => {
    assertInstance(rsn, C, cc, true);
    assertInstance(rsn, C, a, false);
    assertInstance(rsn, C, b, false);
    assertInstance(rsn, D, b, true);
    assertInstance(rsn, D, a, true);
    assertInstance(rsn, D, cc, false);
  });
});

// ===========================================================================
// 7. DataRangeAtom in the body, positive and negative
// ===========================================================================

test('RulesTest.testPositiveBodyDataRange — a body data range fires on a matching value', () => {
  const dp = dpn('dp');
  const [A, B] = [c('A'), c('B')];
  const a = ni('a');
  // dp(x,y) ∧ (([xsd:integer ≥ 5]) ⊓ ([xsd:decimal ≤ 10]))(y) → B(x)
  const intersection = E.dataIntersectionOf([
    DR('integer', minInc('5', 'int')),
    DR('decimal', maxInc('10', 'int'))
  ]);
  const rl = rule([DPA(dp, V('x'), V('y')), DRA(intersection, V('y'))], [CA(B, V('x'))]);
  withReasoner([
    ...decls(dp, A, B, a),
    E.classAssertion(A, a),
    E.subclassOf(A, E.dataSomeValuesFrom(dp, DR('integer', minInc('6', 'integer'), maxInc('9', 'integer')))),
    rl
  ], (rsn) => {
    assertInstance(rsn, B, a, true);
  });
});

test('RulesTest.testNegativeBodyDataRange — a complemented body data range', () => {
  const dp = dpn('dp');
  const [A, B] = [c('A'), c('B')];
  const [a, b] = [ni('a'), ni('b')];
  // dp(x,y) ∧ ¬(([xsd:integer ≥ 5]) ⊓ ([xsd:decimal ≤ 10]))(y) → C(x)
  const intersection = E.dataIntersectionOf([
    DR('integer', minInc('5', 'int')),
    DR('decimal', maxInc('10', 'int'))
  ]);
  const rl = rule([DPA(dp, V('x'), V('y')), DRA(E.dataComplementOf(intersection), V('y'))],
    [CA(c('C'), V('x'))]);
  withReasoner([
    ...decls(dp, A, B, a, b),
    E.classAssertion(A, a),
    E.classAssertion(B, b),
    E.subclassOf(A, E.dataSomeValuesFrom(dp, DR('integer', minInc('6', 'integer'), maxInc('9', 'integer')))),
    E.subclassOf(B, E.dataHasValue(dp, TL('abc', 'string'))),
    rl
  ], (rsn) => {
    // UPSTREAM TYPO, PRESERVED: HermiT binds its local `C` to
    // `getOWLClass(IRI.create(NS + "B"))`, so BOTH assertions are about class
    // B even though the rule head names C. See the file header.
    assertInstance(rsn, B, a, false);
    assertInstance(rsn, B, b, true);
  });
});

test('RulesTest.testNegDRInHead — a negated data range in the head clashes with the value space', () => {
  const dp = dpn('dp');
  const A = c('A');
  const a = ni('a');
  // dp(x,y) → ¬([xsd:short ≥ 1])(y)
  const rl = rule([DPA(dp, V('x'), V('y'))],
    [DRA(E.dataComplementOf(DR('short', minInc('1', 'int'))), V('y'))]);
  withReasoner([
    ...decls(dp, A, a),
    E.classAssertion(A, a),
    E.subclassOf(A, E.dataSomeValuesFrom(dp, DR('integer', minInc('6', 'integer'), maxInc('9', 'integer')))),
    rl
  ], (rsn) => {
    // a's dp value is an integer in 6..9, hence a short ≥ 1, hence the head is
    // unsatisfiable.
    assertABoxSatisfiable(rsn, false);
  });
});

// ===========================================================================
// 8. sameAs / differentFrom in the HEAD
// ===========================================================================

test('RulesTest.testSameAs — a sameAs head merges two disjoint individuals', () => {
  const r = op('r');
  const [A, B] = [c('A'), c('B')];
  const [a, b] = [ni('a'), ni('b')];
  // r(x,y) → SameIndividualAtom(x,y)
  const rl = rule([OPA(r, V('x'), V('y'))], [SA(V('x'), V('y'))]);
  withReasoner([
    ...decls(r, A, B, a, b),
    E.classAssertion(A, a),
    E.classAssertion(B, b),
    E.disjointClasses([A, B]),
    E.objectPropertyAssertion(r, a, b),
    rl
  ], (rsn) => {
    assertABoxSatisfiable(rsn, false);
  });
});

test('RulesTest.testDifferentFrom — a differentFrom head clashes with functionality', () => {
  const f = op('f');
  const [a, b, cc] = [ni('a'), ni('b'), ni('c')];
  // f(x,y) ∧ f(x,z) → DifferentIndividualsAtom(y,z)
  const rl = rule([OPA(f, V('x'), V('y')), OPA(f, V('x'), V('z'))], [DFA(V('y'), V('z'))]);
  withReasoner([
    ...decls(f, a, b, cc),
    E.objectPropertyAssertion(f, a, b),
    E.objectPropertyAssertion(f, a, cc),
    func(f),
    rl
  ], (rsn) => {
    // f is functional, so b and c are the same individual — and the rule then
    // demands they be different.
    assertABoxSatisfiable(rsn, false);
  });
});

test('RulesTest.testDiffrentFrom2 — a differentFrom BODY atom is a sameAs head atom', () => {
  const r = op('r');
  const [A, B, C] = [c('A'), c('B'), c('C')];
  const [a, b] = [ni('a'), ni('b')];
  // r(x,y) ∧ DifferentIndividualsAtom(x,y) → C(x)
  const rl = rule([OPA(r, V('x'), V('y')), DFA(V('x'), V('y'))], [CA(C, V('x'))]);
  withReasoner([
    ...decls(r, A, B, C, a, b),
    E.classAssertion(A, a),
    E.classAssertion(B, b),
    E.disjointClasses([A, B]),
    E.objectPropertyAssertion(r, a, b),
    rl
  ], (rsn) => {
    // ¬differentFrom(x,y) in the body is normalized to sameAs(x,y) in the HEAD,
    // so the clause is `r(x,y) → C(x) ∨ x=y`; a≠b kills the second disjunct.
    assertInstance(rsn, C, a, true);
    assertInstance(rsn, C, b, false);
  });
});

// ===========================================================================
// 9. head shapes: fresh individuals, empty bodies, Lloyd-Topor
// ===========================================================================

test('RulesTest.testRuleWithFreshIndividuals — a ground head individual is not the body variable', () => {
  const [A, B, C] = [c('A'), c('B'), c('C')];
  const [a, b] = [ni('a'), ni('b')];
  withReasoner([
    ...decls(A, B, C, a, b),
    E.classAssertion(A, a),
    // A(x) → B(b)
    rule([CA(A, V('x'))], [CA(B, b)]),
    // B(x) → C(x)
    rule([CA(B, V('x'))], [CA(C, V('x'))])
  ], (rsn) => {
    assertInstance(rsn, C, b, true);
    assertInstance(rsn, B, b, true);
    assertInstance(rsn, C, a, false);
    assertInstance(rsn, B, a, false);
  });
});

test('RulesTest.testAddingFactsByRules — empty bodies become unconditional facts', () => {
  const [A, B, C, D, Ecls] = [c('A'), c('B'), c('C'), c('D'), c('E')];
  const [a, b, e] = [ni('a'), ni('b'), ni('e')];
  withReasoner([
    ...decls(A, B, C, D, Ecls, a, b, e),
    E.classAssertion(A, a),
    // → B(a)          (empty body ⇒ Rule2FactConverter, not RuleNormalizer)
    rule([], [CA(B, a)]),
    // → B(b)
    rule([], [CA(B, b)]),
    // B(x) → C(x)
    rule([CA(B, V('x'))], [CA(C, V('x'))]),
    // B(x) ∧ A(x) → D(x)
    rule([CA(B, V('x')), CA(A, V('x'))], [CA(D, V('x'))]),
    // B(x) ∧ D(y) → E(e)
    rule([CA(B, V('x')), CA(D, V('y'))], [CA(Ecls, e)])
  ], (rsn) => {
    assertInstance(rsn, A, a, true);
    assertInstance(rsn, A, b, false);
    assertInstance(rsn, B, a, true);
    assertInstance(rsn, B, b, true);
    assertInstance(rsn, B, e, false);
    assertInstance(rsn, C, a, true);
    assertInstance(rsn, C, b, true);
    assertInstance(rsn, C, e, false);
    assertInstance(rsn, D, a, true);
    assertInstance(rsn, D, b, false);
    assertInstance(rsn, D, e, false);
    assertInstance(rsn, Ecls, a, false);
    assertInstance(rsn, Ecls, b, false);
    assertInstance(rsn, Ecls, e, true);
  });
});

test('RulesTest.testLloydTopor — a conjunctive head is split into one rule per atom', () => {
  const [A, B, C] = [c('A'), c('B'), c('C')];
  const [a, b] = [ni('a'), ni('b')];
  // A(x) → B(x) ∧ C(x)
  const rl = rule([CA(A, V('x'))], [CA(B, V('x')), CA(C, V('x'))]);
  withReasoner([
    ...decls(A, B, C, a, b),
    E.classAssertion(A, a),
    E.classAssertion(B, b),
    rl
  ], (rsn) => {
    assertInstance(rsn, A, a, true);
    assertInstance(rsn, B, a, true);
    assertInstance(rsn, C, a, true);
    assertInstance(rsn, A, b, false);
    assertInstance(rsn, B, b, true);
    assertInstance(rsn, C, b, false);
  });
});

// ===========================================================================
// 10. DL-safety rejection
//
// HermiT expects `IllegalArgumentException` from `createReasoner()`. The rule
// `A(x) ∧ xsd:integer(y) → dp(x,y)` has a data-range variable `y` that occurs
// ONLY in a `DataRangeAtom`. `RuleNormalizer` always files data-range atoms
// under `headDataRangeVariables` (a body `DataRangeAtom` is negated into the
// head), and nothing ever adds `y` to `bodyDataRangeVariables` — only a
// `DataPropertyAtom` in the body does that. The post-check therefore fires.
//
// This port throws a plain `Error` (JavaScript has no checked-exception
// hierarchy and `IllegalArgumentException` is not a JS built-in); the MESSAGE is
// HermiT's verbatim, which is what makes the two distinguishable from an
// unrelated crash.
// ===========================================================================

test('RulesTest.testDataRangeSafety — an unbound data-range variable is rejected', () => {
  const dp = dpn('dp');
  const A = c('A');
  const a = ni('a');
  // A(x) ∧ xsd:integer(y) → dp(x,y)
  const rl = rule([CA(A, V('x')), DRA(E.datatype(XSD + 'integer'), V('y'))],
    [DPA(dp, V('x'), V('y'))]);
  let message = null;
  try {
    reasonerFor([...decls(dp, A, a), E.classAssertion(A, a), rl]).dispose();
  } catch (err) {
    message = err.message;
  }
  assert.notEqual(message, null, 'createReasoner() was expected to throw');
  assert.match(message, /data range variables in the head, but not in the body/);
});
