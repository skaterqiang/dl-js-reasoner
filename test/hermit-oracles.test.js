'use strict';

// ---------------------------------------------------------------------------
// test/hermit-oracles.test.js — differential tests against HermiT's own JUnit
// suite.
//
// Every other test file in this project asserts behaviour we DERIVED from the
// reference implementation. This one asserts behaviour the reference
// implementation itself PINS, by porting its test methods verbatim:
//
//   org.semanticweb.HermiT.reasoner.SimpleRolesTest   (4 oracles)
//   org.semanticweb.HermiT.reasoner.RIATest           (11 oracles)
//   org.semanticweb.HermiT.structural.ClausificationTest (2 oracles)
//   org.semanticweb.HermiT.reasoner.EntailmentTest    (10 oracles)
//
// `hermit-reasoner-master/src/test/java/...` is the source; the method name is
// quoted above each test. HermiT's `AbstractReasonerTest` supplies the helpers
// this file mirrors:
//
//   assertSimple(axioms, expected)  — `loadReasonerWithAxioms` must throw
//                                     "Non-simple property '<p>'…" iff !expected
//   assertRegular(axioms, expected) — …must throw "The given property hierarchy
//                                     is not regular" iff !expected
//   assertEntails(axioms, expected) — `EntailmentChecker.entails` must return
//                                     `expected`, or throw for a malformed query
//
// Our port raises the IDENTICAL error messages from
// `structural/ObjectPropertyInclusionManager`, so the assertions below match on
// the message text rather than on a Java exception type.
//
// TWO REAL DEFECTS were found by this file and are fixed in `src/`:
//
//   1. `EntailmentTest.testBlankWithDTs3` — an untagged, untyped literal
//      defaulted to `rdf:PlainLiteral` instead of `xsd:string` (OWL 2 Syntax
//      §2.3; OWL API's `getOWLLiteral(String)`). `"test"` and
//      `"test"^^xsd:string` were therefore two DIFFERENT constants. Fixed in
//      `owl/OWLExpressions.js` (`literal` + `OWLLiteral.getDatatypeIRI`).
//
//   2. `EntailmentTest.testHasKey` — the disjoint-datatype clash in
//      `DatatypeReasoning.checkConstraintsSatisfiable` step 2 filtered on
//      `LiteralDataRange`, but `OWLClausification._convertDatatype` turns every
//      bare datatype into a FACET-FREE `DatatypeRestriction` (`xsd:string[]`),
//      exactly as HermiT does. The clash was consequently unreachable from real
//      input. Fixed by adding `DatatypeReasoning.datatypeIRIOf`.
//
// TWO ORACLES DELIBERATELY DIVERGE from HermiT; both are documented in place
// below (`testHasKeys`, `testValidBlankNodesWithNominals`).
// ---------------------------------------------------------------------------

const test = require('node:test');
const assert = require('node:assert/strict');

const E = require('../src/owl/OWLExpressions');
const C = require('../src/structural/OWLClausification');
const { createReasoner } = require('../src/reasoner/Reasoner');

const AT = E.AxiomType;

// HermiT's tests use `NS = "http://www.test.com/"`; the exact IRI is irrelevant
// to every oracle here EXCEPT the two clause-string comparisons, which are
// pinned against this value.
const EX = 'http://ex.org#';
const XSD = 'http://www.w3.org/2001/XMLSchema#';

const c = (n) => E.owlClass(EX + n);
const p = (n) => E.objectProperty(EX + n);
const dp = (n) => E.dataProperty(EX + n);
const ind = (n) => E.namedIndividual(EX + n);
const anon = (n) => E.anonymousIndividual(n);
const xsd = (n) => E.datatype(XSD + n);
const declaration = (entity) => ({ axiomType: AT.DECLARATION, entity });

// Property axioms have no factory in OWLExpressions, so they are hand-built in
// the exact shape `OWLNormalization` reads. NOTE the asymmetry, which cost a
// debugging cycle: OWL API models `InverseObjectProperties` as a PAIR
// (`getFirstProperty`/`getSecondProperty`; protege-js spells them
// `property1`/`property2`), whereas `EquivalentObjectProperties` and
// `DisjointObjectProperties` take a `properties` SET.
const sub = (s, u) => ({ axiomType: AT.SUB_OBJECT_PROPERTY_OF, subProperty: s, superProperty: u });
const chain = (arr, u) => ({ axiomType: AT.SUB_PROPERTY_CHAIN_OF, propertyChain: arr, superProperty: u });
const inv = (a, b) => ({ axiomType: AT.INVERSE_OBJECT_PROPERTIES, firstProperty: a, secondProperty: b });
const equiv = (arr) => ({ axiomType: AT.EQUIVALENT_OBJECT_PROPERTIES, properties: arr });
const trans = (x) => ({ axiomType: AT.TRANSITIVE_OBJECT_PROPERTY, property: x });
const asymmetric = (x) => ({ axiomType: AT.ASYMMETRIC_OBJECT_PROPERTY, property: x });
const negOPA = (prop, s, o) => E.negativeObjectPropertyAssertion(prop, s, o);

/** HermiT's `loadReasonerWithAxioms`, reduced to the clausification stage. */
function load(axioms) {
  return new C.OWLClausification().preprocessAndClausify(axioms, { ontologyIRI: 'urn:test' });
}

function ontoOf(axioms) {
  return {
    getAxioms: () => axioms.slice(),
    getOntologyID: () => ({ ontologyIRI: 'urn:test' })
  };
}

/**
 * HermiT's `assertSimple(axioms, expected)`.
 *
 * `expected === false` means the hierarchy must be REJECTED with a
 * `Non-simple property` error; `true` means clausification must succeed.
 */
function assertSimple(axioms, expected) {
  if (expected) {
    assert.doesNotThrow(() => load(axioms));
    return;
  }
  assert.throws(() => load(axioms), /Non-simple property '/);
}

/** HermiT's `assertRegular(axioms, expected)`. */
function assertRegular(axioms, expected) {
  if (expected) {
    assert.doesNotThrow(() => load(axioms));
    return;
  }
  assert.throws(() => load(axioms), /The given property hierarchy is not regular/);
}

/**
 * HermiT's `assertEntails(conclusions.getLogicalAxioms(), expected)`.
 *
 * `expected === 'THROW'` mirrors a test whose body wraps the call in
 * `try { … fail(); } catch (Exception e) { … }` — i.e. the query is malformed
 * and MUST be rejected rather than answered.
 */
function assertEntails(premise, conclusion, expected) {
  const r = createReasoner(ontoOf(premise), {});
  try {
    if (expected === 'THROW') {
      assert.throws(() => r.isEntailed(conclusion));
    } else {
      assert.equal(r.isEntailed(conclusion), expected);
    }
  } finally {
    r.dispose();
  }
}

// ===========================================================================
// org.semanticweb.HermiT.reasoner.SimpleRolesTest
//
// All four assert `assertSimple(axioms, false)`: a property made non-simple by
// transitivity or by a role chain it participates in cannot appear inside a
// cardinality restriction.
// ===========================================================================

test('SimpleRolesTest.testSimpleRoles1 — transitive R ⊑ P rejects ≤2 P', () => {
  assertSimple([
    trans(p('R')),
    sub(p('R'), p('P')),
    E.subclassOf(c('C'), E.objectMinCardinality(2, p('P')))
  ], false);
});

test('SimpleRolesTest.testSimpleRoles2 — R∘Q ⊑ R rejects ≤2 P via R ⊑ P', () => {
  assertSimple([
    chain([p('R'), p('Q')], p('R')),
    sub(p('R'), p('P')),
    E.subclassOf(c('C'), E.objectMaxCardinality(2, p('P')))
  ], false);
});

test('SimpleRolesTest.testSimpleRoles3 — non-simplicity propagates through inverses', () => {
  assertSimple([
    chain([p('R'), p('Q')], p('R')),
    sub(p('R'), p('S')),
    inv(p('S'), p('S-')),
    E.subclassOf(c('C'), E.objectMaxCardinality(2, p('S-')))
  ], false);
});

test('SimpleRolesTest.testSimpleRoles4 — non-simplicity propagates up a chain', () => {
  assertSimple([
    trans(p('R-')),
    sub(p('R'), p('P')),
    sub(p('P'), p('S')),
    inv(p('R'), p('R-')),
    inv(p('S'), p('S-')),
    E.subclassOf(c('C'), E.objectMaxCardinality(2, p('S-')))
  ], false);
});

// ===========================================================================
// org.semanticweb.HermiT.reasoner.RIATest
//
// Role-inclusion-axiom regularity. `testRIARegularity0`–`9` mirror HermiT's
// numbering exactly, including the two counter-intuitive answers: a CYCLE of
// plain subproperties (`1`) is regular, and `topObjectProperty` inside a chain
// (`0`) is regular, whereas a chain that reuses its own superproperty is not.
// ===========================================================================

test('RIATest.testInverseAndChain — the marriage ontology is inconsistent', () => {
  const r = createReasoner(ontoOf([
    E.objectPropertyAssertion(p('hasFemalePartner'), ind('marriage_of_david_and_margaret'), ind('margaret')),
    E.objectPropertyAssertion(p('hasHusband'), ind('marriage_of_david_and_margaret'), ind('david')),
    sub(E.objectInverseOf(p('hasWife')), p('isWifeOf')),
    sub(E.objectInverseOf(p('isWifeOf')), p('hasWife')),
    sub(E.objectInverseOf(p('hasHusband')), p('isHusbandOf')),
    chain([p('isHusbandOf'), p('hasFemalePartner')], p('hasWife')),
    negOPA(p('isWifeOf'), ind('margaret'), ind('david'))
  ]), {});
  try { assert.equal(r.isConsistent(), false); } finally { r.dispose(); }
});

test('RIATest.testRIARegularity0 — ⊤ inside a chain is regular', () => {
  assertRegular([
    sub(p('loves'), E.topObjectProperty()),
    chain([p('pHuman'), E.topObjectProperty(), p('pCat')], p('loves'))
  ], true);
});

test('RIATest.testRIARegularity1 — a plain subproperty cycle is regular', () => {
  assertRegular([
    sub(p('A'), p('B')), sub(p('B'), p('C')), sub(p('C'), p('D')), sub(p('D'), p('A'))
  ], true);
});

test('RIATest.testRIARegularity2 — R∘Q ⊑ P with P ≡ Q⁻ is irregular', () => {
  assertRegular([chain([p('R'), p('Q')], p('P')), inv(p('P'), p('Q'))], false);
});

test('RIATest.testRIARegularity3 — an inverse inside the chain is still irregular', () => {
  assertRegular([chain([p('R'), E.objectInverseOf(p('Q'))], p('P')), inv(p('P'), p('Q'))], false);
});

test('RIATest.testRIARegularity4 — left-recursive chains are irregular', () => {
  assertRegular([
    chain([p('R'), p('Q'), p('P')], p('P')), chain([p('P'), p('S')], p('Q')), sub(p('Q'), p('R'))
  ], false);
});

test('RIATest.testRIARegularity5 — the same shape with an equivalence is regular', () => {
  assertRegular([
    chain([p('R'), p('Q'), p('P')], p('P')), chain([p('P'), p('S')], p('L')),
    sub(p('L'), p('R')), sub(p('R'), p('L'))
  ], true);
});

test('RIATest.testRIARegularity6 — P∘P⁻∘P ⊑ P is irregular', () => {
  assertRegular([chain([p('P'), E.objectInverseOf(p('P')), p('P')], p('P'))], false);
});

test('RIATest.testRIARegularity7 — a two-level chain cycle is irregular', () => {
  assertRegular([
    inv(p('P'), p('P-')), chain([p('L'), p('P-')], p('L')), chain([p('R'), p('L')], p('P'))
  ], false);
});

test('RIATest.testRIARegularity8 — an all-equivalent four-cycle is regular', () => {
  assertRegular([
    chain([p('R4'), p('R1')], p('R1')), chain([p('R1'), p('R2')], p('R2')),
    chain([p('R2'), p('R3')], p('R3')), chain([p('R3'), p('R4')], p('R4')),
    equiv([p('R1'), p('R2')]), equiv([p('R2'), p('R3')]),
    equiv([p('R3'), p('R4')]), equiv([p('R4'), p('R1')])
  ], true);
});

test('RIATest.testRIARegularity9 — R1∘R2∘R3 ⊑ R with R2 ≡ R is irregular', () => {
  assertRegular([chain([p('R1'), p('R2'), p('R3')], p('R')), equiv([p('R2'), p('R')])], false);
});

// ===========================================================================
// org.semanticweb.HermiT.structural.ClausificationTest
//
// These compare the DL-clause set against `src/test/resources/.../structural/res`
// control files. NOTE: `known-test-failures.txt` lists `testBasic`,
// `testNominals1`–`4`, `testExistsSelf1` and `testHasKeys` as FAILING in
// HermiT's own build, so their control files are stale and are not ported.
// ===========================================================================

test('ClausificationTest.testAsymmetry — matches the control file exactly', () => {
  const o = load([
    asymmetric(p('as')),
    sub(p('r'), p('as')),
    E.objectPropertyAssertion(p('r'), ind('a'), ind('b')),
    E.objectPropertyAssertion(p('as'), ind('b'), ind('a'))
  ]).dlOntology;

  // asymmetry-control.txt: " :- :as(X,Y), :as(Y,X)" / ":as(X,Y) :- :r(X,Y)".
  assert.deepEqual([...o.dlClauses].map(String).sort(), [
    ' :- http://ex.org#as(X, Y) ^ http://ex.org#as(Y, X)',
    'http://ex.org#as(X, Y) :- http://ex.org#r(X, Y)'
  ].sort());
  assert.deepEqual([...o.positiveFacts].map(String).sort(), [
    'http://ex.org#as(<http://ex.org#b>, <http://ex.org#a>)',
    'http://ex.org#r(<http://ex.org#a>, <http://ex.org#b>)'
  ].sort());
  assert.deepEqual([...o.negativeFacts].map(String), []);
});

// DIVERGENCE (stale upstream oracle).
//
// HermiT's `has-keys-control.txt` wants the body atoms
//   r_test(X1,Y0) / r_test(X2,Y0) / Named(Y0) / dp_test(X1,Y1) / dp_test(X2,Y2)
// and we emit
//   r_test(X1,Y1) / r_test(X2,Y1) / Named(Y1) / dp_test(X1,Y2) / dp_test(X2,Y3)
// — the SAME clause, differing only in where the variable counter starts.
// `known-test-failures.txt:77` lists
// `testHasKeys(org.semanticweb.HermiT.structural.ClausificationTest)` as a KNOWN
// HERMIT FAILURE, i.e. HermiT's own build no longer reproduces its control file.
// We therefore pin OUR numbering and assert the structure HermiT's oracle
// actually cares about: 9 body atoms, 2 head atoms, one `=(..)` and one `!=(..)`.
test('ClausificationTest.testHasKeys — structure matches; numbering is ours', () => {
  const clause = [...load([
    E.hasKey(c('C_test'), [p('r_test'), dp('dp_test')])
  ]).dlOntology.dlClauses][0];

  const body = [];
  const head = [];
  for (let i = 0; i < clause.getBodyLength(); i++) body.push(String(clause.getBodyAtom(i)));
  for (let i = 0; i < clause.getHeadLength(); i++) head.push(String(clause.getHeadAtom(i)));

  assert.equal(body.length, 9);
  assert.equal(head.length, 2);
  // The key rule concludes "the two individuals are equal" and, from that,
  // "their data-property fillers must differ" (a key has at most one value).
  assert.deepEqual(head.slice().sort(), ['!=(Y2, Y3)', '=(X1, X2)']);
  assert.deepEqual(body.slice().sort(), [
    'http://ex.org#C_test(X1)',
    'http://ex.org#C_test(X2)',
    'http://ex.org#dp_test(X1, Y2)',
    'http://ex.org#dp_test(X2, Y3)',
    'http://ex.org#r_test(X1, Y1)',
    'http://ex.org#r_test(X2, Y1)',
    'internal:nam#Named(X1)',
    'internal:nam#Named(X2)',
    'internal:nam#Named(Y1)'
  ].sort());
});

// ===========================================================================
// org.semanticweb.HermiT.reasoner.EntailmentTest
// ===========================================================================

test('EntailmentTest.testIntegerEntailment — "010" and "0010" are the same integer', () => {
  assertEntails(
    [declaration(dp('dp')), declaration(ind('a')),
      E.dataPropertyAssertion(dp('dp'), ind('a'), E.literal('010', xsd('integer')))],
    E.dataPropertyAssertion(dp('dp'), ind('a'), E.literal('0010', xsd('integer'))),
    true);
});

// REGRESSION for defect (2) above. The premise forces every `dp` filler to be
// both an `xsd:string` and an `xsd:integer`, which is impossible, so `a` can
// have at most one `dp` value — making `dp` a key for `owl:Thing`. Reaching the
// clash requires two facet-free `DatatypeRestriction`s from disjoint groups to
// conflict on one concrete node.
test('EntailmentTest.testHasKey — HasKey(⊤ () (dp)) is entailed', () => {
  assertEntails(
    [declaration(dp('dp')), E.classAssertion(E.owlThing(), ind('a')),
      E.subclassOf(E.owlThing(), E.objectIntersectionOf([
        E.dataAllValuesFrom(dp('dp'), xsd('string')),
        E.dataAllValuesFrom(dp('dp'), xsd('integer'))
      ]))],
    E.hasKey(E.owlThing(), [dp('dp')]),
    true);
});

test('EntailmentTest.testBlankNodes1 — a blank-node filler is rolled up', () => {
  assertEntails(
    [declaration(p('p')), E.classAssertion(E.owlThing(), ind('a')),
      E.objectPropertyAssertion(p('p'), ind('a'), anon('anon'))],
    E.classAssertion(E.objectSomeValuesFrom(p('p'), E.owlThing()), ind('a')),
    true);
});

// The CONCLUSION's blank nodes must form a forest of trees each with a single
// named root; a cycle has no such root and must be rejected, not answered.
test('EntailmentTest.testInvalidBlankNodes — a cyclic query is rejected', () => {
  assertEntails(
    [E.classAssertion(E.objectSomeValuesFrom(p('p'),
        E.objectSomeValuesFrom(p('s'), E.owlThing())), ind('a')),
      sub(p('s'), E.objectInverseOf(p('r'))),
      inv(p('r-'), p('r'))],
    [E.objectPropertyAssertion(p('p'), ind('a'), anon('anon1')),
      E.objectPropertyAssertion(p('s'), anon('anon1'), anon('anon2')),
      E.objectPropertyAssertion(p('r'), anon('anon2'), anon('anon1'))],
    'THROW');
});

// DIVERGENCE (HermiT bug; our behaviour is the spec-correct one).
//
// The query forest has ONE anonymous individual `_:anon1` with TWO named
// neighbours: `a` via `p`, and `b` via `r`. OWL 2 Structural Specification
// §11.2 requires that "for each anonymous individual _:x that is a root in F,
// the set Ax contains at most one assertion of the form
// ObjectPropertyAssertion(OPE _:x a) or ObjectPropertyAssertion(OPE a _:x)".
// Two named neighbours violate that, so there is no suitable root and the query
// must be REJECTED — which is what we do.
//
// HermiT's oracle expects `true` only because
// `EntailmentChecker.visit(OWLObjectPropertyAssertionAxiom)`
// (EntailmentChecker.java:744-751) does
//   specialEdges = new HashMap<>(); … specialOPEdges.put(unnamed, specialEdges);
// i.e. it REPLACES the inner map for each new edge, discarding the earlier
// named neighbour. `specialOPEdges[_:anon1]` therefore ends up with size 1 and
// `findSuitableRoots` succeeds. Our port deliberately MERGES instead — see the
// DEVIATION comment at `src/reasoner/EntailmentChecker.js:730-732`.
test('EntailmentTest.testValidBlankNodesWithNominals — DIVERGES: we reject the two-root query', () => {
  assertEntails(
    [E.classAssertion(E.objectSomeValuesFrom(p('p'),
        E.objectSomeValuesFrom(p('s'), E.objectOneOf([ind('b')]))), ind('a')),
      sub(p('s'), p('r'))],
    [E.objectPropertyAssertion(p('p'), ind('a'), anon('anon1')),
      E.objectPropertyAssertion(p('r'), anon('anon1'), ind('b'))],
    'THROW');
});

test('EntailmentTest.testValidBlankNodesInPremise — premise blank nodes need no root', () => {
  assertEntails(
    [E.objectPropertyAssertion(p('r'), ind('a'), anon('anon1')),
      E.objectPropertyAssertion(p('s'), anon('anon1'), anon('anon2'))],
    E.objectPropertyAssertion(p('r'), anon('anon1'), anon('anon2')),
    true);
});

test('EntailmentTest.testValidBlankNodes — a purely anonymous query is entailed', () => {
  assertEntails(
    [E.objectPropertyAssertion(p('r'), ind('a'), ind('b')),
      E.objectPropertyAssertion(p('s'), ind('b'), ind('c'))],
    E.objectPropertyAssertion(p('r'), anon('anon1'), anon('anon2')),
    true);
});

// No `dp` assertion exists in the premise at all, so nothing entails one.
test('EntailmentTest.testBlankWithDTs — an unrelated premise entails nothing', () => {
  assertEntails(
    [E.objectPropertyAssertion(p('r'), ind('a'), ind('b')),
      E.objectPropertyAssertion(p('s'), ind('b'), ind('c'))],
    E.dataPropertyAssertion(dp('dp'), anon('anon1'), E.literal('test')),
    false);
});

test('EntailmentTest.testBlankWithDTs2 — untyped literals match each other', () => {
  assertEntails(
    [E.dataPropertyAssertion(dp('dp'), ind('a'), E.literal('test')),
      E.objectPropertyAssertion(p('s'), ind('b'), ind('c'))],
    E.dataPropertyAssertion(dp('dp'), anon('anon1'), E.literal('test')),
    true);
});

// REGRESSION for defect (1) above. This is `testBlankWithDTs2` with the
// conclusion's literal explicitly typed `xsd:string`. `testBlankWithDTs2`
// passed even while the default was wrong, because BOTH sides were untyped and
// so folded identically; only this oracle exposes the mismatch.
test('EntailmentTest.testBlankWithDTs3 — an untyped literal IS an xsd:string', () => {
  // Pin the OWL 2 §2.3 default directly, so a regression is reported at its
  // source rather than only as an entailment failure.
  assert.equal(E.literal('test').getDatatypeIRI(), E.IRI_XSD_STRING);
  assert.equal(E.exprEquals(E.literal('test'), E.literal('test', xsd('string'))), true);
  // A language tag still means rdf:PlainLiteral.
  assert.equal(E.literal('test', null, 'en').getDatatypeIRI(), E.IRI_RDF_PLAIN_LITERAL);

  assertEntails(
    [E.dataPropertyAssertion(dp('dp'), ind('a'), E.literal('test')),
      E.objectPropertyAssertion(p('s'), ind('b'), ind('c'))],
    E.dataPropertyAssertion(dp('dp'), anon('anon1'), E.literal('test', xsd('string'))),
    true);
});
