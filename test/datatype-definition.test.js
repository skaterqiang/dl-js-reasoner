'use strict';

// ---------------------------------------------------------------------------
// test/datatype-definition.test.js — DatatypeDefinition semantics.
//
// `OWLNormalization` turns `DatatypeDefinition(dt, dr)` into a two-way
// data-range equivalence (dt ⊑ dr AND dr ⊑ dt) and records `dt` in
// `definedDatatypesIRIs`.
//
// Entailment is decided by whether the SYMMETRIC DIFFERENCE of the two ranges
// is empty: EntailmentChecker builds `(¬dr ⊓ dt) ⊔ (¬dt ⊓ dr)`, asserts
// `∃freshDataProperty.(...)` on a fresh individual, and returns `!satisfiable`.
//
// A custom datatype IS provably equal to the range it is defined as. The
// symmetric-difference branch `(¬dr ⊓ dt)` forces `dt(v)` and, via the
// defining clause `dt ⊑ dr`, `dr(v)` on the same concrete node; the other
// branch forces `¬dr(v)`. `checkConstraintsSatisfiable` step 1 clashes on a
// data range together with its own negation, so the symmetric difference is
// unsatisfiable and the definition is entailed. That step needs no knowledge
// of the value space, which is why it works for an opaque GROUP.OTHER
// datatype too.
//
// Still incomplete: equivalence between two DIFFERENT ranges that happen to
// denote the same value space (e.g. `xsd:string` vs `xsd:string[minLength 0]`)
// is not recognised, because `checkFacetValue`/`numericSubsumes` cannot
// establish range equivalence. See the facet test below.
// ---------------------------------------------------------------------------

const test = require('node:test');
const assert = require('node:assert/strict');

const { createReasoner } = require('../src/reasoner/Reasoner');
const {
  E, EX, dp, ind, declaration, datatypeDefinition, dataPropertyRange, ontology
} = require('./helpers');

const XS = E.datatype(E.IRI_XSD_STRING);
const XI = E.datatype(E.XSD_NS + 'integer');

test('a DatatypeDefinition makes hasDatatypes true and records definedDatatypesIRIs', () => {
  const MyDT = E.datatype(EX + 'MyDT');
  const r = createReasoner(ontology([declaration(MyDT), datatypeDefinition(MyDT, XS)]));
  try {
    assert.equal(r.dlOntology.hasDatatypes, true);
    assert.deepEqual([...r.dlOntology.definedDatatypesIRIs], [EX + 'MyDT']);
    assert.equal(r.isConsistent(), true);
  } finally { r.dispose(); }
});

test('the hasDatatypes guard makes a trivial definition NOT entailed', () => {
  // HermiT's EntailmentChecker.visit(OWLDatatypeDefinitionAxiom) short-circuits
  // to `false` when `!reasoner.m_dlOntology.hasDatatypes()` — with no datatype
  // in the signature there is nothing to reason about. Our port mirrors that
  // guard exactly, so a Declaration-only ontology answers false even for
  // `DatatypeDefinition(xsd:string, xsd:string)`.
  const r = createReasoner(ontology([declaration(XS), declaration(XI)]));
  try {
    assert.equal(r.dlOntology.hasDatatypes, false);
    assert.equal(r.isEntailed(datatypeDefinition(XS, XS)), false);
  } finally { r.dispose(); }
});

test('identical known datatypes are entailed equal, disjoint ones are not', () => {
  const r = createReasoner(ontology([declaration(XS), datatypeDefinition(XS, XS)]));
  try {
    assert.equal(r.dlOntology.hasDatatypes, true);
    assert.equal(r.isEntailed(datatypeDefinition(XS, XS)), true);
    assert.equal(r.isEntailed(datatypeDefinition(XS, XI)), false);
  } finally { r.dispose(); }
});

test('a custom datatype is entailed equal to the range it is defined as', () => {
  const MyDT = E.datatype(EX + 'MyDT2');
  const r = createReasoner(ontology([declaration(MyDT), datatypeDefinition(MyDT, XS)]));
  try {
    // Equal to itself: the symmetric difference is empty by construction.
    assert.equal(r.isEntailed(datatypeDefinition(MyDT, MyDT)), true);
    // Equal to xsd:string: that IS its definition, so the symmetric difference
    // is empty and the entailment holds.
    assert.equal(r.isEntailed(datatypeDefinition(MyDT, XS)), true);
    // NOT equal to xsd:integer — the two value spaces are disjoint.
    assert.equal(r.isEntailed(datatypeDefinition(MyDT, XI)), false);
  } finally { r.dispose(); }
});

test('facet equivalence is not recognised (sound incompleteness)', () => {
  const r = createReasoner(ontology([declaration(XS), datatypeDefinition(XS, XS)]));
  try {
    const relaxed = E.datatypeRestriction(XS, [
      { facet: E.XSD_NS + 'minLength', value: E.literal('0', XI) }
    ]);
    // xsd:string ≡ xsd:string[minLength 0] is true in principle, but
    // `checkFacetValue`/`numericSubsumes` do not establish range equivalence.
    assert.equal(r.isEntailed(datatypeDefinition(XS, relaxed)), false);
  } finally { r.dispose(); }
});

test('a defined datatype really constrains the literals of a data property range', () => {
  const MyDT = E.datatype(EX + 'MyDT3');
  const hasCode = dp('hasCode');
  const i = ind('i3');

  const build = (lit) => createReasoner(ontology([
    declaration(MyDT), declaration(hasCode), declaration(i),
    datatypeDefinition(MyDT, XS),
    dataPropertyRange(hasCode, MyDT),
    E.dataPropertyAssertion(hasCode, i, lit)
  ]));

  const rStr = build(E.literal('abc', XS));
  try { assert.equal(rStr.isConsistent(), true); } finally { rStr.dispose(); }

  const rInt = build(E.literal('42', XI));
  try { assert.equal(rInt.isConsistent(), false); } finally { rInt.dispose(); }
});

// REGRESSION for the ExtensionTable dependency-set union bug. Enumerated and
// union data ranges make DatatypeManager derive a ground disjunction; choosing
// the second disjunct re-asserted an already-present data-range tuple, and the
// union poisoned the stored dependency set. The crash surfaced as
//   TypeError: Cannot read properties of undefined (reading 'dlPredicate')
// from GroundDisjunction.getDLPredicate. See test/extension-table.test.js.
test('REGRESSION: enumerated and union data ranges do not wedge the disjunction loop', () => {
  const MyDT = E.datatype(EX + 'MyDT4');

  const oneOf = E.dataOneOf([E.literal('red', XS), E.literal('green', XS)]);
  const r1 = createReasoner(ontology([declaration(MyDT), datatypeDefinition(MyDT, oneOf)]));
  try {
    assert.doesNotThrow(() => r1.isEntailed(datatypeDefinition(MyDT, oneOf)));
    assert.equal(r1.isEntailed(datatypeDefinition(MyDT, oneOf)), true);
  } finally { r1.dispose(); }

  const union = E.dataUnionOf([XS, XI]);
  const r2 = createReasoner(ontology([declaration(MyDT), datatypeDefinition(MyDT, union)]));
  try {
    assert.doesNotThrow(() => r2.isEntailed(datatypeDefinition(MyDT, union)));
    assert.equal(r2.isEntailed(datatypeDefinition(MyDT, union)), true);
  } finally { r2.dispose(); }
});

test('a complement range is entailed for a custom datatype defined as one', () => {
  const MyDT = E.datatype(EX + 'MyDT5');
  const comp = E.dataComplementOf(XS);
  const r = createReasoner(ontology([declaration(MyDT), datatypeDefinition(MyDT, comp)]));
  try {
    // MyDT was DEFINED as ¬xsd:string, so it is entailed equal to it. The
    // symmetric difference clashes on a data range against its own negation,
    // which needs no value-space knowledge — so it works for an opaque
    // GROUP.OTHER datatype as well as for a known xsd one.
    assert.equal(r.isEntailed(datatypeDefinition(MyDT, comp)), true);
    // Self-equality holds: the symmetric difference is empty by construction.
    assert.equal(r.isEntailed(datatypeDefinition(MyDT, MyDT)), true);
    // But NOT equal to xsd:string, whose value space is disjoint from ¬string.
    assert.equal(r.isEntailed(datatypeDefinition(MyDT, XS)), false);
  } finally { r.dispose(); }
});

// REGRESSION for the MIRROR-IMAGE soundness bug. `constantSatisfies` used to
// over-approximate an undecidable predicate to `true`, which is safe for a
// POSITIVE membership test but UNSAFE for a NEGATIVE one: `checkConstraints
// Satisfiable` steps 3/4 and `DatatypeManager._finiteSpace` reject a candidate
// when it "satisfies" a negated range, so a permissive `true` rejected EVERY
// candidate and reported a clash the ontology did not imply.
//
// Membership is now three-valued (`constantMembership` → true/false/null), and
// the negative tests use `constantDefinitelySatisfies`, where `null` keeps the
// candidate. See test/datatype-constraints.test.js for the unit-level pins.
test('REGRESSION: an undecidable negated range does not make an ontology inconsistent', () => {
  const MyDT = E.datatype(EX + 'OddDT');
  const p = dp('pOdd');
  const i = ind('iOdd');
  // A facet this port does not implement, on a datatype that DOES match the
  // literal — so `checkFacetValue` returns `null` and membership is undecidable.
  const unknownFacet = E.XSD_NS + 'unknownFacet';
  const oneOf = E.dataOneOf([E.literal('red', E.IRI_XSD_STRING), E.literal('green', E.IRI_XSD_STRING)]);

  const build = () => createReasoner(ontology([
    declaration(MyDT), declaration(p), declaration(i),
    datatypeDefinition(MyDT, E.datatypeRestriction(XS, [
      { facet: unknownFacet, value: E.literal('1', E.XSD_NS + 'integer') }
    ])),
    dataPropertyRange(p, oneOf),
    dataPropertyRange(p, E.dataComplementOf(MyDT)),
    E.dataPropertyAssertion(p, i, E.literal('red', E.IRI_XSD_STRING))
  ]));

  const r = build();
  try {
    // Nothing implies a contradiction: whether "red" lies in MyDT is
    // undecidable, so the ontology must be reported CONSISTENT. Before the fix
    // this returned false — a spurious clash.
    assert.equal(r.isConsistent(), true);
  } finally { r.dispose(); }

  // Guard against a vacuous pass: the SAME shape with a DECIDABLE negated range
  // really is inconsistent, so the assertion above is discriminating.
  const StrDT = E.datatype(EX + 'StrDTGuard');
  const r2 = createReasoner(ontology([
    declaration(StrDT), declaration(p), declaration(i),
    datatypeDefinition(StrDT, XS),
    dataPropertyRange(p, oneOf),
    dataPropertyRange(p, E.dataComplementOf(StrDT)),
    E.dataPropertyAssertion(p, i, E.literal('red', E.IRI_XSD_STRING))
  ]));
  try {
    // "red" IS an xsd:string, and MyDT := xsd:string, so ¬MyDT excludes it.
    assert.equal(r2.isConsistent(), false);
  } finally { r2.dispose(); }
});
