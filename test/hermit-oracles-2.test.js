'use strict';

// ---------------------------------------------------------------------------
// test/hermit-oracles-2.test.js — differential testing against HermiT's JUnit
// corpus, second instalment.
//
// `test/hermit-oracles.test.js` ports the STRUCTURAL oracles
// (`SimpleRolesTest`, `RIATest`, `ClausificationTest`, `EntailmentTest`). This
// file ports the REASONER oracles:
//
//   * org.semanticweb.HermiT.reasoner.ComplexConceptTest  — 8 oracles
//   * org.semanticweb.HermiT.reasoner.OWLReasonerTest     — 8 oracles
//
// Neither class appears in HermiT's `known-test-failures.txt`, so every
// assertion below is a clean oracle: HermiT's own build is expected to pass it.
//
// ---------------------------------------------------------------------------
// Helper semantics, recovered verbatim from HermiT's test base classes.
//
// `AbstractOntologyTest`:
//   ONTOLOGY_IRI = IRI.create("file:/c/test.owl")
//   NS           = ONTOLOGY_IRI + "#"  ===  "file:/c/test.owl#"
//   SL(lex)      = getOWLLiteral(lex)                     // untyped
//   PL(lex, lang)= getOWLLiteral(lex, lang)               // language-tagged
//   TL(lex, dt)  = getOWLLiteral(lex, getOWLDatatype(IRI(expandAbbreviatedIRI(dt))))
//   NS_NI(s)     = getOWLNamedIndividual(IRI(NS + s))
//   NS_DP(s)     = getOWLDataProperty(IRI(NS + s))
//
// `AbstractReasonerTest`:
//   getConfiguration()          → new Configuration() with
//                                 throwInconsistentOntologyException = FALSE
//   loadReasonerWithAxioms(s)   → loadOntologyWithAxioms(s); createReasoner()
//   assertABoxSatisfiable(b)    → assertEquals(b, m_reasoner.isConsistent())
//   assertSubsumedBy(sub,sup,b) → assertEquals(b, isEntailed(SubClassOf(sub,sup)))
//   assertSatisfiable(desc, b)  → assertEquals(b, m_reasoner.isSatisfiable(desc))
//   assertInstanceOf(desc,i,b)  → assertEquals(b, m_reasoner.hasType(i, desc, FALSE))
//
// `AbstractHermiTTest.assertContainsAll(actual, control...)` is EXACT SET
// EQUALITY, not a subset check: it asserts `control.length == actual.size()`
// first, then that every control element is present.
//
// ---------------------------------------------------------------------------
// DEFECT 3 (found and fixed by porting `ComplexConceptTest.testConceptWithDatatypes`
// and `OWLReasonerTest.testGetDataPropertyValues`).
//
// `rdf:PlainLiteral` carries its language tag INSIDE the lexical form, as
// `"abc@en-gb"`. OWL API parses that out at construction time, so HermiT never
// sees the `@`. Three independent authorities agree on the split:
//
//   1. `OWLDataFactoryInternalsImplNoCache.getOWLLiteral(String, OWLDatatype)`:
//        if (datatype.isRDFPlainLiteral() || datatype.equals(LANGSTRING)) {
//            int sep = lexicalValue.lastIndexOf('@');
//            if (sep != -1) return getBasicLiteral(lex, lang, LANGSTRING);
//            else           return getBasicLiteral(lexicalValue, XSDSTRING);
//        }
//
//   2. `OWLLiteral.getLiteral()`'s contract: *"If the literal is of the form
//      `"abc@"^^rdf:PlainLiteral` then the return value will be `"abc"`
//      (without the language tag included)."*
//
//   3. HermiT's OWN value space — `RDFPlainLiteralDatatypeHandler.parseLiteral`
//      splits at `lastIndexOf('@')` and maps an EMPTY tag to a bare `String`,
//      i.e. the `xsd:string` data value.
//
// `E.literal` skipped the split, so `"abc@"^^rdf:PlainLiteral` kept
// `lexicalValue === 'abc@'` with `isRDFPlainLiteral() === true`.
// `OWLClausification.convertLiteral` then appended a SECOND separator and
// emitted `Constant("abc@@", rdf:PlainLiteral)` — a constant equal to neither
// `"abc"` nor `PL("abc","")`. Both oracles above assert that the two spellings
// denote ONE value, and both failed.
//
// NOTE ON OWL API VERSIONS: HermiT builds against `owlapi-distribution:4.2.8`,
// where `OWLLiteralImplPlain.isRDFPlainLiteral()` returns TRUE and
// `getDatatype()` returns `rdf:PlainLiteral`. OWL API v5 returns FALSE /
// `rdf:langString`. This port follows the v4 convention — which is also
// HermiT's internal `Constant(lex + "@" + lang, rdf:PlainLiteral)` convention —
// and that is deliberate. Do NOT "modernise" it toward v5.
// ---------------------------------------------------------------------------

const test = require('node:test');
const assert = require('node:assert/strict');

const E = require('../src/owl/OWLExpressions');
const C = require('../src/structural/OWLClausification');
const { createReasoner } = require('../src/reasoner/Reasoner');
const { ontology } = require('./helpers');

const AT = E.AxiomType;

/** HermiT's `AbstractOntologyTest.ONTOLOGY_IRI` / `.NS`. */
const ONTOLOGY_IRI = 'file:/c/test.owl';
const NS = ONTOLOGY_IRI + '#';
const XSD = 'http://www.w3.org/2001/XMLSchema#';
const RDF_PL = E.IRI_RDF_PLAIN_LITERAL;

const c = (n) => E.owlClass(NS + n);
const p = (n) => E.objectProperty(NS + n);
const dp = (n) => E.dataProperty(NS + n);
const ind = (n) => E.namedIndividual(NS + n);
const declaration = (entity) => ({ axiomType: AT.DECLARATION, entity });

/** HermiT's `SL` / `PL` / `TL`. */
const SL = (lex) => E.literal(lex);
const PL = (lex, lang) => E.literal(lex, null, lang);
const TL = (lex, dtLocalName) => E.literal(lex, XSD + dtLocalName);

// Property-characteristic axioms have no factory in OWLExpressions, so they are
// hand-built in the exact shape `OWLNormalization` reads (see
// `src/structural/OWLNormalization.js:760-790`).
const func = (x) => ({ axiomType: AT.FUNCTIONAL_OBJECT_PROPERTY, property: x });
const invFunc = (x) => ({ axiomType: AT.INVERSE_FUNCTIONAL_OBJECT_PROPERTY, property: x });
const subProp = (s, u) => ({ axiomType: AT.SUB_OBJECT_PROPERTY_OF, subProperty: s, superProperty: u });

// ---- reasoner construction -------------------------------------------------

/**
 * HermiT's `loadReasonerWithAxioms` / `createOWLReasoner`, reduced to this
 * port's single `Reasoner` class.
 *
 * `throwInconsistentOntologyException` is FALSE because
 * `AbstractReasonerTest.getConfiguration()` sets it that way for the whole
 * corpus — this port's `Configuration` defaults it to TRUE, so three oracles
 * that assert an INCONSISTENT ABox would otherwise throw instead of answering.
 */
function reasonerFor(axioms, extraConfig) {
  return createReasoner(
    ontology(axioms, ONTOLOGY_IRI),
    Object.assign({ throwInconsistentOntologyException: false }, extraConfig || {}));
}

/** Run `body(r)` and always dispose — a leaked tableau pins its clause index. */
function withReasoner(axioms, extraConfig, body) {
  const r = reasonerFor(axioms, extraConfig);
  try {
    return body(r);
  } finally {
    r.dispose();
  }
}

// ---- HermiT's assertions, ported one-for-one -------------------------------

/** `AbstractReasonerTest.assertABoxSatisfiable`. */
function assertABoxSatisfiable(r, expected) {
  assert.equal(r.isConsistent(), expected);
}

/** `AbstractReasonerTest.assertSubsumedBy(OWLClassExpression, …, boolean)`. */
function assertSubsumedBy(r, sub, sup, expected) {
  assert.equal(r.isEntailed(E.subclassOf(sub, sup)), expected);
}

/** `AbstractReasonerTest.assertSatisfiable(OWLClassExpression, boolean)`. */
function assertSatisfiable(r, desc, expected) {
  assert.equal(r.isSatisfiable(desc), expected);
}

/**
 * `AbstractReasonerTest.assertInstanceOf` — note the hard-coded `direct=false`.
 * This is `hasType`, NOT intersection-satisfiability.
 */
function assertInstanceOf(r, desc, individual, expected) {
  assert.equal(r.hasType(individual, desc, false), expected);
}

/** A canonical, order-insensitive fingerprint of a Node / NodeSet / iterable. */
function keysOf(nodeOrNodeSet) {
  const items = typeof nodeOrNodeSet.getFlattened === 'function'
    ? nodeOrNodeSet.getFlattened()
    : nodeOrNodeSet.getEntities
      ? nodeOrNodeSet.getEntities()
      : nodeOrNodeSet;
  return [...items].map((x) => E.structuralKey(x)).sort();
}

/**
 * `AbstractHermiTTest.assertContainsAll` — EXACT set equality. The Java version
 * compares sizes then membership; sorting canonical keys is equivalent (no
 * control list below contains duplicates) and produces a far better failure
 * message.
 */
function assertContainsAll(actual, ...control) {
  assert.deepEqual(keysOf(actual), control.map((x) => E.structuralKey(x)).sort());
}

// ===========================================================================
// REGRESSION — DEFECT 3: the `rdf:PlainLiteral` `@`-split.
//
// Pinned at the source (the literal factory) as well as at the clausifier, so a
// regression is reported where it happens rather than only as a mysterious
// oracle failure two layers up.
// ===========================================================================

test('DEFECT 3 — "abc@"^^rdf:PlainLiteral parses to xsd:string "abc"', () => {
  const lit = E.literal('abc@', RDF_PL);
  assert.equal(lit.getLiteral(), 'abc');
  assert.equal(lit.getLang(), null);
  assert.equal(lit.getDatatypeIRI(), E.IRI_XSD_STRING);
  // An EMPTY language tag is the `xsd:string` data value, so this is NOT a
  // plain literal any more — matching `RDFPlainLiteralDatatypeHandler`, which
  // maps `languageTag.length() == 0` to a bare `String`.
  assert.equal(lit.isRDFPlainLiteral(), false);
  assert.equal(E.exprEquals(lit, SL('abc')), true);
  assert.equal(E.exprEquals(lit, PL('abc', '')), true);
  assert.equal(lit.toString(), '"abc"^^<http://www.w3.org/2001/XMLSchema#string>');
});

test('DEFECT 3 — "abc@en-gb"^^rdf:PlainLiteral parses to "abc"@en-gb', () => {
  const lit = E.literal('abc@en-gb', RDF_PL);
  assert.equal(lit.getLiteral(), 'abc');
  assert.equal(lit.getLang(), 'en-gb');
  assert.equal(lit.getDatatypeIRI(), RDF_PL);
  assert.equal(lit.isRDFPlainLiteral(), true);
  assert.equal(E.exprEquals(lit, PL('abc', 'en-gb')), true);
  assert.equal(lit.toString(), '"abc"@en-gb');
});

test('DEFECT 3 — the split is at the LAST "@" and a bare rdf:PlainLiteral is xsd:string', () => {
  // `lastIndexOf`, per both OWL API and HermiT's handler: `"a@b@c"` is the
  // string `a@b` tagged `c`.
  const abc = E.literal('a@b@c', RDF_PL);
  assert.equal(abc.getLiteral(), 'a@b');
  assert.equal(abc.getLang(), 'c');

  // An empty lexical form before the tag is still a tagged literal.
  const empty = E.literal('@en', RDF_PL);
  assert.equal(empty.getLiteral(), '');
  assert.equal(empty.getLang(), 'en');

  // NO separator at all ⇒ OWL API falls back to `xsd:string`.
  const bare = E.literal('abc', RDF_PL);
  assert.equal(bare.getDatatypeIRI(), E.IRI_XSD_STRING);
  assert.equal(E.exprEquals(bare, SL('abc')), true);

  // Other datatypes are untouched — `@` is an ordinary character there.
  const at = E.literal('a@b', XSD + 'string');
  assert.equal(at.getLiteral(), 'a@b');
  assert.equal(at.getDatatypeIRI(), XSD + 'string');
});

test('DEFECT 3 — the clausifier emits ONE constant for both spellings', () => {
  const conv = new C.DataRangeConverter();
  const fromPlainLiteral = conv.convertLiteral(E.literal('abc@', RDF_PL));
  const fromUntyped = conv.convertLiteral(SL('abc'));
  const fromTagged = conv.convertLiteral(E.literal('abc@en-gb', RDF_PL));
  const fromLang = conv.convertLiteral(PL('abc', 'en-gb'));

  // Before the fix this was `Constant("abc@@", rdf:PlainLiteral)`.
  assert.equal(fromPlainLiteral.lexicalValue, 'abc');
  assert.equal(fromPlainLiteral.datatypeIRI, XSD + 'string');
  assert.deepEqual(
    { lex: fromPlainLiteral.lexicalValue, dt: fromPlainLiteral.datatypeIRI },
    { lex: fromUntyped.lexicalValue, dt: fromUntyped.datatypeIRI });

  // `convertLiteral` re-appends the separator, so a tagged literal round-trips
  // to HermiT's internal `Constant(lex + "@" + lang, rdf:PlainLiteral)` form.
  assert.equal(fromTagged.lexicalValue, 'abc@en-gb');
  assert.equal(fromTagged.datatypeIRI, RDF_PL);
  assert.deepEqual(
    { lex: fromTagged.lexicalValue, dt: fromTagged.datatypeIRI },
    { lex: fromLang.lexicalValue, dt: fromLang.datatypeIRI });
});

// ===========================================================================
// org.semanticweb.HermiT.reasoner.ComplexConceptTest
// ===========================================================================

test('ComplexConceptTest.testConceptWithDatatypes — functional f forces the dp value', () => {
  withReasoner([
    declaration(ind('a')), declaration(c('A')), declaration(c('B')), declaration(c('C')),
    declaration(p('f')), declaration(dp('dp')),
    E.subclassOf(c('A'), E.objectSomeValuesFrom(p('f'), c('B'))),
    E.subclassOf(c('A'), E.objectSomeValuesFrom(p('f'), c('C'))),
    E.subclassOf(c('B'), E.dataSomeValuesFrom(dp('dp'),
      E.dataOneOf([E.literal('abc', XSD + 'string'), E.literal('def', XSD + 'string')]))),
    // `"abc@"^^rdf:PlainLiteral` — the DEFECT-3 spelling. It must denote the
    // SAME value as `PL("abc","")` in the query below.
    E.subclassOf(c('C'), E.dataHasValue(dp('dp'), E.literal('abc@', RDF_PL))),
    func(p('f')),
    E.classAssertion(c('A'), ind('a'))
  ], null, (r) => {
    const desc = E.objectSomeValuesFrom(p('f'),
      E.dataSomeValuesFrom(dp('dp'), E.dataOneOf([PL('abc', '')])));
    assertInstanceOf(r, desc, ind('a'), true);
  });
});

test('ComplexConceptTest.testConceptWithDatatypes2 — ∀dp.¬rdfs:Literal excludes ∃dp.⊤', () => {
  withReasoner([
    declaration(ind('a')), declaration(c('A')), declaration(dp('dp')),
    E.subclassOf(c('A'), E.dataAllValuesFrom(dp('dp'), E.dataComplementOf(E.topDatatype()))),
    E.classAssertion(c('A'), ind('a'))
  ], null, (r) => {
    assertInstanceOf(r, E.dataSomeValuesFrom(dp('dp'), E.topDatatype()), ind('a'), false);
  });
});

test('ComplexConceptTest.testConceptWithNominals — two inverse-functional chains collapse', () => {
  withReasoner([
    declaration(ind('a')), declaration(ind('b')), declaration(ind('o')),
    declaration(c('A')), declaration(c('B')),
    declaration(p('f1')), declaration(p('f2')), declaration(dp('dp')),
    E.classAssertion(
      E.objectSomeValuesFrom(p('f1'), E.objectSomeValuesFrom(p('f2'), E.objectOneOf([ind('o')]))),
      ind('a')),
    E.classAssertion(
      E.objectSomeValuesFrom(p('f1'), E.objectSomeValuesFrom(p('f2'), E.objectOneOf([ind('o')]))),
      ind('b')),
    invFunc(p('f1')),
    invFunc(p('f2')),
    E.classAssertion(E.objectAllValuesFrom(p('f1'), c('A')), ind('a')),
    E.classAssertion(E.objectAllValuesFrom(p('f1'), c('B')), ind('b'))
  ], null, (r) => {
    const desc = E.objectAllValuesFrom(E.objectInverseOf(p('f2')),
      E.objectIntersectionOf([c('A'), c('B')]));
    assertInstanceOf(r, desc, ind('o'), true);
  });
});

test('ComplexConceptTest.testConceptWithNominals2 — a and b are the same individual', () => {
  withReasoner([
    declaration(ind('a')), declaration(ind('b')), declaration(ind('o')),
    declaration(c('A')), declaration(c('B')),
    declaration(p('f1')), declaration(p('f2')),
    E.classAssertion(
      E.objectSomeValuesFrom(p('f1'), E.objectSomeValuesFrom(p('f2'), E.objectOneOf([ind('o')]))),
      ind('a')),
    E.classAssertion(
      E.objectSomeValuesFrom(p('f1'), E.objectSomeValuesFrom(p('f2'), E.objectOneOf([ind('o')]))),
      ind('b')),
    invFunc(p('f1')),
    invFunc(p('f2')),
    E.classAssertion(E.objectAllValuesFrom(p('f1'), c('A')), ind('a')),
    E.classAssertion(E.objectAllValuesFrom(p('f1'), c('B')), ind('b'))
  ], null, (r) => {
    const desc = E.objectIntersectionOf([E.objectOneOf([ind('a')]), E.objectOneOf([ind('b')])]);
    assertInstanceOf(r, desc, ind('a'), true);
    assertInstanceOf(r, desc, ind('b'), true);
  });
});

test('ComplexConceptTest.testConceptWithNominals3 — disjoint A/B over a merged nominal', () => {
  withReasoner([
    declaration(ind('a')), declaration(ind('b')), declaration(ind('o')),
    declaration(c('A')), declaration(c('B')),
    declaration(p('f1')), declaration(p('f2')),
    E.disjointClasses([c('A'), c('B')]),
    E.classAssertion(
      E.objectSomeValuesFrom(p('f1'), E.objectSomeValuesFrom(p('f2'), E.objectOneOf([ind('o')]))),
      ind('a')),
    E.classAssertion(
      E.objectSomeValuesFrom(p('f1'), E.objectSomeValuesFrom(p('f2'), E.objectOneOf([ind('o')]))),
      ind('b')),
    invFunc(p('f1')),
    invFunc(p('f2')),
    E.classAssertion(E.objectAllValuesFrom(p('f1'), c('A')), ind('a')),
    E.classAssertion(E.objectAllValuesFrom(p('f1'), c('B')), ind('b'))
  ], null, (r) => {
    assertABoxSatisfiable(r, false);
  });
});

test('ComplexConceptTest.testConceptWithNominals4 — disjoint nominals {a} / {b}', () => {
  withReasoner([
    declaration(ind('a')), declaration(ind('b')), declaration(ind('o')),
    declaration(p('f1')), declaration(p('f2')),
    E.disjointClasses([E.objectOneOf([ind('a')]), E.objectOneOf([ind('b')])]),
    E.classAssertion(
      E.objectSomeValuesFrom(p('f1'), E.objectSomeValuesFrom(p('f2'), E.objectOneOf([ind('o')]))),
      ind('a')),
    E.classAssertion(
      E.objectSomeValuesFrom(p('f1'), E.objectSomeValuesFrom(p('f2'), E.objectOneOf([ind('o')]))),
      ind('b')),
    invFunc(p('f1')),
    invFunc(p('f2'))
  ], null, (r) => {
    assertABoxSatisfiable(r, false);
  });
});

test('ComplexConceptTest.testConceptWithNominals5 — functional f pins the filler to b', () => {
  withReasoner([
    declaration(ind('a')), declaration(ind('b')), declaration(c('B')),
    declaration(p('f')), declaration(dp('dp')),
    E.classAssertion(E.objectSomeValuesFrom(p('f'), c('B')), ind('a')),
    E.objectPropertyAssertion(p('f'), ind('a'), ind('b')),
    func(p('f'))
  ], null, (r) => {
    assertSubsumedBy(r, E.objectOneOf([ind('b')]), c('B'), true);
  });
});

test('ComplexConceptTest.testJustifications — {Matt} ⊓ ¬Sibling is unsatisfiable', () => {
  // HermiT's comment: "test for Matthew's justifications that HermiT originally
  // didn't answer correctly".
  withReasoner([
    declaration(ind('Matt')), declaration(ind('Gemma')),
    declaration(c('Person')), declaration(c('Sibling')),
    declaration(p('hasSibling')), declaration(p('f2')), declaration(dp('dp')),
    E.classAssertion(c('Person'), ind('Matt')),
    E.classAssertion(c('Person'), ind('Gemma')),
    E.objectPropertyAssertion(p('hasSibling'), ind('Matt'), ind('Gemma')),
    E.subclassOf(
      E.objectIntersectionOf([c('Person'), E.objectSomeValuesFrom(p('hasSibling'), c('Person'))]),
      c('Sibling')),
    E.subclassOf(c('Sibling'),
      E.objectIntersectionOf([c('Person'), E.objectSomeValuesFrom(p('hasSibling'), c('Person'))]))
  ], null, (r) => {
    const desc = E.objectIntersectionOf([
      E.objectOneOf([ind('Matt')]),
      E.objectComplementOf(c('Sibling'))
    ]);
    assertSatisfiable(r, desc, false);
  });
});

// ===========================================================================
// org.semanticweb.HermiT.reasoner.OWLReasonerTest
// ===========================================================================

test('OWLReasonerTest.testgetInverseObjectPropertyExpressions — a 3-cycle of inverses', () => {
  withReasoner([
    subProp(p('r'), E.objectInverseOf(p('s'))),
    subProp(p('s'), E.objectInverseOf(p('t'))),
    subProp(p('t'), p('r'))
  ], null, (r) => {
    // `getInverseObjectProperties` returns a NODE, not a NodeSet.
    assert.deepEqual(keysOf(r.getInverseObjectProperties(p('r'))),
      [E.objectInverseOf(p('r')), p('s'), E.objectInverseOf(p('t'))]
        .map((x) => E.structuralKey(x)).sort());
    assert.deepEqual(keysOf(r.getInverseObjectProperties(E.objectInverseOf(p('r')))),
      [E.objectInverseOf(p('s')), p('r'), p('t')]
        .map((x) => E.structuralKey(x)).sort());
  });
});

test('OWLReasonerTest.testBottomObjectPropertySubs — ⊥ has no sub-properties', () => {
  withReasoner([subProp(p('r'), p('s'))], null, (r) => {
    assert.equal(r.getSubObjectProperties(E.bottomObjectProperty(), false).isEmpty(), true);
    assert.equal(r.getSubObjectProperties(E.bottomObjectProperty(), true).isEmpty(), true);
  });
});

test('OWLReasonerTest.testTopObjectPropertySupers — ⊤ has no super-properties', () => {
  withReasoner([subProp(p('r'), p('s'))], null, (r) => {
    assert.equal(r.getSuperObjectProperties(E.topObjectProperty(), false).isEmpty(), true);
    assert.equal(r.getSuperObjectProperties(E.topObjectProperty(), true).isEmpty(), true);
  });
});

test('OWLReasonerTest.testIncrementalAddition — add then retract B ⊑ C', () => {
  const a = c('A');
  const b = c('B');
  const cl = c('C');
  const thing = E.owlThing();

  const base = [E.subclassOf(a, b)];
  const onto = ontology(base, ONTOLOGY_IRI);
  const r = createReasoner(onto, { throwInconsistentOntologyException: false });
  try {
    // ---- phase 1: only A ⊑ B ------------------------------------------------
    let aSuper = r.getSuperClasses(a, false);
    let bSuper = r.getSuperClasses(b, false);
    let aDirect = r.getSuperClasses(a, true);
    let bDirect = r.getSuperClasses(b, true);

    assert.equal(aSuper.containsEntity(a), false);
    assert.equal(aSuper.containsEntity(b), true);
    assert.equal(aSuper.containsEntity(thing), true);
    assert.equal(aSuper.getFlattened().size, 2);
    assert.equal(bSuper.containsEntity(b), false);
    assert.equal(bSuper.containsEntity(thing), true);
    assert.equal(bSuper.getFlattened().size, 1);

    assert.equal(aDirect.containsEntity(b), true);
    assert.equal(aDirect.containsEntity(thing), false);
    assert.equal(aDirect.getFlattened().size, 1);
    assert.equal(bDirect.containsEntity(thing), true);
    assert.equal(bDirect.getFlattened().size, 1);

    // ---- phase 2: add B ⊑ C -------------------------------------------------
    // The OWL API mutates the ontology FIRST and then fires the change the
    // reasoner buffers; mirror that order. Axioms are NOT interned in
    // `OWLExpressions`, so the removal below must pass this very object.
    const bImpliesC = E.subclassOf(b, cl);
    onto.addAxiom(bImpliesC);
    r.applyChange({ axiom: bImpliesC, isAdd: true });
    r.flush();

    aSuper = r.getSuperClasses(a, false);
    bSuper = r.getSuperClasses(b, false);
    const cSuper = r.getSuperClasses(cl, false);
    aDirect = r.getSuperClasses(a, true);
    bDirect = r.getSuperClasses(b, true);
    // NOTE: HermiT computes `cDirect` with `getSuperClasses(c, FALSE)` — an
    // upstream typo, since every sibling uses `direct=true`. Preserved verbatim
    // so this stays a faithful differential; the assertions below happen to hold
    // either way because C's only ancestor is ⊤.
    const cDirect = r.getSuperClasses(cl, false);

    assert.equal(aSuper.containsEntity(a), false);
    assert.equal(aSuper.containsEntity(b), true);
    assert.equal(aSuper.containsEntity(cl), true);
    assert.equal(aSuper.containsEntity(thing), true);
    assert.equal(aSuper.getFlattened().size, 3);
    assert.equal(bSuper.containsEntity(b), false);
    assert.equal(bSuper.containsEntity(cl), true);
    assert.equal(bSuper.containsEntity(thing), true);
    assert.equal(bSuper.getFlattened().size, 2);
    assert.equal(cSuper.containsEntity(a), false);
    assert.equal(cSuper.containsEntity(b), false);
    assert.equal(cSuper.containsEntity(cl), false);
    assert.equal(cSuper.containsEntity(thing), true);
    assert.equal(cSuper.getFlattened().size, 1);

    assert.equal(aDirect.containsEntity(a), false);
    assert.equal(aDirect.containsEntity(b), true);
    assert.equal(aDirect.containsEntity(cl), false);
    assert.equal(aDirect.containsEntity(thing), false);
    assert.equal(aDirect.getFlattened().size, 1);
    assert.equal(bDirect.containsEntity(a), false);
    assert.equal(bDirect.containsEntity(b), false);
    assert.equal(bDirect.containsEntity(cl), true);
    assert.equal(bDirect.containsEntity(thing), false);
    assert.equal(bDirect.getFlattened().size, 1);
    assert.equal(cDirect.containsEntity(a), false);
    assert.equal(cDirect.containsEntity(b), false);
    assert.equal(cDirect.containsEntity(cl), false);
    assert.equal(cDirect.containsEntity(thing), true);
    assert.equal(cDirect.getFlattened().size, 1);

    // ---- phase 3: retract B ⊑ C ---------------------------------------------
    onto.removeAxiom(bImpliesC);
    r.applyChange({ axiom: bImpliesC, isAdd: false });
    r.flush();

    aSuper = r.getSuperClasses(a, false);
    bSuper = r.getSuperClasses(b, false);
    const cSuper2 = r.getSuperClasses(cl, false);
    aDirect = r.getSuperClasses(a, true);
    bDirect = r.getSuperClasses(b, true);
    const cDirect2 = r.getSuperClasses(cl, false);

    assert.equal(aSuper.containsEntity(a), false);
    assert.equal(aSuper.containsEntity(b), true);
    assert.equal(aSuper.containsEntity(cl), false);
    assert.equal(aSuper.containsEntity(thing), true);
    assert.equal(aSuper.getFlattened().size, 2);
    assert.equal(bSuper.containsEntity(b), false);
    assert.equal(bSuper.containsEntity(cl), false);
    assert.equal(bSuper.containsEntity(thing), true);
    assert.equal(bSuper.getFlattened().size, 1);
    assert.equal(cSuper2.containsEntity(a), false);
    assert.equal(cSuper2.containsEntity(b), false);
    assert.equal(cSuper2.containsEntity(cl), false);
    assert.equal(cSuper2.containsEntity(thing), true);
    assert.equal(cSuper2.getFlattened().size, 1);

    assert.equal(aDirect.containsEntity(a), false);
    assert.equal(aDirect.containsEntity(b), true);
    assert.equal(aDirect.containsEntity(cl), false);
    assert.equal(aDirect.containsEntity(thing), false);
    assert.equal(aDirect.getFlattened().size, 1);
    assert.equal(bDirect.containsEntity(a), false);
    assert.equal(bDirect.containsEntity(b), false);
    assert.equal(bDirect.containsEntity(cl), false);
    assert.equal(bDirect.containsEntity(thing), true);
    assert.equal(bDirect.getFlattened().size, 1);
    assert.equal(cDirect2.containsEntity(a), false);
    assert.equal(cDirect2.containsEntity(b), false);
    assert.equal(cDirect2.containsEntity(cl), false);
    assert.equal(cDirect2.containsEntity(thing), true);
    assert.equal(cDirect2.getFlattened().size, 1);
  } finally {
    r.dispose();
  }
});

test('OWLReasonerTest.testIncrementalAddition2 — buffered changes hide inconsistency', () => {
  const f = p('f');
  const a = ind('a');
  const b = ind('b');
  const cl = ind('c');

  const onto = ontology([
    E.objectPropertyAssertion(f, a, b),
    func(f)
  ], ONTOLOGY_IRI);
  const r = createReasoner(onto, {
    throwInconsistentOntologyException: false,
    bufferChanges: true
  });
  try {
    assert.equal(r.isConsistent(), true);

    // f is functional, so adding f(a,c) forces b = c …
    const fac = E.objectPropertyAssertion(f, a, cl);
    onto.addAxiom(fac);
    r.applyChange({ axiom: fac, isAdd: true });
    r.flush();
    assert.equal(r.isConsistent(), true);

    // … which contradicts DifferentIndividuals(b,c) — but ONLY once flushed.
    const bneqc = E.differentIndividuals([b, cl]);
    onto.addAxiom(bneqc);
    r.applyChange({ axiom: bneqc, isAdd: true });
    assert.equal(r.isConsistent(), true, 'a buffered change must not be visible yet');
    r.flush();
    assert.equal(r.isConsistent(), false);

    // Retracting f(a,c) is likewise invisible until the flush.
    onto.removeAxiom(fac);
    r.applyChange({ axiom: fac, isAdd: false });
    assert.equal(r.isConsistent(), false, 'a buffered retraction must not be visible yet');
    r.flush();
    assert.equal(r.isConsistent(), true);
  } finally {
    r.dispose();
  }
});

test('OWLReasonerTest.testGetDataPropertyValues — the two rdf:PlainLiteral spellings collapse', () => {
  const a = ind('a');
  const b = ind('b');
  const ci = ind('c');
  const d = dp('dp');

  withReasoner([
    // :a — four assertions that must collapse to TWO distinct values.
    E.dataPropertyAssertion(d, a, E.literal('RDFPlainLiteralwithEmptyLangTag@', RDF_PL)),
    E.dataPropertyAssertion(d, a, SL('RDFPlainLiteralwithEmptyLangTag')),
    E.dataPropertyAssertion(d, a, E.literal('RDFPlainLiteralWithLangTag@en-gb', RDF_PL)),
    E.dataPropertyAssertion(d, a, PL('RDFPlainLiteralWithLangTag', 'en-gb')),
    // :b — two assertions that must collapse to ONE.
    E.dataPropertyAssertion(d, b, SL('abc')),
    E.dataPropertyAssertion(d, b, E.literal('abc@', RDF_PL)),
    // :c — three genuinely distinct numeric values (`1` and `01` differ lexically;
    // `xsd:short` is a different datatype from `xsd:integer`).
    E.dataPropertyAssertion(d, ci, TL('1', 'integer')),
    E.dataPropertyAssertion(d, ci, TL('01', 'integer')),
    E.dataPropertyAssertion(d, ci, TL('1', 'short'))
  ], null, (r) => {
    assert.equal(r.isConsistent(), true);

    assertContainsAll(r.getDataPropertyValues(a, d),
      PL('RDFPlainLiteralwithEmptyLangTag', ''),
      PL('RDFPlainLiteralWithLangTag', 'en-gb'));

    assertContainsAll(r.getDataPropertyValues(b, d), PL('abc', ''));

    assertContainsAll(r.getDataPropertyValues(ci, d),
      TL('1', 'integer'), TL('01', 'integer'), TL('1', 'short'));
  });
});

// ---- the shared `loadSameAsTest` ontology ----------------------------------
//
// `FunctionalObjectProperty(:f)` plus `f(a1,b1_1)` and `f(a1,b1_2)` forces
// `b1_1 = b1_2`; `SameIndividual(:a2_1 :a2_2)` is asserted outright. So:
//   instances of A = {a1, a2_1, a2_2}   (2 same-as nodes)
//   instances of B = {b1_1, b1_2, b2}   (2 same-as nodes; b1_* via C ⊑ B)
//   direct B       = {b2}
//   instances of C = {b1_1, b1_2}       (1 same-as node)
function sameAsAxioms() {
  return [
    declaration(ind('a1')), declaration(ind('b1_1')), declaration(ind('b1_2')),
    declaration(ind('a2_1')), declaration(ind('a2_2')), declaration(ind('b2')),
    declaration(p('f')),
    E.objectPropertyAssertion(p('f'), ind('a1'), ind('b1_1')),
    E.objectPropertyAssertion(p('f'), ind('a1'), ind('b1_2')),
    E.sameIndividual([ind('a2_1'), ind('a2_2')]),
    E.classAssertion(c('A'), ind('a1')),
    E.classAssertion(c('A'), ind('a2_1')),
    E.classAssertion(c('C'), ind('b1_1')),
    E.classAssertion(c('B'), ind('b2')),
    E.subclassOf(c('C'), c('B')),
    func(p('f'))
  ];
}

test('OWLReasonerTest.testEquivalenceClasses — BY_SAME_AS groups same-as individuals', () => {
  const a1 = ind('a1');
  const a2_1 = ind('a2_1');
  const a2_2 = ind('a2_2');
  const b1_1 = ind('b1_1');
  const b1_2 = ind('b1_2');
  const b2 = ind('b2');

  withReasoner(sameAsAxioms(), { individualNodeSetPolicy: 'BY_SAME_AS' }, (r) => {
    const As = r.getInstances(c('A'), false);
    const Bs = r.getInstances(c('B'), false);
    const directBs = r.getInstances(c('B'), true);
    const Cs = r.getInstances(c('C'), false);

    assert.equal(As.getNodes().size, 2);
    assert.equal(As.getFlattened().size, 3);
    assert.equal(Bs.getNodes().size, 2);
    assert.equal(Bs.getFlattened().size, 3);
    assert.equal(directBs.getNodes().size, 1);
    assert.equal(directBs.getFlattened().size, 1);
    assert.equal(Cs.getNodes().size, 1);
    assert.equal(Cs.getFlattened().size, 2);

    for (const node of As.getNodes()) {
      if (node.getSize() === 1) assert.equal(node.contains(a1), true);
      else if (node.getSize() === 2) {
        assert.equal(node.contains(a2_1), true);
        assert.equal(node.contains(a2_2), true);
      } else assert.fail(`unexpected A node size ${node.getSize()}`);
    }
    for (const node of Bs.getNodes()) {
      if (node.getSize() === 1) assert.equal(node.contains(b2), true);
      else if (node.getSize() === 2) {
        assert.equal(node.contains(b1_1), true);
        assert.equal(node.contains(b1_2), true);
      } else assert.fail(`unexpected B node size ${node.getSize()}`);
    }
    for (const node of directBs.getNodes()) {
      if (node.getSize() === 1) assert.equal(node.contains(b2), true);
      else assert.fail(`unexpected direct-B node size ${node.getSize()}`);
    }
    for (const node of Cs.getNodes()) {
      if (node.getSize() === 2) {
        assert.equal(node.contains(b1_1), true);
        assert.equal(node.contains(b1_2), true);
      } else assert.fail(`unexpected C node size ${node.getSize()}`);
    }
  });
});

test('OWLReasonerTest.testNonEquivalenceClasses — BY_NAME gives one node each', () => {
  withReasoner(sameAsAxioms(), { individualNodeSetPolicy: 'BY_NAME' }, (r) => {
    const As = r.getInstances(c('A'), false);
    const Bs = r.getInstances(c('B'), false);
    const directBs = r.getInstances(c('B'), true);
    const Cs = r.getInstances(c('C'), false);

    assert.equal(As.getNodes().size, 3);
    assert.equal(As.getFlattened().size, 3);
    assert.equal(Bs.getNodes().size, 3);
    assert.equal(Bs.getFlattened().size, 3);
    assert.equal(directBs.getNodes().size, 1);
    assert.equal(directBs.getFlattened().size, 1);
    assert.equal(Cs.getNodes().size, 2);
    assert.equal(Cs.getFlattened().size, 2);

    for (const nodeSet of [As, Bs, directBs, Cs]) {
      for (const node of nodeSet.getNodes()) assert.equal(node.getSize(), 1);
    }

    assert.equal(As.containsEntity(ind('a1')), true);
    assert.equal(As.containsEntity(ind('a2_1')), true);
    assert.equal(As.containsEntity(ind('a2_2')), true);
    assert.equal(Bs.containsEntity(ind('b1_1')), true);
    assert.equal(Bs.containsEntity(ind('b1_2')), true);
    assert.equal(Bs.containsEntity(ind('b2')), true);
    assert.equal(Cs.containsEntity(ind('b1_1')), true);
    assert.equal(Cs.containsEntity(ind('b1_2')), true);
    assert.equal(directBs.containsEntity(ind('b2')), true);
  });
});
