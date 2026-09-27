'use strict';

// ---------------------------------------------------------------------------
// scripts/smoke-clausification.js — exercises every clause shape produced by
// OWLClausification against hand-computed expected clauses.
// ---------------------------------------------------------------------------

const E = require('../src/owl/OWLExpressions');
const C = require('../src/structural/OWLClausification');

const EX = 'http://ex.org#';
const c = (n) => E.owlClass(EX + n);
const p = (n) => E.objectProperty(EX + n);
const dp = (n) => E.dataProperty(EX + n);
const ind = (n) => E.namedIndividual(EX + n);
const xsd = (n) => E.datatype('http://www.w3.org/2001/XMLSchema#' + n);

let pass = 0;
let fail = 0;

function clausesOf(axioms, opts) {
  const r = new C.OWLClausification().preprocessAndClausify(axioms, opts || { ontologyIRI: 'urn:test' });
  return r;
}

/**
 * @param {string} name
 * @param {object[]} axioms
 * @param {string[]} [expectedClauses] exact `DLClause.toString()` forms
 * @param {string[]} [expectedFacts] exact positive `Atom.toString()` forms
 * @param {string[]} [expectedNegFacts] exact negative `Atom.toString()` forms
 */
function check(name, axioms, expectedClauses, expectedFacts, expectedNegFacts) {
  let r;
  try {
    r = clausesOf(axioms);
  } catch (err) {
    console.log(`FAIL ${name}: threw ${err.message}`);
    fail++;
    return null;
  }
  const problems = [];
  const compare = (label, gotList, wantList) => {
    if (wantList === undefined || wantList === null) return;
    const got = gotList.map(String).sort();
    const want = wantList.slice().sort();
    if (got.length !== want.length || !got.every((x, i) => x === want[i])) {
      problems.push(`       expected ${label}: ${JSON.stringify(want)}`);
      problems.push(`       got      ${label}: ${JSON.stringify(got)}`);
    }
  };
  compare('clauses', r.dlOntology.dlClauses, expectedClauses);
  compare('+facts ', r.dlOntology.positiveFacts, expectedFacts);
  compare('-facts ', r.dlOntology.negativeFacts, expectedNegFacts);
  if (problems.length === 0) {
    console.log(`ok   ${name}`);
    pass++;
  } else {
    console.log(`FAIL ${name}`);
    for (const p of problems) console.log(p);
    fail++;
  }
  return r;
}

function checkThrows(name, axioms, messageFragment) {
  try {
    clausesOf(axioms);
    console.log(`FAIL ${name}: expected a throw`);
    fail++;
  } catch (err) {
    if (!messageFragment || err.message.includes(messageFragment)) {
      console.log(`ok   ${name} (threw: ${err.message.split('\n')[0]})`);
      pass++;
    } else {
      console.log(`FAIL ${name}: wrong message: ${err.message}`);
      fail++;
    }
  }
}

// ---- 1. atomic subsumption -------------------------------------------------
check('A ⊑ B',
  [E.subclassOf(c('A'), c('B'))],
  ['http://ex.org#B(X) :- http://ex.org#A(X)']);

// ---- 2. conjunction --------------------------------------------------------
check('A ⊓ B ⊑ C',
  [E.subclassOf(E.objectIntersectionOf([c('A'), c('B')]), c('C'))],
  ['http://ex.org#C(X) :- http://ex.org#A(X) ^ http://ex.org#B(X)']);

// ---- 3. disjunction in the head -------------------------------------------
check('A ⊑ B ⊔ C',
  [E.subclassOf(c('A'), E.objectUnionOf([c('B'), c('C')]))],
  ['http://ex.org#B(X) v http://ex.org#C(X) :- http://ex.org#A(X)']);

// ---- 4. complement ---------------------------------------------------------
check('A ⊑ ¬B',
  [E.subclassOf(c('A'), E.objectComplementOf(c('B')))],
  [' :- http://ex.org#A(X) ^ http://ex.org#B(X)']);

// ---- 5. existential --------------------------------------------------------
check('A ⊑ ∃R.B',
  [E.subclassOf(c('A'), E.objectSomeValuesFrom(p('R'), c('B')))],
  ['atLeast(1 http://ex.org#R http://ex.org#B)(X) :- http://ex.org#A(X)']);

// ---- 6. universal with named filler ---------------------------------------
check('A ⊑ ∀R.B',
  [E.subclassOf(c('A'), E.objectAllValuesFrom(p('R'), c('B')))],
  ['http://ex.org#B(Y) :- http://ex.org#A(X) ^ http://ex.org#R(X, Y)']);

// ---- 7. universal with negated filler -------------------------------------
check('A ⊑ ∀R.¬B',
  [E.subclassOf(c('A'), E.objectAllValuesFrom(p('R'), E.objectComplementOf(c('B'))))],
  [' :- http://ex.org#A(X) ^ http://ex.org#R(X, Y) ^ http://ex.org#B(Y)']);

// ---- 8. inverse roles ------------------------------------------------------
// `∃R⁻.B` keeps the InverseRole inside the AtLeastConcept predicate ...
check('A ⊑ ∃R⁻.B',
  [E.subclassOf(c('A'), E.objectSomeValuesFrom(E.objectInverseOf(p('R')), c('B')))],
  ['atLeast(1 inv(http://ex.org#R) http://ex.org#B)(X) :- http://ex.org#A(X)']);

// ... but `∀R⁻.B` swaps the arguments of the role ATOM instead.
check('A ⊑ ∀R⁻.B',
  [E.subclassOf(c('A'), E.objectAllValuesFrom(E.objectInverseOf(p('R')), c('B')))],
  ['http://ex.org#B(Y) :- http://ex.org#A(X) ^ http://ex.org#R(Y, X)']);

// ---- 9. self restriction ---------------------------------------------------
check('A ⊑ Self(R)',
  [E.subclassOf(c('A'), E.objectHasSelf(p('R')))],
  ['http://ex.org#R(X, X) :- http://ex.org#A(X)']);

check('A ⊑ ¬Self(R)',
  [E.subclassOf(c('A'), E.objectComplementOf(E.objectHasSelf(p('R'))))],
  [' :- http://ex.org#A(X) ^ http://ex.org#R(X, X)']);

// ---- 10. min cardinality ---------------------------------------------------
check('A ⊑ ≥2 R.B',
  [E.subclassOf(c('A'), E.objectMinCardinality(2, p('R'), c('B')))],
  ['atLeast(2 http://ex.org#R http://ex.org#B)(X) :- http://ex.org#A(X)']);

// ---- 11. max cardinality (functionality) ----------------------------------
check('A ⊑ ≤1 R.B',
  [E.subclassOf(c('A'), E.objectMaxCardinality(1, p('R'), c('B')))],
  ['=[1 http://ex.org#R http://ex.org#B](Y1, Y2, X) :- '
   + 'http://ex.org#R(X, Y1) ^ http://ex.org#B(Y1) '
   + '^ http://ex.org#R(X, Y2) ^ http://ex.org#B(Y2) ^ http://ex.org#A(X)']);

// ---- 12. max cardinality with n+1 > 2 → node-id ordering ------------------
check('A ⊑ ≤2 R.B',
  [E.subclassOf(c('A'), E.objectMaxCardinality(2, p('R'), c('B')))],
  ['=[2 http://ex.org#R http://ex.org#B](Y1, Y2, X) '
   + 'v =[2 http://ex.org#R http://ex.org#B](Y1, Y3, X) '
   + 'v =[2 http://ex.org#R http://ex.org#B](Y2, Y3, X) :- '
   + 'http://ex.org#R(X, Y1) ^ http://ex.org#B(Y1) '
   + '^ http://ex.org#R(X, Y2) ^ http://ex.org#B(Y2) '
   + '^ http://ex.org#R(X, Y3) ^ http://ex.org#B(Y3) '
   + '^ <=(Y1, Y2) ^ <=(Y2, Y3) ^ ascendingOrEqual(Y1, Y2, Y3) ^ http://ex.org#A(X)']);

// ---- 13. max cardinality with a negated filler ----------------------------
// The negated filler moves into the HEAD (¬B(y₁) ∨ ¬B(y₂) ∨ y₁≈y₂).
check('A ⊑ ≤1 R.¬B',
  [E.subclassOf(c('A'), E.objectMaxCardinality(1, p('R'), E.objectComplementOf(c('B'))))],
  ['http://ex.org#B(Y1) v http://ex.org#B(Y2) '
   + 'v =[1 http://ex.org#R not(http://ex.org#B)](Y1, Y2, X) :- '
   + 'http://ex.org#R(X, Y1) ^ http://ex.org#R(X, Y2) ^ http://ex.org#A(X)']);

// ---- 14. nominals ----------------------------------------------------------
check('A ⊑ {i}',
  [E.subclassOf(c('A'), E.objectOneOf([ind('i')]))],
  ['=(X, Z) :- http://ex.org#A(X) ^ internal:nom#http://ex.org#i(Z)'],
  ['internal:nom#http://ex.org#i(<http://ex.org#i>)']);

// `A ⊑ ¬{i}` is rewritten by OWLNormalization's optimized negative-OneOf
// translation into the NEGATIVE FACT ¬A(i) — no clause at all.
check('A ⊑ ¬{i}',
  [E.subclassOf(c('A'), E.objectComplementOf(E.objectOneOf([ind('i')])))],
  [], [], ['http://ex.org#A(<http://ex.org#i>)']);

check('A ⊑ ∃R.{i}',
  [E.subclassOf(c('A'), E.objectSomeValuesFrom(p('R'), E.objectOneOf([ind('i')])))],
  ['http://ex.org#R(X, Z) :- http://ex.org#A(X) ^ internal:nom#http://ex.org#i(Z)'],
  ['internal:nom#http://ex.org#i(<http://ex.org#i>)']);

check('A ⊑ ∀R.{i}',
  [E.subclassOf(c('A'), E.objectAllValuesFrom(p('R'), E.objectOneOf([ind('i')])))],
  ['=(Y, Z) :- http://ex.org#A(X) ^ http://ex.org#R(X, Y) ^ internal:nom#http://ex.org#i(Z)'],
  ['internal:nom#http://ex.org#i(<http://ex.org#i>)']);

check('A ⊑ ∀R.¬{i}',
  [E.subclassOf(c('A'), E.objectAllValuesFrom(p('R'), E.objectComplementOf(E.objectOneOf([ind('i')]))))],
  [' :- http://ex.org#A(X) ^ http://ex.org#R(X, Y) ^ internal:nom#http://ex.org#i(Y)'],
  ['internal:nom#http://ex.org#i(<http://ex.org#i>)']);

// ---- 15. simple role inclusions -------------------------------------------
check('R ⊑ S',
  [{ axiomType: E.AxiomType.SUB_OBJECT_PROPERTY_OF, subProperty: p('R'), superProperty: p('S') }],
  ['http://ex.org#S(X, Y) :- http://ex.org#R(X, Y)']);

// `R ⊑ S⁻` swaps the arguments of the head atom.
check('R ⊑ S⁻',
  [{ axiomType: E.AxiomType.SUB_OBJECT_PROPERTY_OF, subProperty: p('R'), superProperty: E.objectInverseOf(p('S')) }],
  ['http://ex.org#S(Y, X) :- http://ex.org#R(X, Y)']);

// ---- 16. transitivity → chain clause --------------------------------------
check('R transitive',
  [{ axiomType: E.AxiomType.TRANSITIVE_OBJECT_PROPERTY, property: p('R') }],
  ['http://ex.org#R(X, W0) :- http://ex.org#R(X, W0_1) ^ http://ex.org#R(W0_1, W0)']);

// ---- 17. property chain ----------------------------------------------------
check('R∘S ⊑ T',
  [{ axiomType: E.AxiomType.SUB_PROPERTY_CHAIN_OF, propertyChain: [p('R'), p('S')], superProperty: p('T') }],
  ['http://ex.org#T(X, W0) :- http://ex.org#R(X, W0_1) ^ http://ex.org#S(W0_1, W0)']);

// ---- 18. asymmetric --------------------------------------------------------
check('R asymmetric',
  [{ axiomType: E.AxiomType.ASYMMETRIC_OBJECT_PROPERTY, property: p('R') }],
  [' :- http://ex.org#R(X, Y) ^ http://ex.org#R(Y, X)']);

// ---- 19. reflexive ---------------------------------------------------------
check('R reflexive',
  [{ axiomType: E.AxiomType.REFLEXIVE_OBJECT_PROPERTY, property: p('R') }],
  ['http://ex.org#R(X, X) :- http://www.w3.org/2002/07/owl#Thing(X)']);

// ---- 20. irreflexive -------------------------------------------------------
check('R irreflexive',
  [{ axiomType: E.AxiomType.IRREFLEXIVE_OBJECT_PROPERTY, property: p('R') }],
  [' :- http://ex.org#R(X, X)']);

// ---- 21. disjoint properties ----------------------------------------------
check('R disjoint S',
  [{ axiomType: E.AxiomType.DISJOINT_OBJECT_PROPERTIES, properties: [p('R'), p('S')] }],
  [' :- http://ex.org#R(X, Y) ^ http://ex.org#S(X, Y)']);

// ---- 21b. functional / inverse-functional / symmetric ---------------------
check('R functional',
  [{ axiomType: E.AxiomType.FUNCTIONAL_OBJECT_PROPERTY, property: p('R') }],
  ['=[1 http://ex.org#R http://www.w3.org/2002/07/owl#Thing](Y1, Y2, X) :- '
   + 'http://ex.org#R(X, Y1) ^ http://ex.org#R(X, Y2)']);

check('R inverse-functional',
  [{ axiomType: E.AxiomType.INVERSE_FUNCTIONAL_OBJECT_PROPERTY, property: p('R') }],
  ['=[1 inv(http://ex.org#R) http://www.w3.org/2002/07/owl#Thing](Y1, Y2, X) :- '
   + 'http://ex.org#R(Y1, X) ^ http://ex.org#R(Y2, X)']);

check('R symmetric',
  [{ axiomType: E.AxiomType.SYMMETRIC_OBJECT_PROPERTY, property: p('R') }],
  ['http://ex.org#R(Y, X) :- http://ex.org#R(X, Y)']);

// ---- 21c. domain / range --------------------------------------------------
check('Domain(R, A)',
  [{ axiomType: E.AxiomType.OBJECT_PROPERTY_DOMAIN, property: p('R'), domain: c('A') }],
  ['http://ex.org#A(X) :- http://ex.org#R(X, Y)']);

check('Range(R, A)',
  [{ axiomType: E.AxiomType.OBJECT_PROPERTY_RANGE, property: p('R'), range: c('A') }],
  ['http://ex.org#A(Y) :- http://ex.org#R(X, Y)']);

// ---- 22. disjoint data properties -----------------------------------------
check('d1 disjoint d2',
  [{ axiomType: E.AxiomType.DISJOINT_DATA_PROPERTIES, properties: [dp('d1'), dp('d2')] }],
  ['!=(Y, Z) :- http://ex.org#d1(X, Y) ^ http://ex.org#d2(X, Z)']);

// ---- 23. data property inclusion ------------------------------------------
check('d1 ⊑ d2',
  [{ axiomType: E.AxiomType.SUB_DATA_PROPERTY_OF, subProperty: dp('d1'), superProperty: dp('d2') }],
  ['http://ex.org#d2(X, Y) :- http://ex.org#d1(X, Y)']);

check('d1 functional',
  [{ axiomType: E.AxiomType.FUNCTIONAL_DATA_PROPERTY, property: dp('d1') }],
  ['=(Y1, Y2) :- http://ex.org#d1(X, Y1) ^ http://www.w3.org/2000/01/rdf-schema#Literal(Y1) '
   + '^ http://ex.org#d1(X, Y2) ^ http://www.w3.org/2000/01/rdf-schema#Literal(Y2)']);

// ---- 24. data existential / universal -------------------------------------
// A bare datatype becomes a DatatypeRestriction with ZERO facets, which prints
// as `iri[]`.
check('A ⊑ ∃d.xsd:integer',
  [E.subclassOf(c('A'), E.dataSomeValuesFrom(dp('d'), xsd('integer')))],
  ['atLeast(1 http://ex.org#d http://www.w3.org/2001/XMLSchema#integer[])(X) :- http://ex.org#A(X)']);

check('A ⊑ ∀d.xsd:integer',
  [E.subclassOf(c('A'), E.dataAllValuesFrom(dp('d'), xsd('integer')))],
  ['http://www.w3.org/2001/XMLSchema#integer[](Y) :- http://ex.org#d(X, Y) ^ http://ex.org#A(X)']);

check('A ⊑ ≥2 d.xsd:string',
  [E.subclassOf(c('A'), E.dataMinCardinality(2, dp('d'), xsd('string')))],
  ['atLeast(2 http://ex.org#d http://www.w3.org/2001/XMLSchema#string[])(X) :- http://ex.org#A(X)']);

check('A ⊑ ≤1 d.xsd:string',
  [E.subclassOf(c('A'), E.dataMaxCardinality(1, dp('d'), xsd('string')))],
  ['not(http://www.w3.org/2001/XMLSchema#string[])(Y1) '
   + 'v not(http://www.w3.org/2001/XMLSchema#string[])(Y2) v =(Y1, Y2) :- '
   + 'http://ex.org#d(X, Y1) ^ http://ex.org#d(X, Y2) ^ http://ex.org#A(X)']);

check('A ⊑ ∃d.{"a"}',
  [E.subclassOf(c('A'), E.dataSomeValuesFrom(dp('d'), E.dataOneOf([E.literal('a', xsd('string'))])))],
  ['atLeast(1 http://ex.org#d {"a"^^<http://www.w3.org/2001/XMLSchema#string>})(X) :- http://ex.org#A(X)']);

check('A ⊑ ∀d.¬xsd:integer',
  [E.subclassOf(c('A'), E.dataAllValuesFrom(dp('d'), E.dataComplementOf(xsd('integer'))))],
  ['not(http://www.w3.org/2001/XMLSchema#integer[])(Y) :- http://ex.org#d(X, Y) ^ http://ex.org#A(X)']);

check('Range(d, xsd:integer)',
  [{ axiomType: E.AxiomType.DATA_PROPERTY_RANGE, property: dp('d'), range: xsd('integer') }],
  ['http://www.w3.org/2001/XMLSchema#integer[](Y) :- http://ex.org#d(X, Y)']);

// ---- 25. datatype definition ----------------------------------------------
// `DatatypeDefinition(MyDT, xsd:integer)` is the ONLY route into
// `axioms.dataRangeInclusions` (there is no data-range-inclusion axiom type).
// Normalization emits two disjunctions, hence two clauses.
check('DatatypeDefinition(MyDT, xsd:integer)',
  [{ axiomType: E.AxiomType.DATATYPE_DEFINITION, datatype: E.datatype(EX + 'MyDT'), dataRange: xsd('integer') }],
  ['http://ex.org#MyDT(X) v not(http://www.w3.org/2001/XMLSchema#integer[])(X) :- '
   + 'http://www.w3.org/2000/01/rdf-schema#Literal(X)',
   'http://www.w3.org/2001/XMLSchema#integer[](X) :- http://ex.org#MyDT(X)']);

// ---- 26. facts -------------------------------------------------------------
check('A(i)',
  [E.classAssertion(c('A'), ind('i'))],
  [], ['http://ex.org#A(<http://ex.org#i>)']);

check('¬A(i)',
  [E.classAssertion(E.objectComplementOf(c('A')), ind('i'))],
  [], [], ['http://ex.org#A(<http://ex.org#i>)']);

check('R(i,j)',
  [E.objectPropertyAssertion(p('R'), ind('i'), ind('j'))],
  [], ['http://ex.org#R(<http://ex.org#i>, <http://ex.org#j>)']);

check('¬R(i,j)',
  [E.negativeObjectPropertyAssertion(p('R'), ind('i'), ind('j'))],
  [], [], ['http://ex.org#R(<http://ex.org#i>, <http://ex.org#j>)']);

check('d(i,"1"^^xsd:integer)',
  [E.dataPropertyAssertion(dp('d'), ind('i'), E.literal('1', xsd('integer')))],
  [], ['http://ex.org#d(<http://ex.org#i>, "1"^^<http://www.w3.org/2001/XMLSchema#integer>)']);

check('¬d(i,"1"^^xsd:integer)',
  [E.negativeDataPropertyAssertion(dp('d'), ind('i'), E.literal('1', xsd('integer')))],
  [], [], ['http://ex.org#d(<http://ex.org#i>, "1"^^<http://www.w3.org/2001/XMLSchema#integer>)']);

check('i ≈ j',
  [E.sameIndividual([ind('i'), ind('j')])],
  [], ['=(<http://ex.org#i>, <http://ex.org#j>)']);

check('i ≠ j ≠ k',
  [E.differentIndividuals([ind('i'), ind('j'), ind('k')])],
  [], ['!=(<http://ex.org#i>, <http://ex.org#j>)',
       '!=(<http://ex.org#i>, <http://ex.org#k>)',
       '!=(<http://ex.org#j>, <http://ex.org#k>)']);

// `Self(R)(i)` is normalized into a fresh definition class `internal:def#0`.
check('Self(R)(i)',
  [E.classAssertion(E.objectHasSelf(p('R')), ind('i'))],
  ['http://ex.org#R(X, X) :- internal:def#0(X)'],
  ['internal:def#0(<http://ex.org#i>)']);

// ---- 27. keys --------------------------------------------------------------
// Keys force every named individual to be tagged with `internal:nam#Named`.
check('Key(A, d)',
  [E.hasKey(c('A'), [dp('d')]), E.classAssertion(c('A'), ind('i'))],
  ['=(X1, X2) v !=(Y1, Y2) :- internal:nam#Named(X1) ^ internal:nam#Named(X2) '
   + '^ http://ex.org#A(X1) ^ http://ex.org#A(X2) '
   + '^ http://ex.org#d(X1, Y1) ^ http://ex.org#d(X2, Y2)'],
  ['http://ex.org#A(<http://ex.org#i>)', 'internal:nam#Named(<http://ex.org#i>)']);

check('Key(A, R)',
  [E.hasKey(c('A'), [p('R')])],
  ['=(X1, X2) :- internal:nam#Named(X1) ^ internal:nam#Named(X2) '
   + '^ http://ex.org#A(X1) ^ http://ex.org#A(X2) '
   + '^ http://ex.org#R(X1, Y1) ^ http://ex.org#R(X2, Y1) ^ internal:nam#Named(Y1)']);

check('Key(⊤, d)',
  [E.hasKey(E.owlThing(), [dp('d')])],
  ['=(X1, X2) v !=(Y1, Y2) :- internal:nam#Named(X1) ^ internal:nam#Named(X2) '
   + '^ http://ex.org#d(X1, Y1) ^ http://ex.org#d(X2, Y2)']);

// ---- 28. SWRL rules --------------------------------------------------------
// A rule is detected structurally (`Array.isArray(body) && Array.isArray(head)`),
// normalized by RuleNormalizer, then clausified with an `internal:nam#Named`
// guard on every abstract variable.
check('SWRL rule A(?x) → B(?x)',
  [{
    type: 'SWRLRule',
    body: [{ type: 'ClassAtom', classExpression: c('A'), arg: { type: 'SWRLVariable', name: 'x' } }],
    head: [{ type: 'ClassAtom', classExpression: c('B'), arg: { type: 'SWRLVariable', name: 'x' } }]
  }, E.classAssertion(c('A'), ind('i'))],
  ['http://ex.org#B(x) :- http://ex.org#A(x) ^ internal:nam#Named(x)'],
  ['http://ex.org#A(<http://ex.org#i>)', 'internal:nam#Named(<http://ex.org#i>)']);

// ---- 29. unsupported datatype ---------------------------------------------
checkThrows('unsupported datatype throws',
  [E.subclassOf(c('A'), E.dataSomeValuesFrom(dp('d'), E.datatype('http://ex.org#weird')))],
  'Unsupported datatype');

{
  const r = new C.OWLClausification({ ignoreUnsupportedDatatypes: true, warningMonitor: () => {} })
    .preprocessAndClausify([E.subclassOf(c('A'), E.dataSomeValuesFrom(dp('d'), E.datatype('http://ex.org#weird')))],
      { ontologyIRI: 'urn:test' });
  if (r.dlOntology.allUnknownDatatypeRestrictions.size === 1) {
    console.log('ok   ignoreUnsupportedDatatypes records the unknown restriction');
    pass++;
  } else {
    console.log('FAIL ignoreUnsupportedDatatypes: ' + r.dlOntology.allUnknownDatatypeRestrictions.size);
    fail++;
  }
}

// ---- 30. irregular hierarchy ----------------------------------------------
checkThrows('irregular hierarchy throws',
  [{ axiomType: E.AxiomType.SUB_PROPERTY_CHAIN_OF, propertyChain: [p('R'), p('R'), p('R')], superProperty: p('R') }],
  'not regular');

// ---- 31. non-simple role in a cardinality restriction ---------------------
checkThrows('transitive in ≤1 R throws',
  [
    { axiomType: E.AxiomType.TRANSITIVE_OBJECT_PROPERTY, property: p('R') },
    E.subclassOf(c('A'), E.objectMaxCardinality(1, p('R')))
  ],
  'Non-simple property');

// ---- 32. expressivity flags reach the DLOntology --------------------------
{
  const r = clausesOf([
    E.subclassOf(c('A'), E.objectAllValuesFrom(E.objectInverseOf(p('R')), c('B'))),
    E.subclassOf(c('A'), E.objectMaxCardinality(1, p('S'))),
    E.subclassOf(c('A'), E.objectOneOf([ind('i')])),
    E.subclassOf(c('A'), E.dataSomeValuesFrom(dp('d'), xsd('integer')))
  ]);
  const o = r.dlOntology;
  const ok = o.hasInverseRoles && o.hasAtMostRestrictions && o.hasNominals && o.hasDatatypes;
  if (ok) { console.log('ok   expressivity flags propagate to DLOntology'); pass++; }
  else {
    console.log(`FAIL expressivity flags: inv=${o.hasInverseRoles} atMost=${o.hasAtMostRestrictions} nom=${o.hasNominals} dt=${o.hasDatatypes}`);
    fail++;
  }
}

// ---- 33. signature completeness -------------------------------------------
{
  const r = clausesOf([
    { axiomType: E.AxiomType.DECLARATION, entity: c('Unused') },
    { axiomType: E.AxiomType.DECLARATION, entity: p('UnusedR') },
    { axiomType: E.AxiomType.DECLARATION, entity: dp('UnusedD') },
    { axiomType: E.AxiomType.DECLARATION, entity: ind('UnusedI') },
    E.subclassOf(c('A'), c('B'))
  ]);
  const o = r.dlOntology;
  const ok = o.allAtomicConcepts.size === 3 && o.allAtomicObjectRoles.size === 1
    && o.allAtomicDataRoles.size === 1 && o.allIndividuals.size === 1;
  if (ok) { console.log('ok   declared-but-unused entities reach the signature'); pass++; }
  else {
    console.log(`FAIL signature: concepts=${o.allAtomicConcepts.size} objRoles=${o.allAtomicObjectRoles.size} dataRoles=${o.allAtomicDataRoles.size} inds=${o.allIndividuals.size}`);
    fail++;
  }
}

console.log(`\n${pass} passed, ${fail} failed`);
process.exit(fail === 0 ? 0 : 1);
