'use strict';

// ---------------------------------------------------------------------------
// scripts/dump-clausification.js — prints the clauses produced for a set of
// hand-written scenarios, so the output can be inspected against the expected
// hypertableau rules.
// ---------------------------------------------------------------------------

const E = require('../src/owl/OWLExpressions');
const C = require('../src/structural/OWLClausification');

const EX = 'http://ex.org#';
const XSD = 'http://www.w3.org/2001/XMLSchema#';
const c = (n) => E.owlClass(EX + n);
const p = (n) => E.objectProperty(EX + n);
const dp = (n) => E.dataProperty(EX + n);
const ind = (n) => E.namedIndividual(EX + n);
const xsd = (n) => E.datatype(XSD + n);
const inv = (x) => E.objectInverseOf(x);
const not = (x) => E.objectComplementOf(x);
const and = (xs) => E.objectIntersectionOf(xs);
const or = (xs) => E.objectUnionOf(xs);

const AT = E.AxiomType;

const scenarios = [
  ['A ⊑ B', [E.subclassOf(c('A'), c('B'))]],
  ['A ⊓ B ⊑ C', [E.subclassOf(and([c('A'), c('B')]), c('C'))]],
  ['A ⊑ B ⊔ C', [E.subclassOf(c('A'), or([c('B'), c('C')]))]],
  ['A ⊑ ¬B', [E.subclassOf(c('A'), not(c('B')))]],
  ['A ⊑ ∃R.B', [E.subclassOf(c('A'), E.objectSomeValuesFrom(p('R'), c('B')))]],
  ['A ⊑ ∀R.B', [E.subclassOf(c('A'), E.objectAllValuesFrom(p('R'), c('B')))]],
  ['A ⊑ ∀R.¬B', [E.subclassOf(c('A'), E.objectAllValuesFrom(p('R'), not(c('B'))))]],
  ['A ⊑ ∃R⁻.B', [E.subclassOf(c('A'), E.objectSomeValuesFrom(inv(p('R')), c('B')))]],
  ['A ⊑ ∀R⁻.B', [E.subclassOf(c('A'), E.objectAllValuesFrom(inv(p('R')), c('B')))]],
  ['A ⊑ Self(R)', [E.subclassOf(c('A'), E.objectHasSelf(p('R')))]],
  ['A ⊑ ¬Self(R)', [E.subclassOf(c('A'), not(E.objectHasSelf(p('R'))))]],
  ['A ⊑ ≥2 R.B', [E.subclassOf(c('A'), E.objectMinCardinality(2, p('R'), c('B')))]],
  ['A ⊑ ≤1 R.B', [E.subclassOf(c('A'), E.objectMaxCardinality(1, p('R'), c('B')))]],
  ['A ⊑ ≤1 R', [E.subclassOf(c('A'), E.objectMaxCardinality(1, p('R')))]],
  ['A ⊑ ≤2 R.B', [E.subclassOf(c('A'), E.objectMaxCardinality(2, p('R'), c('B')))]],
  ['A ⊑ ≤1 R.¬B', [E.subclassOf(c('A'), E.objectMaxCardinality(1, p('R'), not(c('B'))))]],
  ['A ⊑ {i}', [E.subclassOf(c('A'), E.objectOneOf([ind('i')]))]],
  ['A ⊑ ¬{i}', [E.subclassOf(c('A'), not(E.objectOneOf([ind('i')])))]],
  ['A ⊑ ∃R.{i}', [E.subclassOf(c('A'), E.objectSomeValuesFrom(p('R'), E.objectOneOf([ind('i')])))]],
  ['A ⊑ ∀R.{i}', [E.subclassOf(c('A'), E.objectAllValuesFrom(p('R'), E.objectOneOf([ind('i')])))]],
  ['A ⊑ ∀R.¬{i}', [E.subclassOf(c('A'), E.objectAllValuesFrom(p('R'), not(E.objectOneOf([ind('i')]))))]],
  ['R ⊑ S', [{ axiomType: AT.SUB_OBJECT_PROPERTY_OF, subProperty: p('R'), superProperty: p('S') }]],
  ['R ⊑ S⁻', [{ axiomType: AT.SUB_OBJECT_PROPERTY_OF, subProperty: p('R'), superProperty: inv(p('S')) }]],
  ['R transitive', [{ axiomType: AT.TRANSITIVE_OBJECT_PROPERTY, property: p('R') }]],
  ['R∘S ⊑ T', [{ axiomType: AT.SUB_PROPERTY_CHAIN_OF, propertyChain: [p('R'), p('S')], superProperty: p('T') }]],
  ['R asymmetric', [{ axiomType: AT.ASYMMETRIC_OBJECT_PROPERTY, property: p('R') }]],
  ['R reflexive', [{ axiomType: AT.REFLEXIVE_OBJECT_PROPERTY, property: p('R') }]],
  ['R irreflexive', [{ axiomType: AT.IRREFLEXIVE_OBJECT_PROPERTY, property: p('R') }]],
  ['R disjoint S', [{ axiomType: AT.DISJOINT_OBJECT_PROPERTIES, properties: [p('R'), p('S')] }]],
  ['R functional', [{ axiomType: AT.FUNCTIONAL_OBJECT_PROPERTY, property: p('R') }]],
  ['R inverse-functional', [{ axiomType: AT.INVERSE_FUNCTIONAL_OBJECT_PROPERTY, property: p('R') }]],
  ['R symmetric', [{ axiomType: AT.SYMMETRIC_OBJECT_PROPERTY, property: p('R') }]],
  ['Domain(R,A)', [{ axiomType: AT.OBJECT_PROPERTY_DOMAIN, property: p('R'), domain: c('A') }]],
  ['Range(R,A)', [{ axiomType: AT.OBJECT_PROPERTY_RANGE, property: p('R'), range: c('A') }]],
  ['d1 ⊑ d2', [{ axiomType: AT.SUB_DATA_PROPERTY_OF, subProperty: dp('d1'), superProperty: dp('d2') }]],
  ['d1 disjoint d2', [{ axiomType: AT.DISJOINT_DATA_PROPERTIES, properties: [dp('d1'), dp('d2')] }]],
  ['d1 functional', [{ axiomType: AT.FUNCTIONAL_DATA_PROPERTY, property: dp('d1') }]],
  ['A ⊑ ∃d.int', [E.subclassOf(c('A'), E.dataSomeValuesFrom(dp('d'), xsd('integer')))]],
  ['A ⊑ ∀d.int', [E.subclassOf(c('A'), E.dataAllValuesFrom(dp('d'), xsd('integer')))]],
  ['A ⊑ ≥2 d.str', [E.subclassOf(c('A'), E.dataMinCardinality(2, dp('d'), xsd('string')))]],
  ['A ⊑ ≤1 d.str', [E.subclassOf(c('A'), E.dataMaxCardinality(1, dp('d'), xsd('string')))]],
  ['A ⊑ ∃d.{"a"}', [E.subclassOf(c('A'), E.dataSomeValuesFrom(dp('d'), E.dataOneOf([E.literal('a', xsd('string'))])))]],
  ['A ⊑ ∀d.¬int', [E.subclassOf(c('A'), E.dataAllValuesFrom(dp('d'), E.dataComplementOf(xsd('integer'))))]],
  ['Range(d,int)', [{ axiomType: AT.DATA_PROPERTY_RANGE, property: dp('d'), range: xsd('integer') }]],
  ['A(i)', [E.classAssertion(c('A'), ind('i'))]],
  ['¬A(i)', [E.classAssertion(not(c('A')), ind('i'))]],
  ['R(i,j)', [E.objectPropertyAssertion(p('R'), ind('i'), ind('j'))]],
  ['¬R(i,j)', [E.negativeObjectPropertyAssertion(p('R'), ind('i'), ind('j'))]],
  ['d(i,"1"^^int)', [E.dataPropertyAssertion(dp('d'), ind('i'), E.literal('1', xsd('integer')))]],
  ['¬d(i,"1"^^int)', [E.negativeDataPropertyAssertion(dp('d'), ind('i'), E.literal('1', xsd('integer')))]],
  ['Self(R)(i)', [E.classAssertion(E.objectHasSelf(p('R')), ind('i'))]],
  ['¬Self(R)(i)', [E.classAssertion(not(E.objectHasSelf(p('R'))), ind('i'))]],
  ['i ≈ j', [E.sameIndividual([ind('i'), ind('j')])]],
  ['i≠j≠k', [E.differentIndividuals([ind('i'), ind('j'), ind('k')])]],
  ['Key(A, d)', [E.hasKey(c('A'), [dp('d')])]],
  ['Key(A, R)', [E.hasKey(c('A'), [p('R')])]],
  ['Key(⊤, d)', [E.hasKey(E.owlThing(), [dp('d')])]],
  ['DatatypeDefinition', [
    { axiomType: AT.DATATYPE_DEFINITION, datatype: E.datatype(EX + 'MyDT'), dataRange: xsd('integer') }
  ]],
  ['A ⊑ ∃R.B + R transitive', [
    { axiomType: AT.TRANSITIVE_OBJECT_PROPERTY, property: p('R') },
    E.subclassOf(c('A'), E.objectSomeValuesFrom(p('R'), c('B')))
  ]]
];

for (const [name, axioms] of scenarios) {
  try {
    const r = new C.OWLClausification().preprocessAndClausify(axioms, { ontologyIRI: 'urn:test' });
    const o = r.dlOntology;
    console.log(`\n=== ${name}`);
    for (const cl of o.dlClauses) console.log(`  clause: ${cl}`);
    for (const f of o.positiveFacts) console.log(`  +fact : ${f}`);
    for (const f of o.negativeFacts) console.log(`  -fact : ${f}`);
    console.log(`  sig   : concepts=${o.allAtomicConcepts.size} objRoles=${o.allAtomicObjectRoles.size}`
      + ` dataRoles=${o.allAtomicDataRoles.size} inds=${o.allIndividuals.size}`
      + ` complexRoles=${o.complexObjectRoles.size}`);
    console.log(`  flags : horn=${o.isHorn} inv=${o.hasInverseRoles} atMost=${o.hasAtMostRestrictions}`
      + ` nom=${o.hasNominals} dt=${o.hasDatatypes}`);
  } catch (err) {
    console.log(`\n=== ${name}\n  THROW: ${err.message.split('\n')[0]}`);
  }
}
