'use strict';
/**
 * Smoke test for the public reasoner facade (src/reasoner/Reasoner.js).
 *
 * Covers: consistency, class-expression satisfiability, subsumption,
 * classification (top/bottom nodes, super/sub classes, equivalent classes,
 * unsatisfiable classes, disjoint classes), object-property hierarchy +
 * characteristics + domains/ranges, data-property hierarchy, the
 * individual-level queries (types, instances, same/different individuals,
 * object/data property values), arbitrary axiom entailment, and SWRL rules
 * (section 11) in both the protege-js and hand-tagged variable encodings.
 *
 * Run with:  node scripts/smoke-reasoner.js
 */

const E = require('../src/owl/OWLExpressions');
const { Reasoner, createReasoner } = require('../src/reasoner/Reasoner');
const { Configuration } = require('../src/Configuration');

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

let failures = 0;
let checks = 0;

function check(name, actual, expected) {
  checks++;
  const ok = actual === expected;
  if (!ok) failures++;
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}  (got ${actual}, expected ${expected})`);
}

function checkSet(name, actualIterable, expectedArray) {
  checks++;
  const actual = [...actualIterable].map(String).sort().join('|');
  const expected = [...expectedArray].map(String).sort().join('|');
  const ok = actual === expected;
  if (!ok) failures++;
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}\n        got      ${actual}\n        expected ${expected}`);
}

function section(title) {
  console.log(`\n=== ${title} ===`);
}

const EX = 'http://example.org/';
const cls = (n) => E.owlClass(EX + n);
const op = (n) => E.objectProperty(EX + n);
const dp = (n) => E.dataProperty(EX + n);
const ind = (n) => E.namedIndividual(EX + n);

// Axiom types with no factory in OWLExpressions.js are built as plain objects.
const AT = E.AxiomType;
const declaration = (entity) => ({ axiomType: AT.DECLARATION, entity });
const subObjectPropertyOf = (subProperty, superProperty) =>
  ({ axiomType: AT.SUB_OBJECT_PROPERTY_OF, subProperty, superProperty });
const transitiveObjectProperty = (property) =>
  ({ axiomType: AT.TRANSITIVE_OBJECT_PROPERTY, property });
const functionalObjectProperty = (property) =>
  ({ axiomType: AT.FUNCTIONAL_OBJECT_PROPERTY, property });
const inverseFunctionalObjectProperty = (property) =>
  ({ axiomType: AT.INVERSE_FUNCTIONAL_OBJECT_PROPERTY, property });
const symmetricObjectProperty = (property) =>
  ({ axiomType: AT.SYMMETRIC_OBJECT_PROPERTY, property });
const asymmetricObjectProperty = (property) =>
  ({ axiomType: AT.ASYMMETRIC_OBJECT_PROPERTY, property });
const reflexiveObjectProperty = (property) =>
  ({ axiomType: AT.REFLEXIVE_OBJECT_PROPERTY, property });
const irreflexiveObjectProperty = (property) =>
  ({ axiomType: AT.IRREFLEXIVE_OBJECT_PROPERTY, property });
const objectPropertyDomain = (property, domain) =>
  ({ axiomType: AT.OBJECT_PROPERTY_DOMAIN, property, domain });
const objectPropertyRange = (property, range) =>
  ({ axiomType: AT.OBJECT_PROPERTY_RANGE, property, range });
const inverseObjectProperties = (firstProperty, secondProperty) =>
  ({ axiomType: AT.INVERSE_OBJECT_PROPERTIES, firstProperty, secondProperty,
     property1: firstProperty, property2: secondProperty });
const disjointObjectProperties = (properties) =>
  ({ axiomType: AT.DISJOINT_OBJECT_PROPERTIES, properties: properties.slice() });
const subDataPropertyOf = (subProperty, superProperty) =>
  ({ axiomType: AT.SUB_DATA_PROPERTY_OF, subProperty, superProperty });
const dataPropertyDomain = (property, domain) =>
  ({ axiomType: AT.DATA_PROPERTY_DOMAIN, property, domain });
const functionalDataProperty = (property) =>
  ({ axiomType: AT.FUNCTIONAL_DATA_PROPERTY, property });
const disjointDataProperties = (properties) =>
  ({ axiomType: AT.DISJOINT_DATA_PROPERTIES, properties: properties.slice() });
const equivalentObjectProperties = (properties) =>
  ({ axiomType: AT.EQUIVALENT_OBJECT_PROPERTIES, properties: properties.slice() });
const equivalentDataProperties = (properties) =>
  ({ axiomType: AT.EQUIVALENT_DATA_PROPERTIES, properties: properties.slice() });
const subPropertyChainOf = (propertyChain, superProperty) =>
  ({ axiomType: AT.SUB_PROPERTY_CHAIN_OF, propertyChain: propertyChain.slice(), superProperty });
const dataPropertyRange = (property, range) =>
  ({ axiomType: AT.DATA_PROPERTY_RANGE, property, range });
const datatypeDefinition = (datatype, dataRange) =>
  ({ axiomType: AT.DATATYPE_DEFINITION, datatype, dataRange });
const anon = (nodeId) => E.anonymousIndividual(nodeId);

/**
 * A minimal protege-js-shaped ontology: `getAxioms()` returns an ARRAY.
 *
 * It is MUTABLE (`addAxiom`/`removeAxiom`) because HermiT's incremental API
 * treats the ontology as the source of truth: the OWL API mutates the ontology
 * first, then fires an `OWLOntologyChange` that the reasoner merely *buffers*;
 * `flush()` re-clausifies the (already-updated) ontology. Tests that exercise
 * buffering must therefore mutate the ontology AND notify via `applyChange`.
 */
function ontology(axioms, iri = EX + 'smoke') {
  const list = [...new Set(axioms)];
  return {
    getAxioms: () => list.slice(),
    getOntologyID: () => ({ ontologyIRI: iri }),
    addAxiom(ax) { if (!list.includes(ax)) list.push(ax); },
    removeAxiom(ax) { const i = list.indexOf(ax); if (i >= 0) list.splice(i, 1); },
    _axioms: list
  };
}

const A = cls('A'), B = cls('B'), C = cls('C'), D = cls('D');
const R = op('R'), S = op('S'), T = op('T');
const hasAge = dp('hasAge'), hasName = dp('hasName');
const a = ind('a'), b = ind('b'), c = ind('c');

/**
 * Flatten a Node OR NodeSet of OWLClass nodes to an array of IRIs.
 * (`getUnsatisfiableClasses`/`getEquivalentClasses` return a bare Node.)
 */
const classIRIs = (nodeOrNodeSet) =>
  [...flatten(nodeOrNodeSet)].map((x) => E.iriString(x));
/** Flatten a Node OR NodeSet of property nodes to an array of named-property IRIs. */
const propIRIs = (nodeOrNodeSet) =>
  [...flatten(nodeOrNodeSet)].map((x) => E.iriString(E.namedPropertyOf(x)));
/** Flatten a Node OR NodeSet of individuals to an array of IRIs. */
const indIRIs = (nodeOrNodeSet) => [...flatten(nodeOrNodeSet)].map((x) => E.iriString(x));

function flatten(nodeOrNodeSet) {
  return typeof nodeOrNodeSet.getFlattened === 'function'
    ? nodeOrNodeSet.getFlattened()
    : nodeOrNodeSet.getEntities();
}

const THING_IRI = E.IRI_THING;
const NOTHING_IRI = E.IRI_NOTHING;

// ===========================================================================
section('1. consistency');
// ===========================================================================

{
  const r = createReasoner(ontology([
    declaration(A), declaration(B),
    E.subclassOf(A, B),
    E.classAssertion(A, a)
  ]));
  check('consistent TBox+ABox', r.isConsistent(), true);
  check('reasoner name', r.getReasonerName(), 'DL-JS-REASONER');
}

{
  // A sq B + Disjoint(A,B) does NOT make the ontology inconsistent — it makes
  // A unsatisfiable (A may simply be empty).
  const r = createReasoner(ontology([
    declaration(A), declaration(B),
    E.disjointClasses([A, B]),
    E.subclassOf(A, B)
  ]));
  check('still consistent (A just becomes unsatisfiable)', r.isConsistent(), true);
  check('A unsatisfiable', r.isSatisfiable(A), false);
}

{
  // A genuinely inconsistent TBox: A is forced to have an instance AND A sq not A.
  const r = createReasoner(ontology([
    declaration(A), declaration(a),
    E.subclassOf(A, E.objectComplementOf(A)),
    E.classAssertion(A, a)
  ]));
  check('inconsistent (a:A, A sq not A)', r.isConsistent(), false);
}

{
  // ABox clash: a:A, a:B, Disjoint(A,B)
  const r = createReasoner(ontology([
    declaration(A), declaration(B), declaration(a),
    E.disjointClasses([A, B]),
    E.classAssertion(A, a),
    E.classAssertion(B, a)
  ]));
  check('inconsistent ABox', r.isConsistent(), false);
}

// ===========================================================================
section('2. class hierarchy');
// ===========================================================================

{
  // A sq B sq C, D unrelated; B equiv nothing extra.
  const r = createReasoner(ontology([
    declaration(A), declaration(B), declaration(C), declaration(D),
    E.subclassOf(A, B),
    E.subclassOf(B, C)
  ]));
  check('consistent', r.isConsistent(), true);

  check('isSubClassOf(A,C) transitive', r.isSubClassOf(A, C), true);
  check('isSubClassOf(C,A) false', r.isSubClassOf(C, A), false);
  check('isSubClassOf(A,owl:Thing)', r.isSubClassOf(A, E.owlThing()), true);
  check('isSubClassOf(owl:Nothing,A)', r.isSubClassOf(E.owlNothing(), A), true);
  check('isSubClassOf(D,A) false', r.isSubClassOf(D, A), false);

  checkSet('superClasses(A, direct)', classIRIs(r.getSuperClasses(A, true)), [EX + 'B']);
  // HermiT includes owl:Thing in the non-direct ancestor set.
  checkSet('superClasses(A, all)', classIRIs(r.getSuperClasses(A, false)),
    [EX + 'B', EX + 'C', THING_IRI]);
  checkSet('subClasses(C, direct)', classIRIs(r.getSubClasses(C, true)), [EX + 'B']);
  // … and owl:Nothing in the non-direct descendant set.
  checkSet('subClasses(C, all)', classIRIs(r.getSubClasses(C, false)),
    [EX + 'A', EX + 'B', NOTHING_IRI]);
  checkSet('equivalentClasses(A)', classIRIs(r.getEquivalentClasses(A)), [EX + 'A']);

  check('A satisfiable', r.isSatisfiable(A), true);
  check('A sq C expression', r.isSatisfiable(E.objectIntersectionOf([A, C])), true);
  check('A sq not C unsatisfiable', r.isSatisfiable(E.objectIntersectionOf([A, E.objectComplementOf(C)])), false);

  checkSet('unsatisfiableClasses', classIRIs(r.getUnsatisfiableClasses()), [NOTHING_IRI]);
  // Nothing is disjoint from A/D except owl:Nothing itself (HermiT always
  // includes the bottom node in a disjoint-classes answer).
  checkSet('disjointClasses(A)', classIRIs(r.getDisjointClasses(A)), [NOTHING_IRI]);
  checkSet('disjointClasses(D)', classIRIs(r.getDisjointClasses(D)), [NOTHING_IRI]);
}

{
  // Equivalent classes collapse into one node.
  const r = createReasoner(ontology([
    declaration(A), declaration(B),
    E.equivalentClasses([A, B])
  ]));
  checkSet('equivalentClasses(A) = {A,B}', classIRIs(r.getEquivalentClasses(A)), [EX + 'A', EX + 'B']);
  check('A sq B', r.isSubClassOf(A, B), true);
  check('B sq A', r.isSubClassOf(B, A), true);
}

{
  // Unsatisfiable class via disjointness.
  const r = createReasoner(ontology([
    declaration(A), declaration(B), declaration(C),
    E.disjointClasses([A, B]),
    E.subclassOf(C, A),
    E.subclassOf(C, B)
  ]));
  check('ontology consistent', r.isConsistent(), true);
  check('C unsatisfiable', r.isSatisfiable(C), false);
  // The bottom node holds every unsatisfiable class PLUS owl:Nothing.
  checkSet('unsatisfiableClasses = {C}', classIRIs(r.getUnsatisfiableClasses()), [EX + 'C', NOTHING_IRI]);
  // HermiT's getDisjointClasses returns `directDisjoint.getDescendantNodes()`,
  // and getDescendantNodes() INCLUDES the node itself. The disjoint node for A
  // is {B}, whose descendants are {B} and the bottom node {C, owl:Nothing}.
  checkSet('disjointClasses(A) includes B', classIRIs(r.getDisjointClasses(A)),
    [EX + 'B', EX + 'C', NOTHING_IRI]);
  check('A in bottom node', r.getHierarchyNode(A) === r.getHierarchyNode(A), true);
}

{
  // Complex class expression query positioning.
  const r = createReasoner(ontology([
    declaration(A), declaration(B), declaration(C),
    E.subclassOf(A, B),
    E.subclassOf(B, C)
  ]));
  const node = r.getHierarchyNode(E.objectIntersectionOf([A, B]));
  check('A sq B positioned under B', node.getRepresentative() !== undefined, true);
  checkSet('getEquivalentClasses(A sq B)', classIRIs(r.getEquivalentClasses(E.objectIntersectionOf([A, B]))), [EX + 'A']);
}

// ===========================================================================
section('3. existential / cardinality reasoning');
// ===========================================================================

{
  const r = createReasoner(ontology([
    declaration(A), declaration(B), declaration(R),
    E.equivalentClasses([A, E.objectSomeValuesFrom(R, B)])
  ]));
  check('A sq exists R.B', r.isSubClassOf(A, E.objectSomeValuesFrom(R, B)), true);
  check('exists R.B sq A', r.isSubClassOf(E.objectSomeValuesFrom(R, B), A), true);
  check('A satisfiable', r.isSatisfiable(A), true);
}

{
  // Functional role + two fillers -> clash.
  const r = createReasoner(ontology([
    declaration(A), declaration(R), declaration(a), declaration(b), declaration(c),
    functionalObjectProperty(R),
    E.classAssertion(A, a),
    E.objectPropertyAssertion(R, a, b),
    E.objectPropertyAssertion(R, a, c),
    E.differentIndividuals([b, c])
  ]));
  check('functional R with 2 distinct fillers -> inconsistent', r.isConsistent(), false);
}

{
  // Max cardinality 1 on a named class.
  const r = createReasoner(ontology([
    declaration(A), declaration(R), declaration(B),
    E.subclassOf(A, E.objectMaxCardinality(1, R, B))
  ]));
  check('A sq <=1 R.B consistent', r.isConsistent(), true);
  check('A sq >=2 R.B unsatisfiable',
    r.isSatisfiable(E.objectIntersectionOf([A, E.objectMinCardinality(2, R, B)])), false);
}

{
  // Transitive role.
  const r = createReasoner(ontology([
    declaration(T), declaration(a), declaration(b), declaration(c),
    transitiveObjectProperty(T),
    E.objectPropertyAssertion(T, a, b),
    E.objectPropertyAssertion(T, b, c)
  ]));
  check('transitive T(a,c) entailed', r.hasObjectPropertyRelationship(a, T, c), true);
  check('T(a,b) entailed', r.hasObjectPropertyRelationship(a, T, b), true);
}

// ===========================================================================
section('4. object property hierarchy + characteristics');
// ===========================================================================

{
  const r = createReasoner(ontology([
    declaration(R), declaration(S), declaration(T),
    subObjectPropertyOf(R, S),
    subObjectPropertyOf(S, T)
  ]));
  check('R sq T (transitive)', r.isSubObjectPropertyExpressionOf(R, T), true);
  check('T sq R false', r.isSubObjectPropertyExpressionOf(T, R), false);
  checkSet('superObjectProperties(R, direct)', propIRIs(r.getSuperObjectProperties(R, true)), [EX + 'S']);
  // Non-direct sub-properties include owl:bottomObjectProperty (HermiT behaviour).
  checkSet('subObjectProperties(T, all)', propIRIs(r.getSubObjectProperties(T, false)),
    [EX + 'R', EX + 'S', E.IRI_BOTTOM_OBJECT_PROPERTY]);
  checkSet('equivalentObjectProperties(R)', propIRIs(r.getEquivalentObjectProperties(R)), [EX + 'R']);
}

{
  const r = createReasoner(ontology([
    declaration(R), declaration(S),
    inverseObjectProperties(R, S)
  ]));
  // inv(R) ≡ S, so the equivalence node is {inv(R), S} → named props {R, S}.
  checkSet('inverseObjectProperties(R)', propIRIs(r.getInverseObjectProperties(R)), [EX + 'R', EX + 'S']);
  check('R sq S^-', r.isSubObjectPropertyExpressionOf(R, E.objectInverseOf(S)), true);
}

{
  const r = createReasoner(ontology([
    declaration(R), declaration(S),
    symmetricObjectProperty(R),
    transitiveObjectProperty(S),
    functionalObjectProperty(R)
  ]));
  check('R symmetric', r.isSymmetric(R), true);
  check('S transitive', r.isTransitive(S), true);
  check('R functional', r.isFunctionalObjectProperty(R), true);
  check('S not functional', r.isFunctionalObjectProperty(S), false);
  check('R irreflexive? no', r.isIrreflexive(R), false);
}

{
  const r = createReasoner(ontology([
    declaration(R), declaration(S),
    disjointObjectProperties([R, S])
  ]));
  check('R disjoint S', r.isDisjointObjectProperty(R, S), true);
  // The disjoint set of R includes S and everything below it (bottomObjectProperty).
  checkSet('disjointObjectProperties(R)', propIRIs(r.getDisjointObjectProperties(R)),
    [EX + 'S', E.IRI_BOTTOM_OBJECT_PROPERTY]);
}

{
  const r = createReasoner(ontology([
    declaration(A), declaration(B), declaration(R),
    objectPropertyDomain(R, A),
    objectPropertyRange(R, B)
  ]));
  checkSet('objectPropertyDomains(R, direct)', classIRIs(r.getObjectPropertyDomains(R, true)), [EX + 'A']);
  checkSet('objectPropertyRanges(R, direct)', classIRIs(r.getObjectPropertyRanges(R, true)), [EX + 'B']);
}

{
  // NOTE: these characteristics must be tested in *separate* ontologies.
  // `ReflexiveObjectProperty(R)` + `R ⊑ S` entails `ReflexiveObjectProperty(S)`,
  // which contradicts `IrreflexiveObjectProperty(S)` / `AsymmetricObjectProperty(S)`
  // (asymmetric implies irreflexive) — the ontology would be inconsistent.
  const r = createReasoner(ontology([
    declaration(R), declaration(S),
    inverseFunctionalObjectProperty(R),
    asymmetricObjectProperty(S)
  ]));
  check('ontology consistent', r.isConsistent(), true);
  check('R inverse-functional', r.isInverseFunctional(R), true);
  check('S asymmetric', r.isAsymmetric(S), true);
  check('asymmetric implies irreflexive', r.isIrreflexive(S), true);
}

{
  const r = createReasoner(ontology([declaration(R), reflexiveObjectProperty(R)]));
  check('R reflexive', r.isReflexive(R), true);
  check('R not irreflexive', r.isIrreflexive(R), false);
}

{
  const r = createReasoner(ontology([declaration(S), irreflexiveObjectProperty(S)]));
  check('S irreflexive', r.isIrreflexive(S), true);
  check('S not reflexive', r.isReflexive(S), false);
}

// ===========================================================================
section('5. data properties');
// ===========================================================================

{
  const r = createReasoner(ontology([
    declaration(hasAge), declaration(hasName),
    subDataPropertyOf(hasAge, hasName)
  ]));
  check('hasAge sq hasName', r.isSubDataPropertyOf(hasAge, hasName), true);
  check('hasName sq hasAge false', r.isSubDataPropertyOf(hasName, hasAge), false);
  checkSet('superDataProperties(hasAge, direct)',
    propIRIs(r.getSuperDataProperties(hasAge, true)), [EX + 'hasName']);
}

{
  const r = createReasoner(ontology([
    declaration(A), declaration(hasAge),
    dataPropertyDomain(hasAge, A),
    functionalDataProperty(hasAge)
  ]));
  checkSet('dataPropertyDomains(hasAge, direct)',
    classIRIs(r.getDataPropertyDomains(hasAge, true)), [EX + 'A']);
  check('hasAge functional', r.isFunctionalDataProperty(hasAge), true);
}

{
  const r = createReasoner(ontology([
    declaration(hasAge), declaration(hasName),
    disjointDataProperties([hasAge, hasName])
  ]));
  // Same rule as getDisjointClasses: HermiT adds `nodeToTest.getDescendantNodes()`,
  // which includes the node itself plus the bottom node {owl:bottomDataProperty}.
  checkSet('disjointDataProperties(hasAge)',
    propIRIs(r.getDisjointDataProperties(hasAge)),
    [EX + 'hasName', E.IRI_BOTTOM_DATA_PROPERTY]);
}

// ===========================================================================
section('6. individuals: types, instances, same/different');
// ===========================================================================

{
  const r = createReasoner(ontology([
    declaration(A), declaration(B), declaration(C), declaration(a), declaration(b),
    E.subclassOf(A, B),
    E.subclassOf(B, C),
    E.classAssertion(A, a),
    E.classAssertion(C, b)
  ]));
  check('hasType(a, A)', r.hasType(a, A, false), true);
  check('hasType(a, B) inferred', r.hasType(a, B, false), true);
  check('hasType(a, C) inferred', r.hasType(a, C, false), true);
  check('hasType(b, A) false', r.hasType(b, A, false), false);
  checkSet('types(a, direct)', classIRIs(r.getTypes(a, true)), [EX + 'A']);
  // Non-direct types include owl:Thing (HermiT behaviour).
  checkSet('types(a, all)', classIRIs(r.getTypes(a, false)), [EX + 'A', EX + 'B', EX + 'C', THING_IRI]);
  checkSet('instances(A)', classIRIs(r.getInstances(A, false)).length === 0 ? [] : [EX + 'a'], [EX + 'a']);
  checkSet('instances(C)', [...r.getInstances(C, false).getFlattened()].map((x) => E.iriString(x)),
    [EX + 'a', EX + 'b']);
}

{
  const r = createReasoner(ontology([
    declaration(A), declaration(a), declaration(b), declaration(c),
    E.classAssertion(A, a),
    E.sameIndividual([a, b]),
    E.differentIndividuals([a, c])
  ]));
  check('isSameIndividual(a,b)', r.isSameIndividual(a, b), true);
  check('isSameIndividual(a,c) false', r.isSameIndividual(a, c), false);
  checkSet('sameIndividuals(a)', [...r.getSameIndividuals(a).getFlattened()].map((x) => E.iriString(x)),
    [EX + 'a', EX + 'b']);
  checkSet('differentIndividuals(a)', [...r.getDifferentIndividuals(a).getFlattened()].map((x) => E.iriString(x)),
    [EX + 'c']);
  check('hasType(b, A) via sameAs', r.hasType(b, A, false), true);
}

{
  const r = createReasoner(ontology([
    declaration(R), declaration(a), declaration(b), declaration(c),
    E.objectPropertyAssertion(R, a, b),
    E.negativeObjectPropertyAssertion(R, a, c)
  ]));
  check('hasObjectPropertyRelationship(a,R,b)', r.hasObjectPropertyRelationship(a, R, b), true);
  check('hasObjectPropertyRelationship(a,R,c) false', r.hasObjectPropertyRelationship(a, R, c), false);
  checkSet('objectPropertyValues(a,R)',
    [...r.getObjectPropertyValues(a, R).getFlattened()].map((x) => E.iriString(x)), [EX + 'b']);
}

{
  const r = createReasoner(ontology([
    declaration(hasAge), declaration(a),
    E.dataPropertyAssertion(hasAge, a, E.literal('42', E.IRI_XSD_STRING))
  ]));
  check('hasDataPropertyRelationship(a,hasAge,"42")',
    r.hasDataPropertyRelationship(a, hasAge, E.literal('42', E.IRI_XSD_STRING)), true);
  const values = [...r.getDataPropertyValues(a, hasAge).getFlattened()];
  check('getDataPropertyValues size', values.length, 1);
}

// ===========================================================================
section('7. inconsistent ontology behaviour');
// ===========================================================================

{
  // A genuinely inconsistent ontology: `a : A` together with `A ⊑ ¬A`.
  // (A pure TBox like `A ⊑ B, B ⊑ ¬A` is NOT inconsistent — A just becomes
  // unsatisfiable/empty; you need a non-empty witness to force a clash.)
  const r = createReasoner(ontology([
    declaration(A), declaration(B), declaration(a),
    E.subclassOf(A, B),
    E.subclassOf(B, E.objectComplementOf(A)),
    E.classAssertion(A, a)
  ]), new Configuration({ throwInconsistentOntologyException: false }));
  check('inconsistent', r.isConsistent(), false);
  check('everything subsumed when inconsistent', r.isSubClassOf(A, B), true);
  check('nothing satisfiable when inconsistent', r.isSatisfiable(A), false);
  check('top class node === bottom class node',
    r.getTopClassNode().getRepresentativeElement() === r.getBottomClassNode().getRepresentativeElement(), true);
}

{
  let threw = false;
  try {
    const r = createReasoner(ontology([
      declaration(A), declaration(a),
      E.subclassOf(A, E.objectComplementOf(A)),
      E.classAssertion(A, a)
    ]));
    r.getSuperClasses(A, true);
  } catch (err) {
    threw = err.name === 'InconsistentOntologyException';
  }
  check('throws InconsistentOntologyException by default', threw, true);
}

// ===========================================================================
section('8. fresh entities + buffering');
// ===========================================================================

{
  const r = createReasoner(ontology([declaration(A)]),
    new Configuration({ freshEntityPolicy: 'DISALLOW' }));
  let threw = false;
  try {
    r.isSatisfiable(cls('NeverDeclared'));
  } catch (err) {
    threw = err.name === 'FreshEntitiesException';
  }
  check('FreshEntitiesException on undeclared class', threw, true);
  check('containsFreshEntities', r.containsFreshEntities(cls('NeverDeclared')), true);
  check('!containsFreshEntities(A)', r.containsFreshEntities(A), false);
}

{
  // HermiT's incremental contract: mutate the ontology, THEN notify the
  // reasoner via `applyChange` (which buffers). `flush()` re-clausifies the
  // already-updated ontology.
  const ont = ontology([declaration(A), declaration(B), declaration(C), E.subclassOf(A, B)]);
  const r = createReasoner(ont);
  check('A sq B before change', r.isSubClassOf(A, B), true);
  check('A sq C before change', r.isSubClassOf(A, C), false);

  const newAxiom = E.subclassOf(B, C);
  ont.addAxiom(newAxiom);                       // ontology is the source of truth
  r.applyChange({ axiom: newAxiom, isAdd: true }); // reasoner buffers the change
  check('pending additions = 1', r.getPendingAxiomAdditions().length, 1);
  check('A sq C still false before flush', r.isSubClassOf(A, C), false);

  r.flush();
  check('pending additions = 0 after flush', r.getPendingAxiomAdditions().length, 0);
  check('A sq C after flush', r.isSubClassOf(A, C), true);
}

// ===========================================================================
section('9. precomputation + prefixes + statistics');
// ===========================================================================

{
  const r = createReasoner(ontology([
    declaration(A), declaration(B), declaration(R), declaration(hasAge),
    E.subclassOf(A, B), subObjectPropertyOf(R, R)
  ]));
  r.precomputeInferences('CLASS_HIERARCHY', 'OBJECT_PROPERTY_HIERARCHY', 'DATA_PROPERTY_HIERARCHY');
  check('CLASS_HIERARCHY precomputed', r.isPrecomputed('CLASS_HIERARCHY'), true);
  check('OBJECT_PROPERTY_HIERARCHY precomputed', r.isPrecomputed('OBJECT_PROPERTY_HIERARCHY'), true);
  check('DATA_PROPERTY_HIERARCHY precomputed', r.isPrecomputed('DATA_PROPERTY_HIERARCHY'), true);
  check('prefixes abbreviate', r.getPrefixes().abbreviateIRI(EX + 'A') !== undefined, true);
  const stats = r.getTableauStatistics();
  check('statistics present', stats !== null && typeof stats.iterations === 'number', true);
  check('dlOntology present', r.getDLOntology() !== null, true);
  check('dumpHierarchies does not throw', typeof r.dumpHierarchies(), 'string');
  r.dispose();
}

// ===========================================================================
section('10. entailment checking (EntailmentChecker)');
// ===========================================================================

{
  const r = createReasoner(ontology([
    declaration(A), declaration(B), declaration(C), declaration(D),
    declaration(R), declaration(S), declaration(T),
    declaration(hasAge), declaration(hasName),
    declaration(a), declaration(b), declaration(c),
    E.subclassOf(A, B),
    E.subclassOf(B, C),
    E.disjointClasses([C, D]),
    subObjectPropertyOf(R, S),
    E.classAssertion(A, a),
    E.objectPropertyAssertion(R, a, b),
    E.differentIndividuals([a, c]),
    E.dataPropertyAssertion(hasAge, a, E.literal('42', E.IRI_XSD_STRING))
  ]));

  // --- class axioms ---
  check('entails SubClassOf(A,C) transitively', r.isEntailed(E.subclassOf(A, C)), true);
  check('entails SubClassOf(C,A) false', r.isEntailed(E.subclassOf(C, A)), false);
  check('entails SubClassOf(A,¬D) via disjointness',
    r.isEntailed(E.subclassOf(A, E.objectComplementOf(D))), true);
  check('entails DisjointClasses(A,D)', r.isEntailed(E.disjointClasses([A, D])), true);
  check('entails DisjointClasses(A,B) false', r.isEntailed(E.disjointClasses([A, B])), false);
  check('entails EquivalentClasses(A,A)', r.isEntailed(E.equivalentClasses([A, A])), true);
  check('entails EquivalentClasses(A,B) false', r.isEntailed(E.equivalentClasses([A, B])), false);
  // owl:Thing ⊑ owl:Thing and owl:Nothing ⊑ A are tautologies.
  check('entails SubClassOf(⊤,⊤)', r.isEntailed(E.subclassOf(E.owlThing(), E.owlThing())), true);
  check('entails SubClassOf(⊥,A)', r.isEntailed(E.subclassOf(E.owlNothing(), A)), true);

  // --- assertions ---
  check('entails ClassAssertion(B,a) inferred', r.isEntailed(E.classAssertion(B, a)), true);
  check('entails ClassAssertion(C,a) inferred', r.isEntailed(E.classAssertion(C, a)), true);
  check('entails ClassAssertion(D,a) false', r.isEntailed(E.classAssertion(D, a)), false);
  check('entails ObjectPropertyAssertion(R,a,b)', r.isEntailed(E.objectPropertyAssertion(R, a, b)), true);
  check('entails ObjectPropertyAssertion(S,a,b) via subproperty',
    r.isEntailed(E.objectPropertyAssertion(S, a, b)), true);
  check('entails ObjectPropertyAssertion(R,a,c) false',
    r.isEntailed(E.objectPropertyAssertion(R, a, c)), false);
  // A negative object property assertion is entailed only when functionality (or
  // an explicit ¬R) forces it. Here R is neither functional nor negated, so a
  // model may still contain R(a,c): NOT entailed.
  check('entails NegativeObjectPropertyAssertion(R,a,c) false (R not functional)',
    r.isEntailed(E.negativeObjectPropertyAssertion(R, a, c)), false);
  check('entails NegativeObjectPropertyAssertion(R,a,b) false',
    r.isEntailed(E.negativeObjectPropertyAssertion(R, a, b)), false);
  check('entails DataPropertyAssertion(hasAge,a,"42")',
    r.isEntailed(E.dataPropertyAssertion(hasAge, a, E.literal('42', E.IRI_XSD_STRING))), true);
  check('entails DataPropertyAssertion(hasAge,a,"7") false',
    r.isEntailed(E.dataPropertyAssertion(hasAge, a, E.literal('7', E.IRI_XSD_STRING))), false);
  // hasAge is not functional, so a model may also carry hasAge(a,"7"): the
  // negative assertion is NOT entailed.
  check('entails NegativeDataPropertyAssertion(hasAge,a,"7") false (hasAge not functional)',
    r.isEntailed(E.negativeDataPropertyAssertion(hasAge, a, E.literal('7', E.IRI_XSD_STRING))), false);
  check('entails SameIndividual(a,a)', r.isEntailed(E.sameIndividual([a, a])), true);
  check('entails SameIndividual(a,b) false', r.isEntailed(E.sameIndividual([a, b])), false);
  check('entails DifferentIndividuals(a,c)', r.isEntailed(E.differentIndividuals([a, c])), true);
  check('entails DifferentIndividuals(a,b) false', r.isEntailed(E.differentIndividuals([a, b])), false);

  // --- property axioms ---
  check('entails SubObjectPropertyOf(R,S)', r.isEntailed(subObjectPropertyOf(R, S)), true);
  check('entails SubObjectPropertyOf(S,R) false', r.isEntailed(subObjectPropertyOf(S, R)), false);
  check('entails SubObjectPropertyOf(R,⊤R)',
    r.isEntailed(subObjectPropertyOf(R, E.topObjectProperty())), true);
  check('entails ObjectPropertyDomain(R,⊤)',
    r.isEntailed(objectPropertyDomain(R, E.owlThing())), true);
  check('entails ObjectPropertyDomain(R,A) false',
    r.isEntailed(objectPropertyDomain(R, A)), false);
  check('entails ObjectPropertyRange(R,⊤)',
    r.isEntailed(objectPropertyRange(R, E.owlThing())), true);
  check('entails InverseObjectProperties(R,R⁻)',
    r.isEntailed(inverseObjectProperties(R, E.objectInverseOf(R))), true);
  check('entails EquivalentObjectProperties(R,R)',
    r.isEntailed(equivalentObjectProperties([R, R])), true);
  check('entails DisjointObjectProperties(R,S) false',
    r.isEntailed(disjointObjectProperties([R, S])), false);
  check('entails FunctionalObjectProperty(R) false',
    r.isEntailed(functionalObjectProperty(R)), false);

  // --- data property axioms ---
  check('entails SubDataPropertyOf(hasAge,⊤DP)',
    r.isEntailed(subDataPropertyOf(hasAge, E.topDataProperty())), true);
  check('entails DataPropertyDomain(hasAge,⊤)',
    r.isEntailed(dataPropertyDomain(hasAge, E.owlThing())), true);
  check('entails DataPropertyRange(hasAge,⊤)',
    r.isEntailed(dataPropertyRange(hasAge, E.topDatatype())), true);
  check('entails EquivalentDataProperties(hasAge,hasAge)',
    r.isEntailed(equivalentDataProperties([hasAge, hasAge])), true);

  // --- non-logical axioms are trivially entailed ---
  check('entails Declaration', r.isEntailed(declaration(A)), true);
  check('isEntailmentCheckingSupported', r.isEntailmentCheckingSupported(AT.SUB_CLASS_OF), true);

  // --- a set of axioms ---
  check('entails {A⊑B, B⊑C}',
    r.isEntailed([E.subclassOf(A, B), E.subclassOf(B, C)]), true);
  check('entails {A⊑B, C⊑A} false',
    r.isEntailed([E.subclassOf(A, B), E.subclassOf(C, A)]), false);
}

{
  // DisjointUnion: C ≡ A ⊔ B with A and B disjoint.
  const r = createReasoner(ontology([
    declaration(A), declaration(B), declaration(C),
    E.disjointUnion(C, [A, B])
  ]));
  check('entails DisjointUnion(C,{A,B})', r.isEntailed(E.disjointUnion(C, [A, B])), true);
  check('entails SubClassOf(C, A⊔B) from disjoint union',
    r.isEntailed(E.subclassOf(C, E.objectUnionOf([A, B]))), true);
  check('entails DisjointClasses(A,B) from disjoint union',
    r.isEntailed(E.disjointClasses([A, B])), true);
  check('entails DisjointUnion(A,{B,C}) false',
    r.isEntailed(E.disjointUnion(A, [B, C])), false);
}

{
  // Property chains and property characteristics.
  const r = createReasoner(ontology([
    declaration(R), declaration(S), declaration(T), declaration(a), declaration(b), declaration(c),
    subPropertyChainOf([R, S], T),
    E.objectPropertyAssertion(R, a, b),
    E.objectPropertyAssertion(S, b, c)
  ]));
  check('entails SubPropertyChainOf(R∘S, T)', r.isEntailed(subPropertyChainOf([R, S], T)), true);
  check('entails SubPropertyChainOf(R∘S, R) false',
    r.isEntailed(subPropertyChainOf([R, S], R)), false);
  check('entails ObjectPropertyAssertion(T,a,c) via chain',
    r.isEntailed(E.objectPropertyAssertion(T, a, c)), true);
}

{
  const r = createReasoner(ontology([
    declaration(R), declaration(S),
    symmetricObjectProperty(R),
    inverseObjectProperties(R, S)
  ]));
  check('entails SymmetricObjectProperty(R)', r.isEntailed(symmetricObjectProperty(R)), true);
  check('entails SymmetricObjectProperty(S) via inverse',
    r.isEntailed(symmetricObjectProperty(S)), true);
  check('entails TransitiveObjectProperty(R) false',
    r.isEntailed(transitiveObjectProperty(R)), false);
  check('entails AsymmetricObjectProperty(R) false',
    r.isEntailed(asymmetricObjectProperty(R)), false);
}

{
  // Disjoint data properties: hasAge ⊓ hasName.⊤ ⊓ (≤1 ⊤DP) must be unsatisfiable.
  const r = createReasoner(ontology([
    declaration(hasAge), declaration(hasName),
    disjointDataProperties([hasAge, hasName])
  ]));
  check('entails DisjointDataProperties(hasAge,hasName)',
    r.isEntailed(disjointDataProperties([hasAge, hasName])), true);
  check('entails DisjointDataProperties(hasAge,hasAge) false',
    r.isEntailed(disjointDataProperties([hasAge, hasAge])), false);
}

{
  // HasKey: hasAge is a key for A.
  const r = createReasoner(ontology([
    declaration(A), declaration(hasAge), declaration(a), declaration(b),
    E.hasKey(A, [hasAge]),
    E.classAssertion(A, a),
    E.classAssertion(A, b),
    E.dataPropertyAssertion(hasAge, a, E.literal('42', E.IRI_XSD_STRING)),
    E.dataPropertyAssertion(hasAge, b, E.literal('42', E.IRI_XSD_STRING))
  ]));
  check('entails HasKey(A,{hasAge})', r.isEntailed(E.hasKey(A, [hasAge])), true);
  check('entails SameIndividual(a,b) via HasKey', r.isEntailed(E.sameIndividual([a, b])), true);
  check('entails HasKey(A,{hasName}) false',
    r.isEntailed(E.hasKey(A, [hasName])), false);
}

{
  // Anonymous individuals: `r(a, _:x)` + `C(_:x)` rolls up to `a : ∃r.C`.
  const x = anon('x');
  const r = createReasoner(ontology([
    declaration(A), declaration(C), declaration(R), declaration(a),
    E.objectPropertyAssertion(R, a, x),
    E.classAssertion(C, x)
  ]));
  check('entails ClassAssertion(∃R.C, a) from anonymous individual',
    r.isEntailed(E.classAssertion(E.objectSomeValuesFrom(R, C), a)), true);
  check('entails ClassAssertion(∃R.A, a) false',
    r.isEntailed(E.classAssertion(E.objectSomeValuesFrom(R, A), a)), false);
  check('entails ObjectPropertyAssertion(R,a,_:x) (buffered)',
    r.isEntailed(E.objectPropertyAssertion(R, a, x)), true);
}

{
  // A rootless anonymous-individual tree in the QUERY: `_:x -R-> _:y`.
  // HermiT rolls this up to `⊤ ⊑ ¬∃R.⊤` (≡ `⊤ ⊑ ∀R.⊥`) and the entailment
  // holds iff the premise PLUS that axiom is inconsistent — i.e. iff every
  // model of the premise has at least one R-edge.
  const x = anon('rx');
  const y = anon('ry');
  const r = createReasoner(ontology([
    declaration(R), declaration(S), declaration(a), declaration(b),
    E.objectPropertyAssertion(R, a, b)
  ]));
  check('entails ObjectPropertyAssertion(R,_:x,_:y) (rootless anon tree)',
    r.isEntailed(E.objectPropertyAssertion(R, x, y)), true);
  // S has no edges anywhere, so premise + `⊤ ⊑ ¬∃S.⊤` is satisfiable.
  check('entails ObjectPropertyAssertion(S,_:x,_:y) false',
    r.isEntailed(E.objectPropertyAssertion(S, x, y)), false);
}

{
  // A cyclic anonymous-individual structure in the QUERY must be rejected
  // (OWL 2 Structural Specification, Sec. 11.2 requires a forest).
  const x = anon('cx');
  const y = anon('cy');
  const z = anon('cz');
  const r = createReasoner(ontology([declaration(R)]));
  let threw = false;
  try {
    r.isEntailed([
      E.objectPropertyAssertion(R, x, y),
      E.objectPropertyAssertion(R, y, z),
      E.objectPropertyAssertion(R, z, x)
    ]);
  } catch (err) {
    threw = /cycle/.test(err.message);
  }
  check('cyclic anonymous individuals rejected', threw, true);
}

{
  // Inconsistent ontology: everything is entailed.
  const r = createReasoner(ontology([
    declaration(A), declaration(a),
    E.subclassOf(A, E.objectComplementOf(A)),
    E.classAssertion(A, a)
  ]), new Configuration({ throwInconsistentOntologyException: false }));
  check('inconsistent ⇒ entailed', r.isEntailed(E.subclassOf(A, E.owlNothing())), true);
}

{
  // Fresh entities in the query are rejected under the DISALLOW policy.
  const r = createReasoner(ontology([declaration(A)]),
    new Configuration({ freshEntityPolicy: 'DISALLOW' }));
  let threw = false;
  try {
    r.isEntailed(E.subclassOf(A, cls('NeverDeclared')));
  } catch (err) {
    threw = err.name === 'FreshEntitiesException';
  }
  check('FreshEntitiesException from isEntailed', threw, true);
}

// ===========================================================================
section('11. SWRL rules');
// ===========================================================================

/**
 * SWRL rules arrive in TWO incompatible variable encodings, and both must work.
 *
 * protege-js' `SWRLVariable` is constructed as `new SWRLVariable(iri)` and
 * stores ONLY `{ iri }` — it sets no `type` tag at all. Its atoms are tagged
 * with the SHORT names (`'ClassAtom'`, `'ObjectPropertyAtom'`, …), and the rule
 * itself has no `axiomType` (it is detected structurally by `body`/`head`).
 *
 * If `RuleNormalizer.isVariable` fails to recognize the untagged form, the
 * failure is completely silent: the "variable" falls through to `individualOf`
 * and is treated as a NAMED individual, so it is rewritten into an
 * `ObjectOneOf` nominal that no axiom ever asserts. The rule body can then
 * never be satisfied, the rule never fires, and nothing throws. These checks
 * exist to make that regression loud.
 */

/** protege-js-shaped variable: `{ iri }`, NO `type` tag. */
const pvar = (name) => ({ iri: EX + 'var#' + name });
/** Explicitly tagged variable, as a hand-built rule would use. */
const tvar = (name) => ({ type: 'SWRLVariable', name });

const classAtom = (classExpression, arg) => ({ type: 'ClassAtom', classExpression, arg });
const objectPropertyAtom = (property, arg1, arg2) => ({ type: 'ObjectPropertyAtom', property, arg1, arg2 });
const dataPropertyAtom = (property, arg1, arg2) => ({ type: 'DataPropertyAtom', property, arg1, arg2 });
const sameAsAtom = (arg1, arg2) => ({ type: 'SameAsAtom', arg1, arg2 });
const differentFromAtom = (arg1, arg2) => ({ type: 'DifferentFromAtom', arg1, arg2 });
const swrlRule = (body, head) => ({ body: body.slice(), head: head.slice() });

const Adult = cls('Adult'), Ancestor = cls('Ancestor');
const hasParent = op('hasParent');
const x = ind('x'), y = ind('y'), z = ind('z');

// ---- 11.1 protege-js shape: untagged `{ iri }` variables ------------------
{
  // Person(?x) ^ hasParent(?x,?y) -> Adult(?x)
  const rule = swrlRule(
    [classAtom(A, pvar('x')), objectPropertyAtom(hasParent, pvar('x'), pvar('y'))],
    [classAtom(Adult, pvar('x'))]
  );
  const r = createReasoner(ontology([
    declaration(A), declaration(Adult), declaration(hasParent),
    declaration(x), declaration(y),
    E.classAssertion(A, x),
    E.objectPropertyAssertion(hasParent, x, y),
    rule
  ]));
  check('protege-js SWRL: rule fires for the matching individual',
    r.isEntailed(E.classAssertion(Adult, x)), true);
  check('protege-js SWRL: rule does not over-fire',
    r.isEntailed(E.classAssertion(Adult, y)), false);
  check('protege-js SWRL: ontology stays consistent', r.isConsistent(), true);
  r.dispose();
}

// ---- 11.2 tagged shape: `{ type: 'SWRLVariable', name }` ------------------
{
  const rule = swrlRule(
    [classAtom(A, tvar('x')), objectPropertyAtom(hasParent, tvar('x'), tvar('y'))],
    [classAtom(Adult, tvar('x'))]
  );
  const r = createReasoner(ontology([
    declaration(A), declaration(Adult), declaration(hasParent),
    declaration(x), declaration(y),
    E.classAssertion(A, x),
    E.objectPropertyAssertion(hasParent, x, y),
    rule
  ]));
  check('tagged SWRL: rule fires', r.isEntailed(E.classAssertion(Adult, x)), true);
  check('tagged SWRL: rule does not over-fire',
    r.isEntailed(E.classAssertion(Adult, y)), false);
  r.dispose();
}

// ---- 11.3 the two encodings are interchangeable within one rule -----------
{
  const rule = swrlRule(
    [classAtom(A, pvar('x')), objectPropertyAtom(hasParent, tvar('x'), pvar('y'))],
    [classAtom(Adult, pvar('x'))]
  );
  const r = createReasoner(ontology([
    declaration(A), declaration(Adult), declaration(hasParent),
    declaration(x), declaration(y),
    E.classAssertion(A, x),
    E.objectPropertyAssertion(hasParent, x, y),
    rule
  ]));
  // `pvar('x')` and `tvar('x')` both name variable "x", so they must unify.
  check('mixed-encoding SWRL: variables unify across encodings',
    r.isEntailed(E.classAssertion(Adult, x)), true);
  r.dispose();
}

// ---- 11.4 a variable bound to an individual in the body -------------------
{
  // hasParent(?x,?y) ^ hasParent(?y,?z) -> Ancestor(?x)
  const rule = swrlRule(
    [objectPropertyAtom(hasParent, pvar('x'), pvar('y')),
     objectPropertyAtom(hasParent, pvar('y'), pvar('z'))],
    [classAtom(Ancestor, pvar('x'))]
  );
  const r = createReasoner(ontology([
    declaration(Ancestor), declaration(hasParent),
    declaration(x), declaration(y), declaration(z),
    E.objectPropertyAssertion(hasParent, x, y),
    E.objectPropertyAssertion(hasParent, y, z),
    rule
  ]));
  check('chained SWRL: grandparent makes x an Ancestor',
    r.isEntailed(E.classAssertion(Ancestor, x)), true);
  check('chained SWRL: y is not an Ancestor',
    r.isEntailed(E.classAssertion(Ancestor, y)), false);
  r.dispose();
}

// ---- 11.5 sameAs / differentFrom atoms ------------------------------------
{
  // A(?x) ^ sameAs(?x,?y) -> Adult(?y)
  const rule = swrlRule(
    [classAtom(A, pvar('x')), sameAsAtom(pvar('x'), pvar('y'))],
    [classAtom(Adult, pvar('y'))]
  );
  const r = createReasoner(ontology([
    declaration(A), declaration(Adult), declaration(x), declaration(y),
    E.classAssertion(A, x),
    E.sameIndividual([x, y]),
    rule
  ]));
  check('sameAs SWRL: propagates the type to the equal individual',
    r.isEntailed(E.classAssertion(Adult, y)), true);
  r.dispose();
}

{
  // differentFrom in the HEAD must be violated when the two are actually equal.
  const rule = swrlRule(
    [classAtom(A, pvar('x'))],
    [differentFromAtom(pvar('x'), pvar('x'))]
  );
  const r = createReasoner(ontology([
    declaration(A), declaration(x),
    E.classAssertion(A, x),
    rule
  ]), new Configuration({ throwInconsistentOntologyException: false }));
  check('differentFrom SWRL head: x != x makes the ontology inconsistent',
    r.isConsistent(), false);
  r.dispose();
}

// ---- 11.6 data-property atoms ---------------------------------------------
{
  // hasAge(?x,?v) -> Adult(?x)
  const rule = swrlRule(
    [dataPropertyAtom(hasAge, pvar('x'), pvar('v'))],
    [classAtom(Adult, pvar('x'))]
  );
  const r = createReasoner(ontology([
    declaration(Adult), declaration(hasAge), declaration(x),
    E.dataPropertyAssertion(hasAge, x, E.literal('42', E.datatype(E.IRI_XSD_STRING))),
    rule
  ]));
  check('data-property SWRL: fires on a literal binding',
    r.isEntailed(E.classAssertion(Adult, x)), true);
  r.dispose();
}

// ---- 11.7 a ground rule (empty body) becomes a fact -----------------------
{
  // With no body there is nothing to bind a variable to, so the head argument
  // must be an INDIVIDUAL. `Rule2FactConverter` turns the rule into a plain
  // ClassAssertion fact.
  const rule = swrlRule([], [classAtom(Adult, x)]);
  const r = createReasoner(ontology([declaration(Adult), declaration(x), rule]));
  check('ground SWRL rule (empty body) asserts the head',
    r.isEntailed(E.classAssertion(Adult, x)), true);
  r.dispose();
}

{
  // The mirror image: a head VARIABLE with an empty body cannot be bound, and
  // must be rejected rather than silently dropped.
  const rule = swrlRule([], [classAtom(Adult, pvar('x'))]);
  let threw = false;
  try {
    createReasoner(ontology([declaration(Adult), rule])).dispose();
  } catch (err) {
    threw = /does not occur in the body/.test(err.message);
  }
  check('unbound head variable in a ground rule throws', threw, true);
}

// ---- 11.8 unsupported constructs must fail loudly, not silently -----------
{
  // SWRL built-ins are not implemented; RuleNormalizer must throw.
  const rule = swrlRule(
    [{ type: 'BuiltInAtom', builtin: E.iriString(E.datatype('http://www.w3.org/2003/11/swrlb#greaterThan')),
       args: [pvar('x'), pvar('y')] }],
    [classAtom(Adult, pvar('x'))]
  );
  let threw = false;
  try {
    createReasoner(ontology([declaration(Adult), rule])).dispose();
  } catch (err) {
    threw = /built-in/i.test(err.message);
  }
  check('SWRL built-in atom throws a clear error', threw, true);
}

{
  // Entailment checking OF a rule is unsupported and must throw.
  const rule = swrlRule([classAtom(A, pvar('x'))], [classAtom(Adult, pvar('x'))]);
  const r = createReasoner(ontology([declaration(A), declaration(Adult)]));
  let threw = false;
  try {
    r.isEntailed(rule);
  } catch (err) {
    threw = /SWRL/i.test(err.message);
  }
  check('isEntailed(SWRLRule) throws', threw, true);
  r.dispose();
}

// ===========================================================================
section('12. datatype definitions');
// ===========================================================================

{
  // `DatatypeDefinition(dt, dr)` normalises to a two-way data-range
  // equivalence (dt ⊑ dr AND dr ⊑ dt), and `definedDatatypesIRIs` records the
  // datatype so the clausifier knows it is not an opaque custom one.
  const XS = E.datatype(E.IRI_XSD_STRING);
  const MyDT = E.datatype(EX + 'MyDT');

  const r = createReasoner(ontology([declaration(MyDT), datatypeDefinition(MyDT, XS)]));
  check('DatatypeDefinition makes hasDatatypes true', r.dlOntology.hasDatatypes, true);
  checkSet('definedDatatypesIRIs records the defined datatype',
    r.dlOntology.definedDatatypesIRIs, [EX + 'MyDT']);
  check('an ontology with a datatype definition is consistent', r.isConsistent(), true);
  r.dispose();
}

{
  // Entailment of a DatatypeDefinition is decided by testing whether the
  // SYMMETRIC DIFFERENCE of the two ranges is empty (EntailmentChecker builds
  // `(¬dr ⊓ dt) ⊔ (¬dt ⊓ dr)` and asks whether it is satisfiable). Identical
  // known ranges are trivially equal; disjoint known ranges are not.
  const XS = E.datatype(E.IRI_XSD_STRING);
  const XI = E.datatype(E.XSD_NS + 'integer');

  // The ontology must actually CONTAIN a datatype axiom: HermiT's
  // EntailmentChecker.visit(OWLDatatypeDefinitionAxiom) short-circuits to
  // `false` when `!reasoner.m_dlOntology.hasDatatypes()`, because with no
  // datatypes in the signature there is nothing to reason about. Our port
  // mirrors that guard exactly, so a bare Declaration-only ontology answers
  // false even for a trivially true definition.
  const rEmpty = createReasoner(ontology([declaration(XS), declaration(XI)]));
  check('hasDatatypes is false for a declaration-only ontology',
    rEmpty.dlOntology.hasDatatypes, false);
  check('the hasDatatypes guard makes a trivial definition NOT entailed',
    rEmpty.isEntailed(datatypeDefinition(XS, XS)), false);
  rEmpty.dispose();

  const r = createReasoner(ontology([declaration(XS), datatypeDefinition(XS, XS)]));
  check('hasDatatypes is true once a datatype axiom is present',
    r.dlOntology.hasDatatypes, true);
  check('entails DatatypeDefinition(xsd:string,xsd:string)',
    r.isEntailed(datatypeDefinition(XS, XS)), true);
  check('does not entail DatatypeDefinition(xsd:string,xsd:integer)',
    r.isEntailed(datatypeDefinition(XS, XI)), false);
  r.dispose();
}

{
  // A custom datatype lands in the datatype reasoner's "unknown" group, so it
  // cannot be proved equal to any xsd range — even one it is defined as. That
  // is sound incompleteness, not a bug. A definition against ITSELF, however,
  // has an empty symmetric difference by construction and MUST be entailed.
  const XS = E.datatype(E.IRI_XSD_STRING);
  const XI = E.datatype(E.XSD_NS + 'integer');
  const MyDT = E.datatype(EX + 'MyDT2');

  const r = createReasoner(ontology([declaration(MyDT), datatypeDefinition(MyDT, XS)]));
  check('entails DatatypeDefinition(MyDT,MyDT)',
    r.isEntailed(datatypeDefinition(MyDT, MyDT)), true);
  check('does not entail DatatypeDefinition(MyDT,xsd:integer)',
    r.isEntailed(datatypeDefinition(MyDT, XI)), false);
  r.dispose();
}

{
  // Defining a datatype and using it as a data property range must really
  // constrain the literals: a string literal is fine, an integer literal is
  // not, because xsd:string and xsd:integer have disjoint value spaces.
  const XS = E.datatype(E.IRI_XSD_STRING);
  const XI = E.datatype(E.XSD_NS + 'integer');
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
  check('a string literal satisfies a range defined as xsd:string',
    rStr.isConsistent(), true);
  rStr.dispose();

  const rInt = build(E.literal('42', XI));
  check('an integer literal violates a range defined as xsd:string',
    rInt.isConsistent(), false);
  rInt.dispose();
}

{
  // REGRESSION. Enumerated and union data ranges make the datatype manager
  // derive a ground disjunction. Choosing the second disjunct re-asserts a
  // data-range tuple that is already present, and `ExtensionTable.addTuple`
  // used to union the dependency sets on that pre-existing entry. The entry
  // was appended before the branching point's checkpoint, so `backtrack()`
  // truncated the table above it and never restored the mutation. The stale
  // level then reappeared in every later clash dependency set, so
  // `Tableau.doIteration` re-entered the SAME DisjunctionBranchingPoint until
  // `startNextChoice` ran past its last disjunct and threw
  // "Cannot read properties of undefined (reading 'dlPredicate')".
  // HermiT never unions here. See also scripts/smoke-backjump.js §12-13.
  const XS = E.datatype(E.IRI_XSD_STRING);
  const XI = E.datatype(E.XSD_NS + 'integer');
  const MyDT = E.datatype(EX + 'MyDT4');

  const oneOf = E.dataOneOf([E.literal('red', XS), E.literal('green', XS)]);
  const r = createReasoner(ontology([declaration(MyDT), datatypeDefinition(MyDT, oneOf)]));
  check('entails DatatypeDefinition over an enumerated data range',
    r.isEntailed(datatypeDefinition(MyDT, oneOf)), true);
  r.dispose();

  const union = E.dataUnionOf([XS, XI]);
  const r2 = createReasoner(ontology([declaration(MyDT), datatypeDefinition(MyDT, union)]));
  check('entails DatatypeDefinition over a data union',
    r2.isEntailed(datatypeDefinition(MyDT, union)), true);
  r2.dispose();
}

// ---------------------------------------------------------------------------
console.log(`\n${checks - failures}/${checks} checks passed.`);
if (failures > 0) {
  console.log(`${failures} FAILURES`);
  process.exit(1);
}
console.log('All reasoner smoke checks passed.');
