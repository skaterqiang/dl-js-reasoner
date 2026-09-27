'use strict';

// ---------------------------------------------------------------------------
// examples/demo.js — a self-contained tour of DL-JS-REASONER.
//
// Builds a small "family" ontology in memory (no files, no network), then
// exercises the reasoner: consistency, satisfiability, subsumption,
// classification, realisation, property characteristics, disjointness and
// arbitrary axiom entailment. Finally it loads a real ontology (bfo.owl) via
// protege-js if that package is available.
//
// Run with:  node examples/demo.js
// ---------------------------------------------------------------------------

const {
  createReasoner, E, reasonerFor, REASONER_NAME, REASONER_VERSION
} = require('../src/index');

const EX = 'http://example.org/family#';
const AT = E.AxiomType;

// ---- entity shorthands ----------------------------------------------------
const cls = (n) => E.owlClass(EX + n);
const op = (n) => E.objectProperty(EX + n);
const dp = (n) => E.dataProperty(EX + n);
const ind = (n) => E.namedIndividual(EX + n);
const decl = (entity) => ({ axiomType: AT.DECLARATION, entity });
/** Strip the demo and OWL namespaces so printed IRIs stay readable. */
const short = (x) => String(E.iriString(x)).replace(EX, '').replace(E.OWL_NS, 'owl:');

// ---- a tiny family ontology ----------------------------------------------
//
//   Person ⊑ ⊤
//   Man ⊑ Person,  Woman ⊑ Person,  Man ⊓ Woman ⊑ ⊥   (disjoint)
//   Parent ≡ Person ⊓ ∃hasChild.Person
//   Father ≡ Man ⊓ Parent
//   Mother ≡ Woman ⊓ Parent
//   hasChild ⊑ hasDescendant,  hasParent ⊑ hasAncestor
//   hasParent ≡ hasChild⁻
//   Transitive(hasAncestor)
//   Functional(hasBiologicalMother)
//   ABox:  john : Man,  mary : Woman,  sue : Woman,
//          hasChild(john, sue),  hasChild(mary, sue),
//          hasBiologicalMother(sue, mary),  hasAge(sue, "30")
//
// `sue : Woman` matters: without it sue is only known to be a ⊤, so
// `∃hasChild.Person` would NOT be satisfied for john or mary and neither would
// be realised as a Parent. That is correct open-world reasoning, but it makes
// for a dull demo.
//
const Person = cls('Person'), Man = cls('Man'), Woman = cls('Woman');
const Parent = cls('Parent'), Father = cls('Father'), Mother = cls('Mother');
const hasChild = op('hasChild'), hasDescendant = op('hasDescendant');
const hasParent = op('hasParent'), hasAncestor = op('hasAncestor');
const hasBioMother = op('hasBiologicalMother');
const hasAge = dp('hasAge');
const john = ind('john'), mary = ind('mary'), sue = ind('sue');

const axioms = [
  decl(Person), decl(Man), decl(Woman), decl(Parent), decl(Father), decl(Mother),
  decl(hasChild), decl(hasDescendant), decl(hasParent), decl(hasAncestor),
  decl(hasBioMother), decl(hasAge), decl(john), decl(mary), decl(sue),

  E.subclassOf(Man, Person),
  E.subclassOf(Woman, Person),
  E.disjointClasses([Man, Woman]),

  // Parent ≡ Person ⊓ ∃hasChild.Person
  E.equivalentClasses([
    Parent,
    E.objectIntersectionOf([Person, E.objectSomeValuesFrom(hasChild, Person)])
  ]),
  // Father ≡ Man ⊓ Parent ; Mother ≡ Woman ⊓ Parent
  E.equivalentClasses([Father, E.objectIntersectionOf([Man, Parent])]),
  E.equivalentClasses([Mother, E.objectIntersectionOf([Woman, Parent])]),

  { axiomType: AT.SUB_OBJECT_PROPERTY_OF, subProperty: hasChild, superProperty: hasDescendant },
  { axiomType: AT.SUB_OBJECT_PROPERTY_OF, subProperty: hasParent, superProperty: hasAncestor },
  { axiomType: AT.INVERSE_OBJECT_PROPERTIES,
    firstProperty: hasParent, secondProperty: hasChild,
    property1: hasParent, property2: hasChild },
  { axiomType: AT.TRANSITIVE_OBJECT_PROPERTY, property: hasAncestor },
  { axiomType: AT.FUNCTIONAL_OBJECT_PROPERTY, property: hasBioMother },

  E.classAssertion(Man, john),
  E.classAssertion(Woman, mary),
  E.classAssertion(Woman, sue),
  E.objectPropertyAssertion(hasChild, john, sue),
  E.objectPropertyAssertion(hasChild, mary, sue),
  E.objectPropertyAssertion(hasBioMother, sue, mary),
  E.dataPropertyAssertion(hasAge, sue, E.literal('30', E.datatype(E.IRI_XSD_STRING)))
].filter(Boolean);

function rule(title) {
  console.log(`\n${'='.repeat(70)}\n${title}\n${'='.repeat(70)}`);
}
function show(label, value) {
  console.log(`  ${label.padEnd(46)} ${value}`);
}

rule(`${REASONER_NAME} v${REASONER_VERSION} — family ontology demo`);

const reasoner = createReasoner(
  { getAxioms: () => axioms.slice(), getOntologyID: () => ({ ontologyIRI: EX, isAnonymous: () => false }) },
  { throwInconsistentOntologyException: false }
);

// ---- consistency ----------------------------------------------------------
rule('1. Consistency');
show('isConsistent()', reasoner.isConsistent());

// ---- satisfiability -------------------------------------------------------
rule('2. Class-expression satisfiability');
show('isSatisfiable(Man)', reasoner.isSatisfiable(Man));
show('isSatisfiable(Woman)', reasoner.isSatisfiable(Woman));
show('isSatisfiable(Father)', reasoner.isSatisfiable(Father));
show('isSatisfiable(Man ⊓ Woman)',
  reasoner.isSatisfiable(E.objectIntersectionOf([Man, Woman])));
show('isSatisfiable(∃hasChild.Person)',
  reasoner.isSatisfiable(E.objectSomeValuesFrom(hasChild, Person)));

// ---- subsumption ----------------------------------------------------------
rule('3. Subsumption');
show('Man ⊑ Person', reasoner.isSubClassOf(Man, Person));
show('Father ⊑ Parent', reasoner.isSubClassOf(Father, Parent));
show('Father ⊑ Man', reasoner.isSubClassOf(Father, Man));
show('Father ⊑ Woman', reasoner.isSubClassOf(Father, Woman));
show('Parent ⊑ Person', reasoner.isSubClassOf(Parent, Person));

// ---- classification -------------------------------------------------------
rule('4. Classification (direct superclasses)');
reasoner.precomputeInferences('CLASS_HIERARCHY');
for (const c of [Man, Woman, Father, Mother, Parent]) {
  const supers = [...reasoner.getSuperClasses(c, true).getFlattened()]
    .map(short).filter((s) => s !== 'Thing').sort();
  show(`super(${short(c)})`, supers.length ? supers.join(', ') : '(only owl:Thing)');
}
show('unsatisfiable classes',
  [...reasoner.getUnsatisfiableClasses().getEntities()].map(short).join(', ') || '(none)');

// ---- realisation ----------------------------------------------------------
rule('5. Realisation (individual types)');
for (const i of [john, mary, sue]) {
  const types = [...reasoner.getTypes(i, true).getFlattened()].map(short).sort();
  show(`types(${short(i)})`, types.join(', '));
}
show('instances(Parent)',
  [...reasoner.getInstances(Parent, false).getFlattened()].map(short).sort().join(', '));
show('instances(Father)',
  [...reasoner.getInstances(Father, false).getFlattened()].map(short).sort().join(', ') || '(none)');
show('instances(Mother)',
  [...reasoner.getInstances(Mother, false).getFlattened()].map(short).sort().join(', ') || '(none)');

// ---- property queries -----------------------------------------------------
rule('6. Object/data property queries');
show('hasChild(john, sue)', reasoner.hasObjectPropertyRelationship(john, hasChild, sue));
show('hasChild(sue, john)  [not symmetric]',
  reasoner.hasObjectPropertyRelationship(sue, hasChild, john));
show('hasParent ⊑ hasAncestor',
  reasoner.isSubObjectPropertyExpressionOf(hasParent, hasAncestor));
show('hasChild ⊑ hasDescendant',
  reasoner.isSubObjectPropertyExpressionOf(hasChild, hasDescendant));
show('isTransitive(hasAncestor)', reasoner.isTransitive(hasAncestor));
show('isFunctional(hasBioMother)', reasoner.isFunctional(hasBioMother));
show('isFunctional(hasChild)', reasoner.isFunctional(hasChild));
show('hasAge values(sue)',
  [...reasoner.getDataPropertyValues(sue, hasAge).getFlattened()]
    .map((l) => `"${l.lexicalValue}"`).join(', '));

// ---- entailment -----------------------------------------------------------
rule('7. Axiom entailment');
show('⊨ Father ⊑ Man', reasoner.isEntailed(E.subclassOf(Father, Man)));
show('⊨ Father ⊑ Woman', reasoner.isEntailed(E.subclassOf(Father, Woman)));
show('⊨ DisjointClasses(Man, Woman)', reasoner.isEntailed(E.disjointClasses([Man, Woman])));
show('⊨ ClassAssertion(Parent, john)', reasoner.isEntailed(E.classAssertion(Parent, john)));
show('⊨ ClassAssertion(Father, john)', reasoner.isEntailed(E.classAssertion(Father, john)));
show('⊨ SameIndividual(john, mary)', reasoner.isEntailed(E.sameIndividual([john, mary])));
show('⊨ hasChild ⊑ hasDescendant',
  reasoner.isEntailed({ axiomType: AT.SUB_OBJECT_PROPERTY_OF, subProperty: hasChild, superProperty: hasDescendant }));

reasoner.dispose();

// ---- real ontology via protege-js (optional) ------------------------------
rule('8. Real ontology (bfo.owl via protege-js)');
try {
  const path = require('path');
  const protege = require('@skaterqiang/protege-js');
  const file = path.resolve(__dirname, '../../protege-js/sample/ontologies/bfo.owl');
  const ont = new protege.OntologyLoader().loadFromFile(file);
  const r = reasonerFor(ont);
  const t0 = Date.now();
  show('classes in signature', ont.getClassesInSignature().length);
  show('isConsistent()', r.isConsistent());
  r.precomputeInferences('CLASS_HIERARCHY');
  show('top-level classes', r.getTopClasses().length);
  show('unsatisfiable classes', r.getUnsatisfiableClasses().length);
  const bfoEntity = ont.getClassesInSignature()
    .find((c) => c.getIRI().toString().endsWith('#BFO_0000002'));
  if (bfoEntity) {
    show('super(BFO_0000002 Continuant)',
      r.getSuperClasses(bfoEntity.getIRI().toString(), { direct: true }).map(short).join(', ') || '(only owl:Thing)');
  }
  show('elapsed', `${Date.now() - t0}ms`);
  r.dispose();
} catch (err) {
  console.log(`  (skipped — protege-js or bfo.owl unavailable: ${err.message.split('\n')[0]})`);
}

console.log('\nDemo complete.\n');
