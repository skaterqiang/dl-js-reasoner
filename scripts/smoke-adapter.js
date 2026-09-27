'use strict';

// ---------------------------------------------------------------------------
// scripts/smoke-adapter.js — exercises the public entry point (`src/index.js`)
// and the protege-js adapter (`src/adapter/protege.js`).
//
// Covers: the export surface, IRI-string vs expression-object arguments,
// Node/NodeSet → IRI-array flattening, subsumption + classification queries,
// individual/realisation queries, data-property values, property hierarchies
// and characteristics, entailment, precomputation, buffered vs non-buffering
// incremental changes, and a real-ontology pass over bfo.owl.
//
// Run with:  node scripts/smoke-adapter.js
// ---------------------------------------------------------------------------

const path = require('path');
const protege = require('@skaterqiang/protege-js');
const DL = require('../src/index');

let failures = 0;
let checks = 0;
function check(name, actual, expected) {
  checks++;
  const ok = actual === expected;
  if (!ok) failures++;
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}  (got ${actual}, expected ${expected})`
    + (ok ? '' : `  [${JSON.stringify(actual)}]`));
}

// --- exports present -------------------------------------------------------
for (const k of ['Reasoner', 'createReasoner', 'createNonBufferingReasoner',
  'Node', 'NodeSet', 'EntailmentChecker', 'Configuration', 'Prefixes', 'E',
  'AxiomType', 'EntityType', 'DLOntology', 'OWLClausification', 'Tableau',
  'ProtegeAdapter', 'reasonerFor', 'REASONER_NAME', 'REASONER_VERSION',
  'InconsistentOntologyException', 'FreshEntitiesException',
  'FRESH_ENTITY_POLICY', 'INFERENCE_TYPE',
  'DIRECT_BLOCKING_TYPE', 'BLOCKING_STRATEGY_TYPE', 'BLOCKING_SIGNATURE_CACHE_TYPE',
  'ReducedABoxOnlyClausification', 'INDIVIDUAL_AXIOM_TYPES',
  'INCREMENTAL_CLASS_EXPRESSION_TYPES']) {
  check(`export ${k}`, DL[k] !== undefined, true);
}
check('REASONER_NAME', DL.REASONER_NAME, 'DL-JS-REASONER');
// The blocking enums must carry every value HermiT defines, so a caller can
// spell out a configuration instead of relying on stringly-typed defaults.
check('BLOCKING_STRATEGY_TYPE has 5 values',
  Object.keys(DL.BLOCKING_STRATEGY_TYPE).length, 5);
check('DIRECT_BLOCKING_TYPE has 3 values',
  Object.keys(DL.DIRECT_BLOCKING_TYPE).length, 3);
check('BLOCKING_SIGNATURE_CACHE_TYPE has 2 values',
  Object.keys(DL.BLOCKING_SIGNATURE_CACHE_TYPE).length, 2);

// --- synthetic ontology through the adapter --------------------------------
const E = DL.E;
const EX = 'http://example.org/';
const AT = E.AxiomType;
const cls = (n) => E.owlClass(EX + n);
const op = (n) => E.objectProperty(EX + n);
const dp = (n) => E.dataProperty(EX + n);
const ind = (n) => E.namedIndividual(EX + n);
const decl = (e) => ({ axiomType: AT.DECLARATION, entity: e });

const A = cls('A'), B = cls('B'), C = cls('C'), D = cls('D');
const R = op('R'), hasAge = dp('hasAge');
const a = ind('a'), b = ind('b');

function ontology(axioms) {
  const list = axioms.slice();
  return {
    getAxioms: () => list.slice(),
    getOntologyID: () => ({ ontologyIRI: EX + 'adapter', isAnonymous: () => false }),
    addAxiom: (x) => { list.push(x); return true; },
    removeAxiom: (x) => { const i = list.indexOf(x); if (i >= 0) list.splice(i, 1); return i >= 0; },
    _axioms: list
  };
}

const ont = ontology([
  decl(A), decl(B), decl(C), decl(D), decl(R), decl(hasAge), decl(a), decl(b),
  E.subclassOf(A, B),
  E.subclassOf(B, C),
  E.disjointClasses([C, D]),
  E.classAssertion(A, a),
  E.objectPropertyAssertion(R, a, b),
  E.dataPropertyAssertion(hasAge, a, E.literal('42', E.datatype(E.IRI_XSD_STRING)))
]);

const r = DL.reasonerFor(ont);
check('adapter instanceof ProtegeAdapter', r instanceof DL.ProtegeAdapter, true);
check('adapter.getReasonerName()', r.getReasonerName(), 'DL-JS-REASONER');
check('adapter.isConsistent()', r.isConsistent(), true);

// IRI-string arguments
check('isSubClassOf(A,C) by IRI', r.isSubClassOf(EX + 'A', EX + 'C'), true);
check('isSubClassOf(C,A) by IRI', r.isSubClassOf(EX + 'C', EX + 'A'), false);
check('isSatisfiable(A) by IRI', r.isSatisfiable(EX + 'A'), true);
check('isSatisfiable(D) by IRI', r.isSatisfiable(EX + 'D'), true);
// expression objects still work
check('isSubClassOf by expression', r.isSubClassOf(A, C), true);

check('getSuperClasses(A) includes C', r.getSuperClasses(EX + 'A').includes(EX + 'C'), true);
check('getSuperClasses(A,direct)', r.getSuperClasses(EX + 'A', { direct: true }).join(','), EX + 'B');
check('getSubClasses(C,direct)', r.getSubClasses(EX + 'C', { direct: true }).join(','), EX + 'B');
check('getDisjointClasses(C) has D', r.getDisjointClasses(EX + 'C').includes(EX + 'D'), true);
check('getUnsatisfiableClasses() empty', r.getUnsatisfiableClasses().length, 0);
// protege-js' `getTopClasses()` semantics: classes with no NAMED superclass
// other than owl:Thing. With `A ⊑ B ⊑ C`, only C and D qualify.
check('getTopClasses() is [C,D]', r.getTopClasses().join(','), [EX + 'C', EX + 'D'].sort().join(','));

// individuals
check('getInstances(C)', r.getInstances(EX + 'C').join(','), EX + 'a');
check('getTypes(a,direct)', r.getTypes(EX + 'a', { direct: true }).join(','), EX + 'A');
check('getTypes(a)', r.getTypes(EX + 'a').includes(EX + 'C'), true);
check('hasType(a,C)', r.hasType(EX + 'a', EX + 'C'), true);
check('hasType(a,D)', r.hasType(EX + 'a', EX + 'D'), false);
check('getObjectPropertyValues(a,R)', r.getObjectPropertyValues(EX + 'a', EX + 'R').join(','), EX + 'b');
check('hasObjectPropertyRelationship(a,R,b)', r.hasObjectPropertyRelationship(EX + 'a', EX + 'R', EX + 'b'), true);
check('getSameIndividuals(a)', r.getSameIndividuals(EX + 'a').join(','), EX + 'a');
check('isSameIndividual(a,b)', r.isSameIndividual(EX + 'a', EX + 'b'), false);
check('getDifferentIndividuals(a)', r.getDifferentIndividuals(EX + 'a').length, 0);

// data property values
const dpv = r.getDataPropertyValues(EX + 'a', EX + 'hasAge');
check('getDataPropertyValues(a,hasAge).length', dpv.length, 1);
check('getDataPropertyValues literal value', dpv[0] && dpv[0].lexicalValue, '42');

// properties
check('isSubObjectPropertyOf(R,topObjectProperty)',
  r.isSubObjectPropertyOf(EX + 'R', E.IRI_TOP_OBJECT_PROPERTY), true);
check('isSubDataPropertyOf(hasAge,topDataProperty)',
  r.isSubDataPropertyOf(EX + 'hasAge', E.IRI_TOP_DATA_PROPERTY), true);
check('getSuperDataProperties(hasAge) has top',
  r.getSuperDataProperties(EX + 'hasAge').includes(E.IRI_TOP_DATA_PROPERTY), true);
check('isFunctional(R)', r.isFunctional(EX + 'R'), false);
check('isTransitive(R)', r.isTransitive(EX + 'R'), false);
check('isSymmetric(R)', r.isSymmetric(EX + 'R'), false);

// entailment
check('isEntailed(A⊑C)', r.isEntailed(E.subclassOf(A, C)), true);
check('isEntailed(C⊑A)', r.isEntailed(E.subclassOf(C, A)), false);
check('isEntailmentCheckingSupported', r.isEntailmentCheckingSupported(AT.SUB_CLASS_OF), true);

// precomputation — use a FRESH adapter, because the queries above already
// triggered `classifyClasses()` lazily on `r`.
const rp = DL.reasonerFor(ontology([
  decl(A), decl(B), decl(C), decl(D), decl(R), decl(hasAge), decl(a), decl(b),
  E.subclassOf(A, B), E.subclassOf(B, C), E.disjointClasses([C, D])
]));
check('isPrecomputed(CLASS_HIERARCHY) before', rp.isPrecomputed('CLASS_HIERARCHY'), false);
rp.precomputeInferences('CLASS_HIERARCHY');
check('isPrecomputed(CLASS_HIERARCHY) after', rp.isPrecomputed('CLASS_HIERARCHY'), true);
check('getPrecomputableInferenceTypes length', rp.getPrecomputableInferenceTypes().length, 6);
rp.dispose();

// classification / realisation return `this` for chaining
check('classify() chains', r.classify(), r);
check('realise() chains', r.realise(), r);

// incremental changes: buffer then flush
const ont2 = ontology([decl(A), decl(B), decl(C), E.subclassOf(A, B)]);
const r2 = DL.reasonerFor(ont2, { throwInconsistentOntologyException: false });
check('before change: A⊑C false', r2.isSubClassOf(EX + 'A', EX + 'C'), false);
ont2.addAxiom(E.subclassOf(B, C));
r2.applyChange({ axiom: E.subclassOf(B, C), isAdd: true });
check('change buffered', r2.getPendingChanges().length, 1);
r2.flush();
check('after flush: pending cleared', r2.getPendingChanges().length, 0);
check('after flush: A⊑C true', r2.isSubClassOf(EX + 'A', EX + 'C'), true);
r2.dispose();

// incremental changes: the ADAPTER exposes canProcessPendingChangesIncrementally
const ont2b = ontology([decl(A), decl(B), decl(a), E.subclassOf(A, B)]);
const r2b = DL.reasonerFor(ont2b, { throwInconsistentOntologyException: false });
check('no pending changes → gate true (vacuous)', r2b.canProcessPendingChangesIncrementally(), true);
const assertionAB = E.classAssertion(A, a);
ont2b.addAxiom(assertionAB);
r2b.applyChange({ axiom: assertionAB, isAdd: true });
check('ABox assertion over known entities → gate true',
  r2b.canProcessPendingChangesIncrementally(), true);
r2b.flush();
check('after incremental flush: a is a B', r2b.isSubClassOf(EX + 'A', EX + 'B'), true);
check('after incremental flush: getInstances(B) has a',
  r2b.getInstances(EX + 'B').includes(EX + 'a'), true);
// A TBox change now forces a full reload.
const subBC = E.subclassOf(B, C);
ont2b.addAxiom(subBC);
r2b.applyChange({ axiom: subBC, isAdd: true });
check('TBox change → gate false', r2b.canProcessPendingChangesIncrementally(), false);
r2b.flush();
check('after full reload: A⊑C', r2b.isSubClassOf(EX + 'A', EX + 'C'), true);
r2b.dispose();

// non-buffering RAW reasoner: `createNonBufferingReasoner` returns a `Reasoner`,
// NOT an adapter, so it takes expression objects (an IRI string is not a class).
const ont3 = ontology([decl(A), decl(B), decl(C), E.subclassOf(A, B)]);
const r3 = DL.createNonBufferingReasoner(ont3, { throwInconsistentOntologyException: false });
check('raw reasoner rejects IRI strings', typeof r3.isSubClassOf, 'function');
ont3.addAxiom(E.subclassOf(B, C));
r3.applyChange({ axiom: E.subclassOf(B, C), isAdd: true });
check('non-buffering applies immediately', r3.isSubClassOf(A, C), true);
r3.dispose();

// non-buffering ADAPTER: same, but IRI strings are accepted.
const ont4 = ontology([decl(A), decl(B), decl(C), E.subclassOf(A, B)]);
const r4 = DL.reasonerFor(ont4, { throwInconsistentOntologyException: false, bufferChanges: false });
check('adapter buffering mode', r4.getBufferingMode(), 'NON_BUFFERING');
ont4.addAxiom(E.subclassOf(B, C));
r4.applyChange({ axiom: E.subclassOf(B, C), isAdd: true });
check('non-buffering adapter by IRI', r4.isSubClassOf(EX + 'A', EX + 'C'), true);
r4.dispose();

// --- real ontology through the adapter ------------------------------------
const DIR = path.resolve(__dirname, '../../protege-js/sample/ontologies');
const loader = new protege.OntologyLoader();
const bfo = loader.loadFromFile(path.join(DIR, 'bfo.owl'));
const rb = DL.reasonerFor(bfo);
check('bfo consistent via adapter', rb.isConsistent(), true);
const bfoClasses = bfo.getClassesInSignature().map((c) => c.getIRI().toString());
const bfoThing = bfoClasses.find((s) => s.endsWith('#Thing'));
check('bfo has classes', bfoClasses.length > 10, true);
check('bfo getTopClasses non-empty', rb.getTopClasses().length > 0, true);
check('bfo every class subsumed by Thing',
  bfoClasses.filter((s) => s !== E.IRI_THING && s !== E.IRI_NOTHING)
    .every((s) => rb.isSubClassOf(s, E.IRI_THING)), true);
// `getSubClasses(⊤)` yields every class EXCEPT owl:Thing itself but INCLUDING
// the inferred owl:Nothing; the signature is the mirror image. Reconcile both.
const bfoSubs = new Set(rb.getSubClasses(E.IRI_THING));
bfoSubs.delete(E.IRI_NOTHING);
bfoSubs.add(E.IRI_THING);
check('bfo getSubClasses(Thing) covers signature',
  bfoSubs.size, new Set(bfoClasses).size);
check('bfo getSubClasses(Thing) == signature',
  [...bfoSubs].sort().join('|'), [...new Set(bfoClasses)].sort().join('|'));
void bfoThing;
rb.dispose();

// --- real protege-js SWRL rule objects through the adapter ----------------
// This is the end-to-end interop case that motivated the `isVariable` fix:
// protege-js' `SWRLVariable` stores only `{ iri }` with NO type tag, and its
// atoms use short type names ('ClassAtom', 'ObjectPropertyAtom'). If the
// normalizer fails to recognize such a variable it silently treats it as a
// named individual, the rule never fires, and nothing throws.
{
  const EX = 'http://example.org/swrl#';
  const Person = E.owlClass(EX + 'Person');
  const Adult = E.owlClass(EX + 'Adult');
  const hasParent = E.objectProperty(EX + 'hasParent');
  const p = E.namedIndividual(EX + 'p');
  const q = E.namedIndividual(EX + 'q');
  const decl = (entity) => ({ axiomType: E.AxiomType.DECLARATION, entity });

  // Build the rule with protege-js' OWN model classes.
  const vx = new protege.SWRLVariable(EX + 'x');
  const vy = new protege.SWRLVariable(EX + 'y');
  check('protege-js SWRLVariable has no type tag', vx.type, undefined);
  const rule = new protege.SWRLRule(
    [new protege.SWRLClassAtom(Person, vx),
     new protege.SWRLObjectPropertyAtom(hasParent, vx, vy)],
    [new protege.SWRLClassAtom(Adult, new protege.SWRLVariable(EX + 'x'))]
  );

  const ont = ontology([decl(Person), decl(Adult), decl(hasParent), decl(p), decl(q),
    E.classAssertion(Person, p), E.objectPropertyAssertion(hasParent, p, q), rule]);
  const r = DL.reasonerFor(ont);
  check('protege-js SWRL rule fires through the adapter',
    r.isEntailed(E.classAssertion(Adult, p)), true);
  check('protege-js SWRL rule does not over-fire',
    r.isEntailed(E.classAssertion(Adult, q)), false);
  r.dispose();
}

console.log(`\n${checks - failures}/${checks} checks passed.`);
if (failures > 0) { console.log(`${failures} FAILURES`); process.exit(1); }
console.log('All adapter/index checks passed.');
