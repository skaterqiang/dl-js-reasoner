'use strict';

// ---------------------------------------------------------------------------
// scripts/smoke-incremental.js — the incremental ABox flush path.
//
// `Reasoner.flush()` has two modes:
//   • FULL   — `loadOntology()`, re-clausify everything.
//   • INCREMENTAL — `ReducedABoxOnlyClausification` re-clausifies only the
//     changed assertions and splices them into the existing DLOntology.
//
// The invariant this suite guards: **for any ABox-only change, the incremental
// path must give EXACTLY the same answers as a full reload of the mutated
// ontology.** Every scenario below therefore runs the query three ways:
//
//   1. a reasoner that had the change applied + flushed incrementally;
//   2. a fresh reasoner built from the same mutated axiom list (full reload);
//   3. (for the gate) an assertion that `canProcessPendingChangesIncrementally`
//      reported the mode we expected.
//
// It also checks the NEGATIVE gate: TBox changes, fresh entities, nominals and
// SWRL rules must force a full reload (return false), never the fast path.
//
// Run with:  node scripts/smoke-incremental.js
// ---------------------------------------------------------------------------

const DL = require('../src/index');

const { Reasoner, Configuration, E } = DL;
const AT = E.AxiomType;

let failures = 0;
let checks = 0;
function check(name, actual, expected) {
  checks++;
  const ok = actual === expected;
  if (!ok) failures++;
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}  (got ${actual}, expected ${expected})`);
}
function section(title) { console.log(`\n=== ${title} ===`); }

const EX = 'http://example.org/';
const cls = (n) => E.owlClass(EX + n);
const op = (n) => E.objectProperty(EX + n);
const dp = (n) => E.dataProperty(EX + n);
const ind = (n) => E.namedIndividual(EX + n);
const decl = (e) => ({ axiomType: AT.DECLARATION, entity: e });

const A = cls('A'), B = cls('B'), C = cls('C'), D = cls('D');
const R = op('R'), S = op('S'), hasAge = dp('hasAge');
const a = ind('a'), b = ind('b'), c = ind('c');

/** A minimal mutable ontology mock (same shape as the other smoke scripts). */
function ontology(axioms) {
  const list = axioms.slice();
  return {
    getAxioms: () => list.slice(),
    getOntologyID: () => ({ ontologyIRI: EX + 'incr', isAnonymous: () => false }),
    addAxiom: (x) => { list.push(x); return true; },
    removeAxiom: (x) => { const i = list.indexOf(x); if (i >= 0) list.splice(i, 1); return i >= 0; },
    getImportsClosure: () => [ { getAxioms: () => list.slice() } ],
    _axioms: list
  };
}

/** A non-buffering config so `isConsistent` etc. flush automatically. */
function config(extra) {
  return new Configuration(Object.assign({
    throwInconsistentOntologyException: false,
    bufferChanges: true
  }, extra || {}));
}

/**
 * Apply `change` to `baseAxioms`, then answer `queries` two ways and compare:
 *   • incremental: a reasoner on `baseAxioms`, `applyChange`, `flush`;
 *   • full: a fresh reasoner on the mutated list.
 * `queries` is an array of `[label, fn(reasoner) => value]`.
 *
 * NOTE: the branch actually taken is verified by spying on `loadOntology`, NOT
 * by DLOntology object identity — `DLOntology`'s constructor copies its clause
 * array (`[...new Set(...)]`), so `dlClauses` identity can never survive a
 * flush on either path.
 *
 * NOTE: axioms are NOT interned in `OWLExpressions` (`_axiom` builds a fresh
 * object each call), so a removal change MUST pass the very same object that is
 * in `baseAxioms`, or `removeAxiom` will not find it.
 */
function compareIncrementalVsFull(baseAxioms, change, queries, expectIncremental = true) {
  const incOnt = ontology(baseAxioms);
  const inc = new Reasoner(incOnt, config());

  // OWL API contract: the ontology is mutated FIRST, then the reasoner is
  // notified. Doing it in this order means a full reload and an incremental
  // flush both see the same source of truth, so the only thing the two paths
  // can differ on is how they got there.
  if (change.isAdd) incOnt.addAxiom(change.axiom);
  else incOnt.removeAxiom(change.axiom);
  inc.applyChange(change);

  const gate = inc.canProcessPendingChangesIncrementally();
  check('gate canProcessPendingChangesIncrementally', gate, expectIncremental);

  // Spy on loadOntology to prove which branch flush() really took.
  let fullReloads = 0;
  const realLoadOntology = inc.loadOntology.bind(inc);
  inc.loadOntology = () => { fullReloads++; return realLoadOntology(); };
  inc.flush();
  check(`flush took the ${expectIncremental ? 'INCREMENTAL' : 'FULL'} path`,
    fullReloads, expectIncremental ? 0 : 1);

  const full = new Reasoner(ontology(incOnt.getAxioms()), config());

  for (const [label, fn] of queries) {
    let incVal, fullVal;
    try { incVal = fn(inc); } catch (e) { incVal = `THROW:${e.message}`; }
    try { fullVal = fn(full); } catch (e) { fullVal = `THROW:${e.message}`; }
    check(`${label}: incremental === full`, JSON.stringify(incVal), JSON.stringify(fullVal));
  }
}

// ===========================================================================
section('1. Add a class assertion (A(a) on top of A⊑B⊑C)');
// ===========================================================================
{
  const base = [
    decl(A), decl(B), decl(C), decl(a),
    E.subclassOf(A, B), E.subclassOf(B, C)
  ];
  const change = { axiom: E.classAssertion(A, a), isAdd: true };
  compareIncrementalVsFull(base, change, [
    ['isConsistent', (r) => r.isConsistent()],
    ['getTypes(a) direct', (r) => [...r.getTypes(a, true).getFlattened()].map((x) => E.iriString(x)).sort()],
    ['getTypes(a) all', (r) => [...r.getTypes(a, false).getFlattened()].map((x) => E.iriString(x)).sort()],
    ['hasType(a,B,false)', (r) => r.hasType(a, B, false)],
    ['hasType(a,C,false)', (r) => r.hasType(a, C, false)]
  ]);
}

// ===========================================================================
section('2. Add an object property assertion R(a,b)');
// ===========================================================================
{
  const base = [
    decl(A), decl(R), decl(a), decl(b),
    E.subclassOf(A, E.objectSomeValuesFrom(R, E.owlThing()))
  ];
  const change = { axiom: E.objectPropertyAssertion(R, a, b), isAdd: true };
  compareIncrementalVsFull(base, change, [
    ['isConsistent', (r) => r.isConsistent()],
    ['getObjectPropertyValues(a,R)', (r) => [...r.getObjectPropertyValues(a, R)].map((x) => E.iriString(x)).sort()],
    ['hasObjectPropertyRelationship(a,R,b)', (r) => r.hasObjectPropertyRelationship(a, R, b)]
  ]);
}

// ===========================================================================
section('3. Add a data property assertion hasAge(a,"42")');
// ===========================================================================
{
  const base = [decl(hasAge), decl(a)];
  const change = {
    axiom: E.dataPropertyAssertion(hasAge, a, E.literal('42', E.datatype(E.IRI_XSD_STRING))),
    isAdd: true
  };
  compareIncrementalVsFull(base, change, [
    ['isConsistent', (r) => r.isConsistent()],
    ['getDataPropertyValues(a,hasAge)', (r) => r.getDataPropertyValues(a, hasAge).getFlattened().map((x) => x.lexicalValue).sort()]
  ]);
}

// ===========================================================================
section('4. Add DifferentIndividuals(a,b) then make it inconsistent');
// ===========================================================================
{
  // A ⊑ ≤1 R.⊤, R(a,b), R(a,c) with b≠c forces a clash.
  const base = [
    decl(A), decl(R), decl(a), decl(b), decl(c),
    E.subclassOf(A, E.objectMaxCardinality(1, R, E.owlThing())),
    E.classAssertion(A, a),
    E.objectPropertyAssertion(R, a, b),
    E.objectPropertyAssertion(R, a, c)
  ];
  // Without b≠c the reasoner may merge b and c → consistent.
  const change = { axiom: E.differentIndividuals([b, c]), isAdd: true };
  compareIncrementalVsFull(base, change, [
    ['isConsistent', (r) => r.isConsistent()],
    ['getUnsatisfiableClasses', (r) => [...r.getUnsatisfiableClasses().getEntities()].map((x) => E.iriString(x)).sort()]
  ]);
}

// ===========================================================================
section('5. REMOVE a class assertion (retract A(a))');
// ===========================================================================
{
  // Axions are not interned: build the assertion ONCE and use the same object
  // in both the base list and the removal change.
  const assertion = E.classAssertion(A, a);
  const base = [
    decl(A), decl(B), decl(a),
    E.subclassOf(A, B),
    assertion
  ];
  const change = { axiom: assertion, isAdd: false };
  compareIncrementalVsFull(base, change, [
    ['isConsistent', (r) => r.isConsistent()],
    ['hasType(a,B,false)', (r) => r.hasType(a, B, false)],
    ['getInstances(B)', (r) => [...r.getInstances(B, false).getFlattened()].map((x) => E.iriString(x)).sort()]
  ]);
}

// ===========================================================================
section('6. Add SameIndividual(a,b) — equality fact');
// ===========================================================================
{
  const base = [decl(A), decl(a), decl(b), E.classAssertion(A, a)];
  const change = { axiom: E.sameIndividual([a, b]), isAdd: true };
  compareIncrementalVsFull(base, change, [
    ['isConsistent', (r) => r.isConsistent()],
    ['getSameIndividuals(a)', (r) => [...r.getSameIndividuals(a)].map((x) => E.iriString(x)).sort()],
    ['hasType(b,A,false)', (r) => r.hasType(b, A, false)]
  ]);
}

// ===========================================================================
section('7. Add ObjectHasSelf class assertion Self(R)(a)');
// ===========================================================================
{
  const base = [decl(R), decl(a)];
  const change = { axiom: E.classAssertion(E.objectHasSelf(R), a), isAdd: true };
  compareIncrementalVsFull(base, change, [
    ['isConsistent', (r) => r.isConsistent()],
    ['hasObjectPropertyRelationship(a,R,a)', (r) => r.hasObjectPropertyRelationship(a, R, a)]
  ]);
}

// ===========================================================================
section('8. Add ObjectHasValue class assertion ∃R.{b}(a)');
// ===========================================================================
{
  const base = [decl(R), decl(a), decl(b)];
  const change = { axiom: E.classAssertion(E.objectHasValue(R, b), a), isAdd: true };
  compareIncrementalVsFull(base, change, [
    ['isConsistent', (r) => r.isConsistent()],
    ['hasObjectPropertyRelationship(a,R,b)', (r) => r.hasObjectPropertyRelationship(a, R, b)]
  ]);
}

// ===========================================================================
section('9. NEGATIVE gate — a TBox change forces a full reload');
// ===========================================================================
{
  const base = [decl(A), decl(B), decl(a), E.classAssertion(A, a)];
  const ont = ontology(base);
  const r = new Reasoner(ont, config());
  const sub = E.subclassOf(A, B);
  // A full reload re-reads the ontology, so mutate it first.
  ont.addAxiom(sub);
  r.applyChange({ axiom: sub, isAdd: true });
  check('SubClassOf addition → gate false', r.canProcessPendingChangesIncrementally(), false);
  r.flush();
  check('after full reload A⊑B holds', r.isSubClassOf(A, B), true);
}

// ===========================================================================
section('10. NEGATIVE gate — a FRESH entity forces a full reload');
// ===========================================================================
{
  const base = [decl(A), decl(a)];
  const r = new Reasoner(ontology(base), config());
  // `NewClass` is not in the signature.
  const NewClass = cls('NewClass');
  r.applyChange({ axiom: E.classAssertion(NewClass, a), isAdd: true });
  check('fresh class in assertion → gate false', r.canProcessPendingChangesIncrementally(), false);
}

// ===========================================================================
section('11. NEGATIVE gate — a fresh INDIVIDUAL forces a full reload');
// ===========================================================================
{
  const base = [decl(A), decl(a)];
  const r = new Reasoner(ontology(base), config());
  const newInd = ind('newIndividual');
  r.applyChange({ axiom: E.classAssertion(A, newInd), isAdd: true });
  check('fresh individual in assertion → gate false', r.canProcessPendingChangesIncrementally(), false);
}

// ===========================================================================
section('12. NEGATIVE gate — nominals force a full reload');
// ===========================================================================
{
  // An ontology WITH a nominal (ObjectOneOf) sets hasNominals.
  const base = [
    decl(A), decl(a),
    E.equivalentClasses([A, E.objectOneOf([a])])
  ];
  const r = new Reasoner(ontology(base), config());
  check('ontology hasNominals', r.dlOntology.hasNominals, true);
  r.applyChange({ axiom: E.classAssertion(A, a), isAdd: true });
  check('nominal ontology → gate false even for an ABox change',
    r.canProcessPendingChangesIncrementally(), false);
}

// ===========================================================================
section('13. NEGATIVE gate — a SWRL rule forces a full reload');
// ===========================================================================
{
  const base = [decl(A), decl(a)];
  const r = new Reasoner(ontology(base), config());
  const rule = { body: [], head: [] }; // structurally a SWRLRule
  r.applyChange({ axiom: rule, isAdd: true });
  check('SWRL rule → gate false', r.canProcessPendingChangesIncrementally(), false);
}

// ===========================================================================
section('14. Declaration of an EXISTING entity is incrementally safe');
// ===========================================================================
{
  const base = [decl(A), decl(a), E.classAssertion(A, a)];
  const ont = ontology(base);
  const r = new Reasoner(ont, config());
  const redecl = decl(A);
  ont.addAxiom(redecl);
  r.applyChange({ axiom: redecl, isAdd: true });
  check('re-declaring an existing class → gate true', r.canProcessPendingChangesIncrementally(), true);
  let fullReloads = 0;
  const real = r.loadOntology.bind(r);
  r.loadOntology = () => { fullReloads++; return real(); };
  r.flush();
  check('re-declaration took the incremental path', fullReloads, 0);
  check('still consistent', r.isConsistent(), true);
  check('A(a) survived the no-op flush', r.hasType(a, A, true), true);
}

// ===========================================================================
section('15. Declaration of a NEW entity forces a full reload');
// ===========================================================================
{
  const base = [decl(A), decl(a)];
  const r = new Reasoner(ontology(base), config());
  r.applyChange({ axiom: decl(cls('BrandNew')), isAdd: true });
  check('declaring a new class → gate false', r.canProcessPendingChangesIncrementally(), false);
}

// ===========================================================================
section('16. Multiple changes flush together (add + add)');
// ===========================================================================
{
  const base = [
    decl(A), decl(B), decl(R), decl(a), decl(b),
    E.subclassOf(A, B)
  ];
  const incOnt = ontology(base);
  const inc = new Reasoner(incOnt, config());
  const assertion = E.classAssertion(A, a);
  const propAssertion = E.objectPropertyAssertion(R, a, b);
  // Mutate first, then notify (OWL API contract).
  incOnt.addAxiom(assertion);
  incOnt.addAxiom(propAssertion);
  inc.applyChange({ axiom: assertion, isAdd: true });
  inc.applyChange({ axiom: propAssertion, isAdd: true });
  check('two ABox changes → gate true', inc.canProcessPendingChangesIncrementally(), true);
  let fullReloads = 0;
  const real = inc.loadOntology.bind(inc);
  inc.loadOntology = () => { fullReloads++; return real(); };
  inc.flush();
  check('two-change flush took the incremental path', fullReloads, 0);

  const full = new Reasoner(ontology(incOnt.getAxioms()), config());
  check('hasType(a,B,false) matches', inc.hasType(a, B, false), full.hasType(a, B, false));
  check('hasObjectPropertyRelationship matches',
    inc.hasObjectPropertyRelationship(a, R, b), full.hasObjectPropertyRelationship(a, R, b));
}

// ===========================================================================
section('17. Incremental flush clears cached hierarchies (consistency flip)');
// ===========================================================================
{
  // Start consistent; adding a conflicting assertion must flip isConsistent.
  const base = [
    decl(A), decl(B), decl(a),
    E.disjointClasses([A, B]),
    E.classAssertion(A, a)
  ];
  const ont = ontology(base);
  const r = new Reasoner(ont, config());
  check('consistent before', r.isConsistent(), true);
  // Prime the cache.
  check('A⊑B false before', r.isSubClassOf(A, B), false);
  // Now assert B(a) too → a and B clash with DisjointClasses(A,B).
  const bAssertion = E.classAssertion(B, a);
  ont.addAxiom(bAssertion);
  r.applyChange({ axiom: bAssertion, isAdd: true });
  check('gate true for the conflicting add', r.canProcessPendingChangesIncrementally(), true);
  let fullReloads = 0;
  const real = r.loadOntology.bind(r);
  r.loadOntology = () => { fullReloads++; return real(); };
  r.flush();
  check('conflicting add took the incremental path', fullReloads, 0);
  check('inconsistent after incremental flush', r.isConsistent(), false);

  const full = new Reasoner(ontology(ont.getAxioms()), config());
  check('full reload also inconsistent', full.isConsistent(), false);
}

// ===========================================================================
section('18. NON_BUFFERING mode flushes incrementally on query');
// ===========================================================================
{
  const base = [decl(A), decl(B), decl(a), E.subclassOf(A, B)];
  const ont = ontology(base);
  const r = new Reasoner(ont, config({ bufferChanges: false }));
  check('buffering mode', r.getBufferingMode(), 'NON_BUFFERING');
  const assertion = E.classAssertion(A, a);
  ont.addAxiom(assertion);
  r.applyChange({ axiom: assertion, isAdd: true });
  // No explicit flush: the next query flushes automatically.
  check('hasType(a,B,false) after implicit flush', r.hasType(a, B, false), true);
}

// ===========================================================================
section('19. REGRESSION: the per-individual type cache is invalidated by flush');
// ===========================================================================
// `getDirectSuperConceptNodes` is MEMOISED per individual, because
// `getInstances(C, true)` otherwise recomputes every individual's direct types
// once per class queried (measured: 2200 tableau runs vs 440 on iao.owl).
//
// A cache is only sound if it is dropped when the answers can change. Sections
// 1-18 all flush BEFORE querying, so they cannot expose a stale entry — this
// section is the one that PRIMES the cache, then mutates, then re-queries.
//
// Both directions are covered: a retraction must REMOVE a type, and an addition
// must INTRODUCE one. Each is compared against a fresh reasoner built from the
// mutated ontology, so a stale answer cannot pass by accident.
{
  const typesOf = (r, i, direct) =>
    [...r.getTypes(i, direct).getFlattened()].map((x) => E.iriString(x)).sort();
  const instancesOf = (r, k, direct) =>
    [...r.getInstances(k, direct).getFlattened()].map((x) => E.iriString(x)).sort();

  // --- 19a. RETRACT A(a): a's cached types must shrink -------------------
  {
    const assertion = E.classAssertion(A, a);
    const base = [decl(A), decl(B), decl(a), E.subclassOf(A, B), assertion];
    const ont = ontology(base);
    const r = new Reasoner(ont, config());

    // PRIME the cache before the change.
    check('19a primed: getTypes(a,true) includes A', typesOf(r, a, true).includes(EX + 'A'), true);
    check('19a primed: getInstances(A,true) includes a', instancesOf(r, A, true).includes(EX + 'a'), true);

    ont.removeAxiom(assertion);
    r.applyChange({ axiom: assertion, isAdd: false });
    r.flush();

    const fresh = new Reasoner(ontology(ont.getAxioms()), config());
    check('19a after retract: getTypes(a,true) === fresh',
      JSON.stringify(typesOf(r, a, true)), JSON.stringify(typesOf(fresh, a, true)));
    check('19a after retract: A is no longer a type of a',
      typesOf(r, a, true).includes(EX + 'A'), false);
    check('19a after retract: getInstances(A,true) === fresh',
      JSON.stringify(instancesOf(r, A, true)), JSON.stringify(instancesOf(fresh, A, true)));
    check('19a after retract: a is no longer an instance of A',
      instancesOf(r, A, true).includes(EX + 'a'), false);
  }

  // --- 19b. ADD B(a): a's cached DIRECT types must grow ------------------
  // A and B are deliberately UNRELATED here. Under `A ⊑ B` this check would be
  // vacuous: asserting B(a) adds nothing, because B is already an ANCESTOR of
  // the direct type A and `getTypes(_, true)` returns only the most specific
  // nodes. With no subsumption between them, B genuinely becomes a second
  // direct type — which a stale cache would still report as [A] alone.
  {
    const base = [decl(A), decl(B), decl(a), E.classAssertion(A, a)];
    const ont = ontology(base);
    const r = new Reasoner(ont, config());

    // PRIME: a's only direct type is A.
    check('19b primed: getTypes(a,true) is [A]',
      JSON.stringify(typesOf(r, a, true)), JSON.stringify([EX + 'A']));
    check('19b primed: B is not yet a direct type of a',
      typesOf(r, a, true).includes(EX + 'B'), false);

    const bAssertion = E.classAssertion(B, a);
    ont.addAxiom(bAssertion);
    r.applyChange({ axiom: bAssertion, isAdd: true });
    r.flush();

    const fresh = new Reasoner(ontology(ont.getAxioms()), config());
    check('19b after add: getTypes(a,true) === fresh',
      JSON.stringify(typesOf(r, a, true)), JSON.stringify(typesOf(fresh, a, true)));
    check('19b after add: B became a direct type of a',
      typesOf(r, a, true).includes(EX + 'B'), true);
    check('19b after add: getTypes(a,true) is [A,B]',
      JSON.stringify(typesOf(r, a, true)), JSON.stringify([EX + 'A', EX + 'B']));
    check('19b after add: getInstances(B,true) === fresh',
      JSON.stringify(instancesOf(r, B, true)), JSON.stringify(instancesOf(fresh, B, true)));
    check('19b after add: a is now an instance of B',
      instancesOf(r, B, true).includes(EX + 'a'), true);
  }

  // --- 19c. consistency flip: ex falso, owl:Nothing becomes a type -------
  // In an INCONSISTENT ontology every class is a type of every individual, so
  // the pre-flush answer [A] is still "true" — asserting that A DISAPPEARS
  // would be wrong. The discriminating signal is `owl:Nothing`, which is absent
  // while the ontology is consistent and present once it is not. A stale cache
  // would still report the consistent-era answer and omit it.
  {
    const NOTHING = 'http://www.w3.org/2002/07/owl#Nothing';
    const base = [decl(A), decl(B), decl(a), E.disjointClasses([A, B]), E.classAssertion(A, a)];
    const ont = ontology(base);
    const r = new Reasoner(ont, config());

    check('19c primed: consistent', r.isConsistent(), true);
    check('19c primed: getTypes(a,true) is [A]',
      JSON.stringify(typesOf(r, a, true)), JSON.stringify([EX + 'A']));
    check('19c primed: owl:Nothing is NOT a type of a',
      typesOf(r, a, true).includes(NOTHING), false);

    const conflict = E.classAssertion(B, a);
    ont.addAxiom(conflict);
    r.applyChange({ axiom: conflict, isAdd: true });
    r.flush();

    const fresh = new Reasoner(ontology(ont.getAxioms()), config());
    check('19c after conflict: inconsistent', r.isConsistent(), false);
    check('19c after conflict: getTypes(a,true) === fresh',
      JSON.stringify(typesOf(r, a, true)), JSON.stringify(typesOf(fresh, a, true)));
    check('19c after conflict: owl:Nothing IS now a type of a',
      typesOf(r, a, true).includes(NOTHING), true);
  }
}

// ===========================================================================
console.log(`\n${failures === 0 ? 'ALL PASS' : 'FAILURES'}: ${checks - failures}/${checks} checks passed`);
process.exit(failures === 0 ? 0 : 1);
