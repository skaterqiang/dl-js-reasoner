'use strict';

// ---------------------------------------------------------------------------
// test/role-classification.test.js — QuasiOrderClassificationForRoles.
//
// Object properties are classified by proxying each role `R` as a fresh concept
// `internal:prop#R ≡ ∃R.F` and running concept classification. Two things make
// the plain `QuasiOrderClassification` a poor fit for that encoding, and
// `QuasiOrderClassificationForRoles` fixes both:
//
//   1. its seeder reads the told ROLE inclusions (the base seeder only
//      recognises clauses whose predicates are `AtomicConcept`s, so it seeds
//      NOTHING for role proxies);
//   2. it mirrors every subsumption onto the inverse roles, because
//      `R ⊑ S` implies `R⁻ ⊑ S⁻`.
//
// Both are OPTIMISATIONS: the resulting hierarchy is identical either way, and
// only the number of tableau runs differs. That is why the load-bearing
// assertion below counts `isSatisfiable` calls rather than comparing hierarchies
// — a hierarchy comparison would pass with the class deleted.
// ---------------------------------------------------------------------------

const test = require('node:test');
const assert = require('node:assert/strict');

const { Reasoner, Configuration } = require('../src/index');
const E = require('../src/owl/OWLExpressions');
const P = require('../src/model/DLPredicate');
const { QuasiOrderClassification } = require('../src/hierarchy/QuasiOrderClassification');
const { QuasiOrderClassificationForRoles } =
  require('../src/hierarchy/QuasiOrderClassificationForRoles');
const { EX, ontology, declaration } = require('./helpers');

const AT = E.AxiomType;

// Axiom types with no factory in OWLExpressions.js are built as plain objects.
const subObjectPropertyOf = (subProperty, superProperty) =>
  ({ axiomType: AT.SUB_OBJECT_PROPERTY_OF, subProperty, superProperty });
const equivalentObjectProperties = (properties) =>
  ({ axiomType: AT.EQUIVALENT_OBJECT_PROPERTIES, properties: properties.slice() });

const op = (n) => E.objectProperty(EX + n);
const cls = (n) => E.owlClass(EX + n);
const role = (n) => P.internAtomicRole(E.iriString(EX + n), false);
const proxy = (n) => P.internAtomicConcept(`internal:prop#${EX}${n}`);
const invProxy = (n) => P.internAtomicConcept(`internal:prop#inv#${EX}${n}`);

/**
 * A non-Horn ontology with told role inclusions AND an inverse role.
 *
 * The disjunctive `A ⊑ B ⊔ C` makes the tableau non-deterministic, so the
 * quasi-order path — the only path that uses `ForRoles` — is the one exercised.
 * `forceQuasiOrderClassification` is set anyway to make that explicit.
 */
const AXIOMS = [
  declaration(op('mother')), declaration(op('father')), declaration(op('parent')),
  declaration(op('ancestor')), declaration(op('child')),
  declaration(cls('A')), declaration(cls('B')), declaration(cls('C')),
  subObjectPropertyOf(op('mother'), op('parent')),
  subObjectPropertyOf(op('father'), op('parent')),
  subObjectPropertyOf(op('parent'), op('ancestor')),
  equivalentObjectProperties([op('child'), E.objectInverseOf(op('parent'))]),
  E.subclassOf(cls('A'), E.objectUnionOf([cls('B'), cls('C')])),
  E.subclassOf(cls('B'), E.objectSomeValuesFrom(op('mother'), cls('A')))
];

function makeReasoner() {
  const configuration = new Configuration();
  configuration.forceQuasiOrderClassification = true;
  const reasoner = new Reasoner(ontology(AXIOMS), configuration);
  reasoner.isConsistent();
  return reasoner;
}

/**
 * Rebuild the role→proxy maps exactly as `Reasoner.classifyObjectProperties`
 * does, so the classification classes can be driven directly.
 */
function buildProxies(reasoner) {
  const conceptsForRoles = new Map();
  const rolesForConcepts = new Map();
  const relevant = new Set();
  for (const atomicRole of reasoner.dlOntology.allAtomicObjectRoles) {
    if (atomicRole !== P.TOP_OBJECT_ROLE && atomicRole !== P.BOTTOM_OBJECT_ROLE) {
      relevant.add(atomicRole);
      if (reasoner.dlOntology.hasInverseRoles) relevant.add(atomicRole.getInverse());
    }
  }
  const freshConcept = E.owlClass('internal:fresh-concept');
  const additionalAxioms = [];
  for (const objectRole of relevant) {
    let conceptForRole;
    let objectPropertyExpression;
    if (objectRole instanceof P.AtomicRole) {
      conceptForRole = P.internAtomicConcept(`internal:prop#${objectRole.iri}`);
      objectPropertyExpression = E.objectProperty(objectRole.iri);
    } else {
      conceptForRole = P.internAtomicConcept(`internal:prop#inv#${objectRole.inverseRole.iri}`);
      objectPropertyExpression = E.objectInverseOf(E.objectProperty(objectRole.inverseRole.iri));
    }
    additionalAxioms.push(E.equivalentClasses([
      E.owlClass(conceptForRole.iri),
      E.objectSomeValuesFrom(objectPropertyExpression, freshConcept)
    ]));
    conceptsForRoles.set(objectRole, conceptForRole);
    rolesForConcepts.set(conceptForRole, objectRole);
  }
  conceptsForRoles.set(P.TOP_OBJECT_ROLE, P.THING);
  rolesForConcepts.set(P.THING, P.TOP_OBJECT_ROLE);
  conceptsForRoles.set(P.BOTTOM_OBJECT_ROLE, P.NOTHING);
  rolesForConcepts.set(P.NOTHING, P.BOTTOM_OBJECT_ROLE);
  additionalAxioms.push(
    E.classAssertion(freshConcept, E.anonymousIndividual('fresh-individual')));
  return { conceptsForRoles, rolesForConcepts, additionalAxioms };
}

// ---------------------------------------------------------------------------
// AtomicRole.getInverse() — the extreme object roles are their own inverses.
//
// This is load-bearing for the mirroring: `classifyObjectProperties` only puts
// the roles it ENUMERATES into `conceptsForRoles`, and TOP/BOTTOM are added
// separately as `owl:Thing`/`owl:Nothing`. If `TOP_OBJECT_ROLE.getInverse()`
// returned a distinct `InverseRole`, the mirror lookup would yield `undefined`.
// ---------------------------------------------------------------------------

test('AtomicRole.getInverse(): the extreme OBJECT roles are their own inverses', () => {
  assert.equal(P.TOP_OBJECT_ROLE.getInverse(), P.TOP_OBJECT_ROLE);
  assert.equal(P.BOTTOM_OBJECT_ROLE.getInverse(), P.BOTTOM_OBJECT_ROLE);
});

test('AtomicRole.getInverse(): ordinary roles still get a distinct InverseRole', () => {
  const r = role('r');
  assert.notEqual(r.getInverse(), r);
  assert.ok(r.getInverse() instanceof P.InverseRole);
  // (R⁻)⁻ = R, and interning makes it the SAME object.
  assert.equal(r.getInverse().getInverse(), r);
});

test('AtomicRole.getInverse(): DATA roles are not special-cased (HermiT parity)', () => {
  // HermiT's AtomicRole.getInverse() only guards TOP/BOTTOM_OBJECT_ROLE, so
  // owl:topDataProperty does get an InverseRole. OWL 2 has no inverse data
  // properties, so the case never arises in practice.
  assert.ok(P.TOP_DATA_ROLE.getInverse() instanceof P.InverseRole);
  assert.ok(P.BOTTOM_DATA_ROLE.getInverse() instanceof P.InverseRole);
});

// ---------------------------------------------------------------------------
// Seeding from told role inclusions.
// ---------------------------------------------------------------------------

test('told role inclusions seed the known-subsumption graph', () => {
  const reasoner = makeReasoner();
  const { conceptsForRoles, rolesForConcepts } = buildProxies(reasoner);
  const tableau = reasoner.getTableau([]);
  const q = new QuasiOrderClassificationForRoles(tableau, { elementClassified() {} },
    conceptsForRoles.get(P.TOP_OBJECT_ROLE), conceptsForRoles.get(P.BOTTOM_OBJECT_ROLE),
    new Set(rolesForConcepts.keys()), reasoner.dlOntology.hasInverseRoles,
    conceptsForRoles, rolesForConcepts);
  q.initialiseKnownSubsumptionsUsingToldSubsumers();

  const knownMother = q.getAllKnownSubsumers(proxy('mother'));
  assert.ok(knownMother.has(proxy('parent')), 'mother ⊑ parent');
  // `parent ⊑ ancestor` is also told, so the closure reaches it.
  assert.ok(knownMother.has(proxy('ancestor')), 'mother ⊑ ancestor transitively');
  assert.ok(q.getAllKnownSubsumers(proxy('father')).has(proxy('parent')), 'father ⊑ parent');
});

test('the BASE class seeds nothing for role proxies', () => {
  // This is the whole reason ForRoles exists: the base seeder requires both
  // predicates to be AtomicConcepts, and role inclusions clausify to
  // `R(X,Y) → S(X,Y)` whose predicates are AtomicRoles.
  const reasoner = makeReasoner();
  const { conceptsForRoles, rolesForConcepts } = buildProxies(reasoner);
  const tableau = reasoner.getTableau([]);
  const base = new QuasiOrderClassification(tableau, { elementClassified() {} },
    conceptsForRoles.get(P.TOP_OBJECT_ROLE), conceptsForRoles.get(P.BOTTOM_OBJECT_ROLE),
    new Set(rolesForConcepts.keys()));
  base.initialiseKnownSubsumptionsUsingToldSubsumers();

  // `getAllKnownSubsumers` is `getReachableSuccessors`, which INCLUDES the node
  // itself, so an unseeded graph still reports one "subsumer" (self).
  const seeded = [...base.getAllKnownSubsumers(proxy('mother'))]
    .filter((c) => c !== proxy('mother'));
  assert.deepEqual(seeded, []);
});

test('an inclusion against an INVERSE seeds through the inverse proxy', () => {
  // `child ≡ parent⁻` clausifies to two 1:1 clauses, one of which is
  // `parent(X,Y) → child(Y,X)` — arguments SWAPPED, because `getRoleAtom`
  // renders `R⁻(X,Y)` as the atom `R(Y,X)`. The override detects that by
  // comparing argument 0 of body and head, and seeds `parent⁻ ⊑ child`.
  const reasoner = makeReasoner();
  const { conceptsForRoles, rolesForConcepts } = buildProxies(reasoner);
  const tableau = reasoner.getTableau([]);
  const q = new QuasiOrderClassificationForRoles(tableau, { elementClassified() {} },
    conceptsForRoles.get(P.TOP_OBJECT_ROLE), conceptsForRoles.get(P.BOTTOM_OBJECT_ROLE),
    new Set(rolesForConcepts.keys()), reasoner.dlOntology.hasInverseRoles,
    conceptsForRoles, rolesForConcepts);
  q.initialiseKnownSubsumptionsUsingToldSubsumers();

  assert.ok(q.getAllKnownSubsumers(invProxy('parent')).has(proxy('child')),
    'parent⁻ ⊑ child');
  assert.ok(q.getAllKnownSubsumers(proxy('child')).has(invProxy('parent')),
    'child ⊑ parent⁻');
});

// ---------------------------------------------------------------------------
// Inverse mirroring.
// ---------------------------------------------------------------------------

/** A hand-built proxy map over two roles and their inverses. */
function mirrorFixture(hasInverses) {
  const conceptsForRoles = new Map();
  const rolesForConcepts = new Map();
  const r = role('r');
  const s = role('s');
  const add = (role_, concept) => {
    conceptsForRoles.set(role_, concept);
    rolesForConcepts.set(concept, role_);
  };
  add(r, proxy('r'));
  add(s, proxy('s'));
  add(r.getInverse(), invProxy('r'));
  add(s.getInverse(), invProxy('s'));
  add(P.TOP_OBJECT_ROLE, P.THING);
  add(P.BOTTOM_OBJECT_ROLE, P.NOTHING);
  return new QuasiOrderClassificationForRoles(null, { elementClassified() {} },
    P.THING, P.NOTHING, new Set(rolesForConcepts.keys()), hasInverses,
    conceptsForRoles, rolesForConcepts);
}

test('addKnownSubsumption mirrors R ⊑ S onto R⁻ ⊑ S⁻', () => {
  const q = mirrorFixture(true);
  q.addKnownSubsumption(proxy('r'), proxy('s'));
  assert.ok(q.knownSubsumptions.getSuccessors(proxy('r')).has(proxy('s')));
  assert.ok(q.knownSubsumptions.getSuccessors(invProxy('r')).has(invProxy('s')));
});

test('the mirror keeps the SAME direction (it is not the converse)', () => {
  // `R ⊑ S` implies `R⁻ ⊑ S⁻`. It does NOT imply `S⁻ ⊑ R⁻` — that would be the
  // converse, and asserting it would corrupt the hierarchy.
  const q = mirrorFixture(true);
  q.addKnownSubsumption(proxy('r'), proxy('s'));
  assert.equal(q.knownSubsumptions.getSuccessors(invProxy('s')).has(invProxy('r')), false);
});

test('addPossibleSubsumption mirrors too', () => {
  const q = mirrorFixture(true);
  q.addPossibleSubsumption(proxy('r'), proxy('s'));
  assert.ok(q.possibleSubsumptions.getSuccessors(proxy('r')).has(proxy('s')));
  assert.ok(q.possibleSubsumptions.getSuccessors(invProxy('r')).has(invProxy('s')));
});

test('hasInverses=false suppresses the mirroring but keeps the direct edge', () => {
  const q = mirrorFixture(false);
  q.addKnownSubsumption(proxy('r'), proxy('s'));
  assert.ok(q.knownSubsumptions.getSuccessors(proxy('r')).has(proxy('s')));
  assert.equal(q.knownSubsumptions.getSuccessors(invProxy('r')).has(invProxy('s')), false);
});

test('mirroring through TOP/BOTTOM does not throw', () => {
  // `makeConceptUnsatisfiable` calls `addKnownSubsumption(concept, bottom)`. For
  // `owl:Thing`/`owl:Nothing` the inverse is the role ITSELF, so the mirror maps
  // back onto the same pair — it must not blow up or recurse.
  const q = mirrorFixture(true);
  assert.doesNotThrow(() => q.makeConceptUnsatisfiable(P.THING));
  assert.equal(q.isUnsatisfiable(P.THING), true);
});

test('a concept with no role mapping is skipped, not thrown', () => {
  // Seeding is an optimisation, so a bookkeeping gap must degrade to "no mirror"
  // rather than a hard failure. The direct edge is still recorded.
  const q = mirrorFixture(true);
  const orphan = P.internAtomicConcept('internal:prop#orphan');
  assert.doesNotThrow(() => q.addKnownSubsumption(orphan, proxy('s')));
  assert.ok(q.knownSubsumptions.getSuccessors(orphan).has(proxy('s')));
});

// ---------------------------------------------------------------------------
// Reasoning-task descriptions.
// ---------------------------------------------------------------------------

test('task descriptions name the ROLE, not the internal proxy concept', () => {
  const q = mirrorFixture(false);
  assert.equal(q.getSatTestDescription(proxy('r')), `isObjectRoleSatisfiable(${EX}r)`);
  assert.equal(q.getSubsumptionTestDescription(proxy('r'), proxy('s')),
    `isObjectRoleSubsumedBy(${EX}r, ${EX}s)`);
  assert.equal(q.getSubsumedByListTestDescription(proxy('r'), [proxy('s')]),
    `isObjectRoleSubsumedByList(${EX}r, [${EX}s])`);
});

test('an unmapped concept falls back to describing itself', () => {
  const q = mirrorFixture(false);
  // NOTE: `owl:Nothing` would NOT exercise the fallback — `classifyObjectProperties`
  // maps it to `BOTTOM_OBJECT_ROLE`, so it IS in `rolesForConcepts`. Use a concept
  // that is genuinely outside the proxy map.
  const orphan = P.internAtomicConcept('internal:prop#orphan');
  assert.equal(q.getSatTestDescription(orphan), `isObjectRoleSatisfiable(${orphan})`);
});

test('the base class descriptions are unchanged (concept-flavoured)', () => {
  const base = new QuasiOrderClassification(null, { elementClassified() {} },
    P.THING, P.NOTHING, new Set([proxy('r')]));
  assert.equal(base.getSatTestDescription(proxy('r')), `isConceptSatisfiable(${proxy('r')})`);
  assert.equal(base.getSubsumptionTestDescription(proxy('r'), P.THING),
    `isConceptSubsumedBy(${proxy('r')}, ${P.THING})`);
  assert.equal(base.getSubsumedByListTestDescription(proxy('r'), [P.THING]),
    `isConceptSubsumedByList(${proxy('r')}, [${P.THING}])`);
});

// ---------------------------------------------------------------------------
// End-to-end: the hierarchy is right, and the class is LOAD-BEARING.
// ---------------------------------------------------------------------------

test('the object-property hierarchy is correct end to end', () => {
  const reasoner = makeReasoner();
  const hierarchy = reasoner.classifyObjectProperties();
  const nodeFor = (n) => hierarchy.getNodeForElement(role(n));
  const parentsOf = (n) => [...nodeFor(n).getParentNodes()]
    .flatMap((x) => [...x.getEquivalentElements()])
    .map((r) => (r instanceof P.InverseRole ? `inv(${r.inverseRole.iri})` : String(r.iri)));

  assert.ok(parentsOf('mother').includes(EX + 'parent'));
  assert.ok(parentsOf('parent').includes(EX + 'ancestor'));
  // An equivalence class always contains its own representative.
  assert.deepEqual([...nodeFor('child').getEquivalentElements()]
    .map((r) => (r instanceof P.InverseRole ? `inv(${r.inverseRole.iri})` : String(r.iri)))
    .sort(), [EX + 'child', `inv(${EX}parent)`].sort());
});

/**
 * Count `Tableau.prototype.isSatisfiable` calls made by a full
 * `classifyObjectProperties()` run.
 *
 * The prototype is patched (not the instance) because `classifyObjectProperties`
 * builds its own tableau internally via `getTableau(additionalAxioms)`.
 */
function countEndToEndTableauRuns(classify) {
  const reasoner = makeReasoner();
  const { Tableau } = require('../src/tableau/Tableau');
  const original = Tableau.prototype.isSatisfiable;
  let calls = 0;
  Tableau.prototype.isSatisfiable = function patched(opts) {
    calls++;
    return original.call(this, opts);
  };
  try {
    classify(reasoner);
  } finally {
    Tableau.prototype.isSatisfiable = original;
  }
  return calls;
}

test('ForRoles halves the tableau runs versus plain quasi-order classification', () => {
  // THE load-bearing assertion. Both paths produce the SAME hierarchy, so
  // comparing hierarchies would pass with ForRoles deleted; only the run count
  // distinguishes them. Measured: 5 with ForRoles, 10 without.
  const withForRoles = countEndToEndTableauRuns((r) => r.classifyObjectProperties());

  const withoutForRoles = countEndToEndTableauRuns((r) => {
    // Revert the dispatch to the pre-port behaviour.
    const original = Reasoner.classifyAtomicConceptsForRoles;
    Reasoner.classifyAtomicConceptsForRoles = function reverted(tableau, progressMonitor,
      topElement, bottomElement, elements, _hasInverses, _conceptsForRoles, _rolesForConcepts,
      forceQuasiOrderClassification) {
      return Reasoner.classifyAtomicConcepts(tableau, progressMonitor, topElement, bottomElement,
        elements, forceQuasiOrderClassification);
    };
    try {
      r.classifyObjectProperties();
    } finally {
      Reasoner.classifyAtomicConceptsForRoles = original;
    }
  });

  assert.ok(withForRoles < withoutForRoles,
    `expected fewer tableau runs with ForRoles, got ${withForRoles} vs ${withoutForRoles}`);
  assert.equal(withForRoles, 5);
  assert.equal(withoutForRoles, 10);
});

test('the hierarchy is IDENTICAL with and without ForRoles', () => {
  // Confirms the optimisation is semantics-preserving: seeding and mirroring
  // change only how much work is done, never the answer.
  //
  // `traverseDepthFirst` takes a VISITOR OBJECT with `redirect(buffer)` and
  // `visit(level, node, parentNode, firstVisit)` — not a bare callback.
  const describe = (hierarchy) => {
    const out = [];
    hierarchy.traverseDepthFirst({
      redirect: () => true,
      visit: (level, node, parentNode, firstVisit) => {
        if (!firstVisit) return;
        out.push([...node.getEquivalentElements()]
          .map((r) => (r instanceof P.InverseRole ? `inv(${r.inverseRole.iri})` : String(r.iri)))
          .sort().join('|'));
      }
    });
    return out.sort();
  };

  const withForRoles = describe(makeReasoner().classifyObjectProperties());

  const reasoner = makeReasoner();
  const original = Reasoner.classifyAtomicConceptsForRoles;
  Reasoner.classifyAtomicConceptsForRoles = function reverted(tableau, progressMonitor,
    topElement, bottomElement, elements, _hasInverses, _conceptsForRoles, _rolesForConcepts,
    forceQuasiOrderClassification) {
    return Reasoner.classifyAtomicConcepts(tableau, progressMonitor, topElement, bottomElement,
      elements, forceQuasiOrderClassification);
  };
  let withoutForRoles;
  try {
    withoutForRoles = describe(reasoner.classifyObjectProperties());
  } finally {
    Reasoner.classifyAtomicConceptsForRoles = original;
  }

  assert.deepEqual(withForRoles, withoutForRoles);
  // Guard against a vacuous pass: the fixture must actually produce a hierarchy.
  // Measured: 10 nodes (top, bottom, mother, father, parent|child⁻, child|parent⁻,
  // ancestor, and the three inverses).
  assert.ok(withForRoles.length >= 8,
    `expected a non-trivial hierarchy, got ${withForRoles.length} nodes`);
});

test('data-property classification does NOT use ForRoles (HermiT parity)', () => {
  // OWL 2 has no inverse data properties, so HermiT classifies data roles with
  // the plain algorithm (Reasoner.java:1404). Guard against someone "fixing"
  // that asymmetry: the data-role path must still produce a correct hierarchy.
  const configuration = new Configuration();
  configuration.forceQuasiOrderClassification = true;
  const dp = (n) => E.dataProperty(EX + n);
  const subDataPropertyOf = (subProperty, superProperty) =>
    ({ axiomType: AT.SUB_DATA_PROPERTY_OF, subProperty, superProperty });
  const reasoner = new Reasoner(ontology([
    declaration(dp('hasName')), declaration(dp('hasLabel')),
    subDataPropertyOf(dp('hasName'), dp('hasLabel')),
    E.subclassOf(cls('A'), E.objectUnionOf([cls('B'), cls('C')]))
  ]), configuration);
  assert.equal(reasoner.isConsistent(), true);
  const hierarchy = reasoner.classifyDataProperties();
  const node = hierarchy.getNodeForElement(
    P.internAtomicRole(E.iriString(EX + 'hasName'), true));
  const parents = [...node.getParentNodes()]
    .flatMap((x) => [...x.getEquivalentElements()]).map((r) => String(r.iri));
  assert.ok(parents.includes(EX + 'hasLabel'));
});
