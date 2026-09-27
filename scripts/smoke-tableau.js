'use strict';
// Temporary smoke test for the Tableau engine.

const { DLOntology } = require('../src/model/DLOntology');
const { createDLClause } = require('../src/model/DLClause');
const { createAtom } = require('../src/model/Atom');
const {
  internAtomicConcept, internAtomicRole, internAtLeastConcept, internInverseRole,
  NOTHING, EQUALITY
} = require('../src/model/DLPredicate');
const { createIndividual, X, Y } = require('../src/model/Term');
const { Tableau } = require('../src/tableau/Tableau');
const { CreationOrderStrategy } = require('../src/tableau/ExpansionStrategy');
const { createBlockingStrategy } = require('../src/tableau/BlockingStrategy');

const A = internAtomicConcept('http://ex.org/A');
const B = internAtomicConcept('http://ex.org/B');
const C = internAtomicConcept('http://ex.org/C');
const R = internAtomicRole('http://ex.org/R', false);
const a = createIndividual('http://ex.org#a');

// Always load the permanent ABox so per-test individuals get nodes.
const RUN = { loadPermanentABox: true };

function mkOntology(clauses, positiveFacts = [], negativeFacts = [], flags = {}) {
  return new DLOntology(Object.assign({
    dlClauses: clauses, positiveFacts, negativeFacts,
    hasInverseRoles: false, hasAtMostRestrictions: false, hasNominals: false,
    hasDatatypes: false, hasUnknownDatatypeRestrictions: false
  }, flags));
}

function mkTableau(onto, hasInverseRoles = false) {
  return new Tableau({
    permanentDLOntology: onto,
    existentialExpansionStrategy: new CreationOrderStrategy(
      createBlockingStrategy(null, hasInverseRoles))
  });
}

let failures = 0;
function check(name, actual, expected) {
  const ok = actual === expected;
  if (!ok) failures++;
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}  (got ${actual}, expected ${expected})`);
}

// 1. A sub B, A(a)  =>  B(a)
{
  const clause = createDLClause([createAtom(B, X)], [createAtom(A, X)]);
  const onto = mkOntology([clause], [createAtom(A, a)]);
  const t = mkTableau(onto);
  const sat = t.isSatisfiable(RUN);
  check('A sub B, A(a) is satisfiable', sat, true);
  check('  B(a) entailed', t.extensionManager.containsConceptAssertion(B, t.termsToNodes.get(a)), true);
}

// 2. A sub B, B sub C, A sub not C  =>  A(a) unsatisfiable
{
  const clauses = [
    createDLClause([createAtom(B, X)], [createAtom(A, X)]),
    createDLClause([createAtom(C, X)], [createAtom(B, X)]),
    createDLClause([], [createAtom(A, X), createAtom(C, X)])
  ];
  const onto = mkOntology(clauses, [createAtom(A, a)]);
  const t = mkTableau(onto);
  check('A sub B sub C, A sub not C, A(a) is inconsistent', t.isSatisfiable(RUN), false);
}

// 3. A sub exists R.B  (existential expansion)
{
  const existsRB = internAtLeastConcept(1, R, B);
  const clauses = [createDLClause([createAtom(existsRB, X)], [createAtom(A, X)])];
  const onto = mkOntology(clauses, [createAtom(A, a)]);
  const t = mkTableau(onto);
  check('A sub exists R.B satisfiable', t.isSatisfiable(RUN), true);
  check('  nodes created > 1', t.numberOfNodesInTableau > 1, true);
}

// 4. A sub exists R.A (infinite chain -- must terminate by blocking)
{
  const existsRA = internAtLeastConcept(1, R, A);
  const clauses = [createDLClause([createAtom(existsRA, X)], [createAtom(A, X)])];
  const onto = mkOntology(clauses, [createAtom(A, a)]);
  const t = mkTableau(onto);
  check('A sub exists R.A terminates (blocking)', t.isSatisfiable(RUN), true);
}

// 5. A sub B or C  (disjunctive branching)
{
  const clauses = [createDLClause([createAtom(B, X), createAtom(C, X)], [createAtom(A, X)])];
  const onto = mkOntology(clauses, [createAtom(A, a)]);
  const t = mkTableau(onto);
  check('A sub B or C satisfiable', t.isSatisfiable(RUN), true);
  const node = t.termsToNodes.get(a);
  check('  B(a) or C(a) holds',
    t.extensionManager.containsConceptAssertion(B, node) || t.extensionManager.containsConceptAssertion(C, node), true);
}

// 6. A sub B or C, B sub bot, C sub bot  =>  A(a) inconsistent
{
  const clauses = [
    createDLClause([createAtom(B, X), createAtom(C, X)], [createAtom(A, X)]),
    createDLClause([], [createAtom(B, X)]),
    createDLClause([], [createAtom(C, X)])
  ];
  const onto = mkOntology(clauses, [createAtom(A, a)]);
  const t = mkTableau(onto);
  check('A sub B or C, not B, not C, A(a) inconsistent', t.isSatisfiable(RUN), false);
}

// 7. A sub B or C, B sub bot  =>  C(a) must hold
{
  const clauses = [
    createDLClause([createAtom(B, X), createAtom(C, X)], [createAtom(A, X)]),
    createDLClause([], [createAtom(B, X)])
  ];
  const onto = mkOntology(clauses, [createAtom(A, a)]);
  const t = mkTableau(onto);
  check('A sub B or C, not B => satisfiable', t.isSatisfiable(RUN), true);
  check('  C(a) holds after backjump', t.extensionManager.containsConceptAssertion(C, t.termsToNodes.get(a)), true);
}

// 8. Inverse roles: R^- sub S
{
  const S = internAtomicRole('http://ex.org/S', false);
  const Rinv = internInverseRole(R);
  const clauses = [createDLClause([createAtom(S, X, Y)], [createAtom(Rinv, X, Y)])];
  const b = createIndividual('http://ex.org#b');
  const onto = mkOntology(clauses, [createAtom(R, b, a)], [], { hasInverseRoles: true });
  const t = mkTableau(onto, true);
  check('R^- sub S satisfiable', t.isSatisfiable(RUN), true);
  check('  S(a,b) entailed',
    t.extensionManager.containsRoleAssertion(S, t.termsToNodes.get(a), t.termsToNodes.get(b)), true);
}

// 9. Equality / merging: A(a), A(b), A sub =1  =>  a = b
{
  const clauses = [createDLClause([createAtom(EQUALITY, X, Y)], [createAtom(A, X), createAtom(A, Y)])];
  const b = createIndividual('http://ex.org#b');
  const onto = mkOntology(clauses, [createAtom(A, a), createAtom(A, b)]);
  const t = mkTableau(onto);
  check('equality clause satisfiable', t.isSatisfiable(RUN), true);
  check('  a and b merged',
    t.termsToNodes.get(a).getCanonicalNode() === t.termsToNodes.get(b).getCanonicalNode(), true);
}

// 10. owl:Nothing asserted  =>  inconsistent
{
  const onto = mkOntology([], [createAtom(NOTHING, a)]);
  const t = mkTableau(onto);
  check('Nothing(a) inconsistent', t.isSatisfiable(RUN), false);
}

console.log(failures === 0 ? '\nALL PASS' : `\n${failures} FAILURE(S)`);
process.exit(failures === 0 ? 0 : 1);
