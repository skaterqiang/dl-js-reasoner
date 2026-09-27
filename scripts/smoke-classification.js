'use strict';
/**
 * Smoke test for the hierarchy / classification layer.
 *
 * Exercises `DeterministicClassification` (Horn ontologies) and
 * `QuasiOrderClassification` (non-Horn), plus the `Hierarchy` /
 * `HierarchyNode` / `HierarchySearch` / `Graph` support classes.
 *
 * Run with:  node scripts/smoke-classification.js
 */

const { DLOntology } = require('../src/model/DLOntology');
const { createDLClause } = require('../src/model/DLClause');
const { createAtom } = require('../src/model/Atom');
const {
  internAtomicConcept, internAtomicRole, internAtLeastConcept,
  THING, NOTHING, TOP_OBJECT_ROLE, BOTTOM_OBJECT_ROLE
} = require('../src/model/DLPredicate');
const { createIndividual, X, Y } = require('../src/model/Term');
const { Tableau } = require('../src/tableau/Tableau');
const { CreationOrderStrategy } = require('../src/tableau/ExpansionStrategy');
const { createBlockingStrategy } = require('../src/tableau/BlockingStrategy');
const { Graph } = require('../src/graph/Graph');
const { Hierarchy, HierarchyNode } = require('../src/hierarchy/Hierarchy');
const { findPosition } = require('../src/hierarchy/HierarchySearch');
const { DeterministicClassification } = require('../src/hierarchy/DeterministicClassification');
const { QuasiOrderClassification } = require('../src/hierarchy/QuasiOrderClassification');
const { QuasiOrderClassificationForRoles } =
  require('../src/hierarchy/QuasiOrderClassificationForRoles');

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

function checkSet(name, actualSet, expectedArray) {
  checks++;
  const actual = [...actualSet].map(String).sort().join('|');
  const expected = [...expectedArray].map(String).sort().join('|');
  const ok = actual === expected;
  if (!ok) failures++;
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}\n        got      ${actual}\n        expected ${expected}`);
}

const EX = 'http://ex.org/';
const concept = (n) => internAtomicConcept(EX + n);
const A = concept('A'), B = concept('B'), C = concept('C'), D = concept('D'), E = concept('E');
const R = internAtomicRole(EX + 'R', false);
const a = createIndividual(EX + 'a');

/** `sub ⊑ sup` as a DL clause. */
const sub = (subC, supC) => createDLClause([createAtom(supC, X)], [createAtom(subC, X)]);
/** `sub ⊑ ¬sup`, i.e. the two are disjoint. */
const disj = (c1, c2) => createDLClause([], [createAtom(c1, X), createAtom(c2, X)]);

function mkOntology(clauses, positiveFacts = [], negativeFacts = [], flags = {}) {
  return new DLOntology(Object.assign({
    dlClauses: clauses, positiveFacts, negativeFacts,
    atomicConcepts: new Set([THING, NOTHING, A, B, C, D, E]),
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

const ALL = new Set([THING, NOTHING, A, B, C, D, E]);
const MONITOR = { elementClassified() {} };

/** Classify with whichever strategy the tableau's determinism dictates. */
function classify(tableau, elements = ALL, forceQuasiOrder = false) {
  if (tableau.isDeterministic() && !forceQuasiOrder) {
    return new DeterministicClassification(tableau, MONITOR, THING, NOTHING, elements).classify();
  }
  return new QuasiOrderClassification(tableau, MONITOR, THING, NOTHING, elements).classify();
}

/** The equivalent elements of the node holding `element`, as sorted IRIs. */
function equivOf(hierarchy, element) {
  const node = hierarchy.getNodeForElement(element);
  if (!node) return ['<absent>'];
  return [...node.getEquivalentElements()].map((e) => String(e).replace(EX, '')).sort();
}

/** Direct parents (super-concepts) of the node holding `element`. */
function parentsOf(hierarchy, element) {
  const node = hierarchy.getNodeForElement(element);
  if (!node) return ['<absent>'];
  return [...node.getParentNodes()].map((n) => String(n.getRepresentative()).replace(EX, '')).sort();
}

/** Direct children (sub-concepts) of the node holding `element`. */
function childrenOf(hierarchy, element) {
  const node = hierarchy.getNodeForElement(element);
  if (!node) return ['<absent>'];
  return [...node.getChildNodes()].map((n) => String(n.getRepresentative()).replace(EX, '')).sort();
}

function section(title) {
  console.log(`\n--- ${title} ---`);
}

// ---------------------------------------------------------------------------
// 0. Graph
// ---------------------------------------------------------------------------
section('Graph');
{
  const g = new Graph();
  g.addEdge('a', 'b');
  g.addEdge('b', 'c');
  g.addEdge('a', 'd');
  check('Graph elements size', g.getElements().size, 4);
  check('Graph successors of a', g.getSuccessors('a').size, 2);
  check('Graph successors of unknown', g.getSuccessors('zzz').size, 0);
  check('Graph isReachableSuccessor a->c', g.isReachableSuccessor('a', 'c'), true);
  check('Graph isReachableSuccessor c->a', g.isReachableSuccessor('c', 'a'), false);
  check('Graph isReachableSuccessor a->a', g.isReachableSuccessor('a', 'a'), true);
  checkSet('Graph reachableSuccessors(a)', g.getReachableSuccessors('a'), ['a', 'b', 'c', 'd']);

  const inv = g.getInverse();
  check('Graph inverse c->b', inv.isReachableSuccessor('c', 'b'), true);
  check('Graph inverse a->c', inv.isReachableSuccessor('a', 'c'), false);

  g.transitivelyClose();
  check('Graph transitivelyClose a->c direct', g.getSuccessors('a').has('c'), true);

  const clone = g.clone();
  clone.addEdge('a', 'zzz');
  check('Graph clone is independent', g.getSuccessors('a').has('zzz'), false);

  const g2 = new Graph();
  g2.addEdge('x', 'y');
  g2.addEdge('y', 'z');
  g2.removeElements(new Set(['y']));
  check('Graph removeElements drops node', g2.getElements().has('y'), false);
  check('Graph removeElements drops edges', g2.getSuccessors('x').size, 0);
}

// ---------------------------------------------------------------------------
// 1. HierarchyNode / Hierarchy primitives
// ---------------------------------------------------------------------------
section('HierarchyNode / Hierarchy');
{
  const top = new HierarchyNode('top');
  const bottom = new HierarchyNode('bottom');
  const mid = new HierarchyNode('mid', new Set(['mid', 'mid2']), new Set([top]), new Set([bottom]));
  top.childNodes.add(mid);
  mid.parentNodes.add(top);
  bottom.parentNodes.add(mid);
  mid.childNodes.add(bottom);
  const h = new Hierarchy(top, bottom);
  h.nodesByElements.set('mid', mid);
  h.nodesByElements.set('mid2', mid);

  check('Hierarchy topNode', h.getTopNode(), top);
  check('Hierarchy isEmpty (has mid)', h.isEmpty(), false);
  check('Hierarchy getNodeForElement mid2', h.getNodeForElement('mid2'), mid);
  check('Hierarchy getAllNodesSet size', h.getAllNodesSet().size, 3);
  check('Hierarchy getDepth', h.getDepth(), 2);
  check('HierarchyNode isEquivalentElement', mid.isEquivalentElement('mid2'), true);
  check('HierarchyNode isAncestorElement (self, inclusive)', mid.isAncestorElement('mid'), true);
  check('HierarchyNode isAncestorElement top', mid.isAncestorElement('top'), true);
  check('HierarchyNode isDescendantElement bottom', mid.isDescendantElement('bottom'), true);
  check('HierarchyNode toString', mid.toString(), '{mid, mid2}');

  const empty = Hierarchy.emptyHierarchy(['x'], 'top', 'bottom');
  check('emptyHierarchy isEmpty', empty.isEmpty(), false);
  check('emptyHierarchy top===bottom node', empty.getTopNode() === empty.getBottomNode(), true);
  check('emptyHierarchy holds x', empty.getNodeForElement('x') === empty.getTopNode(), true);

  const trivial = Hierarchy.trivialHierarchy('top', 'bottom');
  check('trivialHierarchy isEmpty', trivial.isEmpty(), true);
  check('trivialHierarchy top->bottom', trivial.getTopNode().getChildNodes().has(trivial.getBottomNode()), true);
}

// ---------------------------------------------------------------------------
// 2. HierarchySearch.findPosition against a hand-built hierarchy
// ---------------------------------------------------------------------------
section('HierarchySearch');
{
  //   top
  //    |
  //    B
  //   / \
  //  A   C
  //   \ /
  //   bottom
  const top = new HierarchyNode(THING);
  const bottom = new HierarchyNode(NOTHING);
  const nB = new HierarchyNode(B, new Set([B]), new Set([top]), new Set());
  const nA = new HierarchyNode(A, new Set([A]), new Set([nB]), new Set());
  const nC = new HierarchyNode(C, new Set([C]), new Set([nB]), new Set());
  top.childNodes.add(nB);
  nB.parentNodes.add(top);
  nB.childNodes.add(nA); nB.childNodes.add(nC);
  nA.parentNodes.add(nB); nC.parentNodes.add(nB);
  nA.childNodes.add(bottom); nC.childNodes.add(bottom);
  bottom.parentNodes.add(nA); bottom.parentNodes.add(nC);

  const hierarchy = new Hierarchy(top, bottom);
  hierarchy.nodesByElements.set(B, nB);
  hierarchy.nodesByElements.set(A, nA);
  hierarchy.nodesByElements.set(C, nC);

  // A relation that says "D is subsumed by B but by neither A nor C".
  const relation = {
    doesSubsume(parent, child) {
      return parent === THING || parent === B;
    }
  };
  const pos = findPosition(relation, D, top, bottom);
  check('findPosition parents = {B}', [...pos.getParentNodes()].length, 1);
  check('findPosition parent is nB', [...pos.getParentNodes()][0] === nB, true);
  check('findPosition children = {bottom}', [...pos.getChildNodes()].length, 1);
  check('findPosition child is bottom', [...pos.getChildNodes()][0] === bottom, true);

  // A relation in which E is equivalent to A: doesSubsume(p, c) means c ⊑ p,
  // so it must hold in BOTH directions for the pair (A, E).
  const SUBSUMERS = new Map([
    [THING, new Set([THING])],
    [B, new Set([THING, B])],
    [A, new Set([THING, B, A, E])],
    [E, new Set([THING, B, A, E])],
    [C, new Set([THING, B, C])],
    [NOTHING, new Set([THING, B, A, E, C, NOTHING])]
  ]);
  const relation2 = {
    doesSubsume(parent, child) {
      const s = SUBSUMERS.get(child);
      return s !== undefined && s.has(parent);
    }
  };
  const pos2 = findPosition(relation2, E, top, bottom);
  check('findPosition collapses to existing node nA', pos2 === nA, true);

  // A relation in which E sits strictly between B and {A, C}.
  const SUBSUMERS3 = new Map([
    [THING, new Set([THING])],
    [B, new Set([THING, B])],
    [E, new Set([THING, B, E])],
    [A, new Set([THING, B, E, A])],
    [C, new Set([THING, B, E, C])],
    [NOTHING, new Set([THING, B, E, A, C, NOTHING])]
  ]);
  const relation3 = {
    doesSubsume(parent, child) {
      const s = SUBSUMERS3.get(child);
      return s !== undefined && s.has(parent);
    }
  };
  const pos3 = findPosition(relation3, E, top, bottom);
  check('findPosition inserts a new node', pos3 !== nA && pos3 !== nB, true);
  check('findPosition new node parent is nB', [...pos3.getParentNodes()][0] === nB, true);
  checkSet('findPosition new node children', [...pos3.getChildNodes()].map((n) => n.getRepresentative()), [A, C]);
}

// ---------------------------------------------------------------------------
// 3. DeterministicClassification: linear chain A ⊑ B ⊑ C ⊑ D
// ---------------------------------------------------------------------------
section('DeterministicClassification — linear chain');
{
  const onto = mkOntology([sub(A, B), sub(B, C), sub(C, D)]);
  const t = mkTableau(onto);
  check('chain ontology is Horn', onto.isHorn, true);
  check('chain tableau is deterministic', t.isDeterministic(), true);

  const h = classify(t);
  check('chain: A is not top', h.getNodeForElement(A) !== h.getTopNode(), true);
  check('chain: A parent is B', parentsOf(h, A).join(','), 'B');
  check('chain: B parent is C (transitively reduced)', parentsOf(h, B).join(','), 'C');
  check('chain: C parent is D', parentsOf(h, C).join(','), 'D');
  check('chain: D parent is owl:Thing', parentsOf(h, D).join(','), String(THING));
  check('chain: B child is A', childrenOf(h, B).join(','), 'A');
  check('chain: depth is 5 (top,A,B,C,D,bottom path)', h.getDepth() >= 4, true);
  check('chain: A isAncestorElement D', h.getNodeForElement(A).isAncestorElement(D), true);
  check('chain: D isDescendantElement A', h.getNodeForElement(D).isDescendantElement(A), true);
  check('chain: A not subsumed by C directly', h.getNodeForElement(A).getParentNodes().has(h.getNodeForElement(C)), false);
}

// ---------------------------------------------------------------------------
// 4. DeterministicClassification: diamond
// ---------------------------------------------------------------------------
section('DeterministicClassification — diamond');
{
  const onto = mkOntology([sub(A, B), sub(A, C), sub(B, D), sub(C, D)]);
  const t = mkTableau(onto);
  const h = classify(t);
  checkSet('diamond: A parents', parentsOf(h, A), ['B', 'C']);
  checkSet('diamond: D children', childrenOf(h, D), ['B', 'C']);
  check('diamond: B parent is D', parentsOf(h, B).join(','), 'D');
  check('diamond: C parent is D', parentsOf(h, C).join(','), 'D');
  check('diamond: D parent is Thing', parentsOf(h, D).join(','), String(THING));
  // top, bottom, A, B, C, D and the unconstrained E.
  check('diamond: node count', h.getAllNodesSet().size, 7);
}

// ---------------------------------------------------------------------------
// 5. DeterministicClassification: equivalence  A ⊑ B, B ⊑ A
// ---------------------------------------------------------------------------
section('DeterministicClassification — equivalence');
{
  const onto = mkOntology([sub(A, B), sub(B, A), sub(B, C)]);
  const t = mkTableau(onto);
  const h = classify(t);
  check('equiv: A and B share a node', h.getNodeForElement(A) === h.getNodeForElement(B), true);
  checkSet('equiv: node holds {A,B}', equivOf(h, A), ['A', 'B']);
  check('equiv: node parent is C', parentsOf(h, A).join(','), 'C');
  // top, bottom, {A B}, C, D and the unconstrained E.
  check('equiv: node count is 6', h.getAllNodesSet().size, 6);
}

// ---------------------------------------------------------------------------
// 6. DeterministicClassification: unsatisfiable concept sinks to bottom
// ---------------------------------------------------------------------------
section('DeterministicClassification — unsatisfiable concept');
{
  // A ⊑ ¬A  makes A unsatisfiable.
  const onto = mkOntology([disj(A, A), sub(B, C)]);
  const t = mkTableau(onto);
  const h = classify(t);
  check('unsat: A is in the bottom node', h.getNodeForElement(A) === h.getBottomNode(), true);
  check('unsat: B is not in the bottom node', h.getNodeForElement(B) !== h.getBottomNode(), true);
  check('unsat: B parent is C', parentsOf(h, B).join(','), 'C');
}

// ---------------------------------------------------------------------------
// 7. DeterministicClassification: inconsistent ontology -> emptyHierarchy
// ---------------------------------------------------------------------------
section('DeterministicClassification — inconsistent ontology');
{
  // An empty-headed clause with an empty body is an outright clash.
  const onto = mkOntology([createDLClause([], [createAtom(THING, X)])]);
  const t = mkTableau(onto);
  const h = classify(t);
  check('inconsistent: top node === bottom node', h.getTopNode() === h.getBottomNode(), true);
  check('inconsistent: A is in the top/bottom node', h.getNodeForElement(A) === h.getTopNode(), true);
  check('inconsistent: single node', h.getAllNodesSet().size, 1);
}

// ---------------------------------------------------------------------------
// 8. DeterministicClassification: disjoint siblings
// ---------------------------------------------------------------------------
section('DeterministicClassification — disjointness');
{
  const onto = mkOntology([sub(A, C), sub(B, C), disj(A, B)]);
  const t = mkTableau(onto);
  const h = classify(t);
  check('disjoint: A parent is C', parentsOf(h, A).join(','), 'C');
  check('disjoint: B parent is C', parentsOf(h, B).join(','), 'C');
  checkSet('disjoint: C children', childrenOf(h, C), ['A', 'B']);
  check('disjoint: A is not an ancestor of B', h.getNodeForElement(A).isAncestorElement(B), false);
}

// ---------------------------------------------------------------------------
// 9. DeterministicClassification: existential  A ⊑ ∃R.B, B ⊑ C
// ---------------------------------------------------------------------------
section('DeterministicClassification — existential');
{
  const existsRB = internAtLeastConcept(1, R, B);
  const onto = mkOntology([
    createDLClause([createAtom(existsRB, X)], [createAtom(A, X)]),
    sub(B, C)
  ]);
  const t = mkTableau(onto);
  const h = classify(t);
  check('existential: A parent is Thing', parentsOf(h, A).join(','), String(THING));
  check('existential: B parent is C', parentsOf(h, B).join(','), 'C');
  check('existential: A is not subsumed by B', h.getNodeForElement(A).isAncestorElement(B), false);
}

// ---------------------------------------------------------------------------
// 10. QuasiOrderClassification on a Horn ontology (forced)
// ---------------------------------------------------------------------------
section('QuasiOrderClassification — forced on Horn chain');
{
  const onto = mkOntology([sub(A, B), sub(B, C), sub(C, D)]);
  const t = mkTableau(onto);
  const hDet = classify(t);
  const hQ = new QuasiOrderClassification(t, MONITOR, THING, NOTHING, ALL).classify();
  check('quasi: A parent is B', parentsOf(hQ, A).join(','), 'B');
  check('quasi: B parent is C', parentsOf(hQ, B).join(','), 'C');
  check('quasi: C parent is D', parentsOf(hQ, C).join(','), 'D');
  check('quasi: D parent is Thing', parentsOf(hQ, D).join(','), String(THING));
  check('quasi: same node count as deterministic', hQ.getAllNodesSet().size, hDet.getAllNodesSet().size);
}

// ---------------------------------------------------------------------------
// 11. QuasiOrderClassification on a genuinely non-Horn ontology
// ---------------------------------------------------------------------------
section('QuasiOrderClassification — non-Horn (disjunctive)');
{
  // D ⊑ B ⊔ C  — head length 2, so the ontology is not Horn.
  const disjunctive = createDLClause([createAtom(B, X), createAtom(C, X)], [createAtom(D, X)]);
  const onto = mkOntology([disjunctive, sub(A, D)]);
  const t = mkTableau(onto);
  check('non-Horn ontology isHorn === false', onto.isHorn, false);
  check('non-Horn tableau isDeterministic === false', t.isDeterministic(), false);

  const h = classify(t);
  check('non-Horn: A parent is D', parentsOf(h, A).join(','), 'D');
  check('non-Horn: D parent is Thing (neither B nor C is entailed)',
    parentsOf(h, D).join(','), String(THING));
  check('non-Horn: A is not subsumed by B', h.getNodeForElement(A).isAncestorElement(B), false);
  check('non-Horn: A is not subsumed by C', h.getNodeForElement(A).isAncestorElement(C), false);
}

// ---------------------------------------------------------------------------
// 12. QuasiOrderClassification: unsatisfiable concept in a non-Horn ontology
// ---------------------------------------------------------------------------
section('QuasiOrderClassification — non-Horn with unsatisfiable concept');
{
  const disjunctive = createDLClause([createAtom(B, X), createAtom(C, X)], [createAtom(D, X)]);
  const onto = mkOntology([disjunctive, disj(B, B), disj(C, C), sub(A, D)]);
  const t = mkTableau(onto);
  const h = classify(t);
  check('non-Horn unsat: D in bottom node', h.getNodeForElement(D) === h.getBottomNode(), true);
  check('non-Horn unsat: A in bottom node', h.getNodeForElement(A) === h.getBottomNode(), true);
}

// ---------------------------------------------------------------------------
// 13. Hierarchy.toString / traverseDepthFirst
// ---------------------------------------------------------------------------
section('Hierarchy printing');
{
  const A2 = concept('A2');
  const onto = mkOntology([sub(A, B), sub(B, C), sub(B, A2)]);
  const t = mkTableau(onto);
  const elements = new Set([THING, NOTHING, A, B, C, A2]);
  const h = classify(t, elements);
  const text = h.toString();
  check('toString is non-empty', text.length > 0, true);
  check('toString mentions C', text.includes('C'), true);

  let firstVisits = 0;
  let allVisits = 0;
  h.traverseDepthFirst({
    redirect: () => true,
    visit: (level, node, parentNode, firstVisit) => {
      allVisits++;
      if (firstVisit) firstVisits++;
    }
  });
  check('traverseDepthFirst first-visits every node exactly once',
    firstVisits, h.getAllNodesSet().size);
  // C and A2 are siblings above the bottom node, so bottom is reached twice.
  check('traverseDepthFirst revisits shared nodes', allVisits > firstVisits, true);
}

// ---------------------------------------------------------------------------
// 14. ABox-aware classification (facts present)
// ---------------------------------------------------------------------------
section('Classification with an ABox');
{
  const onto = mkOntology([sub(A, B), sub(B, C)], [createAtom(A, a)]);
  const t = mkTableau(onto);
  const h = classify(t);
  check('abox: A parent is B', parentsOf(h, A).join(','), 'B');
  check('abox: C parent is Thing', parentsOf(h, C).join(','), String(THING));
}

// ---------------------------------------------------------------------------
// 15. QuasiOrderClassificationForRoles — seeding and inverse mirroring
//
// Object properties are classified by proxying each role `R` as a fresh concept
// `internal:prop#R ≡ ∃R.F`. The base `QuasiOrderClassification` is a poor fit
// for that encoding, and this subclass fixes two things:
//
//   1. its seeder reads the told ROLE inclusions. The base seeder only
//      recognises clauses whose body AND head predicates are `AtomicConcept`s,
//      but `R ⊑ S` clausifies to `R(X,Y) → S(X,Y)` with `AtomicRole`
//      predicates — so the base seeds NOTHING;
//   2. it mirrors every subsumption onto the inverse roles, because
//      `R ⊑ S` implies `R⁻ ⊑ S⁻`.
//
// Both are OPTIMISATIONS, so the hierarchy is identical either way and only the
// number of tableau runs differs. `test/role-classification.test.js` asserts
// that run count (5 vs 10); here we check the seeding and mirroring directly.
// ---------------------------------------------------------------------------
section('QuasiOrderClassificationForRoles');
{
  const S = internAtomicRole(EX + 'S', false);
  const T = internAtomicRole(EX + 'T', false);
  const cR = internAtomicConcept(`internal:prop#${EX}R`);
  const cS = internAtomicConcept(`internal:prop#${EX}S`);
  const cT = internAtomicConcept(`internal:prop#${EX}T`);
  const cRi = internAtomicConcept(`internal:prop#inv#${EX}R`);
  const cSi = internAtomicConcept(`internal:prop#inv#${EX}S`);
  const cTi = internAtomicConcept(`internal:prop#inv#${EX}T`);

  const conceptsForRoles = new Map([
    [R, cR], [S, cS], [T, cT],
    [R.getInverse(), cRi], [S.getInverse(), cSi], [T.getInverse(), cTi],
    [TOP_OBJECT_ROLE, THING], [BOTTOM_OBJECT_ROLE, NOTHING]
  ]);
  const rolesForConcepts = new Map();
  for (const [role, concept] of conceptsForRoles) rolesForConcepts.set(concept, role);

  /** `sub ⊑ sup` as a role-inclusion DL clause: `sub(X,Y) → sup(X,Y)`. */
  const roleSub = (subRole, supRole) =>
    createDLClause([createAtom(supRole, X, Y)], [createAtom(subRole, X, Y)]);
  /** `sub ⊑ sup⁻`: the head atom for an inverse role has its arguments SWAPPED. */
  const roleSubInverse = (subRole, supRole) =>
    createDLClause([createAtom(supRole, Y, X)], [createAtom(subRole, X, Y)]);

  function mkForRoles(hasInverses) {
    return new QuasiOrderClassificationForRoles(null, MONITOR, THING, NOTHING,
      new Set(rolesForConcepts.keys()), hasInverses, conceptsForRoles, rolesForConcepts);
  }

  // -- seeding -------------------------------------------------------------
  {
    const q = mkForRoles(true);
    q.initialiseKnownSubsumptionsUsingToldSubsumers([roleSub(R, S), roleSub(S, T)]);
    check('roles: R ⊑ S seeded', q.knownSubsumptions.getSuccessors(cR).has(cS), true);
    // The closure is transitive, so the seeded chain reaches T.
    check('roles: R ⊑ T seeded transitively',
      q.knownSubsumptions.isReachableSuccessor(cR, cT), true);
  }
  {
    // The base class seeds nothing: its seeder requires AtomicConcept predicates.
    const base = new QuasiOrderClassification(null, MONITOR, THING, NOTHING,
      new Set(rolesForConcepts.keys()));
    base.initialiseKnownSubsumptionsUsingToldSubsumers([roleSub(R, S), roleSub(S, T)]);
    // `getAllKnownSubsumers` is `getReachableSuccessors`, which INCLUDES the node
    // itself, so an unseeded graph still reports one "subsumer" (self).
    check('roles: BASE seeds nothing',
      [...base.getAllKnownSubsumers(cR)].filter((c) => c !== cR).length, 0);
  }

  // -- seeding through an inverse ------------------------------------------
  {
    const q = mkForRoles(true);
    // `R ⊑ S⁻` ⟺ `R⁻ ⊑ S`.
    q.initialiseKnownSubsumptionsUsingToldSubsumers([roleSubInverse(R, S)]);
    check('roles: R ⊑ S⁻ seeds R⁻ ⊑ S', q.knownSubsumptions.getSuccessors(cRi).has(cS), true);
    check('roles: R ⊑ S⁻ does not seed R ⊑ S',
      q.knownSubsumptions.getSuccessors(cR).has(cS), false);
  }

  // -- mirroring ------------------------------------------------------------
  {
    const q = mkForRoles(true);
    q.addKnownSubsumption(cR, cS);
    check('roles: mirror R⁻ ⊑ S⁻ added',
      q.knownSubsumptions.getSuccessors(cRi).has(cSi), true);
    // `R ⊑ S` implies `R⁻ ⊑ S⁻`. It does NOT imply the converse `S⁻ ⊑ R⁻`.
    check('roles: mirror is not the converse S⁻ ⊑ R⁻',
      q.knownSubsumptions.getSuccessors(cSi).has(cRi), false);

    q.addPossibleSubsumption(cR, cT);
    check('roles: possible subsumption mirrored',
      q.possibleSubsumptions.getSuccessors(cRi).has(cTi), true);
  }
  {
    const q = mkForRoles(false);
    q.addKnownSubsumption(cR, cS);
    check('roles: hasInverses=false keeps the direct edge',
      q.knownSubsumptions.getSuccessors(cR).has(cS), true);
    check('roles: hasInverses=false suppresses the mirror',
      q.knownSubsumptions.getSuccessors(cRi).has(cSi), false);
  }
  {
    // TOP/BOTTOM are their own inverses, so the mirror maps back onto the same
    // pair. `makeConceptUnsatisfiable(THING)` must not throw or recurse.
    const q = mkForRoles(true);
    let threw = false;
    try { q.makeConceptUnsatisfiable(THING); } catch (e) { threw = true; }
    check('roles: makeConceptUnsatisfiable(Thing) does not throw', threw, false);
    check('roles: Thing is unsatisfiable', q.isUnsatisfiable(THING), true);
  }
  {
    // Seeding is an optimisation, so a bookkeeping gap degrades to "no mirror"
    // rather than a hard failure.
    const q = mkForRoles(true);
    const orphan = internAtomicConcept('internal:prop#orphan');
    let threw = false;
    try { q.addKnownSubsumption(orphan, cS); } catch (e) { threw = true; }
    check('roles: unmapped concept does not throw', threw, false);
    check('roles: unmapped concept still records the direct edge',
      q.knownSubsumptions.getSuccessors(orphan).has(cS), true);
  }

  // -- reasoning-task descriptions ------------------------------------------
  {
    const q = mkForRoles(false);
    check('roles: sat description names the role',
      q.getSatTestDescription(cR), `isObjectRoleSatisfiable(${EX}R)`);
    check('roles: subsumption description names both roles',
      q.getSubsumptionTestDescription(cR, cS),
      `isObjectRoleSubsumedBy(${EX}R, ${EX}S)`);
    check('roles: list description names the roles',
      q.getSubsumedByListTestDescription(cR, [cS, cT]),
      `isObjectRoleSubsumedByList(${EX}R, [${EX}S, ${EX}T])`);
    // An unmapped concept falls back to describing itself. NOTE: `owl:Nothing`
    // would NOT exercise the fallback — it maps to BOTTOM_OBJECT_ROLE.
    const orphan = internAtomicConcept('internal:prop#orphan');
    check('roles: unmapped concept describes itself',
      q.getSatTestDescription(orphan), `isObjectRoleSatisfiable(${orphan})`);
  }
  {
    // The base class keeps its concept-flavoured descriptions.
    const base = new QuasiOrderClassification(null, MONITOR, THING, NOTHING, new Set([cR]));
    check('roles: base sat description unchanged',
      base.getSatTestDescription(cR), `isConceptSatisfiable(${cR})`);
  }

  // -- a real classification run over role proxies ---------------------------
  {
    // `R ⊑ S`, each proxied as `c ≡ ∃role.F`, plus `F(fresh)`. Classifying the
    // proxies must place cR below cS — and the told inclusion gets there by
    // SEEDING, with no tableau run for that pair.
    const F = internAtomicConcept(EX + 'F');
    const fresh = createIndividual('internal:fresh-individual');
    // NOTE the signature is internAtLeastConcept(n, role, concept).
    const existsR = internAtLeastConcept(1, R, F);
    const existsS = internAtLeastConcept(1, S, F);
    const equiv = (c, exists) => [
      createDLClause([createAtom(exists, X)], [createAtom(c, X)]),
      createDLClause([createAtom(c, X)], [createAtom(exists, X)])
    ];
    const onto = new DLOntology({
      dlClauses: [...equiv(cR, existsR), ...equiv(cS, existsS), roleSub(R, S)],
      positiveFacts: [createAtom(F, fresh)],
      negativeFacts: [],
      atomicConcepts: new Set([THING, NOTHING, cR, cS, F]),
      hasInverseRoles: false, hasAtMostRestrictions: false, hasNominals: false,
      hasDatatypes: false, hasUnknownDatatypeRestrictions: false
    });
    const t = mkTableau(onto, false);
    const q = new QuasiOrderClassificationForRoles(t, MONITOR, THING, NOTHING,
      new Set([THING, NOTHING, cR, cS]), false, conceptsForRoles, rolesForConcepts);
    const h = q.classify();
    check('roles: proxy cR is below cS', parentsOf(h, cR).join(','),
      String(cS).replace(EX, ''));
    check('roles: proxy cS is below Thing', parentsOf(h, cS).join(','), String(THING));
  }
}

// ---------------------------------------------------------------------------
console.log(`\n${failures === 0 ? 'ALL PASS' : `${failures} FAILURE(S)`}  (${checks - failures}/${checks} checks)`);
process.exit(failures === 0 ? 0 : 1);
