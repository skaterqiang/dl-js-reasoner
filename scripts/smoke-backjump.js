'use strict';

// ---------------------------------------------------------------------------
// scripts/smoke-backjump.js — NON-HORN reasoning and dependency-directed
// backjumping.
//
// Why this file exists
// --------------------
// All four real sample ontologies (bfo, ogms, ro-core, iao) clausify to HORN
// clause sets. A Horn tableau never pushes a disjunction branching point, so
// `smoke-reasoner-real.js` exercises NO backtracking at all — it would stay
// green even if backjumping were completely broken.
//
// That matters because of a real bug found and fixed in `ExtensionTable`:
// every tableau component that checkpoints on `branchingPointPushed()` must
// index its snapshot array by the ABSOLUTE branching-point level, never
// push/pop a stack. `Tableau.backtrackTo(n)` lowers `currentBranchingPoint`
// to `n` and calls each component's `backtrack()` exactly ONCE — so a
// component using a stack would pop one entry while the level dropped by
// several, silently desynchronising every later snapshot and leaving stale
// tuples in the extension table.
//
// Sections 1-3 test that invariant DIRECTLY on the three checkpointing
// components, by driving them through a level-skipping backtrack. This is
// deterministic: sections 4-8 show that no realistic ontology reliably
// produces a skip on its own (the clash almost always depends on the
// innermost choice), so the invariant would otherwise go untested.
//
// Sections 4-8 are the integration half: genuinely non-Horn ontologies, run
// under every blocking strategy and with disjunction learning on and off, all
// of which must agree. A snapshot bug is strategy-sensitive, so agreement
// across configurations is meaningful evidence.
//
// Run with:  node scripts/smoke-backjump.js
// ---------------------------------------------------------------------------

const E = require('../src/owl/OWLExpressions');
const { createReasoner } = require('../src/reasoner/Reasoner');
const { ExtensionTable } = require('../src/tableau/ExtensionTable');
const { ExistentialExpansionManager } = require('../src/tableau/ExistentialExpansionManager');
const { NominalIntroductionManager } = require('../src/tableau/NominalIntroductionManager');
const { internAtomicConcept } = require('../src/model/DLPredicate');
const { PERMANENT, getDependencySet } = require('../src/tableau/DependencySet');

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

function section(title) {
  console.log(`\n=== ${title} ===`);
}

const EX = 'http://example.org/bj#';
const cls = (n) => E.owlClass(EX + n);
const op = (n) => E.objectProperty(EX + n);
const ind = (n) => E.namedIndividual(EX + n);

const AT = E.AxiomType;
const declaration = (entity) => ({ axiomType: AT.DECLARATION, entity });

/** Minimal mutable ontology mock, same shape as the other smoke scripts use. */
function ontology(axioms) {
  const list = axioms.slice();
  return {
    _axioms: list,
    getAxioms() { return list; },
    addAxiom(ax) { list.push(ax); },
    removeAxiom(ax) {
      const i = list.indexOf(ax);
      if (i >= 0) list.splice(i, 1);
    }
  };
}

// ---------------------------------------------------------------------------
// BackjumpRecorder — a tableau monitor that measures backjump distances.
//
// `Tableau.backtrackTo(n)` calls `backtrackToStarted(branchingPoint)` BEFORE
// lowering `currentBranchingPoint`, so at that moment `tableau.currentBranchingPoint`
// is still the level we are jumping FROM and `branchingPoint.level` is the
// level we are jumping TO.
// ---------------------------------------------------------------------------

class BackjumpRecorder {
  constructor() {
    this.tableau = null;
    this.backtracks = [];
    this.maxSkipped = 0;
    this.branchingPointsPushed = 0;
  }

  setTableau(tableau) { this.tableau = tableau; }

  pushBranchingPointStarted() { this.branchingPointsPushed++; }

  backtrackToStarted(branchingPoint) {
    const from = this.tableau.currentBranchingPoint;
    const to = branchingPoint.level;
    const skipped = from - to;
    this.backtracks.push({ from, to, skipped });
    if (skipped > this.maxSkipped) this.maxSkipped = skipped;
  }
}

/** Build a reasoner wired to a fresh recorder; returns `{ r, rec }`. */
function recordingReasoner(axioms, extraConfig) {
  const rec = new BackjumpRecorder();
  const r = createReasoner(ontology(axioms),
    Object.assign({ monitor: rec }, extraConfig || {}));
  return { r, rec };
}

// ===========================================================================
section('1. ExtensionTable snapshots are indexed by ABSOLUTE level');
// ===========================================================================
//
// This is the core regression. A push/pop stack implementation passes every
// test that only ever backtracks ONE level; it corrupts the table the moment a
// backjump skips levels, because `backtrack()` is called once while the level
// drops by several.
//
// We drive the table with a stub tableau whose reported level we control, so
// the skip is deterministic rather than something we have to hope an ontology
// produces.
//
// Levels start at 0: `Tableau.currentBranchingPoint` is initialised to -1 and
// `BranchingPoint`'s ctor sets `level = currentBranchingPoint + 1`. The test
// below checkpoints levels 1, 2 and 3 and then skips 3 -> 1, which is a genuine
// multi-level jump. (Level 0 is skipped only when it is the non-backtrackable
// "dummy dependency" point that `isSatisfiable` installs directly;
// `backtrackTo` refuses to go at or below `nonbacktrackableBranchingPoint`.)
{
  /**
   * Stub tableau: `ExtensionTable` only ever calls `getCurrentBranchingPoint()`
   * plus the optional `tupleAdded`/`tupleRemoved` hooks, and reads the two
   * `needs*Extension` flags.
   */
  let currentLevel = 1;
  const stub = {
    getCurrentBranchingPoint() { return { level: currentLevel }; },
    needsThingExtension: false,
    needsRDFSLiteralExtension: false
  };

  // A node stub: `isTupleActive` only needs `isActive()`, `tupleKey` only `nodeID`.
  const node = { nodeID: 0, isActive() { return true; } };

  const A = internAtomicConcept(EX + 'A1');
  const B = internAtomicConcept(EX + 'B1');
  const C = internAtomicConcept(EX + 'C1');
  const D = internAtomicConcept(EX + 'D1');

  const table = new ExtensionTable(stub, 2);
  const add = (concept, ds) => table.addTuple([concept, node], ds, true);

  // A permanent fact, present before any branching point.
  add(A, PERMANENT);
  check('ext: size before branching', table.size, 1);

  // Checkpoint level 1, then add a fact under it. Repeat for levels 2 and 3.
  // Each snapshot records the table as it was WHEN THE POINT WAS PUSHED, so
  // backtracking to level n undoes everything done at level n and above.
  currentLevel = 1; table.branchingPointPushed(); add(B, getDependencySet([1]));
  currentLevel = 2; table.branchingPointPushed(); add(C, getDependencySet([2]));
  currentLevel = 3; table.branchingPointPushed(); add(D, getDependencySet([3]));
  check('ext: size at level 3', table.size, 4);

  // THE REGRESSION: jump straight from level 3 back to level 1, calling
  // backtrack() exactly ONCE — precisely what Tableau.backtrackTo(1) does.
  // A stack would pop one snapshot (level 3's) and remove only D.
  currentLevel = 1;
  const removed = table.backtrack();

  check('ext: level-skipping backtrack removed 3 tuples', removed.length, 3);
  check('ext: size restored to the level-1 snapshot', table.size, 1);
  check('ext: the permanent fact survived', table.containsTupleRaw([A, node]), true);
  check('ext: the level-1 fact is gone', table.containsTupleRaw([B, node]), false);
  check('ext: the level-2 fact is gone', table.containsTupleRaw([C, node]), false);
  check('ext: the level-3 fact is gone', table.containsTupleRaw([D, node]), false);

  // The delta windows must be rewound too, not just the tuple list — a stale
  // `afterDeltaNew` would make hyperresolution re-fire over removed entries.
  // The level-1 snapshot was taken when only A was present, so all three
  // windows must read back as they did then. (Note `hasDeltaNew()` is
  // `afterExtensionThis !== afterDeltaNew`; we never call propagateDeltaNew()
  // here, so it is legitimately true — the point is that the INDICES were
  // rewound rather than left pointing past the end of the shrunk table.)
  check('ext: afterExtensionOld rewound', table.afterExtensionOld, 0);
  check('ext: afterExtensionThis rewound', table.afterExtensionThis, 0);
  check('ext: afterDeltaNew rewound to the level-1 snapshot', table.afterDeltaNew, 1);
  check('ext: delta-old window is empty after the rewind', table.getDeltaOldSize(), 0);
  check('ext: delta-old entries match the rewound window',
    table.getDeltaOldEntries().length, 0);

  // Re-adding a removed fact must work (its key was dropped from the index).
  currentLevel = 2;
  table.branchingPointPushed();
  check('ext: a removed tuple can be re-added', add(B, getDependencySet([2])), true);
  check('ext: size after re-add', table.size, 2);

  // A PARTIAL skip: build up to level 4, then jump back to level 3. The
  // level-3 snapshot was taken when level 3 was pushed (A and B present), so
  // C and D go but the level-2 work survives. This is the case a push/pop
  // stack happens to get right, and it must keep working after the fix.
  currentLevel = 3;
  table.branchingPointPushed();
  add(C, getDependencySet([3]));
  currentLevel = 4;
  table.branchingPointPushed();
  add(D, getDependencySet([4]));
  check('ext: size before the partial skip', table.size, 4);

  currentLevel = 3;
  table.backtrack();
  check('ext: partial skip 4->3 lands on the level-3 snapshot', table.size, 2);
  check('ext: level-4 fact removed by the partial skip',
    table.containsTupleRaw([D, node]), false);
  check('ext: level-3 fact removed by the partial skip',
    table.containsTupleRaw([C, node]), false);
  check('ext: level-2 fact KEPT by the partial skip',
    table.containsTupleRaw([B, node]), true);
  check('ext: permanent fact KEPT by the partial skip',
    table.containsTupleRaw([A, node]), true);
}

// ===========================================================================
section('2. ExistentialExpansionManager snapshots are indexed by ABSOLUTE level');
// ===========================================================================
{
  let currentLevel = 1;
  // The ctor reads `tableau.extensionManager`; branchingPointPushed/backtrack
  // only need getCurrentBranchingPoint().
  const stub = {
    extensionManager: null,
    getCurrentBranchingPoint() { return { level: currentLevel }; }
  };
  const mgr = new ExistentialExpansionManager(stub);

  // Node stubs: the manager only calls removeFromUnprocessedExistentials /
  // addToUnprocessedExistentials on them.
  const unprocessed = new Map();
  const mkNode = (id) => ({
    id,
    removeFromUnprocessedExistentials(c) { unprocessed.delete(id + ':' + c); },
    addToUnprocessedExistentials(c) { unprocessed.set(id + ':' + c, true); }
  });
  const n1 = mkNode('n1'), n2 = mkNode('n2'), n3 = mkNode('n3');

  mgr.markExistentialProcessed('e1', n1);          // before any checkpoint
  currentLevel = 1; mgr.branchingPointPushed();   // snapshot: length 1
  mgr.markExistentialProcessed('e2', n2);
  currentLevel = 2; mgr.branchingPointPushed();   // snapshot: length 2
  mgr.markExistentialProcessed('e3', n3);

  check('expmgr: three existentials marked processed', mgr.expandedExistentials.length, 3);

  // Level-skipping backtrack 2 -> 1, called ONCE. A stack would pop the
  // level-2 snapshot (length 2) and wrongly keep e2.
  currentLevel = 1;
  mgr.backtrack();

  check('expmgr: level-skipping backtrack restored the level-1 snapshot',
    mgr.expandedExistentials.length, 1);
  // Every rolled-back existential must be returned to its node's work list,
  // otherwise it would never be expanded again and the tableau would silently
  // produce an incomplete model.
  check('expmgr: e2 returned to the unprocessed list', unprocessed.has('n2:e2'), true);
  check('expmgr: e3 returned to the unprocessed list', unprocessed.has('n3:e3'), true);
  check('expmgr: e1 was NOT rolled back', unprocessed.has('n1:e1'), false);

  // Deeper skip: push to level 3, then jump straight back to level 1.
  currentLevel = 2; mgr.branchingPointPushed();
  mgr.markExistentialProcessed('e4', n1);
  currentLevel = 3; mgr.branchingPointPushed();
  mgr.markExistentialProcessed('e5', n2);
  currentLevel = 1;
  mgr.backtrack();
  check('expmgr: 3->1 skip restores the level-1 snapshot',
    mgr.expandedExistentials.length, 1);
  check('expmgr: e4 rolled back by the deep skip', unprocessed.has('n1:e4'), true);
  check('expmgr: e5 rolled back by the deep skip', unprocessed.has('n2:e5'), true);
}

// ===========================================================================
section('3. NominalIntroductionManager snapshots are indexed by ABSOLUTE level');
// ===========================================================================
{
  let currentLevel = 1;
  // The ctor reads dependencySetFactory + mergingManager off the tableau; the
  // checkpoint path itself only needs getCurrentBranchingPoint().
  const stub = {
    dependencySetFactory: null,
    mergingManager: null,
    getCurrentBranchingPoint() { return { level: currentLevel }; }
  };
  const mgr = new NominalIntroductionManager(stub);

  // r0 is added BEFORE the level-1 checkpoint, so it must survive a backtrack
  // to level 1; r1 is added between checkpoints 1 and 2, so it must survive a
  // backtrack to level 2 but not to level 1; r2 is added after checkpoint 2 and
  // must not survive either. This is what makes the `keys` keep-set meaningful
  // rather than a blanket `newRootNodes.clear()`.
  mgr.newRootNodes.set('r0', {});
  mgr.annotatedEqualities.push('ae0');            // before any checkpoint
  currentLevel = 1; mgr.branchingPointPushed();   // snapshot: length 1, keys [r0]
  mgr.annotatedEqualities.push('ae1');
  mgr.newRootNodes.set('r1', {});
  currentLevel = 2; mgr.branchingPointPushed();   // snapshot: length 2, keys [r0, r1]
  mgr.annotatedEqualities.push('ae2');
  mgr.newRootNodes.set('r2', {});

  check('nom: three annotated equalities queued', mgr.annotatedEqualities.length, 3);
  check('nom: three root nodes recorded', mgr.newRootNodes.size, 3);

  // Level-skipping backtrack 2 -> 1, called ONCE.
  currentLevel = 1;
  mgr.backtrack();

  check('nom: level-skipping backtrack restored the level-1 snapshot',
    mgr.annotatedEqualities.length, 1);
  check('nom: firstUnprocessed rewound to the level-1 snapshot',
    mgr.firstUnprocessedAnnotatedEquality, 0);
  check('nom: the level-2 root node was dropped', mgr.newRootNodes.has('r2'), false);
  check('nom: the level-1 root node was dropped', mgr.newRootNodes.has('r1'), false);
  check('nom: the pre-checkpoint root node was KEPT', mgr.newRootNodes.has('r0'), true);
  check('nom: root-node map size matches the level-1 snapshot',
    mgr.newRootNodes.size, 1);

  // A backtrack to level 2 must keep r1 — proving the keep-set is per-level and
  // not simply "everything added before the last checkpoint".
  mgr.newRootNodes.set('r1', {});
  mgr.annotatedEqualities.push('ae1');
  currentLevel = 2; mgr.branchingPointPushed();
  mgr.annotatedEqualities.push('ae2');
  mgr.newRootNodes.set('r2', {});
  currentLevel = 2;
  mgr.backtrack();
  check('nom: backtrack to level 2 keeps the level-2 snapshot length',
    mgr.annotatedEqualities.length, 2);
  check('nom: backtrack to level 2 KEEPS r1', mgr.newRootNodes.has('r1'), true);
  check('nom: backtrack to level 2 drops r2', mgr.newRootNodes.has('r2'), false);

  // Backtracking to a level that was never checkpointed must be a safe no-op,
  // NOT a throw. `indicesByBranchingPoint` is pre-filled with the NUMBER 0, so
  // the old `snapshot.keys || []` idiom resolved to `Array.prototype.keys` (a
  // function) and `new Set(fn)` threw "function is not iterable".
  const before = mgr.annotatedEqualities.length;
  currentLevel = 7;
  let threw = null;
  try { mgr.backtrack(); } catch (err) { threw = err.message; }
  check('nom: backtrack to an uncheckpointed level does not throw', threw, null);
  check('nom: uncheckpointed backtrack left the queue alone',
    mgr.annotatedEqualities.length, before);

  // Same for level 0, whose seeded entry is the NUMBER 0 (falsy) and therefore
  // takes the identical `!snapshot` early-return path.
  currentLevel = 0;
  threw = null;
  try { mgr.backtrack(); } catch (err) { threw = err.message; }
  check('nom: backtrack to level 0 does not throw', threw, null);
  check('nom: level-0 backtrack left the queue alone',
    mgr.annotatedEqualities.length, before);
}

// ===========================================================================
section('4. Sanity: a Horn ontology pushes no branching points');
// ===========================================================================
{
  // A ⊑ B ⊑ C is pure Horn: no disjunctions, so no backtracking whatsoever.
  const A = cls('A'), B = cls('B'), C = cls('C');
  const { r, rec } = recordingReasoner([
    declaration(A), declaration(B), declaration(C),
    E.subclassOf(A, B), E.subclassOf(B, C)
  ]);
  check('Horn: A ⊑ C entailed', r.isEntailed(E.subclassOf(A, C)), true);
  check('Horn: C ⊑ A not entailed', r.isEntailed(E.subclassOf(C, A)), false);
  check('Horn: no branching points pushed', rec.branchingPointsPushed, 0);
  check('Horn: no backtracks', rec.backtracks.length, 0);
  r.dispose();
}

// ===========================================================================
section('5. Disjunction ladder — nested branching points');
// ===========================================================================
{
  // A ⊑ (B1 ⊔ C1), B1 ⊑ (B2 ⊔ C2), B2 ⊑ (B3 ⊔ C3), and every Ci is
  // unsatisfiable. Satisfying A therefore requires walking down the ladder and
  // picking B at every rung, so several branching points get pushed and each
  // wrong choice backtracks.
  const A = cls('A');
  const Bs = [1, 2, 3].map((i) => cls('B' + i));
  const Cs = [1, 2, 3].map((i) => cls('C' + i));

  const axioms = [declaration(A)];
  for (const x of [...Bs, ...Cs]) axioms.push(declaration(x));
  axioms.push(E.subclassOf(A, E.objectUnionOf([Bs[0], Cs[0]])));
  axioms.push(E.subclassOf(Bs[0], E.objectUnionOf([Bs[1], Cs[1]])));
  axioms.push(E.subclassOf(Bs[1], E.objectUnionOf([Bs[2], Cs[2]])));
  // Kill every C so the only model routes through B3.
  for (const c of Cs) axioms.push(E.subclassOf(c, E.owlNothing()));

  const { r, rec } = recordingReasoner(axioms);
  check('ladder: ontology consistent', r.isConsistent(), true);
  check('ladder: A satisfiable', r.isSatisfiable(A), true);
  check('ladder: A ⊑ B3 entailed', r.isEntailed(E.subclassOf(A, Bs[2])), true);
  check('ladder: A ⊑ C1 not entailed', r.isEntailed(E.subclassOf(A, Cs[0])), false);
  check('ladder: branching points were pushed', rec.branchingPointsPushed > 0, true);
  check('ladder: backtracking happened', rec.backtracks.length > 0, true);
  console.log(`        (pushed=${rec.branchingPointsPushed} backtracks=${rec.backtracks.length} maxSkipped=${rec.maxSkipped})`);
  r.dispose();
}

// ===========================================================================
section('6. Both disjuncts clash — A is unsatisfiable but the ontology is not');
// ===========================================================================
{
  // A ⊑ B ⊔ C, A ⊑ X, B ⊑ ¬X, C ⊑ ¬X. Whichever disjunct is tried, X clashes,
  // so A has no model — yet the ontology stays consistent because A simply has
  // no instances. This is the classic non-Horn shape and it forces the tableau
  // to exhaust a branching point rather than satisfy it.
  const A = cls('A6'), B = cls('B6'), C = cls('C6'), X = cls('X6');
  const { r, rec } = recordingReasoner([
    declaration(A), declaration(B), declaration(C), declaration(X),
    E.subclassOf(A, E.objectUnionOf([B, C])),
    E.subclassOf(A, X),
    E.subclassOf(B, E.objectComplementOf(X)),
    E.subclassOf(C, E.objectComplementOf(X))
  ]);
  check('both-clash: ontology consistent', r.isConsistent(), true);
  check('both-clash: A unsatisfiable', r.isSatisfiable(A), false);
  check('both-clash: A ⊑ ⊥ entailed', r.isEntailed(E.subclassOf(A, E.owlNothing())), true);
  check('both-clash: B still satisfiable', r.isSatisfiable(B), true);
  check('both-clash: branching occurred', rec.branchingPointsPushed > 0, true);
  console.log(`        (pushed=${rec.branchingPointsPushed} backtracks=${rec.backtracks.length} maxSkipped=${rec.maxSkipped})`);
  r.dispose();
}

// ===========================================================================
section('7. DisjointUnion chains (non-Horn by construction)');
// ===========================================================================
{
  // C ≡ A ⊔ B with A ⊥ B, and D ≡ C ⊔ E with C ⊥ E. Chained disjoint unions
  // generate both disjunctions AND inequality constraints, so the tableau must
  // branch and then merge — a different backjump shape from §6.
  const A = cls('duA'), B = cls('duB'), C = cls('duC');
  const D = cls('duD'), Ee = cls('duE');

  const { r, rec } = recordingReasoner([
    declaration(A), declaration(B), declaration(C), declaration(D), declaration(Ee),
    E.disjointUnion(C, [A, B]),
    E.disjointUnion(D, [C, Ee])
  ]);

  check('du: consistent', r.isConsistent(), true);
  check('du: C ⊑ A ⊔ B', r.isEntailed(E.subclassOf(C, E.objectUnionOf([A, B]))), true);
  check('du: D ⊑ A ⊔ B ⊔ E',
    r.isEntailed(E.subclassOf(D, E.objectUnionOf([A, B, Ee]))), true);
  check('du: A ⊥ B', r.isEntailed(E.disjointClasses([A, B])), true);
  check('du: C ⊥ E', r.isEntailed(E.disjointClasses([C, Ee])), true);
  check('du: A ⊥ E (transitively)', r.isEntailed(E.disjointClasses([A, Ee])), true);
  check('du: A ⊑ D', r.isEntailed(E.subclassOf(A, D)), true);
  check('du: D ⊑ A false', r.isEntailed(E.subclassOf(D, A)), false);
  check('du: branching occurred', rec.branchingPointsPushed > 0, true);
  console.log(`        (pushed=${rec.branchingPointsPushed} backtracks=${rec.backtracks.length} maxSkipped=${rec.maxSkipped})`);
  r.dispose();
}

// ===========================================================================
section('8. Cardinality + DifferentIndividuals — merge branching');
// ===========================================================================
{
  // a : ≤1 R.⊤ with R(a,b) and R(a,c): b and c must merge. Adding
  // DifferentIndividuals(b,c) forbids the merge, so the ontology becomes
  // inconsistent; removing it makes b and c provably identical.
  const R = op('R8');
  const a = ind('a8'), b = ind('b8'), c = ind('c8');

  const base = [
    declaration(R), declaration(a), declaration(b), declaration(c),
    E.subclassOf(E.owlThing(), E.objectMaxCardinality(1, R, E.owlThing())),
    E.objectPropertyAssertion(R, a, b),
    E.objectPropertyAssertion(R, a, c)
  ];

  const { r } = recordingReasoner([...base, E.differentIndividuals([b, c])]);
  check('card: INCONSISTENT with DifferentIndividuals', r.isConsistent(), false);
  r.dispose();

  const { r: r2, rec: rec2 } = recordingReasoner(base);
  check('card: consistent without DifferentIndividuals', r2.isConsistent(), true);
  check('card: b and c merged (SameIndividual entailed)',
    r2.isEntailed(E.sameIndividual([b, c])), true);
  console.log(`        (pushed=${rec2.branchingPointsPushed} backtracks=${rec2.backtracks.length} maxSkipped=${rec2.maxSkipped})`);
  r2.dispose();
}

// ===========================================================================
section('9. Classification under non-Horn axioms');
// ===========================================================================
{
  // Classification of a genuinely non-Horn TBox. The disjunction plus the
  // two routes into Bad make every class unsatisfiable, and the hierarchy must
  // still be built without error.
  const Top = cls('cTop'), L = cls('cL'), Rr = cls('cR');
  const Bad = cls('cBad'), Leaf = cls('cLeaf');

  const { r } = recordingReasoner([
    declaration(Top), declaration(L), declaration(Rr), declaration(Bad), declaration(Leaf),
    E.subclassOf(Top, E.objectUnionOf([L, Rr])),   // non-Horn
    E.subclassOf(L, Bad),
    E.subclassOf(Rr, Bad),
    E.subclassOf(Bad, E.owlNothing()),
    E.subclassOf(Leaf, Top)
  ]);

  check('classify: consistent', r.isConsistent(), true);
  // getUnsatisfiableClasses() returns a Node (NOT a NodeSet) — the bottom node.
  // It always contains owl:Nothing itself, so filter that out with the proper
  // predicate: `iriString` yields the FULL IRI, so comparing against the
  // prefixed string 'owl:Nothing' never matches.
  const unsat = [...r.getUnsatisfiableClasses().getEntities()]
    .filter((c) => !E.isOWLNothing(c))
    .map((c) => String(E.iriString(c)).replace(EX, ''))
    .sort();
  check('classify: all five classes unsatisfiable',
    unsat.join(','), 'cBad,cL,cLeaf,cR,cTop');
  check('classify: the bottom node also holds owl:Nothing',
    [...r.getUnsatisfiableClasses().getEntities()].some((c) => E.isOWLNothing(c)), true);
  check('classify: Leaf unsatisfiable', r.isSatisfiable(Leaf), false);
  r.dispose();
}

// ===========================================================================
section('10. Results must not depend on the blocking strategy');
// ===========================================================================
{
  // A snapshot-indexing bug is strategy-sensitive: changing the strategy
  // changes how many branching points get pushed and in what order. Agreement
  // across all five strategies is strong evidence the snapshots stay aligned.
  const build = () => {
    const A = cls('sA'), B = cls('sB'), C = cls('sC'), X = cls('sX');
    const axioms = [declaration(A), declaration(B), declaration(C), declaration(X)];
    for (let i = 0; i < 3; i++) {
      const p = cls('sP' + i), q = cls('sQ' + i);
      axioms.push(declaration(p), declaration(q));
      axioms.push(E.subclassOf(E.owlThing(), E.objectUnionOf([p, q])));
    }
    axioms.push(
      E.subclassOf(A, E.objectUnionOf([B, C])),
      E.subclassOf(A, X),
      E.subclassOf(B, E.objectComplementOf(X)),
      E.subclassOf(C, E.objectComplementOf(X))
    );
    return axioms;
  };

  for (const strategy of ['ANYWHERE', 'ANCESTOR', 'SIMPLE_CORE', 'COMPLEX_CORE', 'OPTIMAL']) {
    const { r, rec } = recordingReasoner(build(), { blockingStrategyType: strategy });
    check(`strategy ${strategy}: A unsatisfiable`, r.isSatisfiable(cls('sA')), false);
    check(`strategy ${strategy}: consistent`, r.isConsistent(), true);
    check(`strategy ${strategy}: A ⊑ ⊥`,
      r.isEntailed(E.subclassOf(cls('sA'), E.owlNothing())), true);
    console.log(`        (pushed=${rec.branchingPointsPushed} backtracks=${rec.backtracks.length} maxSkipped=${rec.maxSkipped})`);
    r.dispose();
  }
}

// ===========================================================================
section('11. Disjunction learning on/off must agree');
// ===========================================================================
{
  // `useDisjunctionLearning` caches which disjuncts already failed. A stale
  // cache surviving a backjump would give a wrong answer, so both settings must
  // agree — and both must agree with §6's unlearned result.
  const build = () => {
    const A = cls('dA'), B = cls('dB'), C = cls('dC'), X = cls('dX');
    const axioms = [declaration(A), declaration(B), declaration(C), declaration(X)];
    for (let i = 0; i < 4; i++) {
      const p = cls('dP' + i), q = cls('dQ' + i);
      axioms.push(declaration(p), declaration(q));
      axioms.push(E.subclassOf(E.owlThing(), E.objectUnionOf([p, q])));
    }
    axioms.push(
      E.subclassOf(A, E.objectUnionOf([B, C])),
      E.subclassOf(A, X),
      E.subclassOf(B, E.objectComplementOf(X)),
      E.subclassOf(C, E.objectComplementOf(X))
    );
    return axioms;
  };

  for (const learning of [true, false]) {
    const { r, rec } = recordingReasoner(build(), { useDisjunctionLearning: learning });
    check(`learning=${learning}: A unsatisfiable`, r.isSatisfiable(cls('dA')), false);
    check(`learning=${learning}: consistent`, r.isConsistent(), true);
    console.log(`        (pushed=${rec.branchingPointsPushed} backtracks=${rec.backtracks.length} maxSkipped=${rec.maxSkipped})`);
    r.dispose();
  }
}

// ===========================================================================
section('12. Re-adding an existing tuple must NOT mutate its dependency set');
// ===========================================================================
//
// Second real bug found while writing this file, and the more dangerous of the
// two because it corrupted the CLASH dependency set rather than the table.
//
// `ExtensionTable.addTuple` used to union the incoming dependency set into an
// already-present entry. That looks like the right thing to do — the fact now
// holds on the intersection of branches — but the entry was appended BEFORE
// the current branching point's checkpoint, so `backtrack()` truncates the
// table above the checkpoint and never touches it. The mutation is invisible
// to the snapshot and is never undone.
//
// The stale level then reappears in every later clash dependency set, so
// `Tableau.doIteration` backjumps to the SAME branching point forever and
// `DisjunctionBranchingPoint.startNextChoice` eventually runs past its last
// disjunct: `header.disjuncts[undefined]` → "Cannot read properties of
// undefined (reading 'dlPredicate')".
//
// HermiT does not union here. `ExtensionTableWithTupleIndexes.addTuple` only
// widens the core flag when the tuple is already present, and leaves the
// stored dependency set exactly as it was. Keeping the original set is sound:
// it records one concrete derivation, and a clash built on it backjumps to a
// level at or below the one that really introduced the fact — at worst a
// slightly more conservative jump, never a wrong one.
{
  let currentLevel = 1;
  const stub = {
    getCurrentBranchingPoint() { return { level: currentLevel }; },
    needsThingExtension: false,
    needsRDFSLiteralExtension: false
  };
  const node = { nodeID: 0, isActive() { return true; } };
  const A = internAtomicConcept(EX + 'A12');

  const table = new ExtensionTable(stub, 2);
  const ds1 = getDependencySet([1]);

  check('depset: first add succeeds', table.addTuple([A, node], ds1, true), true);
  check('depset: stored dependency set is the one we passed',
    table.getDependencySet([A, node]), ds1);

  // Re-add the SAME tuple under a DIFFERENT dependency set. Must return false
  // (not new) and must leave the stored set untouched.
  const ds2 = getDependencySet([1, 2]);
  check('depset: re-adding an existing tuple returns false',
    table.addTuple([A, node], ds2, true), false);
  check('depset: the stored dependency set was NOT unioned',
    table.getDependencySet([A, node]), ds1);
  check('depset: the stored set still has exactly one level',
    table.getDependencySet([A, node]).levels.length, 1);
  check('depset: the table did not grow', table.size, 1);

  // The core flag is the ONE thing HermiT does widen, so make sure that still
  // works — a non-core tuple must become core when re-added as core.
  const B = internAtomicConcept(EX + 'B12');
  table.addTuple([B, node], ds1, false);
  check('depset: B starts non-core', table.isCore([B, node]), false);
  table.addTuple([B, node], ds2, true);
  check('depset: re-adding as core widens the core flag', table.isCore([B, node]), true);
  check('depset: widening the core flag did not touch the dependency set',
    table.getDependencySet([B, node]), ds1);
}

// ===========================================================================
section('13. Datatype definitions must not wedge the disjunction loop');
// ===========================================================================
//
// End-to-end form of the §12 bug. `DatatypeDefinition(MyDT, {red,green})`
// makes the datatype manager derive a ground disjunction over the enumerated
// literals; the second disjunct re-asserts a data-range tuple that already
// exists, which is exactly the union path §12 forbids.
//
// Before the fix this threw "Cannot read properties of undefined (reading
// 'dlPredicate')" from GroundDisjunction.getDLPredicate. The assertion here is
// simply that it terminates and answers.
{
  const XS = E.datatype(E.IRI_XSD_STRING);
  const MyDT = E.datatype(EX + 'MyDT');
  const dd = (datatype, dataRange) =>
    ({ axiomType: AT.DATATYPE_DEFINITION, datatype, dataRange });

  const oneOf = E.dataOneOf([E.literal('red', XS), E.literal('green', XS)]);
  const { r } = recordingReasoner([declaration(MyDT), dd(MyDT, oneOf)]);

  let threw = null;
  let entailed = null;
  try { entailed = r.isEntailed(dd(MyDT, oneOf)); } catch (err) { threw = err.message; }
  check('datadef: isEntailed(DatatypeDefinition) does not throw', threw, null);
  check('datadef: a definition present in the ontology is entailed', entailed, true);
  r.dispose();

  // A data UNION as the defining range takes the same disjunction path.
  const { r: r2 } = recordingReasoner([
    declaration(MyDT),
    dd(MyDT, E.dataUnionOf([XS, E.datatype(E.XSD_NS + 'integer')]))
  ]);
  threw = null;
  entailed = null;
  try {
    entailed = r2.isEntailed(dd(MyDT, E.dataUnionOf([XS, E.datatype(E.XSD_NS + 'integer')])));
  } catch (err) { threw = err.message; }
  check('datadef: a union-defined datatype does not throw', threw, null);
  check('datadef: a union definition present in the ontology is entailed', entailed, true);
  r2.dispose();

  // Sanity: a definition that is NOT in the ontology must not be entailed.
  const { r: r3 } = recordingReasoner([declaration(MyDT), dd(MyDT, XS)]);
  check('datadef: an absent definition is not entailed',
    r3.isEntailed(dd(MyDT, E.datatype(E.XSD_NS + 'integer'))), false);
  // A self-definition is entailed regardless of whether the datatype is known:
  // its symmetric difference is empty by construction.
  check('datadef: DatatypeDefinition(MyDT,MyDT) is entailed',
    r3.isEntailed(dd(MyDT, MyDT)), true);
  r3.dispose();
}

// ---------------------------------------------------------------------------
console.log(`\n${failures === 0 ? 'ALL PASS' : 'FAILURES'}  (${checks - failures}/${checks} checks passed.)`);
if (failures > 0) {
  console.log(`${failures} check(s) failed.`);
  process.exit(1);
}
console.log('All backjump smoke checks passed.');
