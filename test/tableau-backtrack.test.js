'use strict';

// ---------------------------------------------------------------------------
// test/tableau-backtrack.test.js — the snapshot-indexing invariants.
//
// Every tableau component that checkpoints on `branchingPointPushed()` must
// index its snapshot array by the ABSOLUTE branching-point level, never
// push/pop a stack. `Tableau.backtrackTo(n)` lowers `currentBranchingPoint`
// to `n` and calls each component's `backtrack()` exactly ONCE — so a stack
// would pop one entry while the level dropped by several, silently
// desynchronising every later snapshot.
//
// These are unit tests driven through stub tableaux so the level skip is
// deterministic. No realistic ontology reliably produces one (see
// scripts/smoke-backjump.js §4-8), so without these the invariant is untested.
// ---------------------------------------------------------------------------

const test = require('node:test');
const assert = require('node:assert/strict');

const { ExtensionTable } = require('../src/tableau/ExtensionTable');
const { ExistentialExpansionManager } = require('../src/tableau/ExistentialExpansionManager');
const { NominalIntroductionManager } = require('../src/tableau/NominalIntroductionManager');
const { internAtomicConcept } = require('../src/model/DLPredicate');
const { PERMANENT, getDependencySet } = require('../src/tableau/DependencySet');
const { EX } = require('./helpers');

// Levels start at 0: `Tableau.currentBranchingPoint` is initialised to -1 and
// `BranchingPoint`'s ctor sets `level = currentBranchingPoint + 1`.

test('ExtensionTable: a level-skipping backtrack removes everything above the target', () => {
  let currentLevel = 1;
  const stub = {
    getCurrentBranchingPoint() { return { level: currentLevel }; },
    needsThingExtension: false,
    needsRDFSLiteralExtension: false
  };
  const node = { nodeID: 0, isActive() { return true; } };
  const A = internAtomicConcept(EX + 'A');
  const B = internAtomicConcept(EX + 'B');
  const C = internAtomicConcept(EX + 'C');
  const D = internAtomicConcept(EX + 'D');

  const table = new ExtensionTable(stub, 2);
  const add = (concept, ds) => table.addTuple([concept, node], ds, true);

  add(A, PERMANENT);
  assert.equal(table.size, 1);

  currentLevel = 1; table.branchingPointPushed(); add(B, getDependencySet([1]));
  currentLevel = 2; table.branchingPointPushed(); add(C, getDependencySet([2]));
  currentLevel = 3; table.branchingPointPushed(); add(D, getDependencySet([3]));
  assert.equal(table.size, 4);

  // Jump 3 -> 1, calling backtrack() exactly ONCE — what Tableau.backtrackTo(1)
  // does. A stack would pop one snapshot and remove only D.
  currentLevel = 1;
  const removed = table.backtrack();

  assert.equal(removed.length, 3);
  assert.equal(table.size, 1);
  assert.equal(table.containsTupleRaw([A, node]), true);
  assert.equal(table.containsTupleRaw([B, node]), false);
  assert.equal(table.containsTupleRaw([C, node]), false);
  assert.equal(table.containsTupleRaw([D, node]), false);
});

test('ExtensionTable: a backtrack rewinds the delta windows, not just the tuple list', () => {
  let currentLevel = 1;
  const stub = {
    getCurrentBranchingPoint() { return { level: currentLevel }; },
    needsThingExtension: false,
    needsRDFSLiteralExtension: false
  };
  const node = { nodeID: 0, isActive() { return true; } };
  const A = internAtomicConcept(EX + 'wA');
  const B = internAtomicConcept(EX + 'wB');

  const table = new ExtensionTable(stub, 2);
  table.addTuple([A, node], PERMANENT, true);

  currentLevel = 1; table.branchingPointPushed();
  table.addTuple([B, node], getDependencySet([1]), true);

  currentLevel = 1;
  table.backtrack();

  // A stale `afterDeltaNew` would make hyperresolution re-fire over removed
  // entries. The level-1 snapshot was taken when only A was present.
  assert.equal(table.afterExtensionOld, 0);
  assert.equal(table.afterExtensionThis, 0);
  assert.equal(table.afterDeltaNew, 1);
  assert.equal(table.getDeltaOldSize(), 0);
  assert.deepEqual(table.getDeltaOldEntries(), []);
});

test('ExtensionTable: a removed tuple can be re-added after a backtrack', () => {
  let currentLevel = 1;
  const stub = {
    getCurrentBranchingPoint() { return { level: currentLevel }; },
    needsThingExtension: false,
    needsRDFSLiteralExtension: false
  };
  const node = { nodeID: 0, isActive() { return true; } };
  const A = internAtomicConcept(EX + 'rA');

  const table = new ExtensionTable(stub, 2);

  // Checkpoint FIRST, then add, so A sits above the snapshot and really gets
  // rolled back. (An entry added before the checkpoint survives by design —
  // that is exactly the case the dependency-set regression covers.)
  currentLevel = 1; table.branchingPointPushed();
  table.addTuple([A, node], getDependencySet([1]), true);
  assert.equal(table.size, 1);

  currentLevel = 1;
  const removed = table.backtrack();
  assert.equal(removed.length, 1);
  assert.equal(table.size, 0);

  // Its key must have been dropped from `entries`/`byPredicate`, or the re-add
  // would be a silent no-op and the fact would be lost forever.
  assert.equal(table.containsTupleRaw([A, node]), false);
  assert.equal(table.addTuple([A, node], getDependencySet([1]), true), true);
  assert.equal(table.size, 1);
});

test('ExistentialExpansionManager: a level-skipping backtrack restores the right snapshot', () => {
  let currentLevel = 1;
  const stub = {
    extensionManager: null,
    getCurrentBranchingPoint() { return { level: currentLevel }; }
  };
  const mgr = new ExistentialExpansionManager(stub);

  const unprocessed = new Map();
  const mkNode = (id) => ({
    id,
    removeFromUnprocessedExistentials(c) { unprocessed.delete(id + ':' + c); },
    addToUnprocessedExistentials(c) { unprocessed.set(id + ':' + c, true); }
  });
  const n1 = mkNode('n1'), n2 = mkNode('n2'), n3 = mkNode('n3');

  mgr.markExistentialProcessed('e1', n1);
  currentLevel = 1; mgr.branchingPointPushed();
  mgr.markExistentialProcessed('e2', n2);
  currentLevel = 2; mgr.branchingPointPushed();
  mgr.markExistentialProcessed('e3', n3);
  assert.equal(mgr.expandedExistentials.length, 3);

  currentLevel = 1;
  mgr.backtrack();

  assert.equal(mgr.expandedExistentials.length, 1);
  // Every rolled-back existential must go back on its node's work list, or it
  // would never be expanded again and the tableau would silently produce an
  // incomplete model.
  assert.equal(unprocessed.has('n2:e2'), true);
  assert.equal(unprocessed.has('n3:e3'), true);
  assert.equal(unprocessed.has('n1:e1'), false);
});

test('NominalIntroductionManager: a level-skipping backtrack restores the root-node keep-set', () => {
  let currentLevel = 1;
  const stub = {
    dependencySetFactory: null,
    mergingManager: null,
    getCurrentBranchingPoint() { return { level: currentLevel }; }
  };
  const mgr = new NominalIntroductionManager(stub);

  // r0 is added BEFORE the level-1 checkpoint so it must survive a backtrack
  // to level 1; r1 sits between checkpoints 1 and 2; r2 after checkpoint 2.
  // That is what makes the `keys` keep-set meaningful rather than a blanket
  // `newRootNodes.clear()`.
  mgr.newRootNodes.set('r0', {});
  mgr.annotatedEqualities.push('ae0');
  currentLevel = 1; mgr.branchingPointPushed();
  mgr.annotatedEqualities.push('ae1');
  mgr.newRootNodes.set('r1', {});
  currentLevel = 2; mgr.branchingPointPushed();
  mgr.annotatedEqualities.push('ae2');
  mgr.newRootNodes.set('r2', {});

  currentLevel = 1;
  mgr.backtrack();

  assert.equal(mgr.annotatedEqualities.length, 1);
  assert.equal(mgr.firstUnprocessedAnnotatedEquality, 0);
  assert.equal(mgr.newRootNodes.has('r2'), false);
  assert.equal(mgr.newRootNodes.has('r1'), false);
  assert.equal(mgr.newRootNodes.has('r0'), true);
});

test('NominalIntroductionManager: the keep-set is per-level, not "before the last checkpoint"', () => {
  let currentLevel = 1;
  const stub = {
    dependencySetFactory: null,
    mergingManager: null,
    getCurrentBranchingPoint() { return { level: currentLevel }; }
  };
  const mgr = new NominalIntroductionManager(stub);

  mgr.annotatedEqualities.push('ae0');
  currentLevel = 1; mgr.branchingPointPushed();
  mgr.annotatedEqualities.push('ae1');
  mgr.newRootNodes.set('r1', {});
  currentLevel = 2; mgr.branchingPointPushed();
  mgr.annotatedEqualities.push('ae2');
  mgr.newRootNodes.set('r2', {});

  currentLevel = 2;
  mgr.backtrack();

  assert.equal(mgr.annotatedEqualities.length, 2);
  assert.equal(mgr.newRootNodes.has('r1'), true);
  assert.equal(mgr.newRootNodes.has('r2'), false);
});

// REGRESSION. `indicesByBranchingPoint` is seeded with the NUMBER 0, so the
// entry for an uncheckpointed level is falsy. The old code fell back to the
// array literal `[0, 0, 0, []]` and then read `snapshot.keys` — which on any
// array resolves to `Array.prototype.keys`, a FUNCTION — so `new Set(fn)`
// threw "TypeError: function is not iterable".
test('NominalIntroductionManager: backtracking to an uncheckpointed level is a safe no-op', () => {
  let currentLevel = 1;
  const stub = {
    dependencySetFactory: null,
    mergingManager: null,
    getCurrentBranchingPoint() { return { level: currentLevel }; }
  };
  const mgr = new NominalIntroductionManager(stub);
  mgr.annotatedEqualities.push('ae0');
  currentLevel = 1; mgr.branchingPointPushed();
  mgr.annotatedEqualities.push('ae1');

  for (const level of [7, 0]) {
    currentLevel = level;
    assert.doesNotThrow(() => mgr.backtrack(), `level ${level} must not throw`);
    assert.equal(mgr.annotatedEqualities.length, 2, `level ${level} must not truncate`);
  }
});
