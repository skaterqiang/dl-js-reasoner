'use strict';

// ---------------------------------------------------------------------------
// test/extension-table.test.js — tuple-index behaviour, and the regression for
// the dependency-set union bug.
//
// BUG (fixed). `addTuple` used to union dependency sets when the tuple was
// already present. That mutation is invisible to `backtrack()`, which only
// truncates `order` above the checkpoint — an entry appended BEFORE the
// checkpoint is never touched. So a stale branching-point level persisted in
// the entry's dependency set forever, kept reappearing in every later clash
// dependency set, and made `Tableau.doIteration` backjump to the SAME
// branching point repeatedly until `DisjunctionBranchingPoint.startNextChoice`
// ran past its last disjunct:
//   TypeError: Cannot read properties of undefined (reading 'dlPredicate')
//
// HermiT's ExtensionTableWithTupleIndexes.addTuple (lines 49-77) does ONLY a
// core-flag widening on the already-present branch — no dependency-set union
// anywhere. Keeping the original set is sound: it records one concrete
// derivation of the fact, and a clash that uses it backjumps to a level at or
// below the one that really introduced it. At worst that is a slightly more
// conservative jump, never a wrong one.
// ---------------------------------------------------------------------------

const test = require('node:test');
const assert = require('node:assert/strict');

const { ExtensionTable, tupleKey } = require('../src/tableau/ExtensionTable');
const { internAtomicConcept } = require('../src/model/DLPredicate');
const { PERMANENT, getDependencySet } = require('../src/tableau/DependencySet');
const { EX } = require('./helpers');

function stubTable() {
  return {
    getCurrentBranchingPoint() { return { level: 0 }; },
    needsThingExtension: false,
    needsRDFSLiteralExtension: false
  };
}

const node = { nodeID: 0, isActive() { return true; } };

test('addTuple returns true for a new tuple and false for a duplicate', () => {
  const table = new ExtensionTable(stubTable(), 2);
  const A = internAtomicConcept(EX + 'dA');

  assert.equal(table.addTuple([A, node], PERMANENT, true), true);
  assert.equal(table.addTuple([A, node], PERMANENT, true), false);
  assert.equal(table.size, 1);
});

test('REGRESSION: re-adding an existing tuple must NOT mutate its dependency set', () => {
  const table = new ExtensionTable(stubTable(), 2);
  const A = internAtomicConcept(EX + 'dA');
  const ds1 = getDependencySet([1]);
  const ds2 = getDependencySet([2]);

  table.addTuple([A, node], ds1, true);
  table.addTuple([A, node], ds2, true);

  // Identity, not just equality: the stored set must still be the ORIGINAL
  // object. A union would have produced a fresh set containing both levels.
  assert.equal(table.getDependencySet([A, node]), ds1);
  assert.deepEqual(table.getDependencySet([A, node]).levels, [1]);
  assert.equal(table.size, 1);
});

test('re-adding a non-core tuple as core widens the core flag but keeps the set', () => {
  const table = new ExtensionTable(stubTable(), 2);
  const A = internAtomicConcept(EX + 'dA');
  const ds1 = getDependencySet([1]);

  table.addTuple([A, node], ds1, false);
  assert.equal(table.isCore([A, node]), false);

  table.addTuple([A, node], getDependencySet([7]), true);
  assert.equal(table.isCore([A, node]), true);
  assert.equal(table.getDependencySet([A, node]), ds1);
});

test('tupleKey is stable across structurally identical tuples', () => {
  const A = internAtomicConcept(EX + 'kA');
  const t1 = [A, node];
  const t2 = [A, node];
  assert.equal(tupleKey(t1), tupleKey(t2));
});

test('PERMANENT is the empty dependency set and unions to itself', () => {
  assert.deepEqual(PERMANENT.levels, []);
  assert.equal(PERMANENT.union(PERMANENT), PERMANENT);
  assert.equal(PERMANENT.isEmpty(), true);
});
