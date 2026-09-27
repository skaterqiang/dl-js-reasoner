'use strict';

// ---------------------------------------------------------------------------
// test/blocking-signature-cache.test.js
//
// Unit tests for the ported blocking signature cache: the bucket hash, the
// SIGNATURE_CACHE_BLOCKER sentinel, and the add/contains/resize mechanics.
// The end-to-end reasoner behaviour (CACHED installs a cache, nominals
// disable it, results unchanged) is pinned in blocking-configuration.test.js.
// ---------------------------------------------------------------------------

const test = require('node:test');
const assert = require('node:assert');

const { BlockingSignatureCache } = require('../src/blocking/BlockingSignatureCache');
const {
  SingleBlockingSignature, stringHashCode
} = require('../src/blocking/BlockingSignature');
const { SetFactory } = require('../src/blocking/SetFactory');
const { NODE_TYPE, Node } = require('../src/tableau/Node');

// ---------------------------------------------------------------------------
// stringHashCode — must match Java's String.hashCode.
// ---------------------------------------------------------------------------

test('stringHashCode matches Java String.hashCode', () => {
  assert.equal(stringHashCode(''), 0);
  assert.equal(stringHashCode('a'), 97);
  assert.equal(stringHashCode('abc'), 96354);
  // A value that overflows 32 bits, verifying the |0 int coercion.
  assert.equal(stringHashCode('http://example.org/test#A'),
    javaStringHash('http://example.org/test#A'));
});

/** Reference implementation, computed with arbitrary precision then wrapped. */
function javaStringHash(s) {
  let h = 0;
  for (let i = 0; i < s.length; i++) {
    h = (h * 31 + s.charCodeAt(i)) | 0;
  }
  return h;
}

// ---------------------------------------------------------------------------
// The sentinel blocker.
// ---------------------------------------------------------------------------

test('SIGNATURE_CACHE_BLOCKER is a sentinel with a stable nodeID', () => {
  // Tableau's debug dump dereferences `node.blocker.nodeID`, so the sentinel
  // must always carry one. It is NOT a real Node (no constructor constraints).
  assert.equal(Node.SIGNATURE_CACHE_BLOCKER.nodeID, 'signature-cache');
  assert.ok(!(Node.SIGNATURE_CACHE_BLOCKER instanceof Node),
    'the sentinel is a plain object, not a Node');
});

// ---------------------------------------------------------------------------
// BlockingSignatureCache add/contains/resize.
// ---------------------------------------------------------------------------

/**
 * A fake checker: nodes carry a label array; signatures capture the interned
 * label. Mirrors the contract SingleDirectBlockingChecker fulfils.
 */
function fakeChecker(setFactory) {
  return {
    _setFactory: setFactory,
    getAtomicConceptsLabel(node) { return setFactory.getSet(node.labels); },
    canBeBlocked(_node) { return true; },
    blockingHashCode(node) {
      return SingleBlockingSignature.labelHash(this.getAtomicConceptsLabel(node));
    },
    getBlockingSignatureFor(node) {
      return new SingleBlockingSignature(setFactory, this.getAtomicConceptsLabel(node));
    }
  };
}

const node = (labels) => ({ labels });

test('addNode deduplicates equal signatures', () => {
  const cache = new BlockingSignatureCache(fakeChecker(new SetFactory()));
  const a1 = node(['A', 'B']);
  const a2 = node(['B', 'A']); // same set, different order
  assert.equal(cache.addNode(a1), true, 'first signature recorded');
  assert.equal(cache.addNode(a2), false, 'an equal signature is not recorded twice');
  assert.equal(cache.addNode(node(['C'])), true, 'a different signature is recorded');
});

test('containsSignature finds remembered shapes', () => {
  const cache = new BlockingSignatureCache(fakeChecker(new SetFactory()));
  cache.addNode(node(['A']));
  assert.equal(cache.containsSignature(node(['A'])), true);
  assert.equal(cache.containsSignature(node(['B'])), false);
});

test('labels are interned so signatures compare by identity', () => {
  const factory = new SetFactory();
  const cache = new BlockingSignatureCache(fakeChecker(factory));
  cache.addNode(node(['A', 'B', 'C']));
  // A fresh, separately-sorted array of equal elements must still match.
  assert.equal(cache.containsSignature(node(['C', 'A', 'B'])), true);
});

test('resize preserves every cached signature', () => {
  const factory = new SetFactory();
  const cache = new BlockingSignatureCache(fakeChecker(factory));
  // Insert enough distinct signatures to force several doublings of the
  // 1024-bucket table (threshold 0.75 -> resize at 768 elements).
  const inserted = [];
  for (let i = 0; i < 2000; i++) {
    const n = node([`C${i}`]);
    if (cache.addNode(n)) inserted.push(n);
  }
  assert.ok(cache._buckets.length > 1024, 'the table grew');
  for (const n of inserted) {
    assert.equal(cache.containsSignature(n), true, `C${n.labels[0].slice(1)} still found`);
  }
});

test('a node not eligible for blocking is never looked up', () => {
  const factory = new SetFactory();
  const checker = fakeChecker(factory);
  checker.canBeBlocked = () => false; // e.g. a root node
  const cache = new BlockingSignatureCache(checker);
  cache.addNode(node(['A']));
  assert.equal(cache.containsSignature(node(['A'])), false,
    'canBeBlocked guards the lookup, exactly as HermiT');
});

test('tree nodes only are blockers (NODE_TYPE guard)', () => {
  // Sanity check the real checker contract the cache relies on.
  const { SingleDirectBlockingChecker } = require('../src/tableau/BlockingStrategy');
  const checker = new SingleDirectBlockingChecker();
  const fakeTree = { nodeType: NODE_TYPE.TREE_NODE };
  const fakeRoot = { nodeType: NODE_TYPE.ROOT };
  assert.equal(checker.canBeBlocker(fakeTree), true);
  assert.equal(checker.canBeBlocker(fakeRoot), false);
});
