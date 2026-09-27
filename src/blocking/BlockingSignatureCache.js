'use strict';

// ---------------------------------------------------------------------------
// blocking/BlockingSignatureCache.js — remember blocker shapes across models.
//
// Mirrors org.semanticweb.HermiT.blocking.BlockingSignatureCache.
//
// After a model is found, every unblocked blocker node's signature is recorded
// here. When a LATER expansion (a different branch of the same ontology, or a
// later satisfiability test over the same permanent ontology) reaches a node
// whose signature matches a remembered one, the node can be blocked
// immediately — without waiting for a live blocker to appear. This is a pure
// performance optimisation: reasoning results are unchanged.
//
// The cache is only consulted when there is no additional (query) ontology —
// matching HermiT's `m_useBlockingSignatureCache = (getAdditionalHyperresolutionManager()==null)`.
// The strategies gate on that themselves, so this class assumes it is only fed
// nodes from a single permanent-ontology context.
//
// Bucket structure and rehashing mirror HermiT exactly (power-of-two table,
// 0.75 load factor, the `getIndexFor` bit-mixing function).
// ---------------------------------------------------------------------------

class BlockingSignatureCache {
  /** @param {DirectBlockingChecker} directBlockingChecker */
  constructor(directBlockingChecker) {
    this._directBlockingChecker = directBlockingChecker;
    this._buckets = new Array(1024).fill(null);
    this._threshold = Math.floor(this._buckets.length * 0.75);
    this._numberOfElements = 0;
  }

  isEmpty() { return this._numberOfElements === 0; }

  /**
   * Record `node`'s signature. Returns false if an equal signature is already
   * cached (the node is already coverable).
   */
  addNode(node) {
    const hashCode = this._directBlockingChecker.blockingHashCode(node);
    const bucketIndex = getIndexFor(hashCode, this._buckets.length);
    let entry = this._buckets[bucketIndex];
    while (entry !== null) {
      if (hashCode === entry.signatureHashCode() && entry.blocksNode(node, this._directBlockingChecker)) {
        return false;
      }
      entry = entry.getNextEntry();
    }
    entry = this._directBlockingChecker.getBlockingSignatureFor(node);
    entry.setNextEntry(this._buckets[bucketIndex]);
    this._buckets[bucketIndex] = entry;
    this._numberOfElements++;
    if (this._numberOfElements >= this._threshold) this._resize(this._buckets.length * 2);
    return true;
  }

  _resize(newCapacity) {
    const newBuckets = new Array(newCapacity).fill(null);
    for (const head of this._buckets) {
      let entry = head;
      while (entry !== null) {
        const nextEntry = entry.getNextEntry();
        const newIndex = getIndexFor(entry.signatureHashCode(), newCapacity);
        entry.setNextEntry(newBuckets[newIndex]);
        newBuckets[newIndex] = entry;
        entry = nextEntry;
      }
    }
    this._buckets = newBuckets;
    this._threshold = Math.floor(newCapacity * 0.75);
  }

  /**
   * Is there a cached signature that blocks `node`? Only tree-eligible nodes
   * are looked up (HermiT guards with `canBeBlocked`).
   */
  containsSignature(node) {
    if (this._directBlockingChecker.canBeBlocked(node)) {
      const hashCode = this._directBlockingChecker.blockingHashCode(node);
      const bucketIndex = getIndexFor(hashCode, this._buckets.length);
      let entry = this._buckets[bucketIndex];
      while (entry !== null) {
        if (hashCode === entry.signatureHashCode() && entry.blocksNode(node, this._directBlockingChecker)) {
          return true;
        }
        entry = entry.getNextEntry();
      }
    }
    return false;
  }
}

/** HermiT's bucket index derivation (java.util.HashMap's pre-Java-8 spreader). */
function getIndexFor(hashCode, tableLength) {
  let h = hashCode | 0;
  h += ~(h << 9); h |= 0;
  h ^= (h >>> 14);
  h += (h << 4); h |= 0;
  h ^= (h >>> 10);
  return h & (tableLength - 1);
}

module.exports = { BlockingSignatureCache };
