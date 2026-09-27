'use strict';

// ---------------------------------------------------------------------------
// blocking/SetFactory.js — canonicalisation for blocking label sets.
//
// Mirrors org.semanticweb.HermiT.blocking.SetFactory.
//
// Blocking labels are immutable sets of DLPredicates. Two nodes with the SAME
// label must compare equal, and the BlockingSignatureCache compares labels by
// IDENTITY (`==` in Java), so every distinct label must exist exactly once.
// This factory interns each distinct label: `getSet(elements)` returns the
// same LabelSet instance for the same set of elements, no matter how many
// times it is asked.
//
// Reference counting: a node holds a reference to its current label while the
// label is cached. When the node's label changes the reference is released;
// when the count reaches zero and the label is not `permanent`, the entry is
// recycled. The BlockingSignatureCache calls `makePermanent` so a signature's
// label survives the nodes it was taken from (HermiT does the same).
//
// Simplification vs HermiT: Java's `SetFactory.Entry` subclasses `AbstractSet`
// and reuses pooled entry objects. Here a LabelSet is a plain frozen-ish
// object; correctness comes from interning + canonical keying, not pooling.
// ---------------------------------------------------------------------------

/**
 * Compute the element multiset key. Two element arrays that contain the same
 * predicates (in any order) produce the same key, because DLPredicates are
 * interned and have a stable `iri`/identity string via `toString()`.
 *
 * @param {Array<object>} elements
 * @returns {string}
 */
function setKey(elements) {
  const parts = new Array(elements.length);
  for (let i = 0; i < elements.length; i++) parts[i] = String(elements[i]);
  parts.sort();
  return parts.length + ':' + parts.join('');
}

class LabelSet {
  /** @param {Array<object>} elements */
  constructor(elements) {
    this.elements = elements;          // the canonical, sorted element array
    this.key = setKey(elements);       // the interning key
    this.referenceCount = 0;
    this.permanent = false;
  }
  contains(o) { return this.elements.indexOf(o) !== -1; }
  size() { return this.elements.length; }
  isEmpty() { return this.elements.length === 0; }
}

class SetFactory {
  constructor() {
    /** @type {Map<string, LabelSet>} canonical key → interned label */
    this._entries = new Map();
  }

  /**
   * Return THE interned label for `elements`. `elements` may be in any order;
   * it is sorted before keying. Callers should NOT mutate the returned
   * `elements` array afterwards (it becomes the canonical store).
   */
  getSet(elements) {
    const sorted = elements.slice().sort((a, b) => {
      const sa = String(a); const sb = String(b);
      return sa < sb ? -1 : sa > sb ? 1 : 0;
    });
    const key = setKey(sorted);
    let entry = this._entries.get(key);
    if (entry === undefined) {
      entry = new LabelSet(sorted);
      this._entries.set(key, entry);
    }
    return entry;
  }

  /** Record that a node now references `set`. */
  addReference(set) { set.referenceCount++; }

  /**
   * Release a reference. When the count reaches zero and the set is not
   * permanent, it is uninterned (so a future identical label gets a fresh
   * entry — matching HermiT's `clearNonpermanent`/`removeReference`).
   */
  removeReference(set) {
    set.referenceCount--;
    if (set.referenceCount === 0 && !set.permanent) this._entries.delete(set.key);
  }

  /** Keep `set` alive even when its reference count drops to zero. */
  makePermanent(set) { set.permanent = true; }

  /** Drop every non-permanent label (HermiT `clearNonpermanent`). */
  clearNonpermanent() {
    for (const [key, entry] of this._entries) {
      if (!entry.permanent) this._entries.delete(key);
    }
  }

  /** Approximate memory footprint — kept for API parity with HermiT. */
  sizeInMemory() { return this._entries.size; }
}

module.exports = { SetFactory, LabelSet };
