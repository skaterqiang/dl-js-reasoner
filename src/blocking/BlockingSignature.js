'use strict';

// ---------------------------------------------------------------------------
// blocking/BlockingSignature.js — a reusable "shape" for a blocked node.
//
// Mirrors org.semanticweb.HermiT.blocking.BlockingSignature plus the two
// concrete subclasses HermiT nests inside its direct blocking checkers:
//   SingleBlockingSignature   (SingleDirectBlockingChecker.SingleBlockingSignature)
//   PairWiseBlockingSignature (PairWiseDirectBlockingChecker.PairWiseBlockingSignature)
//
// A signature captures the blocking label(s) of one model node. Later nodes
// whose labels match can be blocked WITHOUT a live blocker node — this is the
// BlockingSignatureCache optimisation. Labels are SetFactory-interned, so
// `blocksNode` compares by IDENTITY, exactly as HermiT compares with `==`.
// ---------------------------------------------------------------------------

/** Base class: the linked-list slot used by BlockingSignatureCache's buckets. */
class BlockingSignature {
  constructor() {
    /** next entry in a BlockingSignatureCache bucket chain */
    this._nextEntry = null;
  }
  getNextEntry() { return this._nextEntry; }
  setNextEntry(nextEntry) { this._nextEntry = nextEntry; }
  /** @returns {boolean} true when this signature blocks `node` */
  blocksNode(node) { throw new Error('blocksNode must be implemented by subclass'); }
  /** @returns {number} bucket hash — MUST be stable for equal signatures */
  signatureHashCode() { throw new Error('signatureHashCode must be implemented by subclass'); }
}

/**
 * Single-granularity signature: just the node's atomic-concept label.
 * (HermiT `SingleDirectBlockingChecker.SingleBlockingSignature`.)
 */
class SingleBlockingSignature extends BlockingSignature {
  /**
   * @param {SetFactory} conceptsSetFactory  factory that interned the label
   * @param {LabelSet} atomicConceptsLabel   interned concept label of the node
   */
  constructor(conceptsSetFactory, atomicConceptsLabel) {
    super();
    this.atomicConceptsLabel = atomicConceptsLabel;
    // The signature outlives the node it was taken from, so keep the label.
    conceptsSetFactory.makePermanent(atomicConceptsLabel);
  }
  blocksNode(node, checker) {
    return checker.getAtomicConceptsLabel(node) === this.atomicConceptsLabel;
  }
  signatureHashCode() { return SingleBlockingSignature.labelHash(this.atomicConceptsLabel); }
  /** Bucket hash for a single concept label (used by the checker too). */
  static labelHash(atomicConceptsLabel) { return stringHashCode(atomicConceptsLabel.key); }
}

/**
 * Pairwise signature: node concepts + parent concepts + both edge labels.
 * (HermiT `PairWiseDirectBlockingChecker.PairWiseBlockingSignature`.)
 */
class PairWiseBlockingSignature extends BlockingSignature {
  /**
   * @param {SetFactory} rolesSetFactory
   * @param {LabelSet} atomicConceptsLabel  node concept label
   * @param {LabelSet} parentConceptsLabel  parent concept label
   * @param {LabelSet} fromParentLabel      edge label parent→node
   * @param {LabelSet} toParentLabel        edge label node→parent
   */
  constructor(rolesSetFactory, atomicConceptsLabel, parentConceptsLabel, fromParentLabel, toParentLabel) {
    super();
    this.atomicConceptsLabel = atomicConceptsLabel;
    this.parentConceptsLabel = parentConceptsLabel;
    this.fromParentLabel = fromParentLabel;
    this.toParentLabel = toParentLabel;
    rolesSetFactory.makePermanent(atomicConceptsLabel);
    rolesSetFactory.makePermanent(parentConceptsLabel);
    rolesSetFactory.makePermanent(fromParentLabel);
    rolesSetFactory.makePermanent(toParentLabel);
  }
  blocksNode(node, checker) {
    return checker.getAtomicConceptsLabel(node) === this.atomicConceptsLabel
      && checker.getAtomicConceptsLabel(node.parent) === this.parentConceptsLabel
      && checker.getFromParentLabel(node) === this.fromParentLabel
      && checker.getToParentLabel(node) === this.toParentLabel;
  }
  signatureHashCode() {
    return PairWiseBlockingSignature.labelHash(
      this.atomicConceptsLabel, this.parentConceptsLabel,
      this.fromParentLabel, this.toParentLabel
    );
  }
  /** Bucket hash folding all four labels (used by the checker too). */
  static labelHash(concepts, parentConcepts, fromParent, toParent) {
    return stringHashCode(concepts.key + '|' + parentConcepts.key + '|' + fromParent.key + '|' + toParent.key);
  }
}

/**
 * Java-style 32-bit string hash (String.hashCode). HermiT buckets on the
 * label's own hashCode; here labels are interned by canonical key, so the
 * key's hash is the faithful equivalent.
 */
function stringHashCode(s) {
  let h = 0;
  for (let i = 0; i < s.length; i++) {
    h = ((h << 5) - h + s.charCodeAt(i)) | 0;
  }
  return h;
}

module.exports = {
  BlockingSignature,
  SingleBlockingSignature,
  PairWiseBlockingSignature,
  stringHashCode
};
