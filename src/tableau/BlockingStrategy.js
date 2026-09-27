'use strict';

// ---------------------------------------------------------------------------
// tableau/BlockingStrategy.js — termination: block repeating tree patterns.
//
// Mirrors org.semanticweb.HermiT.blocking.{AnywhereBlocking, AncestorBlocking,
// SingleDirectBlockingChecker, PairWiseDirectBlockingChecker} plus the three
// selection switches in HermiT's `Reasoner.createTableau`.
//
// A tree node is *blocked* when an earlier node repeats its blocking label;
// blocked nodes are not expanded, which makes the (otherwise infinite) model
// construction terminate. Two label granularities:
//
//   single  — the node's set of atomic concepts. Sound for ontologies WITHOUT
//             inverse roles.
//   pairwise — node concepts + parent concepts + role labels of the edges to
//             the parent (both directions). Required with inverse roles.
//
// Two candidate-blocker policies, both EXACT (they never block a node that
// could still lead to a model, so reasoning results are identical — only the
// size of the constructed model differs):
//
//   anywhere — a blocker may be any earlier unblocked tree node. HermiT's
//              default; strictly more pruning, usually smaller models.
//   ancestor — a blocker must be one of the node's own ancestors. Bigger
//              models, but the candidate search walks one parent chain instead
//              of scanning every earlier node, so it can be faster.
//
// Simplification vs HermiT: labels are fetched from the extension tables on
// demand and cached per computeBlocking() sweep (no incremental SetFactory
// bookkeeping). computeBlocking() is called once per expansion sweep, so the
// labels are always current when blocking decisions are made.
//
// Not ported: the approximate "core" blocking strategies (SIMPLE_CORE /
// COMPLEX_CORE) and the BlockingSignatureCache. `createBlockingStrategy`
// degrades both and reports it through `configuration.warningMonitor`.
// ---------------------------------------------------------------------------

const { NODE_TYPE, Node } = require('./Node');
const { AtomicConcept, AtomicRole } = require('../model/DLPredicate');
const {
  DIRECT_BLOCKING_TYPE,
  BLOCKING_STRATEGY_TYPE,
  BLOCKING_SIGNATURE_CACHE_TYPE
} = require('../Configuration');
const { SetFactory } = require('../blocking/SetFactory');
const { BlockingSignatureCache } = require('../blocking/BlockingSignatureCache');
const {
  SingleBlockingSignature,
  PairWiseBlockingSignature
} = require('../blocking/BlockingSignature');

// ---- direct blocking checkers ----------------------------------------------

class DirectBlockingChecker {
  constructor() {
    // Labels are SetFactory-interned so equal labels are identical objects —
    // the BlockingSignatureCache compares them with `===`, exactly as HermiT
    // compares its SetFactory-interned sets with `==`.
    this._setFactory = new SetFactory();
  }
  initialize(tableau) { this.tableau = tableau; }
  clear() { this._labelCache = new Map(); }
  /** Fetch (and cache) the INTERNED atomic-concept label of a node. */
  getAtomicConceptsLabel(node) {
    let label = this._labelCache.get(node);
    if (label === undefined) {
      label = this.fetchAtomicConceptsLabel(node);
      this._labelCache.set(node, label);
    }
    return label;
  }
  fetchAtomicConceptsLabel(node) {
    const entries = this.tableau.extensionManager.binaryTable.retrieve(null, [node]);
    const concepts = [];
    for (const e of entries) {
      if (e.tuple[0] instanceof AtomicConcept) concepts.push(e.tuple[0]);
    }
    return this._setFactory.getSet(concepts);
  }
  labelsEqual(l1, l2) { return l1 === l2; } // interned ⇒ identity comparison

  /**
   * Bucket hash for the BlockingSignatureCache (HermiT `blockingHashCode`).
   * Labels are interned, so the canonical key's string hash is stable for
   * equal labels. Overridden by the pairwise checker to fold in the extra
   * labels.
   */
  blockingHashCode(node) {
    return SingleBlockingSignature.labelHash(this.getAtomicConceptsLabel(node));
  }

  /** @returns {BlockingSignature} a signature capturing this node's shape. */
  getBlockingSignatureFor(node) {
    throw new Error('getBlockingSignatureFor must be implemented by subclass');
  }
}

class SingleDirectBlockingChecker extends DirectBlockingChecker {
  isBlockedBy(blocker, blocked) {
    return !blocker.isBlocked()
      && blocker.nodeType === NODE_TYPE.TREE_NODE
      && blocked.nodeType === NODE_TYPE.TREE_NODE
      && this.labelsEqual(this.getAtomicConceptsLabel(blocker), this.getAtomicConceptsLabel(blocked));
  }
  canBeBlocker(node) { return node.nodeType === NODE_TYPE.TREE_NODE; }
  canBeBlocked(node) { return node.nodeType === NODE_TYPE.TREE_NODE; }
  getBlockingSignatureFor(node) {
    return new SingleBlockingSignature(this._setFactory, this.getAtomicConceptsLabel(node));
  }
}

class PairWiseDirectBlockingChecker extends DirectBlockingChecker {
  isBlockedBy(blocker, blocked) {
    if (blocker.isBlocked()) return false;
    if (blocker.nodeType !== NODE_TYPE.TREE_NODE || blocked.nodeType !== NODE_TYPE.TREE_NODE) return false;
    if (!this.labelsEqual(this.getAtomicConceptsLabel(blocker), this.getAtomicConceptsLabel(blocked))) return false;
    if (!this.labelsEqual(this.getAtomicConceptsLabel(blocker.parent), this.getAtomicConceptsLabel(blocked.parent))) return false;
    if (!this.roleLabelsEqual(this.getFromParentLabel(blocker), this.getFromParentLabel(blocked))) return false;
    if (!this.roleLabelsEqual(this.getToParentLabel(blocker), this.getToParentLabel(blocked))) return false;
    return true;
  }
  canBeBlocker(node) {
    return node.nodeType === NODE_TYPE.TREE_NODE && node.parent !== null
      && node.parent.nodeType === NODE_TYPE.TREE_NODE;
  }
  canBeBlocked(node) { return this.canBeBlocker(node); }

  // Edge labels are interned too, so a pairwise signature can hold them.
  getFromParentLabel(node) { return this.fetchEdgeLabel(node.parent, node); }
  getToParentLabel(node) { return this.fetchEdgeLabel(node, node.parent); }
  fetchEdgeLabel(nodeFrom, nodeTo) {
    const entries = this.tableau.extensionManager.ternaryTable.retrieve(null, [nodeFrom, nodeTo]);
    const roles = [];
    for (const e of entries) {
      if (e.tuple[0] instanceof AtomicRole) roles.push(e.tuple[0]);
    }
    return this._setFactory.getSet(roles);
  }
  roleLabelsEqual(l1, l2) { return this.labelsEqual(l1, l2); }

  blockingHashCode(node) {
    return PairWiseBlockingSignature.labelHash(
      this.getAtomicConceptsLabel(node),
      this.getAtomicConceptsLabel(node.parent),
      this.getFromParentLabel(node),
      this.getToParentLabel(node)
    );
  }
  getBlockingSignatureFor(node) {
    return new PairWiseBlockingSignature(
      this._setFactory,
      this.getAtomicConceptsLabel(node),
      this.getAtomicConceptsLabel(node.parent),
      this.getFromParentLabel(node),
      this.getToParentLabel(node)
    );
  }
}

// ---- blocking strategies -----------------------------------------------------

/**
 * Shared machinery for the two exact blocking strategies.
 *
 * Both strategies recompute the blocking status of every active node from
 * scratch once per expansion sweep, so none of HermiT's incremental
 * notification hooks need to do anything: the labels are re-read from the
 * extension tables at the start of the next `computeBlocking()`. They differ
 * only in *which* nodes are eligible to act as a blocker.
 */
class BlockingStrategy {
  /**
   * @param {DirectBlockingChecker} directBlockingChecker
   * @param {BlockingSignatureCache|null} blockingSignatureCache
   */
  constructor(directBlockingChecker, blockingSignatureCache = null) {
    this.checker = directBlockingChecker;
    this.blockingSignatureCache = blockingSignatureCache;
    this.tableau = null;
    // HermiT: m_useBlockingSignatureCache = (tableau.getAdditionalHyperresolutionManager()==null).
    this._useBlockingSignatureCache = false;
  }

  initialize(tableau) {
    this.tableau = tableau;
    this.checker.initialize(tableau);
    this.updateBlockingSignatureCacheUsage();
  }

  additionalDLOntologySet(_additionalDLOntology) { this.updateBlockingSignatureCacheUsage(); }
  additionalDLOntologyCleared() { this.updateBlockingSignatureCacheUsage(); }

  updateBlockingSignatureCacheUsage() {
    this._useBlockingSignatureCache = this.tableau !== null
      && this.tableau.getAdditionalHyperresolutionManager() === null;
  }

  clear() { this.checker.clear(); }

  /**
   * A blocked node's descendants are never expanded, so every assertion on a
   * node that survives into the final model is permanent for both exact
   * strategies. (Only the approximate core-blocking strategies return false
   * here, because they may retract a block during validation.)
   */
  isPermanentAssertion(conceptOrRange, node) { return true; }

  /** Both ported strategies are exact: blocking never loses a model. */
  isExact() { return true; }

  /**
   * Feed the finished model's blocker signatures into the cache (HermiT
   * `AnywhereBlocking.modelFound` / `AncestorBlocking.modelFound`). Without a
   * cache this is a no-op.
   */
  modelFound() {
    if (this._useBlockingSignatureCache && this.blockingSignatureCache !== null) {
      let node = this.tableau.firstTableauNode;
      while (node !== null) {
        if (node.isActive() && !node.isBlocked() && this.checker.canBeBlocker(node)) {
          this.blockingSignatureCache.addNode(node);
        }
        node = node.nextTableauNode;
      }
    }
  }

  // Notification hooks (labels are recomputed per sweep; nothing to maintain).
  assertionAddedConcept(concept, node) {}
  assertionRemovedConcept(concept, node) {}
  assertionAddedRole(role, from, to) {}
  assertionRemovedRole(role, from, to) {}
  nodesMerged(mergeFrom, mergeInto) {}
  nodesUnmerged(mergeFrom, mergeInto) {}
  nodeStatusChanged(node) {}
  nodeInitialized(node) {}
  nodeDestroyed(node) {}
}

/**
 * Anywhere blocking (HermiT's `AnywhereBlocking`, the default).
 *
 * A blocker may be ANY earlier unblocked tree node, not merely an ancestor.
 * This prunes strictly more than ancestor blocking while remaining exact.
 */
class AnywhereBlocking extends BlockingStrategy {
  constructor(directBlockingChecker, blockingSignatureCache = null) {
    super(directBlockingChecker, blockingSignatureCache);
    /** candidate blockers in creation order */
    this.blockers = [];
  }

  clear() {
    super.clear();
    this.blockers.length = 0;
  }

  /**
   * Full recomputation of the blocking status of every node (HermiT does this
   * incrementally from the first changed node; a full sweep per expansion
   * round is simpler and equally correct).
   */
  computeBlocking(finalChance) {
    this.checker.clear();
    this.blockers.length = 0;
    const checkSignatureCache = this._useBlockingSignatureCache
      && this.blockingSignatureCache !== null && !this.blockingSignatureCache.isEmpty();
    let node = this.tableau.firstTableauNode;
    while (node !== null) {
      if (node.isActive()) {
        const parent = node.parent;
        if (parent === null) {
          node.setBlocked(null, false);
        } else if (parent.isBlocked()) {
          // Indirectly blocked: an ancestor is blocked.
          node.setBlocked(parent, false);
        } else if (this.checker.canBeBlocked(node)) {
          // A remembered signature can block this node even when no live
          // blocker exists yet (HermiT's BlockingSignatureCache path).
          if (checkSignatureCache && this.blockingSignatureCache.containsSignature(node)) {
            node.setBlocked(Node.SIGNATURE_CACHE_BLOCKER, true);
          } else {
            const blocker = this.getBlocker(node);
            node.setBlocked(blocker, blocker !== null);
          }
        } else {
          node.setBlocked(null, false);
        }
        if (!node.isBlocked() && this.checker.canBeBlocker(node)) {
          this.blockers.push(node);
        }
      }
      node = node.nextTableauNode;
    }
  }

  /** First earlier unblocked node whose label covers `node`'s. */
  getBlocker(node) {
    for (const candidate of this.blockers) {
      if (candidate.nodeID >= node.nodeID) break; // creation order
      if (this.checker.isBlockedBy(candidate, node)) return candidate;
    }
    return null;
  }
}

/**
 * Ancestor blocking (HermiT's `AncestorBlocking`).
 *
 * Only the node's own ancestors are candidates, so the search walks a single
 * parent chain rather than scanning every earlier node. Models come out larger
 * but the per-node cost is lower, which can win on some ontologies.
 *
 * Like HermiT's version this strategy cannot serve a lazy expansion strategy,
 * because deciding a node's status may require its not-yet-created ancestors.
 * This port only has eager strategies, so that is not a live restriction.
 */
class AncestorBlocking extends BlockingStrategy {
  computeBlocking(finalChance) {
    this.checker.clear();
    let node = this.tableau.firstTableauNode;
    while (node !== null) {
      if (node.isActive()) {
        const parent = node.parent;
        if (parent === null) {
          node.setBlocked(null, false);
        } else if (parent.isBlocked()) {
          // Indirectly blocked: an ancestor is blocked.
          node.setBlocked(parent, false);
        } else {
          this.checkParentBlocking(node);
        }
      }
      node = node.nextTableauNode;
    }
  }

  /** Nearest ancestor whose label covers `node`'s, or leave it unblocked. */
  checkParentBlocking(node) {
    if (this._useBlockingSignatureCache
        && this.blockingSignatureCache !== null
        && this.blockingSignatureCache.containsSignature(node)) {
      node.setBlocked(Node.SIGNATURE_CACHE_BLOCKER, true);
      return;
    }
    let blocker = node.parent;
    while (blocker !== null) {
      if (this.checker.isBlockedBy(blocker, node)) {
        node.setBlocked(blocker, true);
        return;
      }
      blocker = blocker.parent;
    }
    node.setBlocked(null, false);
  }

  /**
   * Unsupported by design — mirrors HermiT's `UnsupportedOperationException`.
   * Ancestor blocking needs the whole parent chain to exist before it can
   * decide, which a lazy (one-node-at-a-time) expansion strategy cannot offer.
   */
  computeIsBlocked(node) {
    throw new Error(
      'Unsupported operation: ancestor blocking cannot be used with a lazy expansion strategy.');
  }
}

// ---- selection ---------------------------------------------------------------

/**
 * Whether the requested strategy is one of HermiT's approximate "core"
 * blocking strategies, which need the unported `AnywhereValidatedBlocking` /
 * `BlockingValidator` stack.
 */
function isCoreBlockingStrategy(blockingStrategyType) {
  return blockingStrategyType === BLOCKING_STRATEGY_TYPE.SIMPLE_CORE
    || blockingStrategyType === BLOCKING_STRATEGY_TYPE.COMPLEX_CORE;
}

/**
 * Build the blocking strategy named by a configuration.
 *
 * Port of the three switches in HermiT's `Reasoner.createTableau`
 * (`Reasoner.java:1968-2025`), which pick a direct blocking checker, then a
 * signature cache, then the strategy that combines them.
 *
 * Two of HermiT's options cannot be honoured and degrade, each with a warning
 * through `configuration.warningMonitor` so the caller is never silently given
 * something other than what they asked for:
 *
 *   - `SIMPLE_CORE` / `COMPLEX_CORE` fall back to `ANYWHERE`. Both ported
 *     strategies are EXACT, so the answers are identical; core blocking only
 *     produces smaller models at the cost of a validation pass.
 *   - `BLOCKING_SIGNATURE_CACHE_TYPE.CACHED` falls back to no cache. It is a
 *     pure speed/memory optimisation: it lets later nodes be blocked by a
 *     signature remembered from an earlier model instead of by a live node.
 *
 * `hasNominals` is only consulted for the cache decision, exactly as in
 * HermiT: caching is unsound with nominals, so HermiT skips it there.
 *
 * @param {object} [configuration] a `Configuration`, or a plain overrides bag
 * @param {boolean} hasInverseRoles  whether either DLOntology has inverse roles
 * @param {boolean} [hasNominals]    whether either DLOntology has nominals
 * @returns {BlockingStrategy}
 */
function createBlockingStrategy(configuration, hasInverseRoles, hasNominals = false) {
  const config = configuration || {};
  const directBlockingType = config.directBlockingType || DIRECT_BLOCKING_TYPE.OPTIMAL;
  const blockingStrategyType = config.blockingStrategyType || BLOCKING_STRATEGY_TYPE.OPTIMAL;
  const cacheType = config.blockingSignatureCacheType === undefined
    ? BLOCKING_SIGNATURE_CACHE_TYPE.NOT_CACHED
    : config.blockingSignatureCacheType;
  const warn = typeof config.warningMonitor === 'function' ? config.warningMonitor : null;

  // Core blocking is not ported. Degrade to ANYWHERE (exact, so results are
  // unchanged) and say so rather than pretending the request was honoured.
  let effectiveStrategyType = blockingStrategyType;
  if (isCoreBlockingStrategy(blockingStrategyType)) {
    if (warn) {
      warn(`Blocking strategy ${blockingStrategyType} is not implemented in this port; `
        + 'falling back to ANYWHERE blocking. Results are unaffected (both are exact), '
        + 'but models may be larger than HermiT would build.');
    }
    effectiveStrategyType = BLOCKING_STRATEGY_TYPE.ANYWHERE;
  }

  // ---- direct blocking checker (HermiT Reasoner.java:1968-1992) -------------
  // HermiT substitutes the *Validated* checkers under a core strategy; those
  // are not ported, and the core strategies degrade above, so the plain
  // checkers are always the right choice here.
  let checker;
  switch (directBlockingType) {
    case DIRECT_BLOCKING_TYPE.OPTIMAL:
      checker = hasInverseRoles
        ? new PairWiseDirectBlockingChecker()
        : new SingleDirectBlockingChecker();
      break;
    case DIRECT_BLOCKING_TYPE.SINGLE:
      // Forcing SINGLE on an ontology with inverse roles is unsound in
      // general; HermiT lets the user do it anyway, and so do we.
      checker = new SingleDirectBlockingChecker();
      break;
    case DIRECT_BLOCKING_TYPE.PAIR_WISE:
      checker = new PairWiseDirectBlockingChecker();
      break;
    default:
      throw new Error(`Unknown direct blocking type: ${directBlockingType}`);
  }

  // ---- blocking signature cache (HermiT Reasoner.java:1994-2006) ------------
  // Validated on its own so an unknown value throws even when the cache would
  // be skipped anyway — matching HermiT, which only skips the switch when the
  // ontology has nominals or a core strategy was requested.
  switch (cacheType) {
    case BLOCKING_SIGNATURE_CACHE_TYPE.CACHED:
    case BLOCKING_SIGNATURE_CACHE_TYPE.NOT_CACHED:
      break;
    default:
      throw new Error(`Unknown blocking signature cache type: ${cacheType}`);
  }
  // The cache IS ported. HermiT's guard is `!hasNominals && !coreStrategy`:
  // caching is unsound with nominals, and the (unported) core strategies
  // validate against live nodes. A core request degrades to ANYWHERE above, so
  // here only the nominals half of the guard survives.
  const useSignatureCache = cacheType === BLOCKING_SIGNATURE_CACHE_TYPE.CACHED && !hasNominals;
  const signatureCache = useSignatureCache ? new BlockingSignatureCache(checker) : null;

  // ---- blocking strategy (HermiT Reasoner.java:2008-2025) -------------------
  switch (effectiveStrategyType) {
    case BLOCKING_STRATEGY_TYPE.ANYWHERE:
    case BLOCKING_STRATEGY_TYPE.OPTIMAL:
      // HermiT's OPTIMAL is SIMPLE_CORE with nominals and ANYWHERE otherwise.
      // SIMPLE_CORE is not ported, so OPTIMAL always resolves to ANYWHERE —
      // which is also what HermiT does for the no-nominals case.
      return new AnywhereBlocking(checker, signatureCache);
    case BLOCKING_STRATEGY_TYPE.ANCESTOR:
      return new AncestorBlocking(checker, signatureCache);
    default:
      throw new Error(`Unknown blocking strategy type: ${effectiveStrategyType}`);
  }
}

module.exports = {
  BlockingStrategy,
  AnywhereBlocking,
  AncestorBlocking,
  DirectBlockingChecker,
  SingleDirectBlockingChecker,
  PairWiseDirectBlockingChecker,
  isCoreBlockingStrategy,
  createBlockingStrategy
};
