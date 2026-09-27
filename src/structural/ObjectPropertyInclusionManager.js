'use strict';

// ---------------------------------------------------------------------------
// structural/ObjectPropertyInclusionManager.js
//
// Analogue of org.semanticweb.HermiT.structural.ObjectPropertyInclusionManager,
// with one deliberate architectural difference.
//
// == What HermiT does ==
// HermiT builds, for every object property expression R, a finite automaton
// whose language is the set of role chains that R subsumes (built from the
// SubPropertyOf / SubPropertyChainOf / Transitive / Symmetric / Inverse
// axioms, using the `rationals` NFA library). `rewriteAxioms` then replaces
// every `∀R.C` whose R has a non-trivial automaton by a fresh concept and
// emits one concept inclusion per automaton transition. Complex roles are
// therefore *never materialised as edges* in the tableau: all of their
// semantics lives in the unfolded `∀R.C` inclusions.
//
// == What this port does ==
// It does NOT build automata. Instead:
//
//   1. Role simplicity is computed directly from the OWL 2 definition (see
//      `computeComplexObjectPropertyExpressions`), which is exactly the set
//      HermiT's `findSimpleProperties` recovers from the dependency graph.
//   2. Every complex inclusion `R1∘…∘Rn ⊑ S` is turned into a DL-clause by
//      `OWLClausification`:
//          R1(X,Y1) ∧ R2(Y1,Y2) ∧ … ∧ Rn(Yn-1,Yn) → S(X,Yn)
//      so complex roles ARE materialised as edges, and `∀S.C` needs no
//      rewriting at all — the S-edge is derived and the ordinary ∀-rule fires.
//
// The two designs are equivalent in expressive power for OWL 2 DL. The
// automaton version produces a smaller tableau (no chain edges) at the cost of
// ~700 lines of NFA construction, mirroring, ε-connection and disjoint union
// — the most bug-prone code in HermiT, as its own comments admit
// ("This part of the code seemed to have a bug in an ontology given by
// Birte…"). The clause version is a few dozen lines and reuses the
// hyperresolution engine that already exists.
//
// What is ported verbatim (none of it needs automata):
//   - findEquivalentProperties
//   - findSymmetricProperties
//   - buildInversePropertiesMap
//   - buildPropertyOrdering
//   - checkForRegularity          (same error messages as HermiT)
//   - the simplicity checks in rewriteAxioms
// ---------------------------------------------------------------------------

const E = require('../owl/OWLExpressions');

// ===========================================================================
// A tiny directed graph over property expressions.
//
// Mirrors org.semanticweb.HermiT.graph.Graph: nodes are keyed structurally
// (protege-js property objects are not interned, so object identity is not
// equality), and `getSuccessors` returns the LIVE set so callers can mutate it
// the way HermiT's checkForRegularity does.
// ===========================================================================

const keyOf = (p) => E.structuralKey(p);
const invKeyOf = (p) => E.structuralKey(E.inversePropertyOf(p));

class Graph {
  constructor() {
    /** @type {Map<string, {expr: object, successors: Set<string>}>} */
    this.nodes = new Map();
  }

  _node(p) {
    const k = keyOf(p);
    let n = this.nodes.get(k);
    if (!n) {
      n = { expr: p, successors: new Set() };
      this.nodes.set(k, n);
    }
    return n;
  }

  addEdge(from, to) {
    this._node(from).successors.add(keyOf(to));
    this._node(to); // ensure the target exists as a node
    return this;
  }

  /** All property expressions occurring in the graph, in insertion order. */
  getElements() {
    return [...this.nodes.values()].map(n => n.expr);
  }

  hasElement(p) { return this.nodes.has(keyOf(p)); }

  /** The live successor set (possibly empty, never null). */
  getSuccessors(p) {
    const n = this.nodes.get(keyOf(p));
    return n ? n.successors : EMPTY_SET;
  }

  /** Successors as property expressions. */
  getSuccessorElements(p) {
    const out = [];
    for (const k of this.getSuccessors(p)) {
      const n = this.nodes.get(k);
      if (n) out.push(n.expr);
    }
    return out;
  }

  clone() {
    const g = new Graph();
    for (const [k, n] of this.nodes) {
      g.nodes.set(k, { expr: n.expr, successors: new Set(n.successors) });
    }
    return g;
  }

  /** The graph with every edge reversed. */
  getInverse() {
    const g = new Graph();
    for (const [, n] of this.nodes) g._node(n.expr);
    for (const [, n] of this.nodes) {
      for (const s of n.successors) {
        const target = this.nodes.get(s);
        if (target) g._node(target.expr).successors.add(keyOf(n.expr));
      }
    }
    return g;
  }

  /** Reflexive-transitive closure of the edge relation (in place). */
  transitivelyClose() {
    // Warshall over the node keys; node counts here are tiny (one per role).
    const keys = [...this.nodes.keys()];
    const index = new Map(keys.map((k, i) => [k, i]));
    const n = keys.length;
    const reach = new Array(n);
    for (let i = 0; i < n; i++) {
      const row = new Uint8Array(n);
      for (const s of this.nodes.get(keys[i]).successors) {
        const j = index.get(s);
        if (j !== undefined) row[j] = 1;
      }
      reach[i] = row;
    }
    for (let k = 0; k < n; k++) {
      for (let i = 0; i < n; i++) {
        if (!reach[i][k]) continue;
        const rowI = reach[i];
        const rowK = reach[k];
        for (let j = 0; j < n; j++) if (rowK[j]) rowI[j] = 1;
      }
    }
    for (let i = 0; i < n; i++) {
      const succ = this.nodes.get(keys[i]).successors;
      for (let j = 0; j < n; j++) if (reach[i][j]) succ.add(keys[j]);
    }
    return this;
  }

  removeElements(elements) {
    const doomed = new Set();
    for (const p of elements) doomed.add(keyOf(p));
    for (const k of doomed) this.nodes.delete(k);
    for (const [, n] of this.nodes) {
      for (const k of doomed) n.successors.delete(k);
    }
    return this;
  }

  get size() { return this.nodes.size; }
}

const EMPTY_SET = new Set();

// ===========================================================================
// The manager
// ===========================================================================

class ObjectPropertyInclusionManager {
  /**
   * Computes everything the clausifier needs about the role hierarchy.
   * @param {import('./OWLAxioms').OWLAxioms} axioms
   */
  constructor(axioms) {
    this.axioms = axioms;

    const simple = axioms.simpleObjectPropertyInclusions;
    const complex = axioms.complexObjectPropertyInclusions;

    /** R ↦ set of property expressions equivalent to R (mutual subsumption). */
    this.equivalentPropertiesMap = findEquivalentProperties(simple);
    /** Properties R with R ⊑ R⁻ (declared symmetric). */
    this.symmetricObjectProperties = findSymmetricProperties(simple);
    /** R ↦ set of S with `InverseObjectProperties(R,S)` semantics. */
    this.inversePropertiesMap = buildInversePropertiesMap(simple);

    /** The sub-property dependency graph (edges point sub → super). */
    this.propertyDependencyGraph = buildPropertyOrdering(simple, complex, this.equivalentPropertiesMap);
    checkForRegularity(this.propertyDependencyGraph, this.equivalentPropertiesMap);

    /**
     * Property expressions that are NOT simple, i.e. transitive roles, roles
     * occurring in (or above) a chain axiom, and all their inverses.
     * @type {Set<string>} structural keys
     */
    this.complexKeys = computeComplexKeys(simple, complex);

    // Publish into the axiom set, exactly as HermiT's createAutomata does.
    for (const p of this._complexExpressions()) axioms.complexObjectPropertyExpressions.add(p);
  }

  /** Materialise the complex property expressions (R and R⁻ for each). */
  *_complexExpressions() {
    const seen = new Set();
    const all = this._allPropertyExpressions();
    for (const p of all) {
      const k = keyOf(p);
      if (this.complexKeys.has(k) && !seen.has(k)) {
        seen.add(k);
        yield p;
        const inv = E.inversePropertyOf(p);
        const ik = keyOf(inv);
        if (!seen.has(ik)) {
          seen.add(ik);
          yield inv;
        }
      }
    }
  }

  /** Every property expression mentioned anywhere in the role axioms. */
  _allPropertyExpressions() {
    const out = [];
    const a = this.axioms;
    for (const [sub, sup] of a.simpleObjectPropertyInclusions) { out.push(sub, sup); }
    for (const inc of a.complexObjectPropertyInclusions) {
      for (const p of inc.subObjectProperties) out.push(p);
      out.push(inc.superObjectProperty);
    }
    for (const group of a.disjointObjectProperties) for (const p of group) out.push(p);
    for (const p of a.reflexiveObjectProperties) out.push(p);
    for (const p of a.irreflexiveObjectProperties) out.push(p);
    for (const p of a.asymmetricObjectProperties) out.push(p);
    for (const p of a.objectProperties) out.push(p);
    return out;
  }

  /** Whether a property expression is non-simple. */
  isComplex(propertyExpression) {
    return this.complexKeys.has(keyOf(propertyExpression));
  }

  /**
   * HermiT rewrites `¬R(a,b)` for non-simple R into a pair of concept
   * assertions, because in its design complex roles never appear as edges and
   * so a negative role assertion could never be matched. Under the
   * chain-clause design used here, `R(a,b)` IS derivable in the head of a
   * clause, so the negative fact clashes directly and no rewriting is needed.
   *
   * Kept for pipeline fidelity; returns the replacement index unchanged.
   */
  rewriteNegativeObjectPropertyAssertions(_factory, axioms, replacementIndex) {
    void axioms;
    return replacementIndex;
  }

  /**
   * Port of HermiT's `rewriteAxioms` minus the automaton construction: only
   * the OWL 2 DL simplicity side-conditions remain. Each of these is a genuine
   * OWL 2 DL violation (a non-simple role may not occur in a cardinality
   * restriction, a Self restriction, or an asymmetry / irreflexivity /
   * disjointness axiom), so throwing is the spec-conformant behaviour.
   *
   * @returns {number} the (unchanged) replacement index
   */
  rewriteAxioms(_factory, axioms, firstReplacementIndex) {
    const complex = axioms.complexObjectPropertyExpressions;
    const isComplex = (p) => complex.has(p) || this.isComplex(p);

    for (const p of axioms.asymmetricObjectProperties) {
      if (isComplex(p)) {
        throw new IllegalArgumentException(
          `Non-simple property '${p}' or its inverse appears in asymmetric object property axiom.`);
      }
    }
    for (const p of axioms.irreflexiveObjectProperties) {
      if (isComplex(p)) {
        throw new IllegalArgumentException(
          `Non-simple property '${p}' or its inverse appears in irreflexive object property axiom.`);
      }
    }
    for (const properties of axioms.disjointObjectProperties) {
      for (const p of properties) {
        if (isComplex(p)) {
          throw new IllegalArgumentException(
            `Non-simple property '${p}' or its inverse appears in disjoint properties axiom.`);
        }
      }
    }

    // Cardinality restrictions and Self restrictions require simple roles.
    const T = E.ClassExpressionType;
    for (const inclusion of axioms.conceptInclusions) {
      for (const classExpression of inclusion) {
        const t = E.exprType(classExpression);
        if (t === T.OBJECT_MIN_CARDINALITY
          || t === T.OBJECT_MAX_CARDINALITY
          || t === T.OBJECT_EXACT_CARDINALITY) {
          if (isComplex(classExpression.property)) {
            throw new IllegalArgumentException(
              `Non-simple property '${classExpression.property}' or its inverse appears in the cardinality restriction '${classExpression}'.`);
          }
        } else if (t === T.OBJECT_HAS_SELF) {
          if (isComplex(classExpression.property)) {
            throw new IllegalArgumentException(
              `Non-simple property '${classExpression.property}' or its inverse appears in the Self restriction '${classExpression}'.`);
          }
        }
      }
    }

    return firstReplacementIndex;
  }
}

/** Error type matching HermiT's IllegalArgumentException. */
class IllegalArgumentException extends Error {
  constructor(message) {
    super(message);
    this.name = 'IllegalArgumentException';
  }
}

// ===========================================================================
// Verbatim ports of the automaton-free helpers
// ===========================================================================

/**
 * R ↦ { S : R ⊑ S and S ⊑ R (possibly via inverses) }.
 * Port of HermiT's findEquivalentProperties.
 */
function findEquivalentProperties(simpleObjectPropertyInclusions) {
  const g = new Graph();
  for (const inclusion of simpleObjectPropertyInclusions) {
    const [sub, sup] = inclusion;
    if (!E.exprEquals(sub, sup) && !E.exprEquals(sub, E.inversePropertyOf(sup))) {
      g.addEdge(sub, sup);
    }
  }
  g.transitivelyClose();

  const result = new Map(); // structuralKey -> Set<structuralKey>
  const exprOf = new Map(); // structuralKey -> expression
  for (const n of g.nodes.values()) exprOf.set(keyOf(n.expr), n.expr);

  for (const p of g.getElements()) {
    const pk = keyOf(p);
    const pik = invKeyOf(p);
    const succ = g.getSuccessors(p);
    if (succ.has(pk) || succ.has(pik)) {
      const equiv = new Set();
      for (const sk of succ) {
        if (sk === pk) continue;
        const s = exprOf.get(sk);
        if (!s) continue;
        const sSucc = g.getSuccessors(s);
        if (sSucc.has(pk) || sSucc.has(pik)) equiv.add(sk);
      }
      result.set(pk, equiv);
    }
  }
  return result;
}

/**
 * Properties declared symmetric, i.e. with an inclusion `R ⊑ R⁻` or `R⁻ ⊑ R`.
 * Port of HermiT's findSymmetricProperties.
 */
function findSymmetricProperties(simpleObjectPropertyInclusions) {
  const symmetric = new Set(); // structural keys
  for (const inclusion of simpleObjectPropertyInclusions) {
    const [sub, sup] = inclusion;
    // HermiT: inclusion[1].getInverseProperty().equals(inclusion[0])
    //      || inclusion[1].equals(inclusion[0].getInverseProperty())
    if (E.exprEquals(sub, E.inversePropertyOf(sup)) || E.exprEquals(sup, E.inversePropertyOf(sub))) {
      symmetric.add(keyOf(sub));
      symmetric.add(invKeyOf(sub));
    }
  }
  return symmetric;
}

/**
 * R ↦ { S : `InverseObjectProperties(R,S)` was asserted }, in both directions.
 * Port of HermiT's buildInversePropertiesMap.
 */
function buildInversePropertiesMap(simpleObjectPropertyInclusions) {
  const map = new Map(); // structuralKey -> Set<structuralKey>
  const exprOf = new Map();
  const add = (a, b) => {
    const ka = keyOf(a);
    let set = map.get(ka);
    if (!set) { set = new Set(); map.set(ka, set); }
    set.add(keyOf(b));
    exprOf.set(ka, a);
    exprOf.set(keyOf(b), b);
  };
  for (const inclusion of simpleObjectPropertyInclusions) {
    const [p0, p1] = inclusion;
    if (E.isAnonymousProperty(p1)) {
      // p0 ⊑ q⁻  means  q ⊑ p0⁻  and  p0 ⊑ q⁻
      add(p0, E.inversePropertyOf(p1));
      add(E.inversePropertyOf(p1), p0);
    } else if (E.isAnonymousProperty(p0)) {
      add(p1, E.inversePropertyOf(p0));
      add(E.inversePropertyOf(p0), p1);
    }
  }
  map.exprOf = exprOf;
  return map;
}

/**
 * The sub-property dependency graph, with edges sub → super, plus the
 * regularity side-conditions on chain axioms.
 * Port of HermiT's buildPropertyOrdering.
 */
function buildPropertyOrdering(simpleObjectPropertyInclusions, complexObjectPropertyInclusions, equivalentPropertiesMap) {
  const g = new Graph();

  for (const inclusion of simpleObjectPropertyInclusions) {
    const [sub, sup] = inclusion;
    if (E.exprEquals(sub, sup)) continue;
    if (E.exprEquals(sub, E.inversePropertyOf(sup))) continue;
    const equiv = equivalentPropertiesMap.get(keyOf(sub));
    if (equiv && equiv.has(keyOf(sup))) continue;
    g.addEdge(sub, sup);
  }

  for (const inclusion of complexObjectPropertyInclusions) {
    const sup = inclusion.superObjectProperty;
    const subs = inclusion.subObjectProperties;
    const supKey = keyOf(sup);
    const supEquiv = equivalentPropertiesMap.get(supKey);

    if (subs.length !== 2 && E.exprEquals(sup, subs[0]) && E.exprEquals(sup, subs[subs.length - 1])) {
      throw new IllegalArgumentException('The given property hierarchy is not regular.');
    }

    for (let i = 0; i < subs.length; i++) {
      const sub = subs[i];
      const isInterior = subs.length !== 2 && i > 0 && i < subs.length - 1;
      if (isInterior && (E.exprEquals(sub, sup) || (supEquiv && supEquiv.has(keyOf(sub))))) {
        throw new IllegalArgumentException('The given property hierarchy is not regular.');
      } else if (E.exprEquals(E.inversePropertyOf(sub), sup)) {
        throw new IllegalArgumentException('The given property hierarchy is not regular.');
      } else if (!E.exprEquals(sub, sup)) {
        g.addEdge(sub, sup);
      }
    }
  }
  return g;
}

/**
 * Reject cyclic role hierarchies. Port of HermiT's checkForRegularity: first
 * contract edges between equivalent properties, then close transitively and
 * look for a node that reaches itself or its own inverse.
 */
function checkForRegularity(propertyDependencyGraph, equivalentPropertiesMap) {
  let regularityCheckGraph = propertyDependencyGraph.clone();

  let trimmed = false;
  do {
    trimmed = false;
    const temp = regularityCheckGraph.clone();
    for (const prop of temp.getElements()) {
      const pk = keyOf(prop);
      for (const succProp of temp.getSuccessorElements(prop)) {
        const sk = keyOf(succProp);
        const equiv = equivalentPropertiesMap.get(pk);
        if (equiv && equiv.has(sk)) {
          for (const succSucc of temp.getSuccessorElements(succProp)) {
            if (!E.exprEquals(prop, succSucc)) regularityCheckGraph.addEdge(prop, succSucc);
          }
          trimmed = true;
          regularityCheckGraph.getSuccessors(prop).delete(sk);
        }
      }
    }
  } while (trimmed);

  regularityCheckGraph.transitivelyClose();

  for (const prop of regularityCheckGraph.getElements()) {
    const successors = regularityCheckGraph.getSuccessors(prop);
    if (successors.has(keyOf(prop)) || successors.has(invKeyOf(prop))) {
      throw new IllegalArgumentException(
        `The given property hierarchy is not regular.\nThere is a cyclic dependency involving property ${prop}`);
    }
  }
}

// ===========================================================================
// Simplicity — the OWL 2 definition, computed without automata
// ===========================================================================

/**
 * The structural keys of all non-simple object property expressions.
 *
 * OWL 2 Structural Specification, "Simple Role": a property expression PE is
 * NOT simple iff
 *   (a) PE is a super-property (reflexively) of a property declared transitive,
 *       or of a property occurring as the SUPER of a chain axiom with n ≥ 2; or
 *   (b) PE is a super-property of any property occurring INSIDE such a chain.
 * Inverses inherit non-simplicity in both directions.
 *
 * This is precisely the set HermiT's `findSimpleProperties` recovers from the
 * dependency graph combined with the individual automata.
 *
 * @returns {Set<string>} structural keys of non-simple expressions
 */
function computeComplexKeys(simpleObjectPropertyInclusions, complexObjectPropertyInclusions) {
  // ---- 1. the "has sub-property" relation, closed under inverses ----
  // Edges point super → sub, so that the fixpoint below reads naturally:
  //   R is non-simple  ⇔  R is seeded  ∨  R has a non-simple sub-property.
  const edges = new Map(); // key -> Set<key>
  const exprByKey = new Map();
  const note = (p) => { const k = keyOf(p); if (!exprByKey.has(k)) exprByKey.set(k, p); return k; };
  const addEdge = (superP, subP) => {
    const ks = note(superP);
    const kb = note(subP);
    let s = edges.get(ks);
    if (!s) { s = new Set(); edges.set(ks, s); }
    s.add(kb);
    if (!edges.has(kb)) edges.set(kb, new Set());
  };

  for (const [sub, sup] of simpleObjectPropertyInclusions) {
    if (E.exprEquals(sub, sup)) continue;
    addEdge(sup, sub);
    // R ⊑ S  implies  R⁻ ⊑ S⁻, i.e. S⁻ has sub-property R⁻.
    addEdge(E.inversePropertyOf(sup), E.inversePropertyOf(sub));
  }
  // Every named property is a node, together with its inverse.
  for (const p of [...exprByKey.values()]) note(E.inversePropertyOf(p));

  // ---- 2. seed the non-simple set ----
  const seeds = new Set();
  const seed = (p) => {
    // Non-simplicity is inherited by the inverse in both directions.
    seeds.add(note(p));
    seeds.add(note(E.inversePropertyOf(p)));
  };
  for (const inc of complexObjectPropertyInclusions) {
    const subs = inc.subObjectProperties;
    const sup = inc.superObjectProperty;
    const isTransitivity = subs.length === 2
      && E.exprEquals(subs[0], sup) && E.exprEquals(subs[1], sup);
    if (isTransitivity) {
      seed(sup);
      continue;
    }
    if (subs.length < 2) continue;
    // (a) the super of a chain is non-simple
    seed(sup);
    // (b) every member of the chain is non-simple
    for (const p of subs) seed(p);
  }

  // ---- 3. propagate upwards through the sub-property relation ----
  // R non-simple  ∧  R ⊑ S   ⇒   S non-simple.
  // Memoised DFS over `edges` (super → sub).
  const complex = new Set();
  const visiting = new Set();

  const visit = (k) => {
    if (complex.has(k)) return true;
    if (visiting.has(k)) return false; // cycle guard (regularity is checked separately)
    visiting.add(k);
    let result = seeds.has(k);
    if (!result) {
      const subs = edges.get(k);
      if (subs) {
        for (const s of subs) {
          if (visit(s)) { result = true; break; }
        }
      }
    }
    visiting.delete(k);
    if (result) complex.add(k);
    return result;
  };

  for (const k of edges.keys()) visit(k);
  for (const k of seeds) complex.add(k);

  return complex;
}

module.exports = {
  ObjectPropertyInclusionManager,
  IllegalArgumentException,
  Graph,
  findEquivalentProperties,
  findSymmetricProperties,
  buildInversePropertiesMap,
  buildPropertyOrdering,
  checkForRegularity,
  computeComplexKeys,
};
