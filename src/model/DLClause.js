'use strict';

// ---------------------------------------------------------------------------
// model/DLClause.js — the rule form the whole calculus runs on.
//
// Mirrors org.semanticweb.HermiT.model.DLClause:
//
//     body₁ ∧ … ∧ bodyₘ  →  head₁ ∨ … ∨ headₙ
//
//   n = 0 → firing the clause produces a clash (body unsatisfiable)
//   n = 1 → deterministic (Horn) consequence
//   n > 1 → disjunction: the tableau must branch (GroundDisjunction)
//
// getSafeVersion() enforces DL-safety: every head variable must also occur in
// the body; unsafe head variables get a guarding body atom (Thing / Literal).
// ---------------------------------------------------------------------------

const { Variable, TERM_KIND, createVariable } = require('./Term');
const {
  AtomicConcept,
  AtomicRole,
  AnnotatedEquality,
  AtLeastConcept,
  AtLeastDataRange,
  LiteralDataRange,
  AtomicNegationDataRange,
  DatatypeRestriction,
  InternalDatatype,
  ConstantEnumeration,
  Equality,
  NodeIDLessEqualThan,
  NodeIDsAscendingOrEqual,
  THING,
  LITERAL
} = require('./DLPredicate');
const { createAtom } = require('./Atom');

class DLClause {
  /**
   * @param {Atom[]} headAtoms  disjunction
   * @param {Atom[]} bodyAtoms  conjunction
   */
  constructor(headAtoms, bodyAtoms) {
    this.headAtoms = headAtoms;
    this.bodyAtoms = bodyAtoms;
  }

  getHeadLength() { return this.headAtoms.length; }
  getBodyLength() { return this.bodyAtoms.length; }
  getHeadAtom(i) { return this.headAtoms[i]; }
  getBodyAtom(i) { return this.bodyAtoms[i]; }

  /**
   * DL-safety: add a guarding body atom for every head variable that does not
   * occur in the body. `safeMakingPredicate` is AtomicConcept(owl:Thing) for
   * object-side clauses and LiteralDataRange(rdfs:Literal) for data-side ones.
   */
  getSafeVersion(safeMakingPredicate) {
    const unsafe = new Set();
    for (const atom of this.headAtoms) {
      for (let i = 0; i < atom.getArity(); i++) {
        const v = atom.getArgumentVariable(i);
        if (v) unsafe.add(v);
      }
    }
    for (const atom of this.bodyAtoms) {
      for (let i = 0; i < atom.getArity(); i++) {
        const v = atom.getArgumentVariable(i);
        if (v) unsafe.delete(v);
      }
    }
    if (this.headAtoms.length === 0 && this.bodyAtoms.length === 0) {
      unsafe.add(createVariable('X'));
    }
    if (unsafe.size === 0) return this;
    const newBody = this.bodyAtoms.slice();
    for (const v of unsafe) newBody.push(createAtom(safeMakingPredicate, v));
    return createDLClause(this.headAtoms, newBody);
  }

  // ---- recognisers (used by classification & the tableau) -------------------

  /** A(X) → B(X) — the cheap "told subsumer" form. */
  isAtomicConceptInclusion() {
    if (this.bodyAtoms.length === 1 && this.headAtoms.length === 1) {
      const body = this.bodyAtoms[0];
      const head = this.headAtoms[0];
      if (body.getArity() === 1 && head.getArity() === 1
        && body.dlPredicate instanceof AtomicConcept
        && head.dlPredicate instanceof AtomicConcept) {
        const arg = body.getArgument(0);
        return arg.kind === TERM_KIND.VARIABLE && arg === head.getArgument(0);
      }
    }
    return false;
  }

  /** R(X,Y) → S(X,Y). */
  isAtomicRoleInclusion() {
    if (this.bodyAtoms.length === 1 && this.headAtoms.length === 1) {
      const body = this.bodyAtoms[0];
      const head = this.headAtoms[0];
      if (body.getArity() === 2 && head.getArity() === 2
        && body.dlPredicate instanceof AtomicRole
        && head.dlPredicate instanceof AtomicRole) {
        const a0 = body.getArgument(0), a1 = body.getArgument(1);
        return a0.kind === TERM_KIND.VARIABLE && a1.kind === TERM_KIND.VARIABLE
          && a0 !== a1
          && a0 === head.getArgument(0) && a1 === head.getArgument(1);
      }
    }
    return false;
  }

  /** R(X,Y) → S(Y,X). */
  isAtomicRoleInverseInclusion() {
    if (this.bodyAtoms.length === 1 && this.headAtoms.length === 1) {
      const body = this.bodyAtoms[0];
      const head = this.headAtoms[0];
      if (body.getArity() === 2 && head.getArity() === 2
        && body.dlPredicate instanceof AtomicRole
        && head.dlPredicate instanceof AtomicRole) {
        const a0 = body.getArgument(0), a1 = body.getArgument(1);
        return a0.kind === TERM_KIND.VARIABLE && a1.kind === TERM_KIND.VARIABLE
          && a0 !== a1
          && a0 === head.getArgument(1) && a1 === head.getArgument(0);
      }
    }
    return false;
  }

  /** R(X,Y₁) ∧ R(X,Y₂) → Y₁ ≈[annotated] Y₂  (functionality). */
  isFunctionalityAxiom() {
    return this._isCardinalityAxiom(0);
  }

  /** R(Y₁,X) ∧ R(Y₂,X) → Y₁ ≈[annotated] Y₂  (inverse functionality). */
  isInverseFunctionalityAxiom() {
    return this._isCardinalityAxiom(1);
  }

  _isCardinalityAxiom(sharedArgIndex) {
    if (this.bodyAtoms.length !== 2 || this.headAtoms.length !== 1) return false;
    const role = this.bodyAtoms[0].dlPredicate;
    if (!(role instanceof AtomicRole)) return false;
    if (this.bodyAtoms[1].dlPredicate !== role) return false;
    if (!(this.headAtoms[0].dlPredicate instanceof AnnotatedEquality)) return false;
    const x1 = this.bodyAtoms[0].getArgumentVariable(sharedArgIndex);
    const x2 = this.bodyAtoms[1].getArgumentVariable(sharedArgIndex);
    if (!x1 || x1 !== x2) return false;
    const other = 1 - sharedArgIndex;
    const y1 = this.bodyAtoms[0].getArgumentVariable(other);
    const y2 = this.bodyAtoms[1].getArgumentVariable(other);
    const h1 = this.headAtoms[0].getArgumentVariable(0);
    const h2 = this.headAtoms[0].getArgumentVariable(1);
    return y1 && y2 && y1 !== y2 && h1 && h2
      && ((y1 === h1 && y2 === h2) || (y1 === h2 && y2 === h1));
  }

  /** True if every head atom is a data-range membership test (no object side). */
  isDataRangeClause() {
    for (const atom of this.headAtoms) {
      if (!isDataRangePredicate(atom.dlPredicate)) return false;
    }
    return this.headAtoms.length > 0;
  }

  toString() {
    const head = this.headAtoms.map(String).join(' v ');
    const body = this.bodyAtoms.map(String).join(' ^ ');
    return `${head} :- ${body}`;
  }
}

function isDataRangePredicate(p) {
  return p instanceof LiteralDataRange
    || p instanceof AtomicNegationDataRange
    || p instanceof DatatypeRestriction
    || p instanceof InternalDatatype
    || p instanceof ConstantEnumeration;
}

// ---- interning --------------------------------------------------------------

const _clauses = new Map();

function clauseKey(headAtoms, bodyAtoms) {
  return `${headAtoms.map(a => a.toString()).join('v')}:-${bodyAtoms.map(a => a.toString()).join('^')}`;
}

/** Interned DLClause factory (mirrors DLClause.create). */
function createDLClause(headAtoms, bodyAtoms) {
  const key = clauseKey(headAtoms, bodyAtoms);
  let c = _clauses.get(key);
  if (!c) {
    c = new DLClause(headAtoms, bodyAtoms);
    _clauses.set(key, c);
  }
  return c;
}

module.exports = { DLClause, createDLClause, isDataRangePredicate };
