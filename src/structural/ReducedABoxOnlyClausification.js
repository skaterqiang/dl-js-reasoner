'use strict';

// ---------------------------------------------------------------------------
// structural/ReducedABoxOnlyClausification.js
//
// Port of org.semanticweb.HermiT.structural.ReducedABoxOnlyClausification.
//
// A *restricted* clausifier used only by `Reasoner.flush()` when every pending
// change is an ABox assertion (or a declaration of an entity that already
// exists). In that situation the TBox/RBox clauses are untouched, so instead of
// re-running the whole normalization + clausification pipeline we translate the
// changed axioms straight into ground facts and splice them into the existing
// `DLOntology`.
//
// What it can translate — exactly the shapes that become ground facts:
//
//   SameIndividual(a,b,…)            → =(a,b) ∧ =(b,…)          [positive]
//   DifferentIndividuals(a,b,…)      → !=(a,b) ∧ …               [positive]
//   ClassAssertion(A, a)             → A(a)                      [positive]
//   ClassAssertion(Self(R), a)       → R(a,a)                    [positive]
//   ClassAssertion(∃R.{b}, a)        → R(a,b)                    [positive]
//   ClassAssertion(¬…, a)            → the same, negated         [negative]
//   ObjectPropertyAssertion(R,a,b)   → R(a,b)                    [positive]
//   NegativeObjectPropertyAssertion  → R(a,b)                    [negative]
//   DataPropertyAssertion(dp,a,"v")  → dp(a,"v")                 [positive]
//   NegativeDataPropertyAssertion    → dp(a,"v")                 [negative]
//
// Every class/property mentioned must ALREADY occur in the loaded ontology's
// signature: a fresh name would need a new clause (or at least a new signature
// entry that classification enumerates), which this path cannot produce. The
// caller (`Reasoner.canProcessPendingChangesIncrementally`) enforces that, and
// this class throws if it is violated anyway — a fresh name here is an internal
// error, not a user error.
//
// == Divergences from HermiT ==
//   • Literal → Constant conversion is delegated to `DataRangeConverter` (the
//     same helper the full clausifier uses) rather than reimplemented, so
//     `ignoreUnsupportedDatatypes` / `warningMonitor` behave identically on
//     both paths.
//   • `ClassAssertion(ObjectHasValue)` is accepted here (as in HermiT) even
//     though the full path's `FactClausifier` never sees it — `OWLNormalization`
//     rewrites it into an `ObjectPropertyAssertion` first. The incremental path
//     receives RAW axioms, so it must handle the un-normalized shape itself.
//   • `ClassAssertion(DataHasValue)` and `ClassAssertion(∃dp.{v})` are accepted
//     too, and rewritten to a data-property fact exactly as
//     `OWLNormalization._visitAxiom` does. HermiT REJECTS both here (they are
//     not `OWLObjectHasValue`), so such a change forces it to reload the whole
//     ontology. Accepting them is sound — it is the same rewrite the full path
//     performs — and strictly widens what can be flushed incrementally.
// ---------------------------------------------------------------------------

const E = require('../owl/OWLExpressions');
const P = require('../model/DLPredicate');
const { createAtom } = require('../model/Atom');
const { DataRangeConverter, getRoleAtom, getDataRoleAtom, getIndividual } = require('./OWLClausification');

const T = E.ClassExpressionType;
const AT = E.AxiomType;

function internalError(what) {
  return new Error(`Internal error: ${what}`);
}

/** The IRI string of an OWL entity (`.iri` first, `getIRI()` as a fallback). */
function entityIRI(entity) {
  return E.iriString(entity.iri !== undefined ? entity.iri : entity.getIRI());
}

class ReducedABoxOnlyClausification {
  /**
   * @param {object} options
   * @param {Set<object>} options.allAtomicConcepts  the loaded ontology's concept signature
   * @param {Set<object>} options.allAtomicObjectRoles
   * @param {Set<object>} options.allAtomicDataRoles
   * @param {Set<string>} [options.definedDatatypeIRIs]
   * @param {Set<object>} [options.allUnknownDatatypeRestrictions]
   * @param {boolean} [options.ignoreUnsupportedDatatypes]
   * @param {function(string):void} [options.warningMonitor]
   */
  constructor(options = {}) {
    this.allAtomicConcepts = options.allAtomicConcepts || new Set();
    this.allAtomicObjectRoles = options.allAtomicObjectRoles || new Set();
    this.allAtomicDataRoles = options.allAtomicDataRoles || new Set();

    this.dataRangeConverter = new DataRangeConverter({
      warningMonitor: options.warningMonitor || null,
      definedDatatypeIRIs: options.definedDatatypeIRIs || new Set(),
      allUnknownDatatypeRestrictions: options.allUnknownDatatypeRestrictions || new Set(),
      ignoreUnsupportedDatatypes: !!options.ignoreUnsupportedDatatypes
    });

    /** @type {Set<object>} facts produced by the most recent `clausify` call */
    this.positiveFacts = new Set();
    /** @type {Set<object>} */
    this.negativeFacts = new Set();
    /** @type {Set<object>} every Individual term seen (accumulates across calls) */
    this.allIndividuals = new Set();
  }

  /**
   * Translate `axioms` into ground facts. The fact sets are CLEARED first, so
   * the result describes exactly the axioms passed in — which is what lets the
   * caller `add` them for an addition and `remove` them for a removal.
   *
   * @param {Iterable<object>} axioms
   */
  clausify(axioms) {
    this.positiveFacts.clear();
    this.negativeFacts.clear();
    for (const axiom of axioms || []) this._visit(axiom);
    return this;
  }

  getPositiveFacts() { return this.positiveFacts; }
  getNegativeFacts() { return this.negativeFacts; }
  getAllIndividuals() { return this.allIndividuals; }

  // ---- atom builders (signature-checked) ------------------------------------

  /** `A(term)` — throws if `A` is not in the loaded concept signature. */
  _conceptAtom(owlClass, term) {
    const concept = P.internAtomicConcept(entityIRI(owlClass));
    if (!this.allAtomicConcepts.has(concept)) {
      throw internalError(
        'fresh classes in class assertions are not compatible with incremental ABox loading!');
    }
    return createAtom(concept, term);
  }

  /** `R(first, second)` for an object property expression (inverses swap args). */
  _objectRoleAtom(objectProperty, first, second) {
    const atom = getRoleAtom(objectProperty, first, second);
    if (!this.allAtomicObjectRoles.has(atom.dlPredicate)) {
      throw internalError(
        'fresh properties in property assertions are not compatible with incremental ABox loading!');
    }
    return atom;
  }

  /** `dp(first, second)` for a data property. */
  _dataRoleAtom(dataProperty, first, second) {
    const atom = getDataRoleAtom(dataProperty, first, second);
    if (!this.allAtomicDataRoles.has(atom.dlPredicate)) {
      throw internalError(
        'fresh properties in property assertions are not compatible with incremental ABox loading!');
    }
    return atom;
  }

  /** OWLIndividual → Individual term, recorded in `allIndividuals`. */
  _individual(individual) {
    const ind = getIndividual(individual);
    this.allIndividuals.add(ind);
    return ind;
  }

  // ---- axiom dispatch --------------------------------------------------------

  _visit(axiom) {
    switch (axiom.axiomType) {
      case AT.SAME_INDIVIDUAL: {
        const individuals = E.operandsOf(axiom).length > 0 ? E.operandsOf(axiom) : axiom.individuals;
        for (let i = 0; i < individuals.length - 1; i++) {
          this.positiveFacts.add(createAtom(
            P.EQUALITY, this._individual(individuals[i]), this._individual(individuals[i + 1])));
        }
        return;
      }
      case AT.DIFFERENT_INDIVIDUALS: {
        const individuals = E.operandsOf(axiom).length > 0 ? E.operandsOf(axiom) : axiom.individuals;
        for (let i = 0; i < individuals.length; i++) {
          for (let j = i + 1; j < individuals.length; j++) {
            this.positiveFacts.add(createAtom(
              P.INEQUALITY, this._individual(individuals[i]), this._individual(individuals[j])));
          }
        }
        return;
      }
      case AT.CLASS_ASSERTION:
        this._visitClassAssertion(axiom);
        return;
      case AT.OBJECT_PROPERTY_ASSERTION:
        this.positiveFacts.add(this._objectRoleAtom(
          axiom.property, this._individual(axiom.subject), this._individual(axiom.object)));
        return;
      case AT.NEGATIVE_OBJECT_PROPERTY_ASSERTION:
        this.negativeFacts.add(this._objectRoleAtom(
          axiom.property, this._individual(axiom.subject), this._individual(axiom.object)));
        return;
      case AT.DATA_PROPERTY_ASSERTION:
        this.positiveFacts.add(this._dataRoleAtom(
          axiom.property,
          this._individual(axiom.subject),
          this.dataRangeConverter.convertLiteral(E.assertionLiteral(axiom))));
        return;
      case AT.NEGATIVE_DATA_PROPERTY_ASSERTION:
        this.negativeFacts.add(this._dataRoleAtom(
          axiom.property,
          this._individual(axiom.subject),
          this.dataRangeConverter.convertLiteral(E.assertionLiteral(axiom))));
        return;
      default:
        throw internalError(`invalid axiom type for ABox updates (${axiom.axiomType}).`);
    }
  }

  /**
   * `ClassAssertion(D, a)`. `D` must be one of the shapes that normalize to a
   * single ground atom; anything else needs a clause and is rejected.
   */
  _visitClassAssertion(axiom) {
    const description = axiom.classExpression;
    const individual = this._individual(axiom.individual);
    const positive = this._classAssertionAtom(description, individual);
    if (positive !== null) this.positiveFacts.add(positive);
    else this.negativeFacts.add(this._negatedClassAssertionAtom(description, individual));
  }

  /** @returns {object|null} the positive atom, or null when `D` is a negation */
  _classAssertionAtom(description, individual) {
    const t = E.exprType(description);
    if (t === T.OWL_CLASS) return this._conceptAtom(description, individual);
    if (t === T.OBJECT_HAS_SELF) {
      return this._objectRoleAtom(description.property, individual, individual);
    }
    if (t === T.OBJECT_HAS_VALUE) {
      return this._objectRoleAtom(
        description.property, individual, this._individual(description.filler));
    }
    if (t === T.DATA_HAS_VALUE) {
      return this._dataRoleAtom(
        description.property,
        individual,
        this.dataRangeConverter.convertLiteral(
          E.literal(description.value !== undefined ? description.value : description.filler)));
    }
    if (t === T.DATA_SOME_VALUES_FROM) {
      const filler = description.filler;
      if (E.exprType(filler) === T.DATA_ONE_OF && E.operandsOf(filler).length === 1) {
        return this._dataRoleAtom(
          description.property,
          individual,
          this.dataRangeConverter.convertLiteral(E.literal(E.operandsOf(filler)[0])));
      }
    }
    if (t === T.OBJECT_COMPLEMENT_OF) return null;
    throw internalError('invalid normal form for ABox updates.');
  }

  /** The atom for `¬D`, i.e. the negative fact of `ClassAssertion(¬D, a)`. */
  _negatedClassAssertionAtom(description, individual) {
    const operand = E.operandOf(description);
    const t = E.exprType(operand);
    if (t === T.OWL_CLASS) return this._conceptAtom(operand, individual);
    if (t === T.OBJECT_HAS_SELF) return this._objectRoleAtom(operand.property, individual, individual);
    if (t === T.OBJECT_HAS_VALUE) {
      return this._objectRoleAtom(operand.property, individual, this._individual(operand.filler));
    }
    throw internalError('invalid normal form for ABox updates (class assertion with negated class).');
  }
}

/**
 * The axiom types this clausifier can translate — i.e. HermiT's
 * `OWLIndividualAxiom`. Exported so `Reasoner.canProcessPendingChangesIncrementally`
 * and this class can never disagree about what is an ABox axiom.
 */
const INDIVIDUAL_AXIOM_TYPES = Object.freeze(new Set([
  AT.SAME_INDIVIDUAL,
  AT.DIFFERENT_INDIVIDUALS,
  AT.CLASS_ASSERTION,
  AT.OBJECT_PROPERTY_ASSERTION,
  AT.NEGATIVE_OBJECT_PROPERTY_ASSERTION,
  AT.DATA_PROPERTY_ASSERTION,
  AT.NEGATIVE_DATA_PROPERTY_ASSERTION
]));

/**
 * The class-expression shapes a `ClassAssertion` may carry and still be
 * translatable to a single ground fact. Mirrors the positive branches of
 * `_classAssertionAtom`; `OBJECT_COMPLEMENT_OF` wraps any of them and is
 * handled separately by `_negatedClassAssertionAtom`.
 *
 * Used by `Reasoner.canProcessPendingChangesIncrementally`, so the gate and the
 * translator can never disagree about what is acceptable.
 */
const INCREMENTAL_CLASS_EXPRESSION_TYPES = Object.freeze(new Set([
  T.OWL_CLASS,
  T.OBJECT_HAS_SELF,
  T.OBJECT_HAS_VALUE,
  T.DATA_HAS_VALUE,
  T.DATA_SOME_VALUES_FROM
]));

module.exports = {
  ReducedABoxOnlyClausification,
  INDIVIDUAL_AXIOM_TYPES,
  INCREMENTAL_CLASS_EXPRESSION_TYPES
};
