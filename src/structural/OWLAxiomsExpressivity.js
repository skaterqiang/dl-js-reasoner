'use strict';

// ---------------------------------------------------------------------------
// structural/OWLAxiomsExpressivity.js
//
// Port of org.semanticweb.HermiT.structural.OWLAxiomsExpressivity.
//
// Scans a normalized `OWLAxioms` set and records which DL features it uses.
// The reasoner consults these flags to pick cheaper algorithms:
//
//   hasAtMostRestrictions  →  ≤n / =n restrictions occur; needed to decide
//                             whether the "anywhere" blocking strategy can be
//                             replaced by the cheaper "pairwise direct" one.
//   hasInverseRoles         →  R⁻ occurs anywhere; without inverses the
//                             calculus never needs to consider inverse edges,
//                             so blocking and existential expansion simplify.
//   hasNominals             →  {a} / ObjectHasValue occurs; triggers the
//                             nominal-introduction and individual-reuse rules.
//   hasDatatypes            →  concrete domain in use; enables the datatype
//                             manager (and its Hall's-condition checks).
//   hasSWRLRules            →  rules survived normalization; the clausifier
//                             must emit disjunctive rule clauses.
//
// Everything is duck-typed: the scan works on protege-js objects as well as on
// the interned expressions from `src/owl/OWLExpressions.js`.
// ---------------------------------------------------------------------------

const E = require('../owl/OWLExpressions');

const T = E.ClassExpressionType;

class OWLAxiomsExpressivity {
  /** @param {import('./OWLAxioms').OWLAxioms} axioms */
  constructor(axioms) {
    /** ≤n / =n object or data cardinality restrictions occur. */
    this.hasAtMostRestrictions = false;
    /** An inverse role R⁻ occurs. */
    this.hasInverseRoles = false;
    /** A nominal ({a} or ObjectHasValue) occurs. */
    this.hasNominals = false;
    /** The concrete domain is used at all. */
    this.hasDatatypes = false;
    /** Normalized SWRL rules are present. */
    this.hasSWRLRules = false;

    if (axioms) this.scan(axioms);
  }

  /**
   * Scan a normalized axiom set. Safe to call repeatedly (e.g. after
   * `ObjectPropertyInclusionManager.rewriteAxioms` has added clauses).
   */
  scan(axioms) {
    // ---- concept inclusions: each entry is a disjunction (clause head) ----
    for (const disjunction of axioms.conceptInclusions) {
      for (const description of disjunction) this.visitDescription(description);
    }

    // ---- object property inclusions ----
    for (const pair of axioms.simpleObjectPropertyInclusions) {
      this.visitProperty(pair[0]);
      this.visitProperty(pair[1]);
    }
    for (const inclusion of axioms.complexObjectPropertyInclusions) {
      for (const sub of inclusion.subObjectProperties) this.visitProperty(sub);
      this.visitProperty(inclusion.superObjectProperty);
    }
    for (const group of axioms.disjointObjectProperties) {
      for (const p of group) this.visitProperty(p);
    }
    for (const p of axioms.reflexiveObjectProperties) this.visitProperty(p);
    for (const p of axioms.irreflexiveObjectProperties) this.visitProperty(p);
    for (const p of axioms.asymmetricObjectProperties) this.visitProperty(p);

    // ---- data properties ----
    // HermiT sets hasDatatypes if any of these collections is non-empty: a
    // declared data property alone already means the concrete domain matters.
    if (axioms.dataProperties.size > 0
      || axioms.disjointDataProperties.length > 0
      || axioms.dataPropertyInclusions.length > 0
      || axioms.dataRangeInclusions.length > 0
      || axioms.definedDatatypesIRIs.size > 0) {
      this.hasDatatypes = true;
    }

    // ---- facts ----
    for (const fact of axioms.facts) this.visitFact(fact);

    // ---- keys ----
    // A key axiom is only satisfiable-checkable with the concrete domain and
    // with equality reasoning, so treat it like a datatype use.
    if (axioms.hasKeys.length > 0) {
      this.hasDatatypes = true;
      for (const key of axioms.hasKeys) {
        for (const p of key.propertyExpressions || []) {
          if (E.isDataProperty(p)) continue;
          this.visitProperty(p);
        }
      }
    }

    // ---- rules ----
    if (axioms.rules.length > 0) this.hasSWRLRules = true;

    return this;
  }

  /** An anonymous property expression means an inverse role is in play. */
  visitProperty(propertyExpression) {
    if (E.isAnonymousProperty(propertyExpression)) this.hasInverseRoles = true;
  }

  visitDescription(description) {
    switch (E.exprType(description)) {
      case T.OWL_CLASS:
      case T.DATATYPE:
        return;

      case T.OBJECT_COMPLEMENT_OF:
      case T.DATA_COMPLEMENT_OF:
        this.visitDescription(E.operandOf(description));
        return;

      case T.OBJECT_INTERSECTION_OF:
      case T.OBJECT_UNION_OF:
      case T.DATA_INTERSECTION_OF:
      case T.DATA_UNION_OF:
        for (const operand of E.operandsOf(description)) this.visitDescription(operand);
        return;

      case T.OBJECT_ONE_OF:
        this.hasNominals = true;
        return;

      case T.OBJECT_SOME_VALUES_FROM:
        this.visitProperty(description.property);
        this.visitDescription(description.filler);
        return;

      case T.OBJECT_HAS_VALUE:
        this.hasNominals = true;
        this.visitProperty(description.property);
        return;

      case T.OBJECT_HAS_SELF:
        this.visitProperty(description.property);
        return;

      case T.OBJECT_ALL_VALUES_FROM:
        this.visitProperty(description.property);
        this.visitDescription(description.filler);
        return;

      case T.OBJECT_MIN_CARDINALITY:
        this.visitProperty(description.property);
        this.visitDescription(E.cardinalityFiller(description, false));
        return;

      case T.OBJECT_MAX_CARDINALITY:
      case T.OBJECT_EXACT_CARDINALITY:
        this.hasAtMostRestrictions = true;
        this.visitProperty(description.property);
        this.visitDescription(E.cardinalityFiller(description, false));
        return;

      // ---- concrete domain ----
      case T.DATA_SOME_VALUES_FROM:
      case T.DATA_ALL_VALUES_FROM:
      case T.DATA_HAS_VALUE:
      case T.DATA_MIN_CARDINALITY:
        this.hasDatatypes = true;
        return;

      case T.DATA_MAX_CARDINALITY:
      case T.DATA_EXACT_CARDINALITY:
        this.hasDatatypes = true;
        this.hasAtMostRestrictions = true;
        return;

      case T.DATA_ONE_OF:
      case T.DATATYPE_RESTRICTION:
        this.hasDatatypes = true;
        return;

      default:
        return;
    }
  }

  visitFact(fact) {
    switch (fact.axiomType) {
      case E.AxiomType.CLASS_ASSERTION:
        this.visitDescription(fact.classExpression);
        return;
      case E.AxiomType.OBJECT_PROPERTY_ASSERTION:
      case E.AxiomType.NEGATIVE_OBJECT_PROPERTY_ASSERTION:
        this.visitProperty(fact.property);
        return;
      case E.AxiomType.DATA_PROPERTY_ASSERTION:
      case E.AxiomType.NEGATIVE_DATA_PROPERTY_ASSERTION:
        this.hasDatatypes = true;
        return;
      default:
        return;
    }
  }

  /** A one-line summary, handy in logs and error messages. */
  toString() {
    const flags = [];
    if (this.hasAtMostRestrictions) flags.push('atMost');
    if (this.hasInverseRoles) flags.push('inverseRoles');
    if (this.hasNominals) flags.push('nominals');
    if (this.hasDatatypes) flags.push('datatypes');
    if (this.hasSWRLRules) flags.push('rules');
    return `Expressivity{${flags.join(',')}}`;
  }
}

module.exports = { OWLAxiomsExpressivity };
