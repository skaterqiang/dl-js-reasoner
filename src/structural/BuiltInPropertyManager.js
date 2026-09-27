'use strict';

// ---------------------------------------------------------------------------
// structural/BuiltInPropertyManager.js
//
// Port of org.semanticweb.HermiT.structural.BuiltInPropertyManager.
//
// owl:topObjectProperty / owl:bottomObjectProperty / owl:topDataProperty /
// owl:bottomDataProperty have no axioms in an ontology — their semantics come
// from the OWL 2 specification. HermiT injects equivalent axioms *only when the
// property is actually used*, so that ordinary ontologies pay nothing for them.
//
// The injected axioms are:
//   topObjectProperty    Transitive(topObjectProperty)
//                        topObjectProperty ⊑ topObjectProperty⁻      (symmetric)
//                        ⊤ ⊑ ∃topObjectProperty.{internal:nam#topIndividual}
//   bottomObjectProperty ⊤ ⊑ ∀bottomObjectProperty.⊥
//   topDataProperty      ⊤ ⊑ ∃topDataProperty.{"internal:constant"^^internal:anonymous-constants}
//   bottomDataProperty   ⊤ ⊑ ∀bottomDataProperty.¬rdfs:Literal
// ---------------------------------------------------------------------------

const E = require('../owl/OWLExpressions');
const { ComplexObjectPropertyInclusion } = require('./OWLAxioms');

const IRI_TOP_INDIVIDUAL = 'internal:nam#topIndividual';
const IRI_ANONYMOUS_CONSTANTS_DATATYPE = 'internal:anonymous-constants';
const IRI_ANONYMOUS_CONSTANT = 'internal:constant';

class BuiltInPropertyManager {
  constructor() {
    this.topObjectProperty = E.objectProperty(E.IRI_TOP_OBJECT_PROPERTY);
    this.bottomObjectProperty = E.objectProperty(E.IRI_BOTTOM_OBJECT_PROPERTY);
    this.topDataProperty = E.dataProperty(E.IRI_TOP_DATA_PROPERTY);
    this.bottomDataProperty = E.dataProperty(E.IRI_BOTTOM_DATA_PROPERTY);
  }

  /**
   * @param {import('./OWLAxioms').OWLAxioms} axioms
   * @param {{skipTopObjectProperty?:boolean, skipBottomObjectProperty?:boolean,
   *          skipTopDataProperty?:boolean, skipBottomDataProperty?:boolean}} [opts]
   */
  axiomatizeBuiltInPropertiesAsNeeded(axioms, opts = {}) {
    const checker = new Checker(axioms);
    if (checker.usesTopObjectProperty && !opts.skipTopObjectProperty) {
      this.axiomatizeTopObjectProperty(axioms);
    }
    if (checker.usesBottomObjectProperty && !opts.skipBottomObjectProperty) {
      this.axiomatizeBottomObjectProperty(axioms);
    }
    if (checker.usesTopDataProperty && !opts.skipTopDataProperty) {
      this.axiomatizeTopDataProperty(axioms);
    }
    if (checker.usesBottomDataProperty && !opts.skipBottomDataProperty) {
      this.axiomatizeBottomDataProperty(axioms);
    }
    return checker;
  }

  axiomatizeTopObjectProperty(axioms) {
    const top = this.topObjectProperty;
    // TransitiveObjectProperty(owl:topObjectProperty)
    axioms.complexObjectPropertyInclusions.push(new ComplexObjectPropertyInclusion(top));
    // SymmetricObjectProperty(owl:topObjectProperty)
    axioms.simpleObjectPropertyInclusions.push([top, E.inversePropertyOf(top)]);
    // ⊤ ⊑ ∃topObjectProperty.{internal:nam#topIndividual}
    const individual = E.namedIndividual(IRI_TOP_INDIVIDUAL);
    const oneOf = E.objectOneOf([individual]);
    const hasTop = E.objectSomeValuesFrom(top, oneOf);
    axioms.conceptInclusions.push([hasTop]);
    axioms.namedIndividuals.add(individual);
  }

  axiomatizeBottomObjectProperty(axioms) {
    // ⊤ ⊑ ∀bottomObjectProperty.⊥
    axioms.conceptInclusions.push([
      E.objectAllValuesFrom(this.bottomObjectProperty, E.owlNothing())
    ]);
  }

  axiomatizeTopDataProperty(axioms) {
    // ⊤ ⊑ ∃topDataProperty.{"internal:constant"^^internal:anonymous-constants}
    const dt = E.datatype(IRI_ANONYMOUS_CONSTANTS_DATATYPE);
    const constant = E.literal(IRI_ANONYMOUS_CONSTANT, dt);
    const oneOf = E.dataOneOf([constant]);
    const hasTop = E.dataSomeValuesFrom(this.topDataProperty, oneOf);
    axioms.conceptInclusions.push([hasTop]);
  }

  axiomatizeBottomDataProperty(axioms) {
    // ⊤ ⊑ ∀bottomDataProperty.¬rdfs:Literal
    axioms.conceptInclusions.push([
      E.dataAllValuesFrom(this.bottomDataProperty, E.dataComplementOf(E.topDatatype()))
    ]);
  }
}

// ===========================================================================
// Checker — does the normalized axiom set mention any built-in property?
// ===========================================================================

class Checker {
  constructor(axioms) {
    this.usesTopObjectProperty = false;
    this.usesBottomObjectProperty = false;
    this.usesTopDataProperty = false;
    this.usesBottomDataProperty = false;

    for (const inclusion of axioms.conceptInclusions) {
      for (const description of inclusion) this.visitDescription(description);
    }
    for (const inclusion of axioms.simpleObjectPropertyInclusions) {
      this.visitObjectProperty(inclusion[0]);
      this.visitObjectProperty(inclusion[1]);
    }
    for (const inclusion of axioms.complexObjectPropertyInclusions) {
      for (const sub of inclusion.subObjectProperties) this.visitObjectProperty(sub);
      this.visitObjectProperty(inclusion.superObjectProperty);
    }
    for (const disjoint of axioms.disjointObjectProperties) {
      for (const p of disjoint) this.visitObjectProperty(p);
    }
    for (const p of axioms.reflexiveObjectProperties) this.visitObjectProperty(p);
    for (const p of axioms.irreflexiveObjectProperties) this.visitObjectProperty(p);
    for (const p of axioms.asymmetricObjectProperties) this.visitObjectProperty(p);
    for (const inclusion of axioms.dataPropertyInclusions) {
      this.visitDataProperty(inclusion[0]);
      this.visitDataProperty(inclusion[1]);
    }
    for (const disjoint of axioms.disjointDataProperties) {
      for (const p of disjoint) this.visitDataProperty(p);
    }
    for (const fact of axioms.facts) this.visitFact(fact);
  }

  visitObjectProperty(p) {
    if (!p) return;
    const named = E.namedPropertyOf(p);
    const iri = E.iriString(named.iri || (named.getIRI && named.getIRI()));
    if (iri === E.IRI_TOP_OBJECT_PROPERTY) this.usesTopObjectProperty = true;
    else if (iri === E.IRI_BOTTOM_OBJECT_PROPERTY) this.usesBottomObjectProperty = true;
  }

  visitDataProperty(p) {
    if (!p) return;
    const iri = E.iriString(p.iri || (p.getIRI && p.getIRI()));
    if (iri === E.IRI_TOP_DATA_PROPERTY) this.usesTopDataProperty = true;
    else if (iri === E.IRI_BOTTOM_DATA_PROPERTY) this.usesBottomDataProperty = true;
  }

  visitDescription(d) {
    if (!d) return;
    switch (E.exprType(d)) {
      case E.ClassExpressionType.OWL_CLASS:
      case E.ClassExpressionType.DATATYPE:
      case E.ClassExpressionType.OBJECT_ONE_OF:
        return;
      case E.ClassExpressionType.OBJECT_COMPLEMENT_OF:
      case E.ClassExpressionType.DATA_COMPLEMENT_OF:
        this.visitDescription(E.operandOf(d));
        return;
      case E.ClassExpressionType.OBJECT_INTERSECTION_OF:
      case E.ClassExpressionType.OBJECT_UNION_OF:
      case E.ClassExpressionType.DATA_INTERSECTION_OF:
      case E.ClassExpressionType.DATA_UNION_OF:
        for (const op of E.operandsOf(d)) this.visitDescription(op);
        return;
      case E.ClassExpressionType.OBJECT_SOME_VALUES_FROM:
        this.visitObjectProperty(d.property);
        this.visitDescription(d.filler);
        return;
      case E.ClassExpressionType.OBJECT_ALL_VALUES_FROM:
        this.visitObjectProperty(d.property);
        this.visitDescription(d.filler);
        return;
      case E.ClassExpressionType.OBJECT_HAS_VALUE:
        this.visitObjectProperty(d.property);
        return;
      case E.ClassExpressionType.OBJECT_HAS_SELF:
        this.visitObjectProperty(d.property);
        return;
      case E.ClassExpressionType.OBJECT_MIN_CARDINALITY:
      case E.ClassExpressionType.OBJECT_MAX_CARDINALITY:
      case E.ClassExpressionType.OBJECT_EXACT_CARDINALITY:
        this.visitObjectProperty(d.property);
        this.visitDescription(d.filler);
        return;
      case E.ClassExpressionType.DATA_SOME_VALUES_FROM:
        this.visitDataProperty(d.property);
        return;
      case E.ClassExpressionType.DATA_ALL_VALUES_FROM:
        this.visitDataProperty(d.property);
        return;
      case E.ClassExpressionType.DATA_HAS_VALUE:
        this.visitDataProperty(d.property);
        return;
      case E.ClassExpressionType.DATA_MIN_CARDINALITY:
      case E.ClassExpressionType.DATA_MAX_CARDINALITY:
      case E.ClassExpressionType.DATA_EXACT_CARDINALITY:
        this.visitDataProperty(d.property);
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
        this.visitObjectProperty(fact.property);
        return;
      case E.AxiomType.DATA_PROPERTY_ASSERTION:
      case E.AxiomType.NEGATIVE_DATA_PROPERTY_ASSERTION:
        this.visitDataProperty(fact.property);
        return;
      default:
        return; // SameIndividual / DifferentIndividuals carry no properties
    }
  }
}

module.exports = {
  BuiltInPropertyManager, Checker,
  IRI_TOP_INDIVIDUAL, IRI_ANONYMOUS_CONSTANTS_DATATYPE, IRI_ANONYMOUS_CONSTANT
};
