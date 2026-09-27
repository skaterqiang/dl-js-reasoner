'use strict';

// ---------------------------------------------------------------------------
// structural/OWLAxioms.js — the intermediate representation produced by
// OWLNormalization and consumed by OWLClausification.
//
// Port of org.semanticweb.HermiT.structural.OWLAxioms. It is a plain data
// holder: normalization decomposes an ontology's axioms into these collections
// and clausification turns them into DL-clauses.
//
// Note on `conceptInclusions`: each entry is an ARRAY representing a
// DISJUNCTION (a clause head), not a conjunction. `A ⊑ B` becomes
// `[¬A, B]` meaning "¬A ∨ B". This matches HermiT exactly and is what makes
// the later clausification a direct head/body split.
// ---------------------------------------------------------------------------

const E = require('../owl/OWLExpressions');

/** `R1∘…∘Rn ⊑ S`. The single-argument form is the transitivity axiom R∘R ⊑ R. */
class ComplexObjectPropertyInclusion {
  /**
   * @param {object[]|object} subObjectProperties array of property expressions,
   *        or a single property expression (→ transitivity axiom).
   * @param {object} [superObjectProperty]
   */
  constructor(subObjectProperties, superObjectProperty) {
    if (Array.isArray(subObjectProperties)) {
      this.subObjectProperties = subObjectProperties.slice();
      this.superObjectProperty = superObjectProperty;
    } else {
      const p = subObjectProperties;
      this.subObjectProperties = [p, p];
      this.superObjectProperty = p;
    }
  }
  toString() {
    return `${this.subObjectProperties.join(' ∘ ')} ⊑ ${this.superObjectProperty}`;
  }
}

/** A SWRL rule in disjunctive form: body ∧ … → head ∨ … */
class DisjunctiveRule {
  constructor(body, head) {
    this.body = body.slice();
    this.head = head.slice();
  }
  toString() {
    return `${this.body.join(' ∧ ')} -> ${this.head.join(' ∨ ')}`;
  }
}

class OWLAxioms {
  constructor() {
    /** @type {Set<object>} named classes (OWLClass) */
    this.classes = new Set();
    /** @type {Set<object>} named object properties */
    this.objectProperties = new Set();
    /**
     * Named object properties that actually occur in OWL axioms (as opposed to
     * merely appearing in a declaration). HermiT uses this to decide whether
     * the built-in top/bottom properties need axiomatizing.
     * @type {Set<object>}
     */
    this.objectPropertiesOccurringInOWLAxioms = new Set();
    /**
     * Object property expressions known to be non-simple (transitive, or
     * containing a non-simple property in a chain). Populated by
     * ObjectPropertyInclusionManager. @type {Set<object>}
     */
    this.complexObjectPropertyExpressions = new Set();
    /** @type {Set<object>} named data properties */
    this.dataProperties = new Set();
    /** @type {Set<object>} named individuals */
    this.namedIndividuals = new Set();

    /** Disjunctions of class expressions: each entry is a clause head. @type {object[][]} */
    this.conceptInclusions = [];
    /** Disjunctions of data ranges. @type {object[][]} */
    this.dataRangeInclusions = [];

    /** Pairs [sub, super]. @type {object[][]} */
    this.simpleObjectPropertyInclusions = [];
    /** @type {ComplexObjectPropertyInclusion[]} */
    this.complexObjectPropertyInclusions = [];
    /** Arrays of pairwise-disjoint property expressions. @type {object[][]} */
    this.disjointObjectProperties = [];
    /** @type {Set<object>} */
    this.reflexiveObjectProperties = new Set();
    /** @type {Set<object>} */
    this.irreflexiveObjectProperties = new Set();
    /** @type {Set<object>} */
    this.asymmetricObjectProperties = new Set();

    /** Pairs [sub, super]. @type {object[][]} */
    this.dataPropertyInclusions = [];
    /** @type {object[][]} */
    this.disjointDataProperties = [];

    /** @type {object[]} OWLIndividualAxiom-shaped facts */
    this.facts = [];
    /** @type {object[]} OWLHasKeyAxiom-shaped */
    this.hasKeys = [];
    /** IRIs of datatypes introduced by DatatypeDefinition axioms. @type {Set<string>} */
    this.definedDatatypesIRIs = new Set();
    /** @type {DisjunctiveRule[]} */
    this.rules = [];
  }

  // ---- collection helpers (HermiT mutates the fields directly; these keep
  // ---- the JS call sites readable and guard against accidental aliasing) ----

  addClass(c) { this.classes.add(c); return this; }
  addObjectProperty(p) { this.objectProperties.add(p); return this; }
  addDataProperty(p) { this.dataProperties.add(p); return this; }
  addNamedIndividual(i) { this.namedIndividuals.add(i); return this; }

  /** Record a named object property that occurs in a *logical* axiom. */
  noteObjectPropertyUse(p) {
    const named = E.namedPropertyOf(p);
    this.objectProperties.add(named);
    this.objectPropertiesOccurringInOWLAxioms.add(named);
    return this;
  }

  addConceptInclusion(disjunction) { this.conceptInclusions.push(disjunction.slice()); return this; }
  addDataRangeInclusion(disjunction) { this.dataRangeInclusions.push(disjunction.slice()); return this; }

  addSimpleObjectPropertyInclusion(sub, sup) {
    this.simpleObjectPropertyInclusions.push([sub, sup]);
    return this;
  }
  addComplexObjectPropertyInclusion(inclusion) {
    this.complexObjectPropertyInclusions.push(inclusion);
    return this;
  }
  /** `R1∘…∘Rn ⊑ S` */
  addPropertyChain(chain, superProperty) {
    this.complexObjectPropertyInclusions.push(
      new ComplexObjectPropertyInclusion(chain, superProperty));
    return this;
  }
  /** `R ⊑ S` for object properties, honouring the ⊥/⊤ shortcuts. */
  addObjectPropertyInclusion(sub, sup) {
    if (E.isBottomObjectProperty(sub) || E.isTopObjectProperty(sup)) return this;
    this.simpleObjectPropertyInclusions.push([sub, sup]);
    return this;
  }
  /** `R ⊑ S` for data properties, honouring the ⊥/⊤ shortcuts. */
  addDataPropertyInclusion(sub, sup) {
    if (E.isBottomDataProperty(sub) || E.isTopDataProperty(sup)) return this;
    this.dataPropertyInclusions.push([sub, sup]);
    return this;
  }
  /** R∘R ⊑ R */
  makeTransitive(p) {
    this.complexObjectPropertyInclusions.push(new ComplexObjectPropertyInclusion(p));
    return this;
  }
  makeReflexive(p) { this.reflexiveObjectProperties.add(p); return this; }
  makeIrreflexive(p) { this.irreflexiveObjectProperties.add(p); return this; }
  makeAsymmetric(p) { this.asymmetricObjectProperties.add(p); return this; }

  addDisjointObjectProperties(properties) {
    this.disjointObjectProperties.push(properties.slice());
    return this;
  }
  addDisjointDataProperties(properties) {
    this.disjointDataProperties.push(properties.slice());
    return this;
  }

  addFact(fact) { this.facts.push(fact); return this; }
  addHasKey(hasKey) { this.hasKeys.push(hasKey); return this; }
  addDefinedDatatype(iri) { this.definedDatatypesIRIs.add(E.iriString(iri)); return this; }
  addRule(rule) { this.rules.push(rule); return this; }

  /** Total number of axioms represented — used for progress reporting. */
  size() {
    return this.classes.size + this.objectProperties.size + this.dataProperties.size
      + this.namedIndividuals.size + this.conceptInclusions.length
      + this.dataRangeInclusions.length + this.simpleObjectPropertyInclusions.length
      + this.complexObjectPropertyInclusions.length + this.disjointObjectProperties.length
      + this.reflexiveObjectProperties.size + this.irreflexiveObjectProperties.size
      + this.asymmetricObjectProperties.size + this.dataPropertyInclusions.length
      + this.disjointDataProperties.length + this.facts.length + this.hasKeys.length
      + this.definedDatatypesIRIs.size + this.rules.length;
  }
}

module.exports = { OWLAxioms, ComplexObjectPropertyInclusion, DisjunctiveRule };
