'use strict';

// ---------------------------------------------------------------------------
// src/adapter/protege.js — glue between protege-js and DL-JS-REASONER.
//
// protege-js parses OWL documents into an `OWLOntology` whose axioms are OWL
// API-shaped objects (`getAxiomType()`, `getIRI()`, `entities()`, ...).
// `Reasoner` already accepts those objects directly (the structural layer
// duck-types on `.axiomType`/`.type`/`.entityType`), so the adapter's job is
// NOT conversion — it is ergonomics:
//
//   * accept IRI strings where the raw reasoner wants expression objects,
//   * return plain arrays of IRI strings where the raw reasoner returns
//     `Node`/`NodeSet`,
//   * mirror protege-js' own `ReasonerQueries` method names, so code written
//     against the forward-chaining RL reasoner can be pointed at full OWL 2 DL
//     reasoning by swapping one constructor.
//
// protege-js' `OWL2RLReasoner` is a forward-chaining rule engine over a triple
// store: it materialises an OWL 2 RL closure and can only answer queries that
// are expressible as triple lookups. This adapter exposes a complete
// tableau-based OWL 2 DL reasoner — consistency, class-expression
// satisfiability, subsumption over arbitrary (not just named) class
// expressions, classification, realisation, arbitrary axiom entailment,
// disjointness, property characteristics, datatype reasoning and conjunctive
// query answering.
// ---------------------------------------------------------------------------

const E = require('../owl/OWLExpressions');
const { createReasoner } = require('../reasoner/Reasoner');
const { Configuration } = require('../Configuration');
const { createIndividual } = require('../model/Term');
const { CollectingQueryResultCollector } = require('../datalog/ConjunctiveQuery');

/** Normalise anything IRI-ish to a plain IRI string. */
function iri(x) {
  return E.iriString(x);
}

/** A `Node`/`NodeSet`/`Set`/array of entities → sorted array of IRI strings. */
function toIriArray(nodeOrSet) {
  let entities;
  if (nodeOrSet === null || nodeOrSet === undefined) {
    entities = [];
  } else if (typeof nodeOrSet.getFlattened === 'function') {
    entities = [...nodeOrSet.getFlattened()];          // NodeSet
  } else if (typeof nodeOrSet.getEntities === 'function') {
    entities = [...nodeOrSet.getEntities()];            // Node
  } else if (nodeOrSet instanceof Set || Array.isArray(nodeOrSet)) {
    entities = [...nodeOrSet];
  } else {
    entities = [nodeOrSet];
  }
  const iris = entities
    .map((e) => iri(e))
    .filter((s) => typeof s === 'string');
  return [...new Set(iris)].sort();
}

/**
 * A protege-js-friendly façade over {@link Reasoner}.
 *
 * Construct with a protege-js `OWLOntology` (or anything with `getAxioms()`):
 *
 *   const { reasonerFor } = require('dl-js-reasoner');
 *   const r = reasonerFor(ont);
 *   r.isConsistent();
 *   r.getSubClasses('http://example.org#A');
 */
class ProtegeAdapter {
  /**
   * @param {object} ontology a protege-js `OWLOntology`
   * @param {object|Configuration} [configuration] reasoner configuration
   */
  constructor(ontology, configuration) {
    const config = configuration instanceof Configuration
      ? configuration
      : new Configuration(configuration || {});
    /** The underlying full-power reasoner. Exposed for anything not wrapped. */
    this.reasoner = createReasoner(ontology, config);
    this.ontology = ontology;
  }

  // ---- metadata -------------------------------------------------------------

  getReasonerName() { return this.reasoner.getReasonerName(); }
  getReasonerVersion() { return this.reasoner.getReasonerVersion(); }
  getRootOntology() { return this.reasoner.getRootOntology(); }
  getConfiguration() { return this.reasoner.getConfiguration(); }
  getBufferingMode() { return this.reasoner.getBufferingMode(); }
  getPrefixes() { return this.reasoner.getPrefixes(); }
  getTableauStatistics() { return this.reasoner.getTableauStatistics(); }
  getDLOntology() { return this.reasoner.getDLOntology(); }

  // ---- incremental changes --------------------------------------------------

  /** Buffer (or, in non-buffering mode, apply) an ontology change. */
  applyChange(change) { this.reasoner.applyChange(change); return this; }
  applyChanges(changes) { this.reasoner.applyChanges(changes); return this; }
  getPendingChanges() { return this.reasoner.getPendingChanges(); }
  /**
   * Whether the buffered changes can be applied by re-clausifying only the
   * ABox (fast) rather than rebuilding the whole `DLOntology`. True when every
   * pending change is an assertion over already-declared entities and the
   * ontology has no nominals. Useful for predicting `flush()` cost.
   */
  canProcessPendingChangesIncrementally() {
    return this.reasoner.canProcessPendingChangesIncrementally();
  }
  /** Force buffered changes to take effect. */
  flush() { this.reasoner.flush(); return this; }
  dispose() { this.reasoner.dispose(); }
  interrupt() { this.reasoner.interrupt(); }

  // ---- consistency / satisfiability ----------------------------------------

  /** Whether the whole ontology (TBox + ABox) has a model. */
  isConsistent() { return this.reasoner.isConsistent(); }

  /**
   * Whether a class is satisfiable. Accepts an IRI string or a class expression.
   * @param {string|object} classIriOrExpression
   */
  isSatisfiable(classIriOrExpression) {
    return this.reasoner.isSatisfiable(_class(classIriOrExpression));
  }

  /** Every unsatisfiable class, as IRI strings (excludes `owl:Nothing`). */
  getUnsatisfiableClasses() {
    return toIriArray(this.reasoner.getUnsatisfiableClasses())
      .filter((s) => s !== E.IRI_NOTHING);
  }

  // ---- subsumption ----------------------------------------------------------

  /**
   * Whether `sub ⊑ super`. Both arguments may be IRI strings or class
   * expressions — unlike protege-js' RL reasoner, arbitrary class expressions
   * (unions, cardinality restrictions, ...) are supported.
   */
  isSubClassOf(sub, sup) {
    return this.reasoner.isSubClassOf(_class(sub), _class(sup));
  }

  /** Superclasses of a class, as IRI strings. `direct` = immediate only. */
  getSuperClasses(classIriOrExpression, { direct = false } = {}) {
    return toIriArray(this.reasoner.getSuperClasses(_class(classIriOrExpression), direct));
  }

  /** Subclasses of a class, as IRI strings. */
  getSubClasses(classIriOrExpression, { direct = false } = {}) {
    return toIriArray(this.reasoner.getSubClasses(_class(classIriOrExpression), direct));
  }

  /** Classes equivalent to a class, as IRI strings. */
  getEquivalentClasses(classIriOrExpression) {
    return toIriArray(this.reasoner.getEquivalentClasses(_class(classIriOrExpression)));
  }

  /** Classes disjoint with a class, as IRI strings (always includes `owl:Nothing`). */
  getDisjointClasses(classIriOrExpression) {
    return toIriArray(this.reasoner.getDisjointClasses(_class(classIriOrExpression)));
  }

  /** Classes with no proper named superclass, as IRI strings. */
  getTopClasses() {
    return toIriArray(this.reasoner.getSubClasses(E.owlThing(), true));
  }

  // ---- individuals ----------------------------------------------------------

  /** Named individuals known to be instances of a class, as IRI strings. */
  getInstances(classIriOrExpression, { direct = false } = {}) {
    return toIriArray(this.reasoner.getInstances(_class(classIriOrExpression), direct));
  }

  /** Classes an individual is an instance of, as IRI strings. */
  getTypes(individualIri, { direct = false } = {}) {
    return toIriArray(this.reasoner.getTypes(E.namedIndividual(iri(individualIri)), direct));
  }

  /** Whether an individual is an instance of a class. */
  hasType(individualIri, classIriOrExpression, direct = false) {
    return this.reasoner.hasType(
      E.namedIndividual(iri(individualIri)), _class(classIriOrExpression), direct);
  }

  /** Individuals provably identical to `individualIri`, as IRI strings. */
  getSameIndividuals(individualIri) {
    return toIriArray(this.reasoner.getSameIndividuals(E.namedIndividual(iri(individualIri))));
  }

  /** Whether two individuals are provably the same. */
  isSameIndividual(individualIri1, individualIri2) {
    return this.reasoner.isSameIndividual(
      E.namedIndividual(iri(individualIri1)), E.namedIndividual(iri(individualIri2)));
  }

  /** Individuals provably different from `individualIri`, as IRI strings. */
  getDifferentIndividuals(individualIri) {
    return toIriArray(this.reasoner.getDifferentIndividuals(E.namedIndividual(iri(individualIri))));
  }

  // ---- property values ------------------------------------------------------

  /** Object-property fillers of an individual, as IRI strings. */
  getObjectPropertyValues(individualIri, propertyIri) {
    return toIriArray(this.reasoner.getObjectPropertyValues(
      E.namedIndividual(iri(individualIri)), E.objectProperty(iri(propertyIri))));
  }

  /** Data-property values of an individual, as protege-js `OWLLiteral`s. */
  getDataPropertyValues(individualIri, propertyIri) {
    const nodeSet = this.reasoner.getDataPropertyValues(
      E.namedIndividual(iri(individualIri)), E.dataProperty(iri(propertyIri)));
    const out = [];
    for (const node of (nodeSet === null ? [] : nodeSet.getNodes())) {
      for (const literal of node.getEntities()) out.push(literal);
    }
    return out;
  }

  /** Whether `subject -property-> object` holds. */
  hasObjectPropertyRelationship(subjectIri, propertyIri, objectIri) {
    return this.reasoner.hasObjectPropertyRelationship(
      E.namedIndividual(iri(subjectIri)),
      E.objectProperty(iri(propertyIri)),
      E.namedIndividual(iri(objectIri)));
  }

  // ---- object properties ----------------------------------------------------

  isSubObjectPropertyOf(sub, sup) {
    return this.reasoner.isSubObjectPropertyExpressionOf(_objectProperty(sub), _objectProperty(sup));
  }

  getSuperObjectProperties(propertyIri, { direct = false } = {}) {
    return toIriArray(this.reasoner.getSuperObjectProperties(_objectProperty(propertyIri), direct));
  }

  getSubObjectProperties(propertyIri, { direct = false } = {}) {
    return toIriArray(this.reasoner.getSubObjectProperties(_objectProperty(propertyIri), direct));
  }

  getEquivalentObjectProperties(propertyIri) {
    return toIriArray(this.reasoner.getEquivalentObjectProperties(_objectProperty(propertyIri)));
  }

  getInverseObjectProperties(propertyIri) {
    return toIriArray(this.reasoner.getInverseObjectProperties(_objectProperty(propertyIri)));
  }

  getDisjointObjectProperties(propertyIri) {
    return toIriArray(this.reasoner.getDisjointObjectProperties(_objectProperty(propertyIri)));
  }

  getObjectPropertyDomains(propertyIri, { direct = false } = {}) {
    return toIriArray(this.reasoner.getObjectPropertyDomains(_objectProperty(propertyIri), direct));
  }

  getObjectPropertyRanges(propertyIri, { direct = false } = {}) {
    return toIriArray(this.reasoner.getObjectPropertyRanges(_objectProperty(propertyIri), direct));
  }

  // ---- data properties ------------------------------------------------------

  isSubDataPropertyOf(sub, sup) {
    return this.reasoner.isSubDataPropertyOf(_dataProperty(sub), _dataProperty(sup));
  }

  getSuperDataProperties(propertyIri, { direct = false } = {}) {
    return toIriArray(this.reasoner.getSuperDataProperties(_dataProperty(propertyIri), direct));
  }

  getSubDataProperties(propertyIri, { direct = false } = {}) {
    return toIriArray(this.reasoner.getSubDataProperties(_dataProperty(propertyIri), direct));
  }

  getEquivalentDataProperties(propertyIri) {
    return toIriArray(this.reasoner.getEquivalentDataProperties(_dataProperty(propertyIri)));
  }

  getDisjointDataProperties(propertyIri) {
    return toIriArray(this.reasoner.getDisjointDataProperties(_dataProperty(propertyIri)));
  }

  getDataPropertyDomains(propertyIri, { direct = false } = {}) {
    return toIriArray(this.reasoner.getDataPropertyDomains(_dataProperty(propertyIri), direct));
  }

  // ---- property characteristics --------------------------------------------

  isFunctional(propertyIri) { return this.reasoner.isFunctional(_property(propertyIri)); }
  isInverseFunctional(propertyIri) { return this.reasoner.isInverseFunctional(_objectProperty(propertyIri)); }
  isSymmetric(propertyIri) { return this.reasoner.isSymmetric(_objectProperty(propertyIri)); }
  isAsymmetric(propertyIri) { return this.reasoner.isAsymmetric(_objectProperty(propertyIri)); }
  isTransitive(propertyIri) { return this.reasoner.isTransitive(_objectProperty(propertyIri)); }
  isReflexive(propertyIri) { return this.reasoner.isReflexive(_objectProperty(propertyIri)); }
  isIrreflexive(propertyIri) { return this.reasoner.isIrreflexive(_objectProperty(propertyIri)); }

  // ---- entailment -----------------------------------------------------------

  /**
   * Whether an axiom (or array/Set of axioms) is entailed. Pass protege-js
   * axiom objects, or build one with the `E.*` factories.
   */
  isEntailed(axiom) { return this.reasoner.isEntailed(axiom); }

  isEntailmentCheckingSupported(axiomType) {
    return this.reasoner.isEntailmentCheckingSupported(axiomType);
  }

  // ---- conjunctive query answering ------------------------------------------

  /**
   * Answer a conjunctive query over the materialised ABox.
   *
   * This is the one query kind protege-js' forward-chaining reasoners cannot
   * answer at all: they materialise an OWL 2 RL closure and can only look up
   * triples, so a multi-atom conjunction with joins, or any query whose answer
   * needs full OWL 2 DL entailment (transitivity, inverse roles, cardinalities,
   * `SameIndividual`), is out of reach.
   *
   *   adapter.query({
   *     select: ['?X', '?Y'],
   *     where: [
   *       { class: EX + 'Person', arg: '?X' },
   *       { objectProperty: EX + 'hasParent', subject: '?X', object: '?Y' }
   *     ]
   *   })
   *   // → [['http://…#mary', 'http://…#john'], …]
   *
   * Answers are returned as arrays of IRI / literal strings, de-duplicated, in
   * the order `select` specifies. **Where the ontology merges individuals**
   * (`SameIndividual`, a functional property, …) each answer is reported in
   * terms of the equivalence-class representative — see
   * {@link ProtegeAdapter#getSameIndividuals} and
   * {@link ProtegeAdapter#getQueryRepresentative}.
   *
   * Requires a **Horn** ontology: a disjunctive head cannot be represented in a
   * materialised ABox, so `getDatalogEngine()` throws for one. An inconsistent
   * ontology throws too, since every answer would be vacuous.
   *
   * @param {{select?: Array, where: Array}} spec see `../datalog/QuerySpec.js`
   * @returns {string[][]}
   */
  query(spec) { return this.reasoner.query(spec); }

  /**
   * As {@link ProtegeAdapter#query}, but returns the raw `Term[][]` so callers
   * can distinguish individuals from literals programmatically.
   */
  answerQuery(spec) {
    const collector = new CollectingQueryResultCollector();
    this.reasoner.createQuery(spec).evaluate(collector);
    return collector.results;
  }

  /**
   * Build a {@link ConjunctiveQuery} for repeated evaluation (e.g. against a
   * stream of collectors). The returned object exposes `getAnswers()`,
   * `evaluate(collector)` and the HermiT-style accessors.
   */
  createQuery(spec) { return this.reasoner.createQuery(spec); }

  /**
   * The `DatalogEngine` behind the query methods — exposes
   * `getEquivalenceClass(term)`, `getRepresentative(term)` and
   * `getTermForNode(node)` for callers that need the raw materialisation.
   */
  getDatalogEngine() { return this.reasoner.getDatalogEngine(); }

  /**
   * The representative that query answers report merged individuals by.
   * Returns an IRI string, or `null` if the individual is unknown to the
   * materialised ABox.
   */
  getQueryRepresentative(individualIri) {
    const rep = this.getDatalogEngine()
      .getRepresentative(createIndividual(iri(individualIri)));
    return rep === null ? null : rep.iri;
  }

  // ---- precomputation -------------------------------------------------------

  precomputeInferences(...inferenceTypes) {
    return this.reasoner.precomputeInferences(...inferenceTypes);
  }

  isPrecomputed(inferenceType) { return this.reasoner.isPrecomputed(inferenceType); }
  getPrecomputableInferenceTypes() { return this.reasoner.getPrecomputableInferenceTypes(); }

  /** Classify the class hierarchy (and, by default, the property hierarchies). */
  classify() { this.reasoner.classifyClasses(); return this; }
  classifyClasses() { this.reasoner.classifyClasses(); return this; }
  classifyObjectProperties() { this.reasoner.classifyObjectProperties(); return this; }
  classifyDataProperties() { this.reasoner.classifyDataProperties(); return this; }
  realise() { this.reasoner.realise(); return this; }
}

// ---- argument coercion helpers ---------------------------------------------

/** IRI string → `OWLClass`; anything else passes through untouched. */
function _class(x) {
  return typeof x === 'string' ? E.owlClass(x) : x;
}

/** IRI string → `OWLObjectProperty`; anything else passes through untouched. */
function _objectProperty(x) {
  return typeof x === 'string' ? E.objectProperty(x) : x;
}

/** IRI string → `OWLDataProperty`; anything else passes through untouched. */
function _dataProperty(x) {
  return typeof x === 'string' ? E.dataProperty(x) : x;
}

/** IRI string → object or data property, guessing from the ontology is not
 *  possible here, so default to an object property; callers who need a data
 *  property should pass an expression object. */
function _property(x) {
  return typeof x === 'string' ? E.objectProperty(x) : x;
}

/**
 * Build a {@link ProtegeAdapter} for a protege-js `OWLOntology`.
 *
 * @param {object} ontology a protege-js `OWLOntology`
 * @param {object|Configuration} [configuration] reasoner configuration
 * @returns {ProtegeAdapter}
 */
function reasonerFor(ontology, configuration) {
  return new ProtegeAdapter(ontology, configuration);
}

module.exports = { ProtegeAdapter, reasonerFor, toIriArray, iri };
