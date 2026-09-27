'use strict';

// ---------------------------------------------------------------------------
// owl/OWLExpressions.js — a minimal, self-contained OWL 2 expression model.
//
// The object shapes here are *structurally identical* to protege-js's model
// (`src/model/OWLEntity.js`, `OWLClassExpression.js`, `OWLAxiom.js`), so the
// structural transformation in `src/structural/` can consume a protege-js
// OWLOntology directly without copying it. Everything is duck-typed: we read
// `.type` / `.axiomType` / `.operands` / `.property` / `.filler` rather than
// doing `instanceof` checks against a particular package.
//
// Two things protege-js does not provide are added here:
//   • OWLObjectInverseOf — an anonymous inverse object property expression.
//     Without it, `R⁻` cannot be represented at all, and HermiT's whole
//     treatment of inverse roles (pairwise blocking, role automata, mirrored
//     automata) depends on it.
//   • structural interning — the factory memoises every expression it builds,
//     so structurally equal expressions are `===`. HermiT gets this for free
//     from the OWL API's structural-equality entity stores; we need it because
//     normalization uses expressions as Map keys (`m_definitions`).
//
// For expressions that come from an *external* parser (protege-js) identity is
// not guaranteed, so all normalization maps key on `structuralKey(expr)`
// instead of the object itself. That works uniformly for both sources.
// ---------------------------------------------------------------------------

const OWL_NS = 'http://www.w3.org/2002/07/owl#';
const RDF_NS = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#';
const RDFS_NS = 'http://www.w3.org/2000/01/rdf-schema#';
const XSD_NS = 'http://www.w3.org/2001/XMLSchema#';

const IRI_THING = OWL_NS + 'Thing';
const IRI_NOTHING = OWL_NS + 'Nothing';
const IRI_RDFS_LITERAL = RDFS_NS + 'Literal';
const IRI_TOP_OBJECT_PROPERTY = OWL_NS + 'topObjectProperty';
const IRI_BOTTOM_OBJECT_PROPERTY = OWL_NS + 'bottomObjectProperty';
const IRI_TOP_DATA_PROPERTY = OWL_NS + 'topDataProperty';
const IRI_BOTTOM_DATA_PROPERTY = OWL_NS + 'bottomDataProperty';
const IRI_RDF_PLAIN_LITERAL = RDF_NS + 'PlainLiteral';
const IRI_XSD_STRING = XSD_NS + 'string';

const EntityType = Object.freeze({
  CLASS: 'Class',
  OBJECT_PROPERTY: 'ObjectProperty',
  DATA_PROPERTY: 'DataProperty',
  NAMED_INDIVIDUAL: 'NamedIndividual',
  DATATYPE: 'Datatype',
  ANNOTATION_PROPERTY: 'AnnotationProperty'
});

/** Mirrors protege-js's ClassExpressionType, plus OBJECT_INVERSE_OF. */
const ClassExpressionType = Object.freeze({
  OWL_CLASS: 'OWLClass',
  OBJECT_INVERSE_OF: 'ObjectInverseOf',
  OBJECT_INTERSECTION_OF: 'ObjectIntersectionOf',
  OBJECT_UNION_OF: 'ObjectUnionOf',
  OBJECT_COMPLEMENT_OF: 'ObjectComplementOf',
  OBJECT_SOME_VALUES_FROM: 'ObjectSomeValuesFrom',
  OBJECT_ALL_VALUES_FROM: 'ObjectAllValuesFrom',
  OBJECT_HAS_VALUE: 'ObjectHasValue',
  OBJECT_ONE_OF: 'ObjectOneOf',
  OBJECT_HAS_SELF: 'ObjectHasSelf',
  OBJECT_MIN_CARDINALITY: 'ObjectMinCardinality',
  OBJECT_MAX_CARDINALITY: 'ObjectMaxCardinality',
  OBJECT_EXACT_CARDINALITY: 'ObjectExactCardinality',
  DATA_SOME_VALUES_FROM: 'DataSomeValuesFrom',
  DATA_ALL_VALUES_FROM: 'DataAllValuesFrom',
  DATA_HAS_VALUE: 'DataHasValue',
  DATA_MIN_CARDINALITY: 'DataMinCardinality',
  DATA_MAX_CARDINALITY: 'DataMaxCardinality',
  DATA_EXACT_CARDINALITY: 'DataExactCardinality',
  DATA_INTERSECTION_OF: 'DataIntersectionOf',
  DATA_UNION_OF: 'DataUnionOf',
  DATA_COMPLEMENT_OF: 'DataComplementOf',
  DATA_ONE_OF: 'DataOneOf',
  DATATYPE: 'Datatype',
  DATATYPE_RESTRICTION: 'DatatypeRestriction'
});

const AxiomType = Object.freeze({
  DECLARATION: 'Declaration',
  SUBCLASS_OF: 'SubClassOf',
  EQUIVALENT_CLASSES: 'EquivalentClasses',
  DISJOINT_CLASSES: 'DisjointClasses',
  DISJOINT_UNION: 'DisjointUnion',
  SUB_OBJECT_PROPERTY_OF: 'SubObjectPropertyOf',
  SUB_PROPERTY_CHAIN_OF: 'SubObjectPropertyChainOf',
  EQUIVALENT_OBJECT_PROPERTIES: 'EquivalentObjectProperties',
  DISJOINT_OBJECT_PROPERTIES: 'DisjointObjectProperties',
  OBJECT_PROPERTY_DOMAIN: 'ObjectPropertyDomain',
  OBJECT_PROPERTY_RANGE: 'ObjectPropertyRange',
  INVERSE_OBJECT_PROPERTIES: 'InverseObjectProperties',
  FUNCTIONAL_OBJECT_PROPERTY: 'FunctionalObjectProperty',
  INVERSE_FUNCTIONAL_OBJECT_PROPERTY: 'InverseFunctionalObjectProperty',
  REFLEXIVE_OBJECT_PROPERTY: 'ReflexiveObjectProperty',
  IRREFLEXIVE_OBJECT_PROPERTY: 'IrreflexiveObjectProperty',
  SYMMETRIC_OBJECT_PROPERTY: 'SymmetricObjectProperty',
  ASYMMETRIC_OBJECT_PROPERTY: 'AsymmetricObjectProperty',
  TRANSITIVE_OBJECT_PROPERTY: 'TransitiveObjectProperty',
  SUB_DATA_PROPERTY_OF: 'SubDataPropertyOf',
  EQUIVALENT_DATA_PROPERTIES: 'EquivalentDataProperties',
  DISJOINT_DATA_PROPERTIES: 'DisjointDataProperties',
  DATA_PROPERTY_DOMAIN: 'DataPropertyDomain',
  DATA_PROPERTY_RANGE: 'DataPropertyRange',
  FUNCTIONAL_DATA_PROPERTY: 'FunctionalDataProperty',
  DATATYPE_DEFINITION: 'DatatypeDefinition',
  HAS_KEY: 'HasKey',
  SAME_INDIVIDUAL: 'SameIndividual',
  DIFFERENT_INDIVIDUALS: 'DifferentIndividuals',
  CLASS_ASSERTION: 'ClassAssertion',
  OBJECT_PROPERTY_ASSERTION: 'ObjectPropertyAssertion',
  NEGATIVE_OBJECT_PROPERTY_ASSERTION: 'NegativeObjectPropertyAssertion',
  DATA_PROPERTY_ASSERTION: 'DataPropertyAssertion',
  NEGATIVE_DATA_PROPERTY_ASSERTION: 'NegativeDataPropertyAssertion',
  ANNOTATION_ASSERTION: 'AnnotationAssertion',
  SUB_ANNOTATION_PROPERTY_OF: 'SubAnnotationPropertyOf',
  ANNOTATION_PROPERTY_DOMAIN: 'AnnotationPropertyDomain',
  ANNOTATION_PROPERTY_RANGE: 'AnnotationPropertyRange'
});

/** Axiom types that carry no DL semantics and are skipped by normalization. */
const NON_LOGICAL_AXIOM_TYPES = new Set([
  AxiomType.DECLARATION,
  AxiomType.ANNOTATION_ASSERTION,
  AxiomType.SUB_ANNOTATION_PROPERTY_OF,
  AxiomType.ANNOTATION_PROPERTY_DOMAIN,
  AxiomType.ANNOTATION_PROPERTY_RANGE
]);

// ===========================================================================
// IRI / literal
// ===========================================================================

/**
 * Accepts an IRI object, a string, or an entity, and returns the IRI string.
 *
 * Entity-aware on purpose: `OWLEntity.toString()` returns the SHORT form in
 * both this module and protege-js, so falling back to `toString()` for an
 * entity would silently yield `integer` instead of
 * `http://www.w3.org/2001/XMLSchema#integer`.
 */
function iriString(x) {
  if (x === null || x === undefined) return null;
  if (typeof x === 'string') return x;
  if (typeof x.getIRI === 'function') return iriString(x.getIRI());
  if (x.iri !== undefined && x.iri !== null) return iriString(x.iri);
  if (x._iri !== undefined) return String(x._iri); // protege-js IRI
  if (typeof x.toString === 'function') return x.toString();
  return String(x);
}

class OWLLiteral {
  constructor(lexicalValue, datatype = null, lang = null) {
    this.lexicalValue = String(lexicalValue);
    this.datatype = datatype; // OWLDatatype | IRI-string | null
    this.lang = lang || null;
  }
  getLiteral() { return this.lexicalValue; }
  getLang() { return this.lang; }
  getDatatype() { return this.datatype; }
  /**
   * The effective datatype IRI.
   *
   * A language-tagged literal is an `rdf:PlainLiteral`. An UNTAGGED, UNTYPED
   * literal is an `xsd:string`: OWL 2 Syntax §2.3 gives `"abc"` the datatype
   * `xsd:string`, and OWL API's `getOWLLiteral(String)` builds it that way — so
   * HermiT's `convertLiteral` reaches its `else` branch and emits
   * `Constant.create("abc", xsd:string)`. Defaulting to `rdf:PlainLiteral`
   * instead made `"test"` and `"test"^^xsd:string` two DIFFERENT constants,
   * which is why HermiT's `EntailmentTest.testBlankWithDTs3` failed here.
   */
  getDatatypeIRI() {
    if (this.lang) return IRI_RDF_PLAIN_LITERAL;
    const dt = iriString(this.datatype);
    return dt || IRI_XSD_STRING;
  }
  isRDFPlainLiteral() { return !!this.lang || iriString(this.datatype) === IRI_RDF_PLAIN_LITERAL; }
  toString() {
    if (this.lang) return `"${this.lexicalValue}"@${this.lang}`;
    const dt = iriString(this.datatype);
    return dt ? `"${this.lexicalValue}"^^<${dt}>` : `"${this.lexicalValue}"`;
  }
}

// ===========================================================================
// Entities
// ===========================================================================

class OWLEntity {
  constructor(iri, entityType) {
    this.iri = iri;
    this.entityType = entityType;
    // protege-js compatibility shims
    this.type = entityType === EntityType.CLASS ? ClassExpressionType.OWL_CLASS
      : entityType === EntityType.DATATYPE ? ClassExpressionType.DATATYPE
      : entityType;
  }
  getIRI() { return this.iri; }
  getEntityType() { return this.entityType; }
  getShortForm() {
    const h = this.iri.lastIndexOf('#');
    if (h >= 0) return this.iri.slice(h + 1);
    const s = this.iri.lastIndexOf('/');
    return s >= 0 ? this.iri.slice(s + 1) : this.iri;
  }
  isOWLClass() { return this.entityType === EntityType.CLASS; }
  isOWLObjectProperty() { return this.entityType === EntityType.OBJECT_PROPERTY; }
  isOWLDataProperty() { return this.entityType === EntityType.DATA_PROPERTY; }
  isOWLNamedIndividual() { return this.entityType === EntityType.NAMED_INDIVIDUAL; }
  isOWLDatatype() { return this.entityType === EntityType.DATATYPE; }
  toString() { return this.getShortForm(); }
}

class OWLClass extends OWLEntity {
  constructor(iri) { super(iri, EntityType.CLASS); }
}
class OWLObjectProperty extends OWLEntity {
  constructor(iri) { super(iri, EntityType.OBJECT_PROPERTY); }
  isAnonymous() { return false; }
  getNamedProperty() { return this; }
  getInverseProperty() { return objectInverseOf(this); }
}
class OWLDataProperty extends OWLEntity {
  constructor(iri) { super(iri, EntityType.DATA_PROPERTY); }
}
class OWLNamedIndividual extends OWLEntity {
  constructor(iri) { super(iri, EntityType.NAMED_INDIVIDUAL); }
  isAnonymous() { return false; }
}
class OWLDatatype extends OWLEntity {
  constructor(iri) { super(iri, EntityType.DATATYPE); }
}

class OWLAnonymousIndividual {
  constructor(nodeId) {
    this.nodeId = String(nodeId).replace(/^_:/, '');
    this.entityType = EntityType.NAMED_INDIVIDUAL;
  }
  getNodeId() { return this.nodeId; }
  isAnonymous() { return true; }
  isOWLNamedIndividual() { return false; }
  getShortForm() { return this.nodeId; }
  toString() { return `_:${this.nodeId}`; }
}

/**
 * R⁻ — the anonymous inverse of an object property expression. protege-js has
 * no class for this; without it inverse roles cannot be represented.
 */
class OWLObjectInverseOf {
  constructor(property) {
    this.type = ClassExpressionType.OBJECT_INVERSE_OF;
    this.property = property; // the expression being inverted
    this.inverse = property;  // OWL API calls the accessor getInverse()
  }
  isAnonymous() { return true; }
  getInverse() { return this.property; }
  getNamedProperty() { return namedPropertyOf(this.property); }
  getInverseProperty() { return this.property; }
  getShortForm() { return `${namedPropertyOf(this.property).getShortForm()}⁻`; }
  toString() { return `ObjectInverseOf(${this.property})`; }
}

// ===========================================================================
// Anonymous class expressions / data ranges
// ===========================================================================

class OWLObjectIntersectionOf {
  constructor(operands) { this.type = ClassExpressionType.OBJECT_INTERSECTION_OF; this.operands = operands.slice(); }
  toString() { return `ObjectIntersectionOf(${this.operands.join(' ')})`; }
}
class OWLObjectUnionOf {
  constructor(operands) { this.type = ClassExpressionType.OBJECT_UNION_OF; this.operands = operands.slice(); }
  toString() { return `ObjectUnionOf(${this.operands.join(' ')})`; }
}
class OWLObjectComplementOf {
  constructor(operand) { this.type = ClassExpressionType.OBJECT_COMPLEMENT_OF; this.operand = operand; }
  toString() { return `ObjectComplementOf(${this.operand})`; }
}
class OWLObjectSomeValuesFrom {
  constructor(property, filler) {
    this.type = ClassExpressionType.OBJECT_SOME_VALUES_FROM;
    this.property = property; this.filler = filler;
  }
  toString() { return `ObjectSomeValuesFrom(${this.property} ${this.filler})`; }
}
class OWLObjectAllValuesFrom {
  constructor(property, filler) {
    this.type = ClassExpressionType.OBJECT_ALL_VALUES_FROM;
    this.property = property; this.filler = filler;
  }
  toString() { return `ObjectAllValuesFrom(${this.property} ${this.filler})`; }
}
class OWLObjectHasValue {
  constructor(property, value) {
    this.type = ClassExpressionType.OBJECT_HAS_VALUE;
    this.property = property; this.value = value; this.filler = value;
  }
  toString() { return `ObjectHasValue(${this.property} ${this.value})`; }
}
class OWLObjectOneOf {
  constructor(individuals) {
    this.type = ClassExpressionType.OBJECT_ONE_OF;
    this.operands = individuals.slice();
    this.individuals = this.operands;
  }
  getIndividuals() { return this.operands; }
  toString() { return `ObjectOneOf(${this.operands.join(' ')})`; }
}
class OWLObjectHasSelf {
  constructor(property) { this.type = ClassExpressionType.OBJECT_HAS_SELF; this.property = property; }
  toString() { return `ObjectHasSelf(${this.property})`; }
}
/**
 * Covers min/max/exact and their qualified variants. protege-js uses the same
 * single class with a discriminating `type`.
 */
class OWLObjectCardinalityRestriction {
  constructor(type, cardinality, property, filler) {
    this.type = type;
    this.cardinality = cardinality;
    this.property = property;
    this.filler = filler;
  }
  getCardinality() { return this.cardinality; }
  getProperty() { return this.property; }
  getFiller() { return this.filler; }
  toString() { return `${this.type}(${this.cardinality} ${this.property} ${this.filler || ''})`; }
}

class OWLDataSomeValuesFrom {
  constructor(property, filler) {
    this.type = ClassExpressionType.DATA_SOME_VALUES_FROM;
    this.property = property; this.filler = filler;
  }
  toString() { return `DataSomeValuesFrom(${this.property} ${this.filler})`; }
}
class OWLDataAllValuesFrom {
  constructor(property, filler) {
    this.type = ClassExpressionType.DATA_ALL_VALUES_FROM;
    this.property = property; this.filler = filler;
  }
  toString() { return `DataAllValuesFrom(${this.property} ${this.filler})`; }
}
class OWLDataHasValue {
  constructor(property, value) {
    this.type = ClassExpressionType.DATA_HAS_VALUE;
    this.property = property; this.value = value; this.filler = value;
  }
  toString() { return `DataHasValue(${this.property} ${this.value})`; }
}
class OWLDataCardinalityRestriction {
  constructor(type, cardinality, property, filler) {
    this.type = type;
    this.cardinality = cardinality;
    this.property = property;
    this.filler = filler;
  }
  getCardinality() { return this.cardinality; }
  getProperty() { return this.property; }
  getFiller() { return this.filler; }
  toString() { return `${this.type}(${this.cardinality} ${this.property} ${this.filler || ''})`; }
}

class OWLDataIntersectionOf {
  constructor(operands) { this.type = ClassExpressionType.DATA_INTERSECTION_OF; this.operands = operands.slice(); }
  toString() { return `DataIntersectionOf(${this.operands.join(' ')})`; }
}
class OWLDataUnionOf {
  constructor(operands) { this.type = ClassExpressionType.DATA_UNION_OF; this.operands = operands.slice(); }
  toString() { return `DataUnionOf(${this.operands.join(' ')})`; }
}
class OWLDataComplementOf {
  constructor(operand) {
    this.type = ClassExpressionType.DATA_COMPLEMENT_OF;
    this.operand = operand;
    this.dataRange = operand; // OWL API calls the accessor getDataRange()
  }
  getDataRange() { return this.operand; }
  toString() { return `DataComplementOf(${this.operand})`; }
}
class OWLDataOneOf {
  constructor(literals) {
    this.type = ClassExpressionType.DATA_ONE_OF;
    this.operands = literals.slice();
    this.values = this.operands;
  }
  getValues() { return this.operands; }
  toString() { return `DataOneOf(${this.operands.join(' ')})`; }
}
class OWLDatatypeRestriction {
  constructor(datatype, facetRestrictions) {
    this.type = ClassExpressionType.DATATYPE_RESTRICTION;
    this.datatype = datatype;
    this.facetRestrictions = (facetRestrictions || []).map(f => ({
      facet: iriString(f.facet),
      value: f.value instanceof OWLLiteral ? f.value : literalOf(f.value)
    }));
  }
  getDatatype() { return this.datatype; }
  getFacetRestrictions() { return this.facetRestrictions; }
  toString() {
    const fr = this.facetRestrictions.map(f => `${f.facet} ${f.value}`).join(' ');
    return `DatatypeRestriction(${this.datatype} ${fr})`;
  }
}

// ===========================================================================
// Axioms
// ===========================================================================

class OWLAxiom {
  constructor(axiomType) { this.axiomType = axiomType; this.annotations = []; }
  getAxiomType() { return this.axiomType; }
  toString() { return `${this.axiomType}(${JSON.stringify(Object.keys(this))})`; }
}

function _axiom(type, fields) {
  const a = new OWLAxiom(type);
  Object.assign(a, fields);
  return a;
}

// ===========================================================================
// Predicates / accessors (duck-typed: work on protege-js objects too)
// ===========================================================================

function exprType(e) {
  if (e === null || e === undefined) return null;
  if (e.type) return e.type;
  // protege-js entities carry only `entityType` (no `type`), and its values
  // ('Class', 'ObjectProperty', 'DataProperty', 'NamedIndividual', 'Datatype')
  // are exactly our EntityType values, so they can be returned as-is.
  if (e.entityType !== undefined && e.entityType !== null) {
    if (e.entityType === EntityType.CLASS) return ClassExpressionType.OWL_CLASS;
    if (e.entityType === EntityType.DATATYPE) return ClassExpressionType.DATATYPE;
    return e.entityType;
  }
  return null;
}

function isNamedClass(e) {
  const t = exprType(e);
  return t === ClassExpressionType.OWL_CLASS || t === EntityType.CLASS;
}
function isObjectProperty(e) {
  const t = exprType(e);
  return t === ClassExpressionType.OBJECT_PROPERTY || t === EntityType.OBJECT_PROPERTY;
}
function isDataProperty(e) {
  const t = exprType(e);
  return t === ClassExpressionType.DATA_PROPERTY || t === EntityType.DATA_PROPERTY;
}
function isDatatype(e) {
  const t = exprType(e);
  return t === ClassExpressionType.DATATYPE || t === EntityType.DATATYPE;
}
function isObjectInverseOf(e) { return exprType(e) === ClassExpressionType.OBJECT_INVERSE_OF; }

function isOWLThing(e) { return isNamedClass(e) && iriString(e.iri || e.getIRI && e.getIRI()) === IRI_THING; }
function isOWLNothing(e) { return isNamedClass(e) && iriString(e.iri || (e.getIRI && e.getIRI())) === IRI_NOTHING; }
function isTopDatatype(e) { return isDatatype(e) && iriString(e.iri || (e.getIRI && e.getIRI())) === IRI_RDFS_LITERAL; }
function isBottomDataRange(e) {
  return exprType(e) === ClassExpressionType.DATA_COMPLEMENT_OF && isTopDatatype(operandOf(e));
}

function isTopObjectProperty(e) {
  return isObjectProperty(e) && iriString(e.iri || (e.getIRI && e.getIRI())) === IRI_TOP_OBJECT_PROPERTY;
}
function isBottomObjectProperty(e) {
  return isObjectProperty(e) && iriString(e.iri || (e.getIRI && e.getIRI())) === IRI_BOTTOM_OBJECT_PROPERTY;
}
function isTopDataProperty(e) {
  return isDataProperty(e) && iriString(e.iri || (e.getIRI && e.getIRI())) === IRI_TOP_DATA_PROPERTY;
}
function isBottomDataProperty(e) {
  return isDataProperty(e) && iriString(e.iri || (e.getIRI && e.getIRI())) === IRI_BOTTOM_DATA_PROPERTY;
}

/** `operand` (complements) or `dataRange`. */
function operandOf(e) { return e.operand !== undefined ? e.operand : e.dataRange; }
/** `operands` (n-ary) or `individuals` / `values`. */
function operandsOf(e) {
  if (Array.isArray(e.operands)) return e.operands;
  if (Array.isArray(e.individuals)) return e.individuals;
  if (Array.isArray(e.values)) return e.values;
  if (Array.isArray(e.classExpressions)) return e.classExpressions;
  return [];
}

/** Whether an object property expression is anonymous (i.e. an inverse). */
function isAnonymousProperty(p) {
  if (typeof p.isAnonymous === 'function') return !!p.isAnonymous();
  return isObjectInverseOf(p);
}

/** The named property underlying an (possibly inverted) property expression. */
function namedPropertyOf(p) {
  if (typeof p.getNamedProperty === 'function' && !isObjectInverseOf(p)) return p.getNamedProperty();
  if (isObjectInverseOf(p)) return namedPropertyOf(operandOf(p) || p.property || p.inverse);
  return p;
}

/** The inverse of an object property expression. */
function inversePropertyOf(p) {
  if (typeof p.getInverseProperty === 'function' && !isObjectInverseOf(p)) {
    const inv = p.getInverseProperty();
    if (inv && inv !== p) return inv;
  }
  if (isObjectInverseOf(p)) return namedPropertyOf(p);
  return objectInverseOf(p);
}

/**
 * The filler of a cardinality restriction, defaulting to owl:Thing (object
 * side) or rdfs:Literal (data side) when the restriction is unqualified.
 */
function cardinalityFiller(e, isDataSide) {
  if (e.filler !== undefined && e.filler !== null) return e.filler;
  return isDataSide ? topDatatype() : owlThing();
}

function isObjectCardinality(e) {
  const t = exprType(e);
  return t === ClassExpressionType.OBJECT_MIN_CARDINALITY
    || t === ClassExpressionType.OBJECT_MAX_CARDINALITY
    || t === ClassExpressionType.OBJECT_EXACT_CARDINALITY;
}
function isDataCardinality(e) {
  const t = exprType(e);
  return t === ClassExpressionType.DATA_MIN_CARDINALITY
    || t === ClassExpressionType.DATA_MAX_CARDINALITY
    || t === ClassExpressionType.DATA_EXACT_CARDINALITY;
}

// ===========================================================================
// Structural keys — canonical strings used for interning and Map keys.
// ===========================================================================

/** A canonical string for an entity, individual, literal, or IRI. */
function atomKey(x) {
  if (x === null || x === undefined) return 'null';
  if (typeof x === 'string') return `s:${x}`;
  if (x instanceof OWLLiteral || (x.lexicalValue !== undefined && x.datatype !== undefined && !x.type)) {
    return `lit:${x.lexicalValue}|${x.lang || ''}|${iriString(x.datatype) || ''}`;
  }
  if (x.lexicalValue !== undefined) {
    return `lit:${x.lexicalValue}|${x.lang || ''}|${(x.getDatatypeIRI && x.getDatatypeIRI()) || iriString(x.datatype) || ''}`;
  }
  if (x.nodeId !== undefined) return `anon:${x.nodeId}`;
  if (x.entityType !== undefined) return `${x.entityType}:${iriString(x.iri || (x.getIRI && x.getIRI()))}`;
  if (typeof x.getIRI === 'function') return `iri:${x.getIRI()}`;
  return `o:${String(x)}`;
}

/**
 * A canonical string for any class expression or data range. Two expressions
 * have the same key iff they are structurally equal.
 */
function structuralKey(e) {
  if (e === null || e === undefined) return 'null';
  const t = exprType(e);
  switch (t) {
    case ClassExpressionType.OWL_CLASS:
    case EntityType.CLASS:
    case ClassExpressionType.DATATYPE:
    case EntityType.DATATYPE:
    case EntityType.OBJECT_PROPERTY:
    case ClassExpressionType.OBJECT_PROPERTY:
    case EntityType.DATA_PROPERTY:
    case ClassExpressionType.DATA_PROPERTY:
    case EntityType.NAMED_INDIVIDUAL:
      return atomKey(e);
    case ClassExpressionType.OBJECT_INVERSE_OF:
      return `inv(${structuralKey(operandOf(e) || e.property)})`;
    case ClassExpressionType.OBJECT_COMPLEMENT_OF:
    case ClassExpressionType.DATA_COMPLEMENT_OF:
      return `not(${structuralKey(operandOf(e))})`;
    case ClassExpressionType.OBJECT_INTERSECTION_OF:
    case ClassExpressionType.DATA_INTERSECTION_OF:
      return `and(${operandsOf(e).map(structuralKey).sort().join(',')})`;
    case ClassExpressionType.OBJECT_UNION_OF:
    case ClassExpressionType.DATA_UNION_OF:
      return `or(${operandsOf(e).map(structuralKey).sort().join(',')})`;
    case ClassExpressionType.OBJECT_ONE_OF:
    case ClassExpressionType.DATA_ONE_OF:
      return `oneOf(${operandsOf(e).map(atomKey).sort().join(',')})`;
    case ClassExpressionType.OBJECT_SOME_VALUES_FROM:
      return `some(${atomKey(e.property)},${structuralKey(e.filler)})`;
    case ClassExpressionType.OBJECT_ALL_VALUES_FROM:
      return `only(${atomKey(e.property)},${structuralKey(e.filler)})`;
    case ClassExpressionType.OBJECT_HAS_VALUE:
      return `value(${atomKey(e.property)},${atomKey(e.value !== undefined ? e.value : e.filler)})`;
    case ClassExpressionType.OBJECT_HAS_SELF:
      return `self(${atomKey(e.property)})`;
    case ClassExpressionType.DATA_SOME_VALUES_FROM:
      return `dsome(${atomKey(e.property)},${structuralKey(e.filler)})`;
    case ClassExpressionType.DATA_ALL_VALUES_FROM:
      return `donly(${atomKey(e.property)},${structuralKey(e.filler)})`;
    case ClassExpressionType.DATA_HAS_VALUE:
      return `dvalue(${atomKey(e.property)},${atomKey(e.value !== undefined ? e.value : e.filler)})`;
    case ClassExpressionType.DATATYPE_RESTRICTION: {
      const frs = (e.facetRestrictions || [])
        .map(f => `${iriString(f.facet)}:${atomKey(f.value)}`)
        .sort();
      return `dtres(${atomKey(e.datatype)},${frs.join(',')})`;
    }
    default:
      if (isObjectCardinality(e) || isDataCardinality(e)) {
        const filler = e.filler === undefined || e.filler === null ? 'null' : structuralKey(e.filler);
        return `card(${t},${e.cardinality},${atomKey(e.property)},${filler})`;
      }
      return `?${t}:${String(e)}`;
  }
}

/** Structural equality that works across protege-js and local objects. */
function exprEquals(a, b) {
  if (a === b) return true;
  if (a === null || b === null || a === undefined || b === undefined) return false;
  return structuralKey(a) === structuralKey(b);
}

// ===========================================================================
// Interning factory
// ===========================================================================

const _entityCache = new Map();
const _exprCache = new Map();
const _literalCache = new Map();

function _internEntity(ctor, iri) {
  const key = `${ctor.name}|${iri}`;
  let e = _entityCache.get(key);
  if (!e) { e = new ctor(iri); _entityCache.set(key, e); }
  return e;
}

function owlClass(iri) { return _internEntity(OWLClass, iriString(iri)); }
function objectProperty(iri) { return _internEntity(OWLObjectProperty, iriString(iri)); }
function dataProperty(iri) { return _internEntity(OWLDataProperty, iriString(iri)); }
function namedIndividual(iri) { return _internEntity(OWLNamedIndividual, iriString(iri)); }
function datatype(iri) { return _internEntity(OWLDatatype, iriString(iri)); }

const _anonIndividualCache = new Map();
function anonymousIndividual(nodeId) {
  const id = String(nodeId).replace(/^_:/, '');
  let a = _anonIndividualCache.get(id);
  if (!a) { a = new OWLAnonymousIndividual(id); _anonIndividualCache.set(id, a); }
  return a;
}

function literal(lexicalValue, datatypeIri = null, lang = null) {
  if (lexicalValue instanceof OWLLiteral) return lexicalValue;
  if (lexicalValue && lexicalValue.lexicalValue !== undefined && typeof lexicalValue !== 'string') {
    // Already a literal-shaped object (possibly from protege-js): normalise it.
    return literal(
      lexicalValue.lexicalValue,
      (lexicalValue.getDatatypeIRI && lexicalValue.getDatatypeIRI()) || iriString(lexicalValue.datatype),
      lexicalValue.lang || lexicalValue.getLang && lexicalValue.getLang()
    );
  }
  // `rdf:PlainLiteral` carries its language tag INSIDE the lexical form, as
  // `"abc@en-gb"`. OWL API parses that out at construction time, so HermiT never
  // sees the `@` — see `OWLDataFactoryInternalsImplNoCache.getOWLLiteral(String,
  // OWLDatatype)`:
  //
  //   if (datatype.isRDFPlainLiteral() || datatype.equals(LANGSTRING)) {
  //       int sep = lexicalValue.lastIndexOf('@');
  //       if (sep != -1) return getBasicLiteral(lex, lang, LANGSTRING);
  //       else           return getBasicLiteral(lexicalValue, XSDSTRING);
  //   }
  //
  // and `OWLLiteral.getLiteral()`'s contract: *"If the literal is of the form
  // `"abc@"^^rdf:PlainLiteral` then the return value will be `"abc"` (without
  // the language tag included)."* HermiT's own value space agrees —
  // `RDFPlainLiteralDatatypeHandler.parseLiteral` splits at `lastIndexOf('@')`
  // and maps an EMPTY tag to a bare `String`, i.e. the `xsd:string` data value.
  //
  // Skipping the split left `lexicalValue === 'abc@'` with
  // `isRDFPlainLiteral() === true`, so `convertLiteral` appended a second
  // separator and emitted `Constant("abc@@", rdf:PlainLiteral)` — a different
  // constant from both `"abc"` and `PL("abc","")`. That broke HermiT's
  // `ComplexConceptTest.testConceptWithDatatypes` and
  // `OWLReasonerTest.testGetDataPropertyValues`, which each assert the two
  // spellings denote ONE value.
  if (!lang && iriString(datatypeIri) === IRI_RDF_PLAIN_LITERAL) {
    const lex = String(lexicalValue);
    const sep = lex.lastIndexOf('@');
    // No separator at all ⇒ OWL API falls back to `xsd:string`.
    return sep === -1 ? literal(lex, IRI_XSD_STRING, null) : literal(lex.substring(0, sep), null, lex.substring(sep + 1));
  }
  // See OWLLiteral.getDatatypeIRI: untagged + untyped ⇒ xsd:string (OWL 2 §2.3).
  const dtIri = lang ? IRI_RDF_PLAIN_LITERAL : (iriString(datatypeIri) || IRI_XSD_STRING);
  const key = `${lexicalValue}|${lang || ''}|${dtIri}`;
  let l = _literalCache.get(key);
  if (!l) {
    l = new OWLLiteral(lexicalValue, lang ? null : datatype(dtIri), lang || null);
    _literalCache.set(key, l);
  }
  return l;
}
/** Alias used when the input may already be an OWLLiteral. */
const literalOf = literal;

function _intern(key, build) {
  let e = _exprCache.get(key);
  if (!e) { e = build(); _exprCache.set(key, e); }
  return e;
}

function objectInverseOf(property) {
  if (isObjectInverseOf(property)) return namedPropertyOf(property);
  return _intern(`inv(${atomKey(property)})`, () => new OWLObjectInverseOf(property));
}

function owlThing() { return owlClass(IRI_THING); }
function owlNothing() { return owlClass(IRI_NOTHING); }
function topDatatype() { return datatype(IRI_RDFS_LITERAL); }
function topObjectProperty() { return objectProperty(IRI_TOP_OBJECT_PROPERTY); }
function bottomObjectProperty() { return objectProperty(IRI_BOTTOM_OBJECT_PROPERTY); }
function topDataProperty() { return dataProperty(IRI_TOP_DATA_PROPERTY); }
function bottomDataProperty() { return dataProperty(IRI_BOTTOM_DATA_PROPERTY); }

/** n-ary connectives flatten, dedupe and sort their operands (like OWL API). */
function _normalizeNary(operands, isDataSide) {
  const byKey = new Map();
  for (const op of operands) {
    if (op === null || op === undefined) continue;
    byKey.set(structuralKey(op), op);
  }
  const sorted = [...byKey.entries()].sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0));
  return sorted.map(kv => kv[1]);
}

function objectIntersectionOf(operands) {
  const ops = _normalizeNary(operands, false);
  if (ops.length === 0) return owlThing();
  if (ops.length === 1) return ops[0];
  const key = `and(${ops.map(structuralKey).join(',')})`;
  return _intern(key, () => new OWLObjectIntersectionOf(ops));
}

function objectUnionOf(operands) {
  const ops = _normalizeNary(operands, false);
  if (ops.length === 0) return owlNothing();
  if (ops.length === 1) return ops[0];
  const key = `or(${ops.map(structuralKey).join(',')})`;
  return _intern(key, () => new OWLObjectUnionOf(ops));
}

function objectComplementOf(operand) {
  const key = `not(${structuralKey(operand)})`;
  return _intern(key, () => new OWLObjectComplementOf(operand));
}

function objectSomeValuesFrom(property, filler) {
  const key = `some(${atomKey(property)},${structuralKey(filler)})`;
  return _intern(key, () => new OWLObjectSomeValuesFrom(property, filler));
}
function objectAllValuesFrom(property, filler) {
  const key = `only(${atomKey(property)},${structuralKey(filler)})`;
  return _intern(key, () => new OWLObjectAllValuesFrom(property, filler));
}
function objectHasValue(property, value) {
  const key = `value(${atomKey(property)},${atomKey(value)})`;
  return _intern(key, () => new OWLObjectHasValue(property, value));
}
function objectOneOf(individuals) {
  const inds = [...new Set(individuals.map(atomKey))].sort()
    .map(k => individuals.find(i => atomKey(i) === k));
  const key = `oneOf(${inds.map(atomKey).join(',')})`;
  return _intern(key, () => new OWLObjectOneOf(inds));
}
function objectHasSelf(property) {
  const key = `self(${atomKey(property)})`;
  return _intern(key, () => new OWLObjectHasSelf(property));
}

function _objectCard(type, cardinality, property, filler) {
  const f = filler === undefined || filler === null ? owlThing() : filler;
  const key = `card(${type},${cardinality},${atomKey(property)},${structuralKey(f)})`;
  return _intern(key, () => new OWLObjectCardinalityRestriction(type, cardinality, property, f));
}
function objectMinCardinality(cardinality, property, filler) {
  return _objectCard(ClassExpressionType.OBJECT_MIN_CARDINALITY, cardinality, property, filler);
}
function objectMaxCardinality(cardinality, property, filler) {
  return _objectCard(ClassExpressionType.OBJECT_MAX_CARDINALITY, cardinality, property, filler);
}
function objectExactCardinality(cardinality, property, filler) {
  return _objectCard(ClassExpressionType.OBJECT_EXACT_CARDINALITY, cardinality, property, filler);
}

function dataSomeValuesFrom(property, filler) {
  const key = `dsome(${atomKey(property)},${structuralKey(filler)})`;
  return _intern(key, () => new OWLDataSomeValuesFrom(property, filler));
}
function dataAllValuesFrom(property, filler) {
  const key = `donly(${atomKey(property)},${structuralKey(filler)})`;
  return _intern(key, () => new OWLDataAllValuesFrom(property, filler));
}
function dataHasValue(property, value) {
  const key = `dvalue(${atomKey(property)},${atomKey(value)})`;
  return _intern(key, () => new OWLDataHasValue(property, value));
}

function _dataCard(type, cardinality, property, filler) {
  const f = filler === undefined || filler === null ? topDatatype() : filler;
  const key = `card(${type},${cardinality},${atomKey(property)},${structuralKey(f)})`;
  return _intern(key, () => new OWLDataCardinalityRestriction(type, cardinality, property, f));
}
function dataMinCardinality(cardinality, property, filler) {
  return _dataCard(ClassExpressionType.DATA_MIN_CARDINALITY, cardinality, property, filler);
}
function dataMaxCardinality(cardinality, property, filler) {
  return _dataCard(ClassExpressionType.DATA_MAX_CARDINALITY, cardinality, property, filler);
}
function dataExactCardinality(cardinality, property, filler) {
  return _dataCard(ClassExpressionType.DATA_EXACT_CARDINALITY, cardinality, property, filler);
}

function dataIntersectionOf(operands) {
  const ops = _normalizeNary(operands, true);
  if (ops.length === 0) return topDatatype();
  if (ops.length === 1) return ops[0];
  const key = `dand(${ops.map(structuralKey).join(',')})`;
  return _intern(key, () => new OWLDataIntersectionOf(ops));
}
function dataUnionOf(operands) {
  const ops = _normalizeNary(operands, true);
  if (ops.length === 0) return dataComplementOf(topDatatype());
  if (ops.length === 1) return ops[0];
  const key = `dor(${ops.map(structuralKey).join(',')})`;
  return _intern(key, () => new OWLDataUnionOf(ops));
}
function dataComplementOf(operand) {
  const key = `dnot(${structuralKey(operand)})`;
  return _intern(key, () => new OWLDataComplementOf(operand));
}
function dataOneOf(literals) {
  const ls = [...new Set(literals.map(atomKey))].sort()
    .map(k => literals.find(l => atomKey(l) === k));
  const key = `doneOf(${ls.map(atomKey).join(',')})`;
  return _intern(key, () => new OWLDataOneOf(ls));
}
function datatypeRestriction(dt, facetRestrictions) {
  const frs = (facetRestrictions || []).map(f => ({
    facet: iriString(f.facet),
    value: literal(f.value)
  }));
  const key = `dtres(${atomKey(dt)},${frs.map(f => `${f.facet}:${atomKey(f.value)}`).sort().join(',')})`;
  return _intern(key, () => new OWLDatatypeRestriction(dt, frs));
}

// ---- axiom constructors ----------------------------------------------------

const subclassOf = (subClass, superClass) =>
  _axiom(AxiomType.SUBCLASS_OF, { subClass, superClass });
const equivalentClasses = (classExpressions) =>
  _axiom(AxiomType.EQUIVALENT_CLASSES, { classExpressions: classExpressions.slice() });
const disjointClasses = (classExpressions) =>
  _axiom(AxiomType.DISJOINT_CLASSES, { classExpressions: classExpressions.slice() });
const disjointUnion = (owlClass, classExpressions) =>
  _axiom(AxiomType.DISJOINT_UNION, { owlClass, classExpressions: classExpressions.slice() });
const classAssertion = (classExpression, individual) =>
  _axiom(AxiomType.CLASS_ASSERTION, { classExpression, individual });
const objectPropertyAssertion = (property, subject, object) =>
  _axiom(AxiomType.OBJECT_PROPERTY_ASSERTION, { property, subject, object });
const negativeObjectPropertyAssertion = (property, subject, object) =>
  _axiom(AxiomType.NEGATIVE_OBJECT_PROPERTY_ASSERTION, { property, subject, object });
const dataPropertyAssertion = (property, subject, lit) =>
  _axiom(AxiomType.DATA_PROPERTY_ASSERTION, { property, subject, object: lit, literal: lit });
const negativeDataPropertyAssertion = (property, subject, lit) =>
  _axiom(AxiomType.NEGATIVE_DATA_PROPERTY_ASSERTION, { property, subject, object: lit, literal: lit });
const sameIndividual = (individuals) =>
  _axiom(AxiomType.SAME_INDIVIDUAL, { individuals: individuals.slice() });
const differentIndividuals = (individuals) =>
  _axiom(AxiomType.DIFFERENT_INDIVIDUALS, { individuals: individuals.slice() });
const hasKey = (classExpression, propertyExpressions) =>
  _axiom(AxiomType.HAS_KEY, { classExpression, propertyExpressions: propertyExpressions.slice() });

/** The literal of a data property assertion (`literal` in protege-js, `object` in OWL API). */
function assertionLiteral(axiom) {
  return axiom.literal !== undefined ? axiom.literal : axiom.object;
}

module.exports = {
  // namespaces / IRIs
  OWL_NS, RDF_NS, RDFS_NS, XSD_NS,
  IRI_THING, IRI_NOTHING, IRI_RDFS_LITERAL,
  IRI_TOP_OBJECT_PROPERTY, IRI_BOTTOM_OBJECT_PROPERTY,
  IRI_TOP_DATA_PROPERTY, IRI_BOTTOM_DATA_PROPERTY,
  IRI_RDF_PLAIN_LITERAL, IRI_XSD_STRING,
  // type registries
  EntityType, ClassExpressionType, AxiomType, NON_LOGICAL_AXIOM_TYPES,
  // classes
  OWLLiteral, OWLEntity, OWLClass, OWLObjectProperty, OWLDataProperty,
  OWLNamedIndividual, OWLAnonymousIndividual, OWLDatatype, OWLObjectInverseOf,
  OWLObjectIntersectionOf, OWLObjectUnionOf, OWLObjectComplementOf,
  OWLObjectSomeValuesFrom, OWLObjectAllValuesFrom, OWLObjectHasValue,
  OWLObjectOneOf, OWLObjectHasSelf, OWLObjectCardinalityRestriction,
  OWLDataSomeValuesFrom, OWLDataAllValuesFrom, OWLDataHasValue,
  OWLDataCardinalityRestriction, OWLDataIntersectionOf, OWLDataUnionOf,
  OWLDataComplementOf, OWLDataOneOf, OWLDatatypeRestriction, OWLAxiom,
  // predicates / accessors
  iriString, exprType, isNamedClass, isObjectProperty, isDataProperty, isDatatype,
  isObjectInverseOf, isOWLThing, isOWLNothing, isTopDatatype, isBottomDataRange,
  isTopObjectProperty, isBottomObjectProperty, isTopDataProperty, isBottomDataProperty,
  operandOf, operandsOf, isAnonymousProperty, namedPropertyOf, inversePropertyOf,
  cardinalityFiller, isObjectCardinality, isDataCardinality,
  structuralKey, exprEquals, atomKey, assertionLiteral,
  // factory
  owlClass, objectProperty, dataProperty, namedIndividual, datatype,
  anonymousIndividual, literal, literalOf,
  owlThing, owlNothing, topDatatype,
  topObjectProperty, bottomObjectProperty, topDataProperty, bottomDataProperty,
  objectInverseOf, objectIntersectionOf, objectUnionOf, objectComplementOf,
  objectSomeValuesFrom, objectAllValuesFrom, objectHasValue, objectOneOf,
  objectHasSelf, objectMinCardinality, objectMaxCardinality, objectExactCardinality,
  dataSomeValuesFrom, dataAllValuesFrom, dataHasValue,
  dataMinCardinality, dataMaxCardinality, dataExactCardinality,
  dataIntersectionOf, dataUnionOf, dataComplementOf, dataOneOf, datatypeRestriction,
  // axiom factory
  subclassOf, equivalentClasses, disjointClasses, disjointUnion, classAssertion,
  objectPropertyAssertion, negativeObjectPropertyAssertion, dataPropertyAssertion,
  negativeDataPropertyAssertion, sameIndividual, differentIndividuals, hasKey
};
