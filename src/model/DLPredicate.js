'use strict';

// ---------------------------------------------------------------------------
// model/DLPredicate.js — the predicate hierarchy the calculus reasons in.
//
// Mirrors org.semanticweb.HermiT.model.{DLPredicate, AtomicConcept,
// AtomicNegationConcept, AtLeast, AtLeastConcept, AtLeastDataRange,
// LiteralDataRange, DatatypeRestriction, InternalDatatype, ConstantEnumeration,
// AtomicNegationDataRange, AtomicRole, InverseRole, NegatedAtomicRole,
// Equality, Inequality, AnnotatedEquality, NodeIDLessEqualThan,
// NodeIDsAscendingOrEqual}.
//
// Every predicate is interned so that identity (===) is equality. This is the
// single most important performance property of the whole model layer: the
// extension tables, blocking signatures and clause indexes all rely on it.
// ---------------------------------------------------------------------------

const PREDICATE_KIND = Object.freeze({
  ATOMIC_CONCEPT: 'AtomicConcept',
  ATOMIC_NEGATION_CONCEPT: 'AtomicNegationConcept',
  AT_LEAST_CONCEPT: 'AtLeastConcept',
  AT_LEAST_DATA_RANGE: 'AtLeastDataRange',
  LITERAL_DATA_RANGE: 'LiteralDataRange',
  DATATYPE_RESTRICTION: 'DatatypeRestriction',
  INTERNAL_DATATYPE: 'InternalDatatype',
  CONSTANT_ENUMERATION: 'ConstantEnumeration',
  ATOMIC_NEGATION_DATA_RANGE: 'AtomicNegationDataRange',
  ATOMIC_ROLE: 'AtomicRole',
  INVERSE_ROLE: 'InverseRole',
  NEGATED_ATOMIC_ROLE: 'NegatedAtomicRole',
  EQUALITY: 'Equality',
  INEQUALITY: 'Inequality',
  ANNOTATED_EQUALITY: 'AnnotatedEquality',
  NODE_ID_LESS_EQUAL_THAN: 'NodeIDLessEqualThan',
  NODE_IDS_ASCENDING_OR_EQUAL: 'NodeIDsAscendingOrEqual'
});

// Well-known IRIs.
const OWL = 'http://www.w3.org/2002/07/owl#';
const RDF = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#';
const RDFS = 'http://www.w3.org/2000/01/rdf-schema#';
const XSD = 'http://www.w3.org/2001/XMLSchema#';

const IRI_THING = OWL + 'Thing';
const IRI_NOTHING = OWL + 'Nothing';
const IRI_LITERAL = RDFS + 'Literal';
const IRI_TOP_OBJECT_PROPERTY = OWL + 'topObjectProperty';
const IRI_BOTTOM_OBJECT_PROPERTY = OWL + 'bottomObjectProperty';
const IRI_TOP_DATA_PROPERTY = OWL + 'topDataProperty';
const IRI_BOTTOM_DATA_PROPERTY = OWL + 'bottomDataProperty';

/** Abstract base for all predicates. */
class DLPredicate {
  constructor(kind) {
    this.kind = kind;
  }
  getArity() { return 1; }
  toString() { return this.kind; }
  /**
   * The negation of this predicate, for the unary concept/data-range
   * predicates. Mirrors HermiT's `LiteralConcept.getNegation()` /
   * `LiteralDataRange.getNegation()`. Overridden below.
   */
  getNegation() {
    throw new Error(`${this.kind} has no negation.`);
  }
}

// ===========================================================================
// Concepts (unary, object-side)
// ===========================================================================

/** A named class. THING (owl:Thing) and NOTHING (owl:Nothing) are special. */
class AtomicConcept extends DLPredicate {
  constructor(iri) {
    super(PREDICATE_KIND.ATOMIC_CONCEPT);
    this.iri = iri;
  }
  isAlwaysTrue() { return this.iri === IRI_THING; }
  isAlwaysFalse() { return this.iri === IRI_NOTHING; }
  /**
   * ¬owl:Thing is owl:Nothing and vice versa — NOT an `AtomicNegationConcept`.
   * HermiT special-cases this; without it `¬Thing(a)` never clashes and every
   * `trueOf(topNode)` test in domain/range/instance retrieval wrongly succeeds.
   */
  getNegation() {
    if (this.isAlwaysTrue()) return NOTHING;
    if (this.isAlwaysFalse()) return THING;
    return internAtomicNegationConcept(this);
  }
  toString() { return this.iri; }
}

/** ¬A — negation of an atomic concept. */
class AtomicNegationConcept extends DLPredicate {
  constructor(atomicConcept) {
    super(PREDICATE_KIND.ATOMIC_NEGATION_CONCEPT);
    this.atomicConcept = atomicConcept;
  }
  isAlwaysTrue() { return this.atomicConcept.isAlwaysFalse(); }
  isAlwaysFalse() { return this.atomicConcept.isAlwaysTrue(); }
  getNegation() { return this.atomicConcept; }
  toString() { return `not(${this.atomicConcept})`; }
}

// ===========================================================================
// Data ranges (unary, data-side)
// ===========================================================================

/**
 * A concrete data range: a datatype IRI (e.g. xsd:integer). rdfs:Literal is the
 * "always true" data range.
 */
class LiteralDataRange extends DLPredicate {
  constructor(iri) {
    super(PREDICATE_KIND.LITERAL_DATA_RANGE);
    this.iri = iri;
  }
  isAlwaysTrue() { return this.iri === IRI_LITERAL; }
  isAlwaysFalse() { return false; }
  getNegation() { return internAtomicNegationDataRange(this); }
  toString() { return this.iri; }
}

/** ¬DR — negation of an atomic data range. */
class AtomicNegationDataRange extends DLPredicate {
  constructor(dataRange) {
    super(PREDICATE_KIND.ATOMIC_NEGATION_DATA_RANGE);
    this.dataRange = dataRange;
  }
  isAlwaysTrue() { return this.dataRange.isAlwaysFalse(); }
  isAlwaysFalse() { return this.dataRange.isAlwaysTrue(); }
  getNegation() { return this.dataRange; }
  /** HermiT's `isNegatedInternalDatatype()`. */
  isNegatedInternalDatatype() { return this.dataRange instanceof InternalDatatype; }
  toString() { return `not(${this.dataRange})`; }
}

/** A datatype with facet restrictions, e.g. xsd:integer[minInclusive 0]. */
class DatatypeRestriction extends DLPredicate {
  constructor(datatypeIRI, facets) {
    super(PREDICATE_KIND.DATATYPE_RESTRICTION);
    this.datatypeIRI = datatypeIRI;
    // facets: array of { facetIRI, lexicalValue, datatypeIRI }
    this.facets = facets || [];
  }
  isAlwaysTrue() { return false; }
  isAlwaysFalse() { return false; }
  getNegation() { return internAtomicNegationDataRange(this); }
  toString() {
    const fr = this.facets.map(f => `${f.facetIRI} "${f.lexicalValue}"`).join(' ');
    return `${this.datatypeIRI}[${fr}]`;
  }
}

/** An internal datatype introduced by normalisation (fresh name for a data range). */
class InternalDatatype extends DLPredicate {
  constructor(iri) {
    super(PREDICATE_KIND.INTERNAL_DATATYPE);
    this.iri = iri;
  }
  isAlwaysTrue() { return false; }
  isAlwaysFalse() { return false; }
  getNegation() { return internAtomicNegationDataRange(this); }
  toString() { return this.iri; }
}

/** A oneOf enumeration of constants: { "a", "b", 3 }. */
class ConstantEnumeration extends DLPredicate {
  constructor(constants) {
    super(PREDICATE_KIND.CONSTANT_ENUMERATION);
    this.constants = constants || []; // Constant[]
  }
  isAlwaysTrue() { return false; }
  isAlwaysFalse() { return this.constants.length === 0; }
  getNegation() { return internAtomicNegationDataRange(this); }
  toString() { return `{${this.constants.map(String).join(', ')}}`; }
}

// ===========================================================================
// Existential concepts (unary): ≥ n R.C
// ===========================================================================

/** ≥ n R.toConcept over an object role. */
class AtLeastConcept extends DLPredicate {
  constructor(number, onRole, toConcept) {
    super(PREDICATE_KIND.AT_LEAST_CONCEPT);
    this.number = number;
    this.onRole = onRole;       // Role
    this.toConcept = toConcept; // LiteralConcept (AtomicConcept | AtomicNegationConcept | data range)
  }
  isAlwaysFalse() {
    return this.number > 0 && (this.onRole.isAlwaysFalse() || this.toConcept.isAlwaysFalse());
  }
  isAlwaysTrue() { return this.number === 0; }
  toString() { return `atLeast(${this.number} ${this.onRole} ${this.toConcept})`; }
}

/** ≥ n R.dataRange over a data role. */
class AtLeastDataRange extends DLPredicate {
  constructor(number, onRole, toDataRange) {
    super(PREDICATE_KIND.AT_LEAST_DATA_RANGE);
    this.number = number;
    this.onRole = onRole;           // AtomicRole (data property)
    this.toDataRange = toDataRange; // LiteralDataRange
  }
  isAlwaysFalse() {
    return this.number > 0 && (this.onRole.isAlwaysFalse() || this.toDataRange.isAlwaysFalse());
  }
  isAlwaysTrue() { return this.number === 0; }
  toString() { return `atLeast(${this.number} ${this.onRole} ${this.toDataRange})`; }
}

// ===========================================================================
// Roles (binary)
// ===========================================================================

/** A named object or data property. */
class AtomicRole extends DLPredicate {
  constructor(iri, isData) {
    super(PREDICATE_KIND.ATOMIC_ROLE);
    this.iri = iri;
    this.isData = !!isData;
  }
  getArity() { return 2; }
  isAlwaysTrue() {
    return this.iri === IRI_TOP_OBJECT_PROPERTY || this.iri === IRI_TOP_DATA_PROPERTY;
  }
  isAlwaysFalse() {
    return this.iri === IRI_BOTTOM_OBJECT_PROPERTY || this.iri === IRI_BOTTOM_DATA_PROPERTY;
  }
  isObjectRole() { return !this.isData; }
  isDataRole() { return this.isData; }
  /**
   * R⁻ — the inverse role. Mirrors HermiT's `AtomicRole.getInverse()`, which
   * returns `this` for the two extreme OBJECT roles: `owl:topObjectProperty` and
   * `owl:bottomObjectProperty` are their own inverses.
   *
   * That special case is load-bearing, not cosmetic. `classifyObjectProperties`
   * builds `conceptsForRoles` / `rolesForConcepts` maps keyed by the roles it
   * actually enumerates, and `QuasiOrderClassificationForRoles` mirrors every
   * subsumption through `conceptsForRoles.get(rolesForConcepts.get(c).getInverse())`.
   * If `TOP_OBJECT_ROLE.getInverse()` returned a distinct `InverseRole`, that
   * lookup would yield `undefined` and the mirrored edge would be garbage.
   *
   * The IRI comparison is used rather than identity against the exported
   * `TOP_OBJECT_ROLE` / `BOTTOM_OBJECT_ROLE` constants only because those are
   * declared further down this module; roles are interned, so the two are
   * equivalent. The DATA roles are deliberately not special-cased, matching
   * HermiT — OWL 2 has no inverse data properties, so the case never arises.
   */
  getInverse() {
    if (this.iri === IRI_TOP_OBJECT_PROPERTY || this.iri === IRI_BOTTOM_OBJECT_PROPERTY) return this;
    return internInverseRole(this);
  }
  toString() { return this.iri; }
}

/** R⁻ — the inverse of a role. inv(R)(Y,X) ≡ R(X,Y). */
class InverseRole extends DLPredicate {
  constructor(inverseRole) {
    super(PREDICATE_KIND.INVERSE_ROLE);
    this.inverseRole = inverseRole; // the role this is the inverse of
  }
  getArity() { return 2; }
  isAlwaysTrue() { return this.inverseRole.isAlwaysTrue(); }
  isAlwaysFalse() { return this.inverseRole.isAlwaysFalse(); }
  /** (R⁻)⁻ = R. */
  getInverse() { return this.inverseRole; }
  toString() { return `inv(${this.inverseRole})`; }
}

/** ¬R — negation of a role (used in disjoint-properties axioms). */
class NegatedAtomicRole extends DLPredicate {
  constructor(atomicRole) {
    super(PREDICATE_KIND.NEGATED_ATOMIC_ROLE);
    this.atomicRole = atomicRole;
  }
  getArity() { return 2; }
  isAlwaysTrue() { return this.atomicRole.isAlwaysFalse(); }
  isAlwaysFalse() { return this.atomicRole.isAlwaysTrue(); }
  toString() { return `not(${this.atomicRole})`; }
}

// ===========================================================================
// Equality / inequality / ordering predicates
// ===========================================================================

/** ≈ — the built-in equality predicate. */
class Equality extends DLPredicate {
  constructor() { super(PREDICATE_KIND.EQUALITY); }
  getArity() { return 2; }
  toString() { return '='; }
}

/** ≉ — the built-in inequality predicate. */
class Inequality extends DLPredicate {
  constructor() { super(PREDICATE_KIND.INEQUALITY); }
  getArity() { return 2; }
  toString() { return '!='; }
}

/**
 * An equality "annotated" with the at-most context (cardinality, role, concept)
 * that produced it. Drives the merge step for ≤ n R.C restrictions. Arity 3:
 * (y_i, y_j, X).
 */
class AnnotatedEquality extends DLPredicate {
  constructor(cardinality, onRole, toConcept) {
    super(PREDICATE_KIND.ANNOTATED_EQUALITY);
    this.cardinality = cardinality;
    this.onRole = onRole;
    this.toConcept = toConcept;
  }
  getArity() { return 3; }
  toString() { return `=[${this.cardinality} ${this.onRole} ${this.toConcept}]`; }
}

/** Node-ID ordering used when translating at-most restrictions. Arity 2. */
class NodeIDLessEqualThan extends DLPredicate {
  constructor() { super(PREDICATE_KIND.NODE_ID_LESS_EQUAL_THAN); }
  getArity() { return 2; }
  toString() { return '<='; }
}

/** "All argument node IDs strictly ascending or all equal". Variable arity. */
class NodeIDsAscendingOrEqual extends DLPredicate {
  constructor(arity) {
    super(PREDICATE_KIND.NODE_IDS_ASCENDING_OR_EQUAL);
    this._arity = arity;
  }
  getArity() { return this._arity; }
  toString() { return 'ascendingOrEqual'; }
}

// ===========================================================================
// Interning managers — one per predicate type.
// ===========================================================================

function makeInterner(keyFn, ctor) {
  const map = new Map();
  return function intern(...args) {
    const key = keyFn(...args);
    let v = map.get(key);
    if (!v) {
      v = ctor(...args);
      map.set(key, v);
    }
    return v;
  };
}

const internAtomicConcept = makeInterner(
  (iri) => iri,
  (iri) => new AtomicConcept(iri)
);

const internAtomicNegationConcept = makeInterner(
  (c) => c.iri,
  (c) => new AtomicNegationConcept(c)
);

const internLiteralDataRange = makeInterner(
  (iri) => iri,
  (iri) => new LiteralDataRange(iri)
);

const internAtomicNegationDataRange = makeInterner(
  (dr) => dr.iri || dr.toString(),
  (dr) => new AtomicNegationDataRange(dr)
);

const internDatatypeRestriction = makeInterner(
  (iri, facets) => iri + '|' + (facets || []).map(f => `${f.facetIRI}:${f.lexicalValue}`).join(','),
  (iri, facets) => new DatatypeRestriction(iri, facets)
);

const internInternalDatatype = makeInterner(
  (iri) => iri,
  (iri) => new InternalDatatype(iri)
);

const internConstantEnumeration = makeInterner(
  (constants) => constants.map(c => c.toString()).join(','),
  (constants) => new ConstantEnumeration(constants)
);

const internAtomicRole = makeInterner(
  (iri, isData) => iri + '|' + (isData ? 'D' : 'O'),
  (iri, isData) => new AtomicRole(iri, isData)
);

const internInverseRole = makeInterner(
  (r) => 'inv|' + r.toString(),
  (r) => new InverseRole(r)
);

const internNegatedAtomicRole = makeInterner(
  (r) => 'not|' + r.toString(),
  (r) => new NegatedAtomicRole(r)
);

const internAtLeastConcept = makeInterner(
  (n, role, concept) => `${n}|${role.toString()}|${concept.toString()}`,
  (n, role, concept) => new AtLeastConcept(n, role, concept)
);

const internAtLeastDataRange = makeInterner(
  (n, role, dr) => `${n}|${role.toString()}|${dr.toString()}`,
  (n, role, dr) => new AtLeastDataRange(n, role, dr)
);

const internAnnotatedEquality = makeInterner(
  (card, role, concept) => `${card}|${role.toString()}|${concept.toString()}`,
  (card, role, concept) => new AnnotatedEquality(card, role, concept)
);

const internNodeIDsAscendingOrEqual = makeInterner(
  (arity) => arity,
  (arity) => new NodeIDsAscendingOrEqual(arity)
);

// Singletons.
const EQUALITY = new Equality();
const INEQUALITY = new Inequality();
const NODE_ID_LESS_EQUAL_THAN = new NodeIDLessEqualThan();

// Distinguished atomic concepts / roles.
const THING = internAtomicConcept(IRI_THING);
const NOTHING = internAtomicConcept(IRI_NOTHING);
/** internal:nam#Named — asserted on every named individual (nominal handling). */
const INTERNAL_NAMED = internAtomicConcept('internal:nam#Named');
const LITERAL = internLiteralDataRange(IRI_LITERAL);
/**
 * rdfs:Literal as an *internal* datatype. HermiT uses this (not
 * LiteralDataRange) for the "always true" data range on concrete nodes, so
 * containsDataRangeAssertion can short-circuit on it.
 */
const RDFS_LITERAL = internInternalDatatype(IRI_LITERAL);
const TOP_OBJECT_ROLE = internAtomicRole(IRI_TOP_OBJECT_PROPERTY, false);
const BOTTOM_OBJECT_ROLE = internAtomicRole(IRI_BOTTOM_OBJECT_PROPERTY, false);
const TOP_DATA_ROLE = internAtomicRole(IRI_TOP_DATA_PROPERTY, true);
const BOTTOM_DATA_ROLE = internAtomicRole(IRI_BOTTOM_DATA_PROPERTY, true);

module.exports = {
  PREDICATE_KIND,
  DLPredicate,
  // concepts
  AtomicConcept,
  AtomicNegationConcept,
  AtLeastConcept,
  AtLeastDataRange,
  // data ranges
  LiteralDataRange,
  AtomicNegationDataRange,
  DatatypeRestriction,
  InternalDatatype,
  ConstantEnumeration,
  // roles
  AtomicRole,
  InverseRole,
  NegatedAtomicRole,
  // equality / ordering
  Equality,
  Inequality,
  AnnotatedEquality,
  NodeIDLessEqualThan,
  NodeIDsAscendingOrEqual,
  // interners
  internAtomicConcept,
  internAtomicNegationConcept,
  internLiteralDataRange,
  internAtomicNegationDataRange,
  internDatatypeRestriction,
  internInternalDatatype,
  internConstantEnumeration,
  internAtomicRole,
  internInverseRole,
  internNegatedAtomicRole,
  internAtLeastConcept,
  internAtLeastDataRange,
  internAnnotatedEquality,
  internNodeIDsAscendingOrEqual,
  // singletons & distinguished
  EQUALITY,
  INEQUALITY,
  NODE_ID_LESS_EQUAL_THAN,
  THING,
  NOTHING,
  INTERNAL_NAMED,
  LITERAL,
  RDFS_LITERAL,
  TOP_OBJECT_ROLE,
  BOTTOM_OBJECT_ROLE,
  TOP_DATA_ROLE,
  BOTTOM_DATA_ROLE,
  // IRI constants
  IRI_THING,
  IRI_NOTHING,
  IRI_LITERAL,
  IRI_TOP_OBJECT_PROPERTY,
  IRI_BOTTOM_OBJECT_PROPERTY,
  IRI_TOP_DATA_PROPERTY,
  IRI_BOTTOM_DATA_PROPERTY,
  OWL,
  RDF,
  RDFS,
  XSD
};
