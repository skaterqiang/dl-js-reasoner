'use strict';

// ---------------------------------------------------------------------------
// structural/OWLClausification.js
//
// Port of org.semanticweb.HermiT.structural.OWLClausification.
//
// Turns a normalized `OWLAxioms` set into a `DLOntology`: a set of DL-clauses
// (head₁ ∨ … ∨ headₙ ← body₁ ∧ … ∧ bodyₘ) plus positive and negative ground
// facts.
//
// == Shape of the input ==
// After `OWLNormalization`, every concept inclusion is a DISJUNCTION whose
// members are drawn from a small restricted grammar:
//
//   A | ¬A | {a₁,…,aₙ} | ¬{a} | ∃R.C | ∀R.C | ∀R.¬{a} | Self(R) | ¬Self(R)
//   ≥n R.C | ≤n R.C | ∃dp.D | ∀dp.D | ≥n dp.D | ≤n dp.D
//
// with C ∈ {A, ¬A} and D a literal data range. That grammar is what makes the
// clausifier a flat visitor with no recursion into sub-expressions: each
// disjunct becomes exactly one head atom or one body atom, and the whole
// disjunction becomes one clause.
//
// == Divergence from HermiT ==
// HermiT never materialises complex (non-simple) roles as edges; it unfolds
// role automata into `∀R.C` inclusions. This port instead emits one clause per
// complex inclusion — see `clausifyComplexObjectPropertyInclusions`.
// ---------------------------------------------------------------------------

const E = require('../owl/OWLExpressions');

const { OWLAxioms } = require('./OWLAxioms');
const { OWLNormalization, ontologyIRIOf } = require('./OWLNormalization');
const { BuiltInPropertyManager } = require('./BuiltInPropertyManager');
const { ObjectPropertyInclusionManager } = require('./ObjectPropertyInclusionManager');
const { OWLAxiomsExpressivity } = require('./OWLAxiomsExpressivity');
const { SWRLAtomType, isVariable, variableName, individualOf, literalOf } = require('./RuleNormalizer');

const { createAtom } = require('../model/Atom');
const { createDLClause } = require('../model/DLClause');
const { DLOntology } = require('../model/DLOntology');
const {
  createVariable, createIndividual, createAnonymousIndividual,
  createConstant, createAnonymousConstant, X, Y: P_Y, Z: P_Z
} = require('../model/Term');
const P = require('../model/DLPredicate');
const { groupOf, GROUP } = require('../datatypes/DatatypeReasoning');

const T = E.ClassExpressionType;
const AT = E.AxiomType;

const INTERNAL_DEFDATA_PREFIX = 'internal:defdata#';
const INTERNAL_UNKNOWN_DATATYPE_PREFIX = 'internal:unknown-datatype#';
const KB_IRI = 'urn:hermit:kb';

function invalidNormalForm(what) {
  return new Error(`Internal error: invalid normal form (${what}).`);
}

// ===========================================================================
// Static translation helpers (HermiT's protected static methods)
// ===========================================================================

/**
 * A | ¬A  →  AtomicConcept(A) | AtomicNegationConcept(A).
 * Port of `getLiteralConcept`.
 */
function getLiteralConcept(description) {
  const t = E.exprType(description);
  if (t === T.OWL_CLASS) return P.internAtomicConcept(E.iriString(description.iri || description.getIRI()));
  if (t === T.OBJECT_COMPLEMENT_OF) {
    const internal = E.operandOf(description);
    if (E.exprType(internal) !== T.OWL_CLASS) throw invalidNormalForm('complement of non-class');
    return P.internAtomicConcept(E.iriString(internal.iri || internal.getIRI())).getNegation();
  }
  throw invalidNormalForm(`getLiteralConcept(${description})`);
}

/**
 * R  →  AtomicRole(R);  R⁻  →  InverseRole(AtomicRole(R)).
 * Port of `getRole`.
 */
function getRole(objectPropertyExpression) {
  if (!E.isAnonymousProperty(objectPropertyExpression)) {
    const named = E.namedPropertyOf(objectPropertyExpression);
    return P.internAtomicRole(E.iriString(named.iri || named.getIRI()), false);
  }
  const internal = E.namedPropertyOf(objectPropertyExpression);
  if (!internal || E.isAnonymousProperty(internal)) throw invalidNormalForm('nested inverse role');
  return P.internAtomicRole(E.iriString(internal.iri || internal.getIRI()), false).getInverse();
}

/** Port of `getAtomicRole` for data properties. */
function getAtomicRole(dataPropertyExpression) {
  if (!E.isDataProperty(dataPropertyExpression)) {
    throw invalidNormalForm(`getAtomicRole(${dataPropertyExpression})`);
  }
  return P.internAtomicRole(
    E.iriString(dataPropertyExpression.iri || dataPropertyExpression.getIRI()), true);
}

/**
 * `R(first, second)` — for an ANONYMOUS property (an inverse) the arguments are
 * SWAPPED and the named role is used, so `R⁻(X,Y)` becomes the atom `R(Y,X)`.
 * InverseRole therefore never reaches the extension tables.
 * Port of the OWLObjectPropertyExpression overload of `getRoleAtom`.
 */
function getRoleAtom(objectProperty, first, second) {
  if (!E.isAnonymousProperty(objectProperty)) {
    const named = E.namedPropertyOf(objectProperty);
    const role = P.internAtomicRole(E.iriString(named.iri || named.getIRI()), false);
    return createAtom(role, first, second);
  }
  const internal = E.namedPropertyOf(objectProperty);
  if (!internal) throw new Error('Internal error: unsupported type of object property!');
  const role = P.internAtomicRole(E.iriString(internal.iri || internal.getIRI()), false);
  return createAtom(role, second, first);
}

/** Port of the OWLDataPropertyExpression overload of `getRoleAtom`. */
function getDataRoleAtom(dataProperty, first, second) {
  return createAtom(getAtomicRole(dataProperty), first, second);
}

/** Port of `getIndividual`. */
function getIndividual(individual) {
  const isAnon = typeof individual.isAnonymous === 'function'
    ? individual.isAnonymous()
    : individual.nodeId !== undefined;
  if (isAnon) {
    const id = individual.nodeId !== undefined
      ? individual.nodeId
      : String((individual.getID && individual.getID()) || individual);
    return createAnonymousIndividual(id);
  }
  return createIndividual(entityIRI(individual));
}

/** The IRI string of an OWL entity (`.iri` first, `getIRI()` as a fallback). */
function entityIRI(entity) {
  return E.iriString(entity.iri !== undefined ? entity.iri : entity.getIRI());
}

// ===========================================================================
// DataRangeConverter
// ===========================================================================

/**
 * Translates an OWL data range into a `LiteralDataRange` predicate.
 * Port of HermiT's inner class `DataRangeConverter`.
 */
class DataRangeConverter {
  /**
   * @param {object} [options]
   * @param {function(string):void} [options.warningMonitor]
   * @param {Set<string>} [options.definedDatatypeIRIs]
   * @param {Set<object>} [options.allUnknownDatatypeRestrictions]
   * @param {boolean} [options.ignoreUnsupportedDatatypes]
   */
  constructor(options = {}) {
    this.warningMonitor = options.warningMonitor || null;
    this.definedDatatypeIRIs = options.definedDatatypeIRIs || new Set();
    this.allUnknownDatatypeRestrictions = options.allUnknownDatatypeRestrictions || new Set();
    this.ignoreUnsupportedDatatypes = !!options.ignoreUnsupportedDatatypes;
  }

  /** @returns {object} a LiteralDataRange predicate */
  convertDataRange(dataRange) {
    const t = E.exprType(dataRange);
    switch (t) {
      case T.DATATYPE:
        return this._convertDatatype(dataRange);
      case T.DATA_COMPLEMENT_OF:
        return this.convertDataRange(E.operandOf(dataRange)).getNegation();
      case T.DATA_ONE_OF:
        return this._convertDataOneOf(dataRange);
      case T.DATATYPE_RESTRICTION:
        return this._convertDatatypeRestriction(dataRange);
      default:
        if (dataRange.lexicalValue !== undefined) return this.convertLiteral(dataRange);
        throw invalidNormalForm(`convertDataRange(${dataRange})`);
    }
  }

  _convertDatatype(object) {
    const datatypeURI = E.iriString(object.iri || object.getIRI());
    if (datatypeURI === P.IRI_LITERAL) return P.RDFS_LITERAL;
    if (datatypeURI.startsWith(INTERNAL_DEFDATA_PREFIX) || this.definedDatatypeIRIs.has(datatypeURI)) {
      return P.internInternalDatatype(datatypeURI);
    }
    const datatype = P.internDatatypeRestriction(datatypeURI, []);
    if (datatypeURI.startsWith(INTERNAL_UNKNOWN_DATATYPE_PREFIX)) {
      this.allUnknownDatatypeRestrictions.add(datatype);
    } else if (!this._isSupportedDatatype(datatypeURI)) {
      if (!this.ignoreUnsupportedDatatypes) {
        throw new UnsupportedDatatypeException(datatypeURI);
      }
      this._warn(`Ignoring unsupported datatype '${datatypeURI}'.`);
      this.allUnknownDatatypeRestrictions.add(datatype);
    }
    return datatype;
  }

  _convertDataOneOf(object) {
    const constants = new Set();
    for (const literal of E.operandsOf(object)) constants.add(this.convertLiteral(literal));
    return P.internConstantEnumeration([...constants]);
  }

  _convertDatatypeRestriction(object) {
    const dt = object.datatype;
    if (!E.isDatatype(dt)) {
      throw new Error('Datatype restrictions are supported only on OWL datatypes.');
    }
    const datatypeURI = E.iriString(dt.iri || dt.getIRI());
    const facets = object.facetRestrictions || [];
    if (datatypeURI === P.IRI_LITERAL) {
      if (facets.length > 0) throw new Error('rdfs:Literal does not support any facets.');
      return P.RDFS_LITERAL;
    }
    const facetDescriptors = facets.map(f => {
      const value = this.convertLiteral(f.value);
      return {
        facetIRI: E.iriString(f.facet),
        lexicalValue: value.lexicalValue,
        datatypeIRI: value.datatypeIRI
      };
    });
    const datatype = P.internDatatypeRestriction(datatypeURI, facetDescriptors);
    if (!this._isSupportedDatatype(datatypeURI)) {
      if (!this.ignoreUnsupportedDatatypes) throw new UnsupportedDatatypeException(datatypeURI);
      this._warn(`Ignoring unsupported datatype '${datatypeURI}'.`);
      this.allUnknownDatatypeRestrictions.add(datatype);
    }
    return datatype;
  }

  /** An OWLLiteral → a Constant term. */
  convertLiteral(object) {
    const lit = E.literal(object);
    try {
      if (lit.isRDFPlainLiteral && lit.isRDFPlainLiteral()) {
        // HermiT appends '@' + lang (empty when there is no language tag).
        return createConstant(`${lit.lexicalValue}@${lit.lang || ''}`, E.IRI_RDF_PLAIN_LITERAL);
      }
      const dtIri = lit.getDatatypeIRI
        ? E.iriString(lit.getDatatypeIRI())
        : E.iriString(lit.datatype);
      if (dtIri === E.IRI_RDF_PLAIN_LITERAL) {
        return createConstant(`${lit.lexicalValue}@${lit.lang || ''}`, E.IRI_RDF_PLAIN_LITERAL);
      }
      if (!this._isSupportedDatatype(dtIri)) throw new UnsupportedDatatypeException(dtIri);
      return createConstant(lit.lexicalValue, dtIri);
    } catch (err) {
      if (err instanceof UnsupportedDatatypeException && this.ignoreUnsupportedDatatypes) {
        this._warn(`Ignoring unsupported datatype '${lit}'.`);
        return createAnonymousConstant(lit.lexicalValue);
      }
      throw err;
    }
  }

  /**
   * Stand-in for HermiT's `DatatypeRegistry.validateDatatypeRestriction`: a
   * datatype is supported iff `DatatypeReasoning` knows its value space.
   */
  _isSupportedDatatype(iri) {
    if (iri === P.IRI_LITERAL) return true;
    return groupOf(iri) !== GROUP.OTHER;
  }

  _warn(message) {
    if (this.warningMonitor) this.warningMonitor(message);
  }
}

class UnsupportedDatatypeException extends Error {
  constructor(iri) {
    super(`Unsupported datatype: ${iri}`);
    this.name = 'UnsupportedDatatypeException';
  }
}

// ===========================================================================
// NormalizedAxiomClausifier
// ===========================================================================

/**
 * Accumulates the head and body atoms of the clause for one concept inclusion.
 * Each disjunct of the inclusion is visited in turn; a positive disjunct
 * yields a head atom and a negative one a body atom.
 * Port of HermiT's inner class `NormalizedAxiomClausifier`.
 */
class NormalizedAxiomClausifier {
  constructor(dataRangeConverter, positiveFacts) {
    this.dataRangeConverter = dataRangeConverter;
    this.headAtoms = [];
    this.bodyAtoms = [];
    this.positiveFacts = positiveFacts;
    this.yIndex = 0;
    this.zIndex = 0;
  }

  getDLClause() {
    const dlClause = createDLClause(this.headAtoms.slice(), this.bodyAtoms.slice());
    this.headAtoms.length = 0;
    this.bodyAtoms.length = 0;
    this.yIndex = 0;
    this.zIndex = 0;
    return dlClause;
  }

  ensureYNotZero() { if (this.yIndex === 0) this.yIndex++; }

  nextY() {
    const result = this.yIndex === 0 ? P_Y : createVariable(`Y${this.yIndex}`);
    this.yIndex++;
    return result;
  }

  nextZ() {
    const result = this.zIndex === 0 ? P_Z : createVariable(`Z${this.zIndex}`);
    this.zIndex++;
    return result;
  }

  /**
   * The internal concept naming a nominal, plus the ground fact asserting it.
   * Port of `getConceptForNominal`.
   */
  getConceptForNominal(individual) {
    const isAnon = typeof individual.isAnonymous === 'function'
      ? individual.isAnonymous()
      : individual.nodeId !== undefined;
    const result = isAnon
      ? P.internAtomicConcept(`internal:anon#${individual.nodeId}`)
      : P.internAtomicConcept(`internal:nom#${E.iriString(individual.iri || individual.getIRI())}`);
    this.positiveFacts.add(createAtom(result, getIndividual(individual)));
    return result;
  }

  /** Visit one disjunct of a concept inclusion. */
  visit(description) {
    switch (E.exprType(description)) {
      case T.OWL_CLASS:
        this.headAtoms.push(createAtom(
          P.internAtomicConcept(E.iriString(description.iri || description.getIRI())), X));
        return;

      case T.OBJECT_INTERSECTION_OF:
      case T.OBJECT_UNION_OF:
        throw invalidNormalForm(`connective in clause head: ${description}`);

      case T.OBJECT_COMPLEMENT_OF:
        this._visitComplement(E.operandOf(description));
        return;

      case T.OBJECT_ONE_OF:
        this._visitObjectOneOf(description);
        return;

      case T.OBJECT_SOME_VALUES_FROM:
        this._visitObjectSomeValuesFrom(description);
        return;

      case T.OBJECT_ALL_VALUES_FROM:
        this._visitObjectAllValuesFrom(description);
        return;

      case T.OBJECT_HAS_VALUE:
        throw invalidNormalForm('ObjectHasValue should have been simplified');

      case T.OBJECT_HAS_SELF:
        this.headAtoms.push(getRoleAtom(description.property, X, X));
        return;

      case T.OBJECT_MIN_CARDINALITY:
        this._visitObjectMinCardinality(description);
        return;

      case T.OBJECT_MAX_CARDINALITY:
        this._visitObjectMaxCardinality(description);
        return;

      case T.OBJECT_EXACT_CARDINALITY:
        throw invalidNormalForm('ObjectExactCardinality should have been split');

      case T.DATA_SOME_VALUES_FROM:
        this._visitDataSomeValuesFrom(description);
        return;

      case T.DATA_ALL_VALUES_FROM:
        this._visitDataAllValuesFrom(description);
        return;

      case T.DATA_HAS_VALUE:
        throw invalidNormalForm('DataHasValue should have been simplified');

      case T.DATA_MIN_CARDINALITY:
        this._visitDataMinCardinality(description);
        return;

      case T.DATA_MAX_CARDINALITY:
        this._visitDataMaxCardinality(description);
        return;

      case T.DATA_EXACT_CARDINALITY:
        throw invalidNormalForm('DataExactCardinality should have been split');

      default:
        throw invalidNormalForm(`unhandled disjunct ${description}`);
    }
  }

  /** ¬D as a body atom. */
  _visitComplement(description) {
    const t = E.exprType(description);
    if (t === T.OBJECT_HAS_SELF) {
      this.bodyAtoms.push(getRoleAtom(description.property, X, X));
      return;
    }
    if (t === T.OBJECT_ONE_OF && E.operandsOf(description).length === 1) {
      const individual = E.operandsOf(description)[0];
      this.bodyAtoms.push(createAtom(this.getConceptForNominal(individual), X));
      return;
    }
    if (t !== T.OWL_CLASS) throw invalidNormalForm(`complement of ${description}`);
    this.bodyAtoms.push(createAtom(
      P.internAtomicConcept(E.iriString(description.iri || description.getIRI())), X));
  }

  /** {a₁,…,aₙ} as a head: X ≈ Z₁ ∨ … ∨ X ≈ Zₙ with internal:nom#ai(Zi) in the body. */
  _visitObjectOneOf(object) {
    for (const individual of E.operandsOf(object)) {
      const z = this.nextZ();
      const conceptForNominal = this.getConceptForNominal(individual);
      this.headAtoms.push(createAtom(P.EQUALITY, X, z));
      this.bodyAtoms.push(createAtom(conceptForNominal, z));
    }
  }

  _visitObjectSomeValuesFrom(object) {
    const filler = object.filler;
    if (E.exprType(filler) === T.OBJECT_ONE_OF) {
      for (const individual of E.operandsOf(filler)) {
        const z = this.nextZ();
        this.bodyAtoms.push(createAtom(this.getConceptForNominal(individual), z));
        this.headAtoms.push(getRoleAtom(object.property, X, z));
      }
      return;
    }
    const toConcept = getLiteralConcept(filler);
    const onRole = getRole(object.property);
    const atLeastConcept = P.internAtLeastConcept(1, onRole, toConcept);
    if (!atLeastConcept.isAlwaysFalse()) this.headAtoms.push(createAtom(atLeastConcept, X));
  }

  _visitObjectAllValuesFrom(object) {
    const y = this.nextY();
    this.bodyAtoms.push(getRoleAtom(object.property, X, y));
    const filler = object.filler;
    const ft = E.exprType(filler);
    if (ft === T.OWL_CLASS) {
      const atomicConcept = P.internAtomicConcept(E.iriString(filler.iri || filler.getIRI()));
      if (!atomicConcept.isAlwaysFalse()) this.headAtoms.push(createAtom(atomicConcept, y));
    } else if (ft === T.OBJECT_ONE_OF) {
      for (const individual of E.operandsOf(filler)) {
        const zInd = this.nextZ();
        this.bodyAtoms.push(createAtom(this.getConceptForNominal(individual), zInd));
        this.headAtoms.push(createAtom(P.EQUALITY, y, zInd));
      }
    } else if (ft === T.OBJECT_COMPLEMENT_OF) {
      const operand = E.operandOf(filler);
      const ot = E.exprType(operand);
      if (ot === T.OWL_CLASS) {
        const internalAtomicConcept = P.internAtomicConcept(E.iriString(operand.iri || operand.getIRI()));
        if (!internalAtomicConcept.isAlwaysTrue()) this.bodyAtoms.push(createAtom(internalAtomicConcept, y));
      } else if (ot === T.OBJECT_ONE_OF && E.operandsOf(operand).length === 1) {
        const individual = E.operandsOf(operand)[0];
        this.bodyAtoms.push(createAtom(this.getConceptForNominal(individual), y));
      } else {
        throw invalidNormalForm(`∀R.¬${operand}`);
      }
    } else {
      throw invalidNormalForm(`∀R.${filler}`);
    }
  }

  _visitObjectMinCardinality(object) {
    const toConcept = getLiteralConcept(E.cardinalityFiller(object, false));
    const onRole = getRole(object.property);
    const atLeastConcept = P.internAtLeastConcept(object.cardinality, onRole, toConcept);
    if (!atLeastConcept.isAlwaysFalse()) this.headAtoms.push(createAtom(atLeastConcept, X));
  }

  /**
   * ≤n R.C becomes the "at most" clause: n+1 distinct R-successors of X that
   * are all C must be pairwise equal. The extra Y variables are guarded by
   * node-id ordering atoms so the clause is deterministic.
   */
  _visitObjectMaxCardinality(object) {
    const cardinality = object.cardinality;
    const onObjectProperty = object.property;
    const filler = E.cardinalityFiller(object, false);
    this.ensureYNotZero();

    let isPositive;
    let atomicConcept;
    const ft = E.exprType(filler);
    if (ft === T.OWL_CLASS) {
      isPositive = true;
      atomicConcept = P.internAtomicConcept(E.iriString(filler.iri || filler.getIRI()));
      if (atomicConcept.isAlwaysTrue()) atomicConcept = null;
    } else if (ft === T.OBJECT_COMPLEMENT_OF) {
      const internal = E.operandOf(filler);
      if (E.exprType(internal) !== T.OWL_CLASS) throw invalidNormalForm(`≤n R.${filler}`);
      isPositive = false;
      atomicConcept = P.internAtomicConcept(E.iriString(internal.iri || internal.getIRI()));
      if (atomicConcept.isAlwaysFalse()) atomicConcept = null;
    } else {
      throw invalidNormalForm(`≤n R.${filler}`);
    }

    const onRole = getRole(onObjectProperty);
    const toConcept = getLiteralConcept(filler);
    const annotatedEquality = P.internAnnotatedEquality(cardinality, onRole, toConcept);

    const yVars = [];
    for (let i = 0; i <= cardinality; i++) {
      const y = this.nextY();
      yVars.push(y);
      this.bodyAtoms.push(getRoleAtom(onObjectProperty, X, y));
      if (atomicConcept !== null) {
        const atom = createAtom(atomicConcept, y);
        if (isPositive) this.bodyAtoms.push(atom);
        else this.headAtoms.push(atom);
      }
    }
    // Node ID comparisons are not needed for functionality axioms, whose
    // effect is simulated by the way the rules are applied.
    if (yVars.length > 2) {
      for (let i = 0; i < yVars.length - 1; i++) {
        this.bodyAtoms.push(createAtom(P.NODE_ID_LESS_EQUAL_THAN, yVars[i], yVars[i + 1]));
      }
      this.bodyAtoms.push(createAtom(P.internNodeIDsAscendingOrEqual(yVars.length), ...yVars));
    }
    for (let i = 0; i < yVars.length; i++) {
      for (let j = i + 1; j < yVars.length; j++) {
        this.headAtoms.push(createAtom(annotatedEquality, yVars[i], yVars[j], X));
      }
    }
  }

  _visitDataSomeValuesFrom(object) {
    if (E.isBottomDataProperty(object.property)) return;
    const atomicRole = getAtomicRole(object.property);
    const literalRange = this.dataRangeConverter.convertDataRange(object.filler);
    const atLeastDataRange = P.internAtLeastDataRange(1, atomicRole, literalRange);
    if (!atLeastDataRange.isAlwaysFalse()) this.headAtoms.push(createAtom(atLeastDataRange, X));
  }

  _visitDataAllValuesFrom(object) {
    const literalRange = this.dataRangeConverter.convertDataRange(object.filler);
    if (E.isTopDataProperty(object.property)) {
      if (literalRange.isAlwaysFalse()) return; // ⊤ ⊑ ⊥
    }
    const y = this.nextY();
    this.bodyAtoms.push(getDataRoleAtom(object.property, X, y));
    if (literalRange.isNegatedInternalDatatype && literalRange.isNegatedInternalDatatype()) {
      const negatedRange = literalRange.getNegation();
      if (!negatedRange.isAlwaysTrue()) this.bodyAtoms.push(createAtom(negatedRange, y));
    } else if (!literalRange.isAlwaysFalse()) {
      this.headAtoms.push(createAtom(literalRange, y));
    }
  }

  _visitDataMinCardinality(object) {
    if (E.isBottomDataProperty(object.property) && object.cardinality !== 0) return;
    const atomicRole = getAtomicRole(object.property);
    const literalRange = this.dataRangeConverter.convertDataRange(
      E.cardinalityFiller(object, true));
    const atLeast = P.internAtLeastDataRange(object.cardinality, atomicRole, literalRange);
    if (!atLeast.isAlwaysFalse()) this.headAtoms.push(createAtom(atLeast, X));
  }

  _visitDataMaxCardinality(object) {
    const number = object.cardinality;
    const negatedDataRange = this.dataRangeConverter
      .convertDataRange(E.cardinalityFiller(object, true)).getNegation();
    this.ensureYNotZero();
    const yVars = [];
    for (let i = 0; i <= number; i++) {
      const y = this.nextY();
      yVars.push(y);
      this.bodyAtoms.push(getDataRoleAtom(object.property, X, y));
      if (negatedDataRange.isNegatedInternalDatatype && negatedDataRange.isNegatedInternalDatatype()) {
        const negated = negatedDataRange.getNegation();
        if (!negated.isAlwaysTrue()) this.bodyAtoms.push(createAtom(negated, y));
      } else if (!negatedDataRange.isAlwaysFalse()) {
        this.headAtoms.push(createAtom(negatedDataRange, y));
      }
    }
    for (let i = 0; i < yVars.length; i++) {
      for (let j = i + 1; j < yVars.length; j++) {
        this.headAtoms.push(createAtom(P.EQUALITY, yVars[i], yVars[j]));
      }
    }
  }
}

// ===========================================================================
// NormalizedDataRangeAxiomClausifier
// ===========================================================================

/**
 * Port of HermiT's inner class `NormalizedDataRangeAxiomClausifier`: turns a
 * data-range inclusion (a disjunction of literal data ranges) into a clause
 * over a single concrete-node variable X.
 */
class NormalizedDataRangeAxiomClausifier {
  constructor(dataRangeConverter, definedDatatypeIRIs) {
    this.dataRangeConverter = dataRangeConverter;
    this.definedDatatypeIRIs = definedDatatypeIRIs;
    this.headAtoms = [];
    this.bodyAtoms = [];
    this.yIndex = 0;
  }

  getDLClause() {
    const dlClause = createDLClause(this.headAtoms.slice(), this.bodyAtoms.slice());
    this.headAtoms.length = 0;
    this.bodyAtoms.length = 0;
    this.yIndex = 0;
    return dlClause;
  }

  ensureYNotZero() { if (this.yIndex === 0) this.yIndex++; }

  nextY() {
    const result = this.yIndex === 0 ? P_Y : createVariable(`Y${this.yIndex}`);
    this.yIndex++;
    return result;
  }

  visit(dataRange) {
    const t = E.exprType(dataRange);
    switch (t) {
      case T.DATATYPE: {
        const literalRange = this.dataRangeConverter.convertDataRange(dataRange);
        this.headAtoms.push(createAtom(literalRange, X));
        return;
      }
      case T.DATA_INTERSECTION_OF:
      case T.DATA_UNION_OF:
        throw invalidNormalForm(`data-range connective: ${dataRange}`);

      case T.DATA_COMPLEMENT_OF: {
        const description = E.operandOf(dataRange);
        const iri = E.isDatatype(description)
          ? E.iriString(description.iri || description.getIRI())
          : null;
        if (iri !== null && (iri.startsWith('internal:') || this.definedDatatypeIRIs.has(iri))) {
          this.bodyAtoms.push(createAtom(P.internInternalDatatype(iri), X));
          return;
        }
        const literalRange = this.dataRangeConverter.convertDataRange(dataRange);
        if (literalRange.isNegatedInternalDatatype && literalRange.isNegatedInternalDatatype()) {
          const negatedDatatype = literalRange.getNegation();
          if (!negatedDatatype.isAlwaysTrue()) this.bodyAtoms.push(createAtom(negatedDatatype, X));
        } else if (!literalRange.isAlwaysFalse()) {
          this.headAtoms.push(createAtom(literalRange, X));
        }
        return;
      }
      case T.DATA_ONE_OF: {
        const literalRange = this.dataRangeConverter.convertDataRange(dataRange);
        this.headAtoms.push(createAtom(literalRange, X));
        return;
      }
      case T.DATATYPE_RESTRICTION: {
        const literalRange = this.dataRangeConverter.convertDataRange(dataRange);
        this.headAtoms.push(createAtom(literalRange, X));
        return;
      }
      default:
        throw invalidNormalForm(`data range ${dataRange}`);
    }
  }
}

// ===========================================================================
// FactClausifier
// ===========================================================================

/** Port of HermiT's inner class `FactClausifier`. */
class FactClausifier {
  constructor(dataRangeConverter, positiveFacts, negativeFacts) {
    this.dataRangeConverter = dataRangeConverter;
    this.positiveFacts = positiveFacts;
    this.negativeFacts = negativeFacts;
  }

  visit(fact) {
    switch (fact.axiomType) {
      case AT.SAME_INDIVIDUAL: {
        const individuals = E.operandsOf(fact).length > 0 ? E.operandsOf(fact) : fact.individuals;
        for (let i = 0; i < individuals.length - 1; i++) {
          this.positiveFacts.add(createAtom(
            P.EQUALITY, getIndividual(individuals[i]), getIndividual(individuals[i + 1])));
        }
        return;
      }
      case AT.DIFFERENT_INDIVIDUALS: {
        const individuals = E.operandsOf(fact).length > 0 ? E.operandsOf(fact) : fact.individuals;
        for (let i = 0; i < individuals.length; i++) {
          for (let j = i + 1; j < individuals.length; j++) {
            this.positiveFacts.add(createAtom(
              P.INEQUALITY, getIndividual(individuals[i]), getIndividual(individuals[j])));
          }
        }
        return;
      }
      case AT.CLASS_ASSERTION:
        this._visitClassAssertion(fact);
        return;
      case AT.OBJECT_PROPERTY_ASSERTION:
        this.positiveFacts.add(getRoleAtom(
          fact.property, getIndividual(fact.subject), getIndividual(fact.object)));
        return;
      case AT.NEGATIVE_OBJECT_PROPERTY_ASSERTION:
        this.negativeFacts.add(getRoleAtom(
          fact.property, getIndividual(fact.subject), getIndividual(fact.object)));
        return;
      case AT.DATA_PROPERTY_ASSERTION: {
        const targetValue = this.dataRangeConverter.convertLiteral(E.assertionLiteral(fact));
        this.positiveFacts.add(getDataRoleAtom(
          fact.property, getIndividual(fact.subject), targetValue));
        return;
      }
      case AT.NEGATIVE_DATA_PROPERTY_ASSERTION: {
        const targetValue = this.dataRangeConverter.convertLiteral(E.assertionLiteral(fact));
        this.negativeFacts.add(getDataRoleAtom(
          fact.property, getIndividual(fact.subject), targetValue));
        return;
      }
      default:
        throw invalidNormalForm(`fact type ${fact.axiomType}`);
    }
  }

  _visitClassAssertion(object) {
    const description = object.classExpression;
    const individual = getIndividual(object.individual);
    const t = E.exprType(description);

    if (t === T.OWL_CLASS) {
      this.positiveFacts.add(createAtom(
        P.internAtomicConcept(E.iriString(description.iri || description.getIRI())), individual));
      return;
    }
    if (t === T.OBJECT_HAS_SELF) {
      this.positiveFacts.add(getRoleAtom(description.property, individual, individual));
      return;
    }
    if (t === T.OBJECT_COMPLEMENT_OF) {
      const operand = E.operandOf(description);
      const ot = E.exprType(operand);
      if (ot === T.OWL_CLASS) {
        this.negativeFacts.add(createAtom(
          P.internAtomicConcept(E.iriString(operand.iri || operand.getIRI())), individual));
        return;
      }
      if (ot === T.OBJECT_HAS_SELF) {
        this.negativeFacts.add(getRoleAtom(operand.property, individual, individual));
        return;
      }
    }
    throw invalidNormalForm(`ClassAssertion(${description}, ${object.individual})`);
  }
}

// ===========================================================================
// NormalizedRuleClausifier
// ===========================================================================

/**
 * Port of HermiT's inner class `NormalizedRuleClausifier`. Description graphs
 * are not supported, so every object property in a rule is "non-graph" and the
 * graph/non-graph disambiguation loop collapses to a single pass.
 */
class NormalizedRuleClausifier {
  /**
   * @param {Set<object>} objectPropertiesOccurringInOWLAxioms
   * @param {DataRangeConverter} dataRangeConverter
   * @param {Set<object>} dlClauses
   */
  constructor(objectPropertiesOccurringInOWLAxioms, dataRangeConverter, dlClauses) {
    this.objectPropertiesOccurringInOWLAxioms = objectPropertiesOccurringInOWLAxioms;
    this.dataRangeConverter = dataRangeConverter;
    this.dlClauses = dlClauses;
    this.headAtoms = [];
    this.bodyAtoms = [];
    this.abstractVariables = new Set();
  }

  processRules(rules) {
    for (const rule of rules) this.clausify(rule, true);
  }

  /**
   * @param {import('./OWLAxioms').DisjunctiveRule} rule
   * @param {boolean} restrictToNamed guard abstract variables with internal:nam#Named
   */
  clausify(rule, restrictToNamed) {
    this.headAtoms.length = 0;
    this.bodyAtoms.length = 0;
    this.abstractVariables.clear();
    for (const atom of rule.body) this.bodyAtoms.push(this.visitAtom(atom));
    for (const atom of rule.head) this.headAtoms.push(this.visitAtom(atom));
    if (restrictToNamed) {
      for (const variable of this.abstractVariables) {
        this.bodyAtoms.push(createAtom(P.INTERNAL_NAMED, variable));
      }
    }
    this.dlClauses.add(createDLClause(this.headAtoms.slice(), this.bodyAtoms.slice()));
    this.headAtoms.length = 0;
    this.bodyAtoms.length = 0;
    this.abstractVariables.clear();
  }

  visitAtom(atom) {
    switch (atom.type) {
      case SWRLAtomType.CLASS: {
        const predicate = atom.classExpression;
        if (!E.isNamedClass(predicate)) {
          throw new Error(
            'Internal error: SWRL rule class atoms should be normalized to contain only named classes, '
            + `but this class atom has a complex concept: ${predicate}`);
        }
        const variable = toVariable(atom.arg);
        this.abstractVariables.add(variable);
        return createAtom(P.internAtomicConcept(E.iriString(predicate.iri || predicate.getIRI())), variable);
      }
      case SWRLAtomType.DATA_RANGE: {
        const variable = toVariable(atom.arg);
        const literalRange = this.dataRangeConverter.convertDataRange(atom.dataRange);
        return createAtom(literalRange, variable);
      }
      case SWRLAtomType.OBJECT_PROPERTY: {
        const v1 = toVariable(atom.arg1);
        const v2 = toVariable(atom.arg2);
        this.abstractVariables.add(v1);
        this.abstractVariables.add(v2);
        return getRoleAtom(atom.property, v1, v2);
      }
      case SWRLAtomType.DATA_PROPERTY: {
        const v1 = toVariable(atom.arg1);
        const v2 = toVariable(atom.arg2);
        this.abstractVariables.add(v1);
        return getDataRoleAtom(atom.property, v1, v2);
      }
      case SWRLAtomType.SAME_AS:
        return createAtom(P.EQUALITY, toVariable(atom.arg1), toVariable(atom.arg2));
      case SWRLAtomType.DIFFERENT_FROM:
        return createAtom(P.INEQUALITY, toVariable(atom.arg1), toVariable(atom.arg2));
      default:
        throw new Error('Rules with SWRL built-in atoms are not yet supported.');
    }
  }
}

function toVariable(argument) {
  if (isVariable(argument)) return createVariable(variableName(argument));
  throw new Error('Internal error: all arguments in a SWRL rule should have been normalized to variables.');
}

// ===========================================================================
// OWLClausification
// ===========================================================================

class OWLClausification {
  /**
   * @param {object} [configuration]
   * @param {function(string):void} [configuration.warningMonitor]
   * @param {boolean} [configuration.ignoreUnsupportedDatatypes]
   */
  constructor(configuration = {}) {
    this.configuration = configuration;
  }

  /**
   * The full HermiT front end: normalize → built-in properties → role
   * hierarchy → expressivity → clausify.
   *
   * @param {object|object[]} ontology a protege-js OWLOntology, or an array of axioms
   * @param {object} [options]
   * @param {number} [options.firstReplacementIndex]
   * @returns {{dlOntology: DLOntology, axioms: OWLAxioms,
   *            objectPropertyInclusionManager: ObjectPropertyInclusionManager,
   *            expressivity: OWLAxiomsExpressivity}}
   */
  preprocessAndClausify(ontology, options = {}) {
    const ontologyIRI = options.ontologyIRI
      || (ontology && !Array.isArray(ontology) ? ontologyIRIOf(ontology) : null)
      || KB_IRI;

    const axioms = new OWLAxioms();
    const normalization = new OWLNormalization(axioms, options.firstReplacementIndex || 0);

    // HermiT walks the import closure; protege-js's OntologyLoader already
    // resolves imports into a single ontology when `loadWithImports` is used,
    // so a single pass suffices. An array of ontologies is also accepted.
    const ontologies = Array.isArray(ontology) && ontology.length > 0 && _looksLikeOntology(ontology[0])
      ? ontology
      : [ontology];
    for (const o of ontologies) normalization.processOntology(o);

    const builtInPropertyManager = new BuiltInPropertyManager();
    builtInPropertyManager.axiomatizeBuiltInPropertiesAsNeeded(axioms);

    // Computes axioms.complexObjectPropertyExpressions.
    const objectPropertyInclusionManager = new ObjectPropertyInclusionManager(axioms);
    objectPropertyInclusionManager.rewriteNegativeObjectPropertyAssertions(
      null, axioms, normalization.definitionsCount);
    objectPropertyInclusionManager.rewriteAxioms(null, axioms, 0);

    const axiomsExpressivity = new OWLAxiomsExpressivity(axioms);
    const dlOntology = this.clausify(ontologyIRI, axioms, axiomsExpressivity);

    return { dlOntology, axioms, objectPropertyInclusionManager, expressivity: axiomsExpressivity };
  }

  /**
   * Port of HermiT's `clausify`.
   * @param {string} ontologyIRI
   * @param {OWLAxioms} axioms
   * @param {OWLAxiomsExpressivity} axiomsExpressivity
   * @returns {DLOntology}
   */
  clausify(ontologyIRI, axioms, axiomsExpressivity) {
    const dlClauses = new Set();
    const positiveFacts = new Set();
    const negativeFacts = new Set();
    const allUnknownDatatypeRestrictions = new Set();

    const dataRangeConverter = new DataRangeConverter({
      warningMonitor: this.configuration.warningMonitor,
      definedDatatypeIRIs: axioms.definedDatatypesIRIs,
      allUnknownDatatypeRestrictions,
      ignoreUnsupportedDatatypes: this.configuration.ignoreUnsupportedDatatypes
    });

    // ---- simple role inclusions: R(X,Y) → S(X,Y) ----
    for (const inclusion of axioms.simpleObjectPropertyInclusions) {
      const subRoleAtom = getRoleAtom(inclusion[0], X, P_Y);
      const superRoleAtom = getRoleAtom(inclusion[1], X, P_Y);
      dlClauses.add(createDLClause([superRoleAtom], [subRoleAtom]));
    }

    // ---- complex role inclusions: chain clauses (see header comment) ----
    for (const clause of clausifyComplexObjectPropertyInclusions(axioms.complexObjectPropertyInclusions)) {
      dlClauses.add(clause);
    }

    // ---- data property inclusions ----
    for (const inclusion of axioms.dataPropertyInclusions) {
      const subProp = getDataRoleAtom(inclusion[0], X, P_Y);
      const superProp = getDataRoleAtom(inclusion[1], X, P_Y);
      dlClauses.add(createDLClause([superProp], [subProp]));
    }

    // ---- asymmetric: R(X,Y) ∧ R(Y,X) → ⊥ ----
    for (const objectPropertyExpression of axioms.asymmetricObjectProperties) {
      const roleAtom = getRoleAtom(objectPropertyExpression, X, P_Y);
      const inverseRoleAtom = getRoleAtom(objectPropertyExpression, P_Y, X);
      dlClauses.add(createDLClause([], [roleAtom, inverseRoleAtom]));
    }

    // ---- reflexive: ⊤(X) → R(X,X) ----
    for (const objectPropertyExpression of axioms.reflexiveObjectProperties) {
      const roleAtom = getRoleAtom(objectPropertyExpression, X, X);
      const bodyAtom = createAtom(P.THING, X);
      dlClauses.add(createDLClause([roleAtom], [bodyAtom]));
    }

    // ---- irreflexive: R(X,X) → ⊥ ----
    for (const objectPropertyExpression of axioms.irreflexiveObjectProperties) {
      dlClauses.add(createDLClause([], [getRoleAtom(objectPropertyExpression, X, X)]));
    }

    // ---- disjoint object properties ----
    for (const properties of axioms.disjointObjectProperties) {
      for (let i = 0; i < properties.length; i++) {
        for (let j = i + 1; j < properties.length; j++) {
          const atomI = getRoleAtom(properties[i], X, P_Y);
          const atomJ = getRoleAtom(properties[j], X, P_Y);
          dlClauses.add(createDLClause([], [atomI, atomJ]));
        }
      }
    }

    // ---- ⊥ data property ----
    if (_containsBottomDataProperty(axioms.dataProperties)) {
      dlClauses.add(createDLClause([], [createAtom(P.BOTTOM_DATA_ROLE, X, P_Y)]));
    }

    // ---- disjoint data properties: dp1(X,Y) ∧ dp2(X,Z) → Y ≠ Z ----
    for (const properties of axioms.disjointDataProperties) {
      for (let i = 0; i < properties.length; i++) {
        for (let j = i + 1; j < properties.length; j++) {
          const atomI = getDataRoleAtom(properties[i], X, P_Y);
          const atomJ = getDataRoleAtom(properties[j], X, P_Z);
          const atomIJ = createAtom(P.INEQUALITY, P_Y, P_Z);
          dlClauses.add(createDLClause([atomIJ], [atomI, atomJ]));
        }
      }
    }

    // ---- concept inclusions ----
    const clausifier = new NormalizedAxiomClausifier(dataRangeConverter, positiveFacts);
    for (const inclusion of axioms.conceptInclusions) {
      for (const description of inclusion) clausifier.visit(description);
      const dlClause = clausifier.getDLClause();
      dlClauses.add(dlClause.getSafeVersion(P.THING));
    }

    // ---- data range inclusions ----
    const dataRangeClausifier = new NormalizedDataRangeAxiomClausifier(
      dataRangeConverter, axioms.definedDatatypesIRIs);
    for (const inclusion of axioms.dataRangeInclusions) {
      for (const description of inclusion) dataRangeClausifier.visit(description);
      const dlClause = dataRangeClausifier.getDLClause();
      dlClauses.add(dlClause.getSafeVersion(P.RDFS_LITERAL));
    }

    // ---- keys ----
    for (const hasKey of axioms.hasKeys) dlClauses.add(clausifyKey(hasKey));

    // ---- facts ----
    const factClausifier = new FactClausifier(dataRangeConverter, positiveFacts, negativeFacts);
    for (const fact of axioms.facts) factClausifier.visit(fact);

    // ---- signature ----
    const atomicConcepts = new Set();
    for (const owlClass of axioms.classes) {
      atomicConcepts.add(P.internAtomicConcept(entityIRI(owlClass)));
    }

    const individuals = new Set();
    const tagNamedIndividuals = axioms.hasKeys.length > 0 || axioms.rules.length > 0;
    for (const owlIndividual of axioms.namedIndividuals) {
      // `getIndividual`, not `createIndividual`: the reasoner's query axioms
      // (and any ABox with blank nodes) put *anonymous* individuals into
      // `axioms.namedIndividuals`, and those have no IRI.
      const individual = getIndividual(owlIndividual);
      individuals.add(individual);
      // All named individuals are tagged with a concept, so that keys/rules are
      // only applied to them.
      if (tagNamedIndividuals && !individual.isAnonymous()) {
        positiveFacts.add(createAtom(P.INTERNAL_NAMED, individual));
      }
    }

    const atomicObjectRoles = new Set();
    for (const owlObjectProperty of axioms.objectProperties) {
      atomicObjectRoles.add(P.internAtomicRole(entityIRI(owlObjectProperty), false));
    }

    const complexObjectRoles = new Set();
    for (const objectPropertyExpression of axioms.complexObjectPropertyExpressions) {
      complexObjectRoles.add(getRole(objectPropertyExpression));
    }

    const atomicDataRoles = new Set();
    for (const owlDataProperty of axioms.dataProperties) {
      atomicDataRoles.add(getAtomicRole(owlDataProperty));
    }

    // ---- SWRL rules ----
    if (axioms.rules.length > 0) {
      new NormalizedRuleClausifier(
        axioms.objectPropertiesOccurringInOWLAxioms, dataRangeConverter, dlClauses
      ).processRules(axioms.rules);
    }

    return new DLOntology({
      ontologyIRI,
      dlClauses: [...dlClauses],
      positiveFacts: [...positiveFacts],
      negativeFacts: [...negativeFacts],
      atomicConcepts,
      atomicObjectRoles,
      complexObjectRoles,
      atomicDataRoles,
      allUnknownDatatypeRestrictions,
      hasUnknownDatatypeRestrictions: allUnknownDatatypeRestrictions.size > 0,
      definedDatatypesIRIs: axioms.definedDatatypesIRIs,
      individuals,
      hasInverseRoles: axiomsExpressivity.hasInverseRoles,
      hasAtMostRestrictions: axiomsExpressivity.hasAtMostRestrictions,
      hasNominals: axiomsExpressivity.hasNominals,
      hasDatatypes: axiomsExpressivity.hasDatatypes
    });
  }
}

function _looksLikeOntology(x) {
  return x && typeof x === 'object' && !x.axiomType
    && (typeof x.getAxioms === 'function' || x._axioms !== undefined);
}

function _containsBottomDataProperty(dataProperties) {
  for (const p of dataProperties) if (E.isBottomDataProperty(p)) return true;
  return false;
}

/**
 * Emit one clause per complex object property inclusion.
 *
 * `R1∘…∘Rn ⊑ S` becomes
 *
 *   R1(X,Y1) ∧ R2(Y1,Y2) ∧ … ∧ Rn(Yn-1,Yn) → S(X,Yn)
 *
 * which is exactly the hyperresolution rule that derives the S-edge whenever
 * the chain is present. Transitivity `R∘R ⊑ R` is the n = 2 special case.
 */
function clausifyComplexObjectPropertyInclusions(complexObjectPropertyInclusions) {
  const clauses = [];
  let index = 0;
  for (const inclusion of complexObjectPropertyInclusions) {
    const subs = inclusion.subObjectProperties;
    const sup = inclusion.superObjectProperty;
    if (subs.length === 0) continue;

    const bodyAtoms = [];
    let previous = X;
    const used = [];
    for (let i = 0; i < subs.length; i++) {
      const next = i === subs.length - 1
        ? createVariable(`W${index}`)
        : createVariable(`W${index}_${i + 1}`);
      bodyAtoms.push(getRoleAtom(subs[i], previous, next));
      used.push(next);
      previous = next;
    }
    const headAtom = getRoleAtom(sup, X, previous);
    clauses.push(createDLClause([headAtom], bodyAtoms));
    index++;
  }
  return clauses;
}

/**
 * Port of HermiT's `clausifyKey`.
 *
 * Key(C, dp₁ … dpₙ op₁ … opₘ) becomes
 *
 *   X1 ≈ X2 ∨ dp₁(X1,Y1) ≠ dp₁(X2,Y2) ∨ …
 *   ← internal:nam#Named(X1) ∧ internal:nam#Named(X2) ∧ C(X1) ∧ C(X2)
 *     ∧ op(X1,Yk) ∧ op(X2,Yk) ∧ internal:nam#Named(Yk) ∧ …
 */
function clausifyKey(object) {
  const headAtoms = [];
  const bodyAtoms = [];
  const X1 = createVariable('X1');
  const X2 = createVariable('X2');

  headAtoms.push(createAtom(P.EQUALITY, X1, X2));
  // Keys only work on datatypes and named individuals.
  bodyAtoms.push(createAtom(P.INTERNAL_NAMED, X1));
  bodyAtoms.push(createAtom(P.INTERNAL_NAMED, X2));

  // After normalization the key's class expression is a concept name or the
  // negation of one.
  const description = object.classExpression;
  const t = E.exprType(description);
  if (t === T.OWL_CLASS) {
    if (!E.isOWLThing(description)) {
      const concept = P.internAtomicConcept(E.iriString(description.iri || description.getIRI()));
      bodyAtoms.push(createAtom(concept, X1));
      bodyAtoms.push(createAtom(concept, X2));
    }
  } else if (t === T.OBJECT_COMPLEMENT_OF) {
    const internal = E.operandOf(description);
    if (E.exprType(internal) !== T.OWL_CLASS) throw invalidNormalForm('HasKey class expression');
    const concept = P.internAtomicConcept(E.iriString(internal.iri || internal.getIRI()));
    headAtoms.push(createAtom(concept, X1));
    headAtoms.push(createAtom(concept, X2));
  } else {
    throw invalidNormalForm('HasKey class expression');
  }

  // protege-js stores object and data properties in one flat array.
  const propertyExpressions = object.propertyExpressions || [];
  let yIndex = 1;
  for (const p of propertyExpressions) {
    if (E.isDataProperty(p)) {
      // Data properties go to the body with different variables; the head
      // gets an atom asserting inequality between the data values.
      const y = createVariable(`Y${yIndex++}`);
      bodyAtoms.push(getDataRoleAtom(p, X1, y));
      const y2 = createVariable(`Y${yIndex++}`);
      bodyAtoms.push(getDataRoleAtom(p, X2, y2));
      headAtoms.push(createAtom(P.INEQUALITY, y, y2));
    } else {
      // Object properties share one variable, and the key value must be named.
      const y = createVariable(`Y${yIndex++}`);
      bodyAtoms.push(getRoleAtom(p, X1, y));
      bodyAtoms.push(getRoleAtom(p, X2, y));
      bodyAtoms.push(createAtom(P.INTERNAL_NAMED, y));
    }
  }

  return createDLClause(headAtoms, bodyAtoms);
}

/**
 * Convenience wrapper matching HermiT's static entry point.
 * @returns {DLOntology}
 */
function createDLOntology(ontology, configuration = {}) {
  return new OWLClausification(configuration).preprocessAndClausify(ontology).dlOntology;
}

module.exports = {
  OWLClausification,
  createDLOntology,
  DataRangeConverter,
  UnsupportedDatatypeException,
  NormalizedAxiomClausifier,
  NormalizedDataRangeAxiomClausifier,
  FactClausifier,
  NormalizedRuleClausifier,
  clausifyKey,
  clausifyComplexObjectPropertyInclusions,
  getLiteralConcept,
  getRole,
  getAtomicRole,
  getRoleAtom,
  getDataRoleAtom,
  getIndividual,
  toVariable
};
