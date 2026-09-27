'use strict';

// ---------------------------------------------------------------------------
// structural/OWLNormalization.js — the structural transformation.
//
// Port of org.semanticweb.HermiT.structural.OWLNormalization (1388 lines of
// Java, six inner visitors). It rewrites an OWL 2 ontology into the flat,
// clause-shaped intermediate representation `OWLAxioms`, which
// `OWLClausification` then turns into DL-clauses.
//
// What the transformation does, in one paragraph: every axiom becomes a
// DISJUNCTION of class expressions (`A ⊑ B` → `[¬A, B]`), all negations are
// pushed inward (NNF), exact cardinalities are split into min/max, value
// restrictions become `∃R.{v}`, and every remaining non-atomic sub-expression
// is replaced by a fresh named class `internal:def#N` (or datatype
// `internal:defdata#N`) plus a defining inclusion. After this pass the only
// class expressions left are exactly the ones `NormalizedAxiomClausifier`
// knows how to translate, one atom at a time.
//
// Departure from the tableau paper (same as HermiT): the concepts
// `∃R.{a₁…aₙ}`, `∀R.{a₁…aₙ}` and `∀R.¬{a}` are deliberately kept intact —
// they are clausified more efficiently than their expanded forms.
// ---------------------------------------------------------------------------

const E = require('../owl/OWLExpressions');
const EM = require('./ExpressionManager');
const { RuleNormalizer, Rule2FactConverter } = require('./RuleNormalizer');

const T = E.ClassExpressionType;
const AT = E.AxiomType;

// ===========================================================================
// Shape predicates used throughout the transformation
// ===========================================================================

/** `C` or `¬C` — the only class expressions that need no definition. */
function isSimple(d) {
  const t = E.exprType(d);
  if (t === T.OWL_CLASS) return true;
  return t === T.OBJECT_COMPLEMENT_OF && E.exprType(E.operandOf(d)) === T.OWL_CLASS;
}

function isAtomicDataRange(dr) {
  const t = E.exprType(dr);
  return t === T.DATATYPE || t === T.DATATYPE_RESTRICTION || t === T.DATA_ONE_OF;
}
function isNegatedAtomicDataRange(dr) {
  return E.exprType(dr) === T.DATA_COMPLEMENT_OF && isAtomicDataRange(E.operandOf(dr));
}
function isLiteralDataRange(dr) {
  return isAtomicDataRange(dr) || isNegatedAtomicDataRange(dr);
}
function isNominal(d) { return E.exprType(d) === T.OBJECT_ONE_OF; }
function isNegatedOneNominal(d) {
  if (E.exprType(d) !== T.OBJECT_COMPLEMENT_OF) return false;
  const operand = E.operandOf(d);
  return E.exprType(operand) === T.OBJECT_ONE_OF && E.operandsOf(operand).length === 1;
}

function isAnonymousIndividual(ind) {
  if (!ind) return false;
  if (typeof ind.isAnonymous === 'function') return !!ind.isAnonymous();
  return ind.nodeId !== undefined;
}

function containsAnonymousIndividuals(individuals) {
  return individuals.some(isAnonymousIndividual);
}

// ===========================================================================
// Polarity (HermiT's PLVisitor)
//
// Decides whether a fresh definition can be introduced *positively*. If an
// expression is "positive literal"-ish, `internal:def#N ≡ expr` is emitted as
// `def`; otherwise the definition is negated so that the defining clause stays
// Horn-ish. This matters for the determinism of the resulting calculus.
// ===========================================================================

function isPositivePolarity(d) {
  switch (E.exprType(d)) {
    case T.OWL_CLASS:
      return !E.isOWLThing(d) && !E.isOWLNothing(d);
    case T.OBJECT_INTERSECTION_OF:
    case T.OBJECT_UNION_OF:
      return E.operandsOf(d).some(isPositivePolarity);
    case T.OBJECT_COMPLEMENT_OF:
      return false;
    case T.OBJECT_ONE_OF:
    case T.OBJECT_SOME_VALUES_FROM:
    case T.OBJECT_HAS_VALUE:
    case T.OBJECT_HAS_SELF:
      return true;
    case T.OBJECT_ALL_VALUES_FROM:
      return isPositivePolarity(d.filler);
    case T.OBJECT_MIN_CARDINALITY:
      return d.cardinality > 0;
    case T.OBJECT_MAX_CARDINALITY:
    case T.OBJECT_EXACT_CARDINALITY:
      return d.cardinality > 0
        ? true
        : isPositivePolarity(EM.getComplementNNF(E.cardinalityFiller(d, false)));
    case T.DATA_SOME_VALUES_FROM:
    case T.DATA_ALL_VALUES_FROM:
    case T.DATA_HAS_VALUE:
    case T.DATA_MIN_CARDINALITY:
    case T.DATA_MAX_CARDINALITY:
    case T.DATA_EXACT_CARDINALITY:
      return true;
    default:
      return false;
  }
}

// ===========================================================================
// OWLNormalization
// ===========================================================================

class OWLNormalization {
  /**
   * @param {import('./OWLAxioms').OWLAxioms} axioms target accumulator
   * @param {number} [firstReplacementIndex] offset for fresh `internal:def#N`
   *        names. Used when several ontologies are normalized into one axiom
   *        set, or when the reasoner needs to add its own definitions later
   *        (e.g. `ObjectPropertyInclusionManager.rewriteNegativeObjectPropertyAssertions`).
   */
  constructor(axioms, firstReplacementIndex = 0) {
    this.axioms = axioms;
    this.firstReplacementIndex = firstReplacementIndex;
    /** structuralKey(expr) → the expression that defines it */
    this.definitions = new Map();
    /** structuralKey(OWLObjectOneOf) → OWLClass */
    this.definitionsForNegativeNominals = new Map();
    /** structuralKey(dataRange) → OWLDatatype */
    this.dataRangeDefinitions = new Map();
  }

  /** Number of fresh definitions introduced so far. */
  get definitionsCount() { return this.definitions.size; }

  // ---- entry points --------------------------------------------------------

  /**
   * @param {object} ontology a protege-js OWLOntology (or anything with
   *        getAxioms()/getClassesInSignature()/…)
   */
  processOntology(ontology) {
    for (const c of _signature(ontology, 'getClassesInSignature')) this.axioms.classes.add(c);
    for (const p of _signature(ontology, 'getObjectPropertiesInSignature')) this.axioms.objectProperties.add(p);
    for (const p of _signature(ontology, 'getDataPropertiesInSignature')) this.axioms.dataProperties.add(p);
    for (const i of _signature(ontology, 'getIndividualsInSignature')) this.axioms.namedIndividuals.add(i);
    // `includeDeclarations` is true here: protege-js computes signatures from
    // only a subset of axiom types, so declarations can be missed. Harvesting
    // them keeps the entity sets complete (they drive reporting and entailment
    // checking, where a missing entity would be a silent error).
    this.processAxioms(logicalAxiomsOf(ontology, true));
    return this;
  }

  _noteEntity(entity) {
    const et = entity.entityType || (entity.getEntityType && entity.getEntityType());
    if (et === E.EntityType.CLASS) this.axioms.classes.add(entity);
    else if (et === E.EntityType.OBJECT_PROPERTY) this.axioms.objectProperties.add(entity);
    else if (et === E.EntityType.DATA_PROPERTY) this.axioms.dataProperties.add(entity);
    else if (et === E.EntityType.NAMED_INDIVIDUAL) this.axioms.namedIndividuals.add(entity);
  }

  /**
   * @param {Iterable<object>} axioms
   * @param {Iterable<object>} [extraOntologies] already-loaded imports
   */
  processAxioms(axioms) {
    const state = {
      classInclusions: [],   // worklist of class-expression disjunctions
      dataRangeInclusions: [], // worklist of data-range disjunctions
      rules: []              // raw SWRL rules
    };

    for (const axiom of axioms) this._visitAxiom(axiom, state);

    // All axioms are now in NNF and converted into disjunctions where possible;
    // exact cardinalities are rewritten into at-least/at-most, etc.
    // Rules with multiple head atoms are split (Lloyd-Topor transformation).
    const ruleNormalizer = new RuleNormalizer(this, state.classInclusions, state.dataRangeInclusions);
    for (const rule of state.rules) ruleNormalizer.normalize(rule);

    // Now simplify the disjuncts (eliminate redundant conjuncts/disjuncts) and
    // introduce fresh atomic concepts for the complex ones.
    this.normalizeInclusions(state.classInclusions, state.dataRangeInclusions);
    return this;
  }

  // ---- NNF/simplification shorthands ---------------------------------------

  positive(d) { return EM.positive(d); }
  negative(d) { return EM.negative(d); }
  positiveDataRange(dr) { return EM.getDataRangeNNF(EM.getDataRangeSimplified(dr)); }
  negativeDataRange(dr) { return EM.getDataRangeComplementNNF(EM.getDataRangeSimplified(dr)); }

  // ---- definition introduction ---------------------------------------------

  /**
   * Return (creating if necessary) the class expression that *is* `description`
   * by definition, together with the defining inclusion.
   *
   * Mirrors `getDefinitionFor(OWLClassExpression, boolean[], boolean)`.
   *
   * @param {object} description
   * @param {boolean} [forcePositive] when true the definition is always a plain
   *        OWLClass (never a complement) — used by `getClassFor`.
   * @returns {{definition:object, alreadyExists:boolean, definingInclusion:(object[]|null)}}
   */
  getDefinitionFor(description, forcePositive = false) {
    const key = E.structuralKey(description);
    let definition = this.definitions.get(key);
    if (definition === undefined || (forcePositive && !E.isNamedClass(definition))) {
      definition = E.owlClass(`internal:def#${this.definitions.size + this.firstReplacementIndex}`);
      if (!forcePositive && !isPositivePolarity(description)) {
        definition = E.objectComplementOf(definition);
      }
      this.definitions.set(key, definition);
      return {
        definition,
        alreadyExists: false,
        definingInclusion: [this.negative(definition), description]
      };
    }
    return { definition, alreadyExists: true, definingInclusion: null };
  }

  /**
   * Positive-only variant: always returns a named OWLClass.
   * Mirrors `getClassFor`.
   */
  getClassFor(description) {
    const r = this.getDefinitionFor(description, true);
    return { definition: r.definition, alreadyExists: r.alreadyExists, definingInclusion: r.definingInclusion };
  }

  /**
   * Return (creating if necessary) the datatype that *is* `dataRange` by
   * definition. Mirrors `getDefinitionFor(OWLDataRange, boolean[])`.
   */
  getDefinitionForDataRange(dataRange) {
    const key = E.structuralKey(dataRange);
    let definition = this.dataRangeDefinitions.get(key);
    if (definition === undefined) {
      definition = E.datatype(`internal:defdata#${this.dataRangeDefinitions.size}`);
      this.dataRangeDefinitions.set(key, definition);
      return {
        definition,
        alreadyExists: false,
        definingInclusion: [this.negativeDataRange(definition), dataRange]
      };
    }
    return { definition, alreadyExists: true, definingInclusion: null };
  }

  /**
   * Fresh class for `¬{a₁,…,aₙ}`. Mirrors `getDefinitionForNegativeNominal`.
   * The individuals are asserted to be instances of the fresh class, and the
   * expression `¬{…}` becomes `¬C` — a plain negated atomic concept.
   */
  getDefinitionForNegativeNominal(nominal) {
    const key = E.structuralKey(nominal);
    let definition = this.definitionsForNegativeNominals.get(key);
    if (definition === undefined) {
      definition = E.owlClass(`internal:nnq#${this.definitionsForNegativeNominals.size}`);
      this.definitionsForNegativeNominals.set(key, definition);
      return { definition, alreadyExists: false };
    }
    return { definition, alreadyExists: true };
  }

  // ===========================================================================
  // normalizeInclusions
  // ===========================================================================

  /**
   * Drive the two worklists to a fixed point.
   * @param {object[][]} inclusions class-expression disjunctions (consumed)
   * @param {object[][]} dataRangeInclusions data-range disjunctions (consumed)
   */
  normalizeInclusions(inclusions, dataRangeInclusions) {
    // ---- class expressions ----
    while (inclusions.length > 0) {
      const raw = inclusions.pop();
      const simplified = EM.getNNF(EM.getSimplified(E.objectUnionOf(raw)));
      if (E.isOWLThing(simplified)) continue;

      if (E.exprType(simplified) === T.OBJECT_UNION_OF) {
        const descriptions = E.operandsOf(simplified).slice();
        if (!this._distributeUnionOverAnd(descriptions, inclusions, false)
          && !this._optimizedNegativeOneOfTranslation(descriptions, this.axioms.facts)) {
          const normalized = descriptions.map(d => this.normalizeClassExpression(d, inclusions, dataRangeInclusions));
          this.axioms.conceptInclusions.push(normalized);
        }
      } else if (E.exprType(simplified) === T.OBJECT_INTERSECTION_OF) {
        for (const conjunct of E.operandsOf(simplified)) inclusions.push([conjunct]);
      } else {
        this.axioms.conceptInclusions.push(
          [this.normalizeClassExpression(simplified, inclusions, dataRangeInclusions)]);
      }
    }

    // ---- data ranges ----
    // NOTE: HermiT's Java version has a bug here — it pops
    // `dataRangeInclusions.remove(classExpressionNormalizer.m_newDataRangeInclusions.size()-1)`
    // (an index into the *wrong* list) and, in the `else` branch, pushes the
    // normalized single data range back onto the worklist instead of into
    // `m_axioms.m_dataRangeInclusions`, which loops forever. The corrected
    // behaviour is implemented below.
    while (dataRangeInclusions.length > 0) {
      const raw = dataRangeInclusions.pop();
      const simplified = EM.getDataRangeNNF(EM.getDataRangeSimplified(E.dataUnionOf(raw)));
      if (E.isTopDatatype(simplified)) continue;

      if (E.exprType(simplified) === T.DATA_UNION_OF) {
        const descriptions = E.operandsOf(simplified).slice();
        if (!this._distributeUnionOverAnd(descriptions, dataRangeInclusions, true)) {
          const normalized = descriptions.map(d => this.normalizeDataRange(d, dataRangeInclusions));
          this.axioms.dataRangeInclusions.push(normalized);
        }
      } else if (E.exprType(simplified) === T.DATA_INTERSECTION_OF) {
        for (const conjunct of E.operandsOf(simplified)) dataRangeInclusions.push([conjunct]);
      } else {
        this.axioms.dataRangeInclusions.push([this.normalizeDataRange(simplified, dataRangeInclusions)]);
      }
    }
  }

  /**
   * `(A⊓B) ∨ C ∨ D` is equivalent to `(A∨C∨D)` and `(B∨C∨D)`; pushing the
   * union inward like this keeps clauses small. Only applies when *exactly one*
   * disjunct is a non-simple conjunction.
   *
   * @returns {boolean} true if the distribution was applied (caller must then
   *          discard `descriptions`).
   */
  _distributeUnionOverAnd(descriptions, inclusions, isDataSide) {
    let andIndex = -1;
    for (let index = 0; index < descriptions.length; index++) {
      const description = descriptions[index];
      const simple = isDataSide ? isLiteralDataRange(description) : isSimple(description);
      if (!simple) {
        const andType = isDataSide ? T.DATA_INTERSECTION_OF : T.OBJECT_INTERSECTION_OF;
        if (E.exprType(description) === andType) {
          if (andIndex === -1) andIndex = index;
          else return false;
        } else {
          return false;
        }
      }
    }
    if (andIndex === -1) return false;
    const conjuncts = E.operandsOf(descriptions[andIndex]);
    for (const conjunct of conjuncts) {
      const newDescriptions = descriptions.slice();
      newDescriptions[andIndex] = conjunct;
      inclusions.push(newDescriptions);
    }
    return true;
  }

  /**
   * `¬{a₁,…,aₙ} ∨ C` (with C simple) is just `C(a₁) ∧ … ∧ C(aₙ)`: turn it into
   * facts instead of a clause. This is a big win for nominals-heavy ontologies.
   *
   * @returns {boolean} true if the translation was applied.
   */
  _optimizedNegativeOneOfTranslation(descriptions, facts) {
    if (descriptions.length !== 2) return false;
    let nominal = null;
    let other = null;
    for (let i = 0; i < 2; i++) {
      const d = descriptions[i];
      if (E.exprType(d) === T.OBJECT_COMPLEMENT_OF && E.exprType(E.operandOf(d)) === T.OBJECT_ONE_OF) {
        nominal = E.operandOf(d);
        other = descriptions[1 - i];
        break;
      }
    }
    if (nominal === null) return false;
    if (!isSimple(other)) return false;
    for (const individual of E.operandsOf(nominal)) {
      facts.push(E.classAssertion(other, individual));
      this.axioms.namedIndividuals.add(individual);
    }
    return true;
  }

  // ===========================================================================
  // ClassExpressionNormalizer
  // ===========================================================================

  /**
   * Replace every non-atomic sub-expression of `object` with a fresh named
   * class, queueing the defining inclusions onto the worklists.
   *
   * @param {object} object a class expression already in simplified NNF
   * @param {object[][]} newInclusions class-expression worklist
   * @param {object[][]} newDataRangeInclusions data-range worklist
   */
  normalizeClassExpression(object, newInclusions, newDataRangeInclusions) {
    const define = (expr) => {
      const r = this.getDefinitionFor(expr);
      if (!r.alreadyExists) newInclusions.push(r.definingInclusion);
      return r.definition;
    };
    const defineDataRange = (dr) => {
      const r = this.getDefinitionForDataRange(dr);
      if (!r.alreadyExists) newDataRangeInclusions.push(r.definingInclusion);
      return r.definition;
    };

    switch (E.exprType(object)) {
      case T.OWL_CLASS:
        return object;

      case T.OBJECT_INTERSECTION_OF: {
        // HermiT queues one inclusion per conjunct: `D ⊑ Ci` for each i, i.e.
        // `{¬D, Ci}`. Combined with the `{D, ¬C1, …, ¬Cn}` direction produced
        // by `getDefinitionFor`'s polarity handling this yields `D ≡ C1⊓…⊓Cn`.
        const r = this.getDefinitionFor(object);
        if (!r.alreadyExists) {
          for (const description of E.operandsOf(object)) {
            newInclusions.push([this.negative(r.definition), description]);
          }
        }
        return r.definition;
      }

      case T.OBJECT_UNION_OF:
        throw new Error('OR should be broken down at the outermost level');

      case T.OBJECT_COMPLEMENT_OF: {
        const operand = E.operandOf(object);
        if (isNominal(operand)) {
          const { definition, alreadyExists } = this.getDefinitionForNegativeNominal(operand);
          if (!alreadyExists) {
            for (const individual of E.operandsOf(operand)) {
              this.axioms.facts.push(E.classAssertion(definition, individual));
              this.axioms.namedIndividuals.add(individual);
            }
          }
          return E.objectComplementOf(definition);
        }
        return object;
      }

      case T.OBJECT_ONE_OF: {
        for (const ind of E.operandsOf(object)) {
          if (isAnonymousIndividual(ind)) {
            throw new Error(
              `Error: The class expression ${object} contains anonymous individuals, `
              + 'which is not allowed in OWL 2.');
          }
          this.axioms.namedIndividuals.add(ind);
        }
        return object;
      }

      case T.OBJECT_SOME_VALUES_FROM: {
        this.axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(object.property));
        const filler = object.filler;
        // Keeping ObjectOneOf fillers intact is an optimization: they clausify
        // into a disjunction of role atoms instead of an existential.
        if (isSimple(filler) || isNominal(filler)) return object;
        return E.objectSomeValuesFrom(object.property, define(filler));
      }

      case T.OBJECT_ALL_VALUES_FROM: {
        this.axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(object.property));
        const filler = object.filler;
        if (isSimple(filler) || isNominal(filler) || isNegatedOneNominal(filler)) return object;
        return E.objectAllValuesFrom(object.property, define(filler));
      }

      case T.OBJECT_HAS_VALUE:
        throw new Error('Internal error: object value restrictions should have been simplified.');

      case T.OBJECT_HAS_SELF:
        this.axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(object.property));
        return object;

      case T.OBJECT_MIN_CARDINALITY: {
        this.axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(object.property));
        const filler = E.cardinalityFiller(object, false);
        if (isSimple(filler)) return object;
        return E.objectMinCardinality(object.cardinality, object.property, define(filler));
      }

      case T.OBJECT_MAX_CARDINALITY: {
        this.axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(object.property));
        const filler = E.cardinalityFiller(object, false);
        if (isSimple(filler)) return object;
        // ≤n.C is normalized via ¬C so that the definition is introduced in the
        // polarity that keeps the clause deterministic.
        const complementDescription = EM.getComplementNNF(filler);
        const definition = define(complementDescription);
        return E.objectMaxCardinality(object.cardinality, object.property, EM.getComplementNNF(definition));
      }

      case T.OBJECT_EXACT_CARDINALITY:
        throw new Error('Internal error: exact object cardinality restrictions should have been simplified.');

      case T.DATA_SOME_VALUES_FROM: {
        this._checkTopDataPropertyUse(object.property, object);
        const filler = object.filler;
        if (isLiteralDataRange(filler)) return E.dataSomeValuesFrom(object.property, filler);
        return E.dataSomeValuesFrom(object.property, defineDataRange(filler));
      }

      case T.DATA_ALL_VALUES_FROM: {
        this._checkTopDataPropertyUse(object.property, object);
        const filler = object.filler;
        if (isLiteralDataRange(filler)) return E.dataAllValuesFrom(object.property, filler);
        return E.dataAllValuesFrom(object.property, defineDataRange(filler));
      }

      case T.DATA_HAS_VALUE:
        throw new Error('Internal error: data value restrictions should have been simplified.');

      case T.DATA_MIN_CARDINALITY: {
        this._checkTopDataPropertyUse(object.property, object);
        const filler = E.cardinalityFiller(object, true);
        if (isLiteralDataRange(filler)) return E.dataMinCardinality(object.cardinality, object.property, filler);
        return E.dataMinCardinality(object.cardinality, object.property, defineDataRange(filler));
      }

      case T.DATA_MAX_CARDINALITY: {
        this._checkTopDataPropertyUse(object.property, object);
        const filler = E.cardinalityFiller(object, true);
        if (isLiteralDataRange(filler)) return E.dataMaxCardinality(object.cardinality, object.property, filler);
        // ≤n.D  becomes  ≤n.¬T  with  T ⊑ ¬D.
        //
        // NOTE: this deliberately differs from HermiT, which defines T for
        // `complementDescription` but then queues `{¬T, filler}` (i.e. T ⊑ D).
        // On the object side that is fine only because `getDefinitionFor`
        // applies the polarity visitor and so returns `¬fresh`, flipping the
        // inclusion; datatypes have no polarity handling, so HermiT's data-side
        // inclusion runs the wrong way and `≤n.¬T` no longer entails `≤n.D`.
        // Queueing `{¬T, ¬D}` (what `defineDataRange(complementDescription)`
        // does) is both sound and equisatisfiable — interpret T as exactly ¬D.
        const complementDescription = EM.getDataRangeComplementNNF(filler);
        const definition = defineDataRange(complementDescription);
        return E.dataMaxCardinality(object.cardinality, object.property, EM.getDataRangeComplementNNF(definition));
      }

      case T.DATA_EXACT_CARDINALITY:
        throw new Error('Internal error: exact data cardinality restrictions should have been simplified.');

      default:
        return object;
    }
  }

  // ===========================================================================
  // DataRangeNormalizer
  // ===========================================================================

  normalizeDataRange(node, newDataRangeInclusions) {
    switch (E.exprType(node)) {
      case T.DATATYPE:
      case T.DATA_COMPLEMENT_OF:
      case T.DATA_ONE_OF:
      case T.DATATYPE_RESTRICTION:
        return node;
      case T.DATA_INTERSECTION_OF: {
        const r = this.getDefinitionForDataRange(node);
        if (!r.alreadyExists) {
          for (const description of E.operandsOf(node)) {
            newDataRangeInclusions.push([this.negativeDataRange(r.definition), description]);
          }
        }
        return r.definition;
      }
      case T.DATA_UNION_OF:
        throw new Error('OR should be broken down at the outermost level');
      default:
        throw new Error(`Internal error: unexpected data range during normalization: ${node}`);
    }
  }

  // ===========================================================================
  // AxiomVisitor
  // ===========================================================================

  _visitAxiom(axiom, state) {
    const classInclusions = state.classInclusions;
    const dataRangeInclusions = state.dataRangeInclusions;
    const axioms = this.axioms;

    // SWRL rules have no axiomType in protege-js; detect them structurally.
    if (Array.isArray(axiom.body) && Array.isArray(axiom.head)) {
      this._visitSWRLRule(axiom, state);
      return;
    }

    const type = axiom.axiomType || (axiom.getAxiomType && axiom.getAxiomType());
    switch (type) {
      // ---- semantics-less axioms ----
      case AT.DECLARATION:
      case AT.ANNOTATION_ASSERTION:
      case AT.SUB_ANNOTATION_PROPERTY_OF:
      case AT.ANNOTATION_PROPERTY_DOMAIN:
      case AT.ANNOTATION_PROPERTY_RANGE:
      case 'ImportsDeclaration':
        if (type === AT.DECLARATION && axiom.entity) {
          const ent = axiom.entity;
          const et = ent.entityType || (ent.getEntityType && ent.getEntityType());
          if (et === E.EntityType.CLASS) axioms.classes.add(ent);
          else if (et === E.EntityType.OBJECT_PROPERTY) axioms.objectProperties.add(ent);
          else if (et === E.EntityType.DATA_PROPERTY) axioms.dataProperties.add(ent);
          else if (et === E.EntityType.NAMED_INDIVIDUAL) axioms.namedIndividuals.add(ent);
        }
        return;

      // ---- class axioms ----
      case AT.SUBCLASS_OF:
        classInclusions.push([this.negative(axiom.subClass), this.positive(axiom.superClass)]);
        return;

      case AT.EQUIVALENT_CLASSES: {
        const ces = axiom.classExpressions;
        if (ces.length > 1) {
          let last = ces[0];
          for (let i = 1; i < ces.length; i++) {
            classInclusions.push([this.negative(last), this.positive(ces[i])]);
            last = ces[i];
          }
          classInclusions.push([this.negative(last), this.positive(ces[0])]);
        }
        return;
      }

      case AT.DISJOINT_CLASSES: {
        const ces = axiom.classExpressions;
        if (ces.length <= 1) {
          throw new Error(
            `Error: Parsed ${axiom}. A DisjointClasses axiom in OWL 2 DL must have `
            + 'at least two classes as parameters.');
        }
        const descriptions = ces.map(d => EM.getComplementNNF(d));
        for (let i = 0; i < descriptions.length; i++) {
          for (let j = i + 1; j < descriptions.length; j++) {
            classInclusions.push([descriptions[i], descriptions[j]]);
          }
        }
        return;
      }

      case AT.DISJOINT_UNION: {
        // DisjointUnion(C CE1 … CEn)
        const ces = axiom.classExpressions;
        const cls = axiom.owlClass;
        // 1. C ⊑ CE1 ⊔ … ⊔ CEn, i.e. {¬C, CE1, …, CEn}
        classInclusions.push([EM.getComplementNNF(cls), ...ces]);
        // 2. CEi ⊑ C, i.e. {¬CEi, C}
        for (const description of ces) {
          classInclusions.push([this.negative(description), cls]);
        }
        // 3. CEi ⊓ CEj ⊑ ⊥ for i<j, i.e. {¬CEi, ¬CEj}
        const descriptions = ces.map(d => EM.getComplementNNF(d));
        for (let i = 0; i < descriptions.length; i++) {
          for (let j = i + 1; j < descriptions.length; j++) {
            classInclusions.push([descriptions[i], descriptions[j]]);
          }
        }
        return;
      }

      // ---- object property axioms ----
      case AT.SUB_OBJECT_PROPERTY_OF: {
        const sub = axiom.subProperty;
        const sup = axiom.superProperty;
        if (!E.isBottomObjectProperty(sub) && !E.isTopObjectProperty(sup)) {
          axioms.addObjectPropertyInclusion(sub, sup);
        }
        axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(sub));
        axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(sup));
        axioms.objectProperties.add(E.namedPropertyOf(sub));
        axioms.objectProperties.add(E.namedPropertyOf(sup));
        return;
      }

      case AT.SUB_PROPERTY_CHAIN_OF: {
        const chain = axiom.propertyChain;
        const sup = axiom.superProperty;
        if (!chain.some(E.isBottomObjectProperty) && !E.isTopObjectProperty(sup)) {
          if (chain.length === 1) {
            axioms.addObjectPropertyInclusion(chain[0], sup);
          } else if (chain.length === 2
            && E.exprEquals(chain[0], sup) && E.exprEquals(chain[1], sup)) {
            axioms.makeTransitive(sup);
          } else if (chain.length === 0) {
            throw new Error(
              'Error: In OWL 2 DL, an empty property chain in property chain axioms '
              + `is not allowed, but the ontology contains an axiom that the empty chain `
              + `is a subproperty of ${sup}.`);
          } else {
            axioms.addPropertyChain(chain, sup);
          }
        }
        for (const p of chain) {
          axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(p));
          axioms.objectProperties.add(E.namedPropertyOf(p));
        }
        axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(sup));
        axioms.objectProperties.add(E.namedPropertyOf(sup));
        return;
      }

      case AT.EQUIVALENT_OBJECT_PROPERTIES: {
        const props = axiom.properties;
        if (props.length > 1) {
          let last = props[0];
          for (let i = 1; i < props.length; i++) {
            axioms.addObjectPropertyInclusion(last, props[i]);
            last = props[i];
          }
          axioms.addObjectPropertyInclusion(last, props[0]);
        }
        for (const p of props) {
          axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(p));
          axioms.objectProperties.add(E.namedPropertyOf(p));
        }
        return;
      }

      case AT.DISJOINT_OBJECT_PROPERTIES: {
        const props = axiom.properties.slice();
        for (const p of props) {
          axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(p));
          axioms.objectProperties.add(E.namedPropertyOf(p));
        }
        axioms.disjointObjectProperties.push(props);
        return;
      }

      case AT.INVERSE_OBJECT_PROPERTIES: {
        // protege-js names the fields property1/property2; OWL API uses
        // getFirstProperty()/getSecondProperty().
        const first = axiom.firstProperty !== undefined ? axiom.firstProperty : axiom.property1;
        const second = axiom.secondProperty !== undefined ? axiom.secondProperty : axiom.property2;
        axioms.addObjectPropertyInclusion(first, E.inversePropertyOf(second));
        axioms.addObjectPropertyInclusion(second, E.inversePropertyOf(first));
        axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(first));
        axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(second));
        axioms.objectProperties.add(E.namedPropertyOf(first));
        axioms.objectProperties.add(E.namedPropertyOf(second));
        return;
      }

      case AT.OBJECT_PROPERTY_DOMAIN:
        // Domain(R, C) ≡ ⊤ ⊑ ∀R.¬C ⊔ C  →  {C, ∀R.⊥}
        classInclusions.push([
          this.positive(axiom.domain),
          E.objectAllValuesFrom(axiom.property, E.owlNothing())
        ]);
        axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(axiom.property));
        axioms.objectProperties.add(E.namedPropertyOf(axiom.property));
        return;

      case AT.OBJECT_PROPERTY_RANGE:
        classInclusions.push([E.objectAllValuesFrom(axiom.property, this.positive(axiom.range))]);
        axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(axiom.property));
        axioms.objectProperties.add(E.namedPropertyOf(axiom.property));
        return;

      case AT.FUNCTIONAL_OBJECT_PROPERTY:
        classInclusions.push([E.objectMaxCardinality(1, axiom.property)]);
        axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(axiom.property));
        axioms.objectProperties.add(E.namedPropertyOf(axiom.property));
        return;

      case AT.INVERSE_FUNCTIONAL_OBJECT_PROPERTY:
        classInclusions.push([E.objectMaxCardinality(1, E.inversePropertyOf(axiom.property))]);
        axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(axiom.property));
        axioms.objectProperties.add(E.namedPropertyOf(axiom.property));
        return;

      case AT.REFLEXIVE_OBJECT_PROPERTY:
        axioms.makeReflexive(axiom.property);
        axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(axiom.property));
        axioms.objectProperties.add(E.namedPropertyOf(axiom.property));
        return;

      case AT.IRREFLEXIVE_OBJECT_PROPERTY:
        axioms.makeIrreflexive(axiom.property);
        axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(axiom.property));
        axioms.objectProperties.add(E.namedPropertyOf(axiom.property));
        return;

      case AT.SYMMETRIC_OBJECT_PROPERTY:
        axioms.addObjectPropertyInclusion(axiom.property, E.inversePropertyOf(axiom.property));
        axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(axiom.property));
        axioms.objectProperties.add(E.namedPropertyOf(axiom.property));
        return;

      case AT.ASYMMETRIC_OBJECT_PROPERTY:
        axioms.makeAsymmetric(axiom.property);
        axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(axiom.property));
        axioms.objectProperties.add(E.namedPropertyOf(axiom.property));
        return;

      case AT.TRANSITIVE_OBJECT_PROPERTY:
        axioms.makeTransitive(axiom.property);
        axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(axiom.property));
        axioms.objectProperties.add(E.namedPropertyOf(axiom.property));
        return;

      // ---- data property axioms ----
      case AT.SUB_DATA_PROPERTY_OF: {
        const sub = axiom.subProperty;
        this._checkTopDataPropertyUse(sub, axiom);
        const sup = axiom.superProperty;
        if (!E.isBottomDataProperty(sub) && !E.isTopDataProperty(sup)) {
          axioms.addDataPropertyInclusion(sub, sup);
        }
        axioms.dataProperties.add(sub);
        axioms.dataProperties.add(sup);
        return;
      }

      case AT.EQUIVALENT_DATA_PROPERTIES: {
        const props = axiom.properties;
        for (const p of props) this._checkTopDataPropertyUse(p, axiom);
        if (props.length > 1) {
          let last = props[0];
          for (let i = 1; i < props.length; i++) {
            axioms.addDataPropertyInclusion(last, props[i]);
            last = props[i];
          }
          axioms.addDataPropertyInclusion(last, props[0]);
        }
        for (const p of props) axioms.dataProperties.add(p);
        return;
      }

      case AT.DISJOINT_DATA_PROPERTIES: {
        const props = axiom.properties.slice();
        for (const p of props) this._checkTopDataPropertyUse(p, axiom);
        axioms.disjointDataProperties.push(props);
        for (const p of props) axioms.dataProperties.add(p);
        return;
      }

      case AT.DATA_PROPERTY_DOMAIN: {
        const dp = axiom.property;
        this._checkTopDataPropertyUse(dp, axiom);
        classInclusions.push([
          this.positive(axiom.domain),
          E.dataAllValuesFrom(dp, E.dataComplementOf(E.topDatatype()))
        ]);
        axioms.dataProperties.add(dp);
        return;
      }

      case AT.DATA_PROPERTY_RANGE: {
        const dp = axiom.property;
        this._checkTopDataPropertyUse(dp, axiom);
        classInclusions.push([E.dataAllValuesFrom(dp, this.positiveDataRange(axiom.range))]);
        axioms.dataProperties.add(dp);
        return;
      }

      case AT.FUNCTIONAL_DATA_PROPERTY: {
        const dp = axiom.property;
        this._checkTopDataPropertyUse(dp, axiom);
        classInclusions.push([E.dataMaxCardinality(1, dp)]);
        axioms.dataProperties.add(dp);
        return;
      }

      // ---- assertions ----
      case AT.SAME_INDIVIDUAL:
        if (containsAnonymousIndividuals(axiom.individuals)) {
          throw new Error(`The axiom ${axiom} contains anonymous individuals, which is not allowed in OWL 2.`);
        }
        for (const ind of axiom.individuals) axioms.namedIndividuals.add(ind);
        axioms.facts.push(E.sameIndividual(axiom.individuals));
        return;

      case AT.DIFFERENT_INDIVIDUALS:
        if (containsAnonymousIndividuals(axiom.individuals)) {
          throw new Error(`The axiom ${axiom} contains anonymous individuals, which is not allowed in OWL 2.`);
        }
        for (const ind of axiom.individuals) axioms.namedIndividuals.add(ind);
        axioms.facts.push(E.differentIndividuals(axiom.individuals));
        return;

      case AT.CLASS_ASSERTION: {
        const ce = axiom.classExpression;
        // DataHasValue(a) as a class assertion is just a data property assertion.
        if (E.exprType(ce) === T.DATA_HAS_VALUE) {
          axioms.dataProperties.add(ce.property);
          axioms.namedIndividuals.add(axiom.individual);
          axioms.facts.push(E.dataPropertyAssertion(
            ce.property, axiom.individual, E.literal(ce.value !== undefined ? ce.value : ce.filler)));
          return;
        }
        // ∃dp.{v}(a) likewise.
        if (E.exprType(ce) === T.DATA_SOME_VALUES_FROM) {
          const filler = ce.filler;
          if (E.exprType(filler) === T.DATA_ONE_OF && E.operandsOf(filler).length === 1) {
            axioms.dataProperties.add(ce.property);
            axioms.namedIndividuals.add(axiom.individual);
            axioms.facts.push(E.dataPropertyAssertion(
              ce.property, axiom.individual, E.literal(E.operandsOf(filler)[0])));
            return;
          }
        }
        let classExpression = this.positive(ce);
        if (!isSimple(classExpression)) {
          const r = this.getDefinitionFor(classExpression);
          if (!r.alreadyExists) classInclusions.push(r.definingInclusion);
          classExpression = r.definition;
        }
        axioms.namedIndividuals.add(axiom.individual);
        axioms.facts.push(E.classAssertion(classExpression, axiom.individual));
        return;
      }

      case AT.OBJECT_PROPERTY_ASSERTION:
        axioms.facts.push(E.objectPropertyAssertion(axiom.property, axiom.subject, axiom.object));
        axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(axiom.property));
        axioms.objectProperties.add(E.namedPropertyOf(axiom.property));
        axioms.namedIndividuals.add(axiom.subject);
        axioms.namedIndividuals.add(axiom.object);
        return;

      case AT.NEGATIVE_OBJECT_PROPERTY_ASSERTION:
        if (isAnonymousIndividual(axiom.subject) || isAnonymousIndividual(axiom.object)) {
          throw new Error(`The axiom ${axiom} contains anonymous individuals, which is not allowed in OWL 2 DL.`);
        }
        axioms.facts.push(E.negativeObjectPropertyAssertion(axiom.property, axiom.subject, axiom.object));
        axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(axiom.property));
        axioms.objectProperties.add(E.namedPropertyOf(axiom.property));
        axioms.namedIndividuals.add(axiom.subject);
        axioms.namedIndividuals.add(axiom.object);
        return;

      case AT.DATA_PROPERTY_ASSERTION: {
        this._checkTopDataPropertyUse(axiom.property, axiom);
        const lit = E.literal(E.assertionLiteral(axiom));
        axioms.dataProperties.add(axiom.property);
        axioms.namedIndividuals.add(axiom.subject);
        axioms.facts.push(E.dataPropertyAssertion(axiom.property, axiom.subject, lit));
        return;
      }

      case AT.NEGATIVE_DATA_PROPERTY_ASSERTION: {
        this._checkTopDataPropertyUse(axiom.property, axiom);
        if (isAnonymousIndividual(axiom.subject)) {
          throw new Error(`The axiom ${axiom} contains anonymous individuals, which is not allowed in OWL 2 DL.`);
        }
        const lit = E.literal(E.assertionLiteral(axiom));
        axioms.dataProperties.add(axiom.property);
        axioms.namedIndividuals.add(axiom.subject);
        axioms.facts.push(E.negativeDataPropertyAssertion(axiom.property, axiom.subject, lit));
        return;
      }

      // ---- datatype definitions ----
      case AT.DATATYPE_DEFINITION: {
        const dtIri = E.iriString(axiom.datatype.iri || axiom.datatype.getIRI());
        axioms.definedDatatypesIRIs.add(dtIri);
        axioms.classes.add(axiom.datatype); // keep the datatype in the signature
        dataRangeInclusions.push([this.negativeDataRange(axiom.datatype), this.positiveDataRange(axiom.dataRange)]);
        dataRangeInclusions.push([this.negativeDataRange(axiom.dataRange), this.positiveDataRange(axiom.datatype)]);
        return;
      }

      // ---- keys ----
      case AT.HAS_KEY: {
        const objectProps = [];
        const dataProps = [];
        for (const p of axiom.propertyExpressions) {
          if (E.isDataProperty(p)) {
            this._checkTopDataPropertyUse(p, axiom);
            dataProps.push(p);
            axioms.dataProperties.add(p);
          } else {
            objectProps.push(p);
            axioms.objectPropertiesOccurringInOWLAxioms.add(E.namedPropertyOf(p));
            axioms.objectProperties.add(E.namedPropertyOf(p));
          }
        }
        let description = this.positive(axiom.classExpression);
        if (!isSimple(description)) {
          const r = this.getDefinitionFor(description);
          if (!r.alreadyExists) classInclusions.push(r.definingInclusion);
          description = r.definition;
        }
        axioms.hasKeys.push(E.hasKey(description, [...objectProps, ...dataProps]));
        return;
      }

      default:
        throw new Error(`Unsupported axiom type during normalization: ${type} (${axiom})`);
    }
  }

  _visitSWRLRule(rule, state) {
    for (const atom of [...rule.body, ...rule.head]) {
      if (atom && atom.type === 'DataPropertyAtom') {
        this._checkTopDataPropertyUse(atom.property, rule);
      }
    }
    if (rule.body.length === 0) {
      // Process as a set of facts.
      const converter = new Rule2FactConverter(this, state.classInclusions);
      for (const atom of rule.head) converter.convert(atom);
    } else {
      state.rules.push(rule);
    }
  }

  _checkTopDataPropertyUse(dataPropertyExpression, axiom) {
    if (E.isTopDataProperty(dataPropertyExpression)) {
      throw new Error(
        'Error: In OWL 2 DL, owl:topDataProperty is only allowed to occur in the '
        + `super property position of SubDataPropertyOf axioms, but the ontology contains an axiom ${axiom} `
        + 'that violates this condition.');
    }
  }
}

// ===========================================================================
// Ontology access helpers (work with protege-js OWLOntology or a plain array)
// ===========================================================================

/**
 * All axioms of an ontology that carry DL semantics.
 * @param {object|object[]} ontology
 * @param {boolean} [includeDeclarations] when true, Declaration axioms are kept
 *        (they have no semantics but are used to complete the signature).
 */
function logicalAxiomsOf(ontology, includeDeclarations = false) {
  const keep = (a) => {
    const t = a.axiomType || (a.getAxiomType && a.getAxiomType());
    if (includeDeclarations && t === E.AxiomType.DECLARATION) return true;
    return !E.NON_LOGICAL_AXIOM_TYPES.has(t);
  };
  if (Array.isArray(ontology)) return ontology.filter(keep);
  if (!includeDeclarations && typeof ontology.getLogicalAxioms === 'function') {
    return ontology.getLogicalAxioms();
  }
  const all = typeof ontology.getAxioms === 'function'
    ? ontology.getAxioms()
    : [...(ontology._axioms || [])];
  // `getAxioms()` may legitimately return a Set (protege-js returns an array).
  return (Array.isArray(all) ? all : [...all]).filter(keep);
}

function _signature(ontology, method) {
  if (Array.isArray(ontology)) return [];
  if (typeof ontology[method] !== 'function') return [];
  return ontology[method]() || [];
}

/** The ontology IRI as a string, or null for an anonymous ontology. */
function ontologyIRIOf(ontology) {
  if (!ontology || Array.isArray(ontology)) return null;
  const id = typeof ontology.getOntologyID === 'function' ? ontology.getOntologyID() : ontology.id;
  if (!id) return null;
  const iri = id.ontologyIRI !== undefined ? id.ontologyIRI : id;
  return E.iriString(iri);
}

module.exports = {
  OWLNormalization,
  isSimple, isNominal, isNegatedOneNominal,
  isAtomicDataRange, isNegatedAtomicDataRange, isLiteralDataRange,
  isPositivePolarity, isAnonymousIndividual, containsAnonymousIndividuals,
  logicalAxiomsOf, ontologyIRIOf
};
