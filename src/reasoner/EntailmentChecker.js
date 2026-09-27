'use strict';

// ---------------------------------------------------------------------------
// reasoner/EntailmentChecker.js
//
// Port of org.semanticweb.HermiT.EntailmentChecker.
//
// HermiT implements this as an `OWLAxiomVisitorEx<Boolean>` — the OWL API's
// double-dispatch visitor. This port has no visitor infrastructure (axioms are
// plain `{axiomType, ...fields}` objects), so the double dispatch is replaced
// by a single `switch (axiomType)` in `_visit`. Every branch is a 1:1
// transcription of the corresponding `visit(...)` method.
//
// Deliberate deviations from HermiT (all in the anonymous-individual roll-up,
// which is buggy upstream — see `AnonymousIndividualForestBuilder` below):
//
//   1. `getClassExpressionFor` skipped the node's OWN labels on the non-leaf
//      branch and followed the back-edge to `predecessor`. For a chain
//      `_:x -r-> _:y -r-> _:z` with `C(_:y)` that rolls up to
//      `∃r.(∃r.C_z ⊓ ∃r.C_x)` instead of `∃r.(C_y ⊓ ∃r.C_z)`. We skip the
//      predecessor and always conjoin the node's own labels.
//   2. The same method could recurse forever whenever a node's parent had two
//      or more children (it re-entered the parent, which re-entered the node).
//      Skipping the predecessor fixes that too.
//   3. When the edge label was found under the reversed pair
//      `(successor, node)` — i.e. the assertion was `r(successor, node)` — the
//      roll-up needs `∃r⁻`, but HermiT used `∃r`. We invert.
//   4. `visit(ObjectPropertyAssertionAxiom)` threw away every previously
//      recorded named neighbour of an anonymous individual when a *second*,
//      different named individual showed up (it replaced the inner map with a
//      fresh one). That silently weakened the roll-up and made
//      `findSuitableRoots`' `size() < 2` test vacuous. We merge instead.
//   5. `entails(axiom)` did not clear `anonymousIndividualAxioms`, so repeated
//      single-axiom calls accumulated stale axioms. We clear in both overloads.
// ---------------------------------------------------------------------------

/** `internal:anonymous-constants` — the datatype HermiT uses for HasKey keys. */
const IRI_ANONYMOUS_CONSTANTS = 'internal:anonymous-constants';

/** True for `OWLAnonymousIndividual`-shaped objects (they have no IRI). */
function isAnonymousIndividual(ind) {
  if (ind === null || ind === undefined) return false;
  if (typeof ind.isAnonymous === 'function') return !!ind.isAnonymous();
  return ind.nodeId !== undefined;
}

/**
 * The axiom type string, tolerating both plain objects and OWL API objects.
 *
 * protege-js `SWRLRule` objects carry NO `axiomType` at all — they are plain
 * `{ body, head }` records. Detect them structurally, exactly as
 * `OWLNormalization._visitAxiom` does, so that a caller gets the specific
 * "SWRL entailment is not supported" error instead of a baffling
 * "unsupported axiom type 'null'".
 */
function axiomTypeOf(axiom) {
  if (axiom === null || axiom === undefined) return null;
  if (Array.isArray(axiom.body) && Array.isArray(axiom.head)) return 'SWRLRule';
  return axiom.axiomType
    || (typeof axiom.getAxiomType === 'function' ? axiom.getAxiomType() : null);
}

/** A stable string identity for an individual (named or anonymous). */
function individualKey(ind) {
  if (ind === null || ind === undefined) return 'null';
  if (isAnonymousIndividual(ind)) return `_:${ind.nodeId}`;
  return `iri:${ind.iri !== undefined ? ind.iri : ind.getIRI()}`;
}

// ===========================================================================
// Edge — HermiT's inner `Edge` class, replaced by a string key.
// ===========================================================================

/** Ordered pair key, matching HermiT's `Edge.hashCode`/`equals` semantics. */
function edgeKey(first, second) {
  return `${individualKey(first)}\u0000${individualKey(second)}`;
}

// ===========================================================================
// EntailmentChecker
// ===========================================================================

class EntailmentChecker {
  /**
   * @param {import('./Reasoner').Reasoner} reasoner
   * @param {typeof import('../owl/OWLExpressions')} factory the OWL expression
   *   module; stands in for HermiT's `OWLDataFactory`.
   */
  constructor(reasoner, factory) {
    this.reasoner = reasoner;
    this.factory = factory;
    /** Axioms mentioning anonymous individuals, deferred to the roll-up. */
    this.anonymousIndividualAxioms = new Set();
  }

  // ---- entry points --------------------------------------------------------

  /**
   * Whether every axiom in `axioms` follows from the loaded ontology.
   *
   * Use this (rather than the single-axiom form) whenever the axioms may
   * contain anonymous individuals: only then can they be rolled up together.
   *
   * @param {Iterable<object>|object} axioms a set/array of axioms, or one axiom
   * @returns {boolean}
   */
  entails(axioms) {
    const E = this.factory;
    this.anonymousIndividualAxioms.clear();

    if (!Array.isArray(axioms) && !(axioms instanceof Set)) {
      // Single-axiom overload (HermiT's `entails(OWLAxiom)`).
      if (!this._visit(axioms)) return false;
      return this._checkAnonymousIndividuals();
    }

    for (const axiom of axioms) {
      // HermiT: `if (axiom.isLogicalAxiom())`. Declarations and annotations
      // carry no DL semantics.
      if (E.NON_LOGICAL_AXIOM_TYPES.has(axiomTypeOf(axiom))) continue;
      if (!this._visit(axiom)) return false;
    }
    return this._checkAnonymousIndividuals();
  }

  /**
   * Rolls the buffered anonymous-individual axioms up into named-individual
   * axioms and checks those.
   * @returns {boolean}
   */
  _checkAnonymousIndividuals() {
    if (this.anonymousIndividualAxioms.size === 0) return true;

    const builder = new AnonymousIndividualForestBuilder(this.factory);
    builder.constructConceptsForAnonymousIndividuals(this.anonymousIndividualAxioms);

    // Roots that hang off a named individual become class assertions, checked
    // the ordinary way.
    for (const ax of builder.getAnonIndAxioms()) {
      if (!this._visit(ax)) return false;
    }

    // Roots with no named neighbour become `⊤ ⊑ ¬C`; the entailment holds iff
    // adding that axiom makes the ontology inconsistent.
    for (const ax of builder.getAnonNoNamedIndAxioms()) {
      const tableau = this.reasoner.getTableau(ax);
      const satisfiable = tableau.isSatisfiable({
        loadPermanentABox: true,
        loadAdditionalABox: true,
        reasoningTaskDescription: `Anonymous individual check: ${ax}`
      });
      tableau.clearAdditionalDLOntology();
      if (satisfiable) return false;
    }
    return true;
  }

  // ---- the visitor ---------------------------------------------------------

  /**
   * Dispatch on the axiom type. Mirrors HermiT's `OWLAxiomVisitorEx`.
   * @param {object} axiom
   * @returns {boolean}
   */
  _visit(axiom) {
    const E = this.factory;
    const AT = E.AxiomType;
    const type = axiomTypeOf(axiom);

    switch (type) {
      // ---- non-logical axioms: always entailed ----
      case AT.DECLARATION:
      case AT.ANNOTATION_ASSERTION:
      case AT.SUB_ANNOTATION_PROPERTY_OF:
      case AT.ANNOTATION_PROPERTY_DOMAIN:
      case AT.ANNOTATION_PROPERTY_RANGE:
      case 'ImportsDeclaration':
        return true;

      // ---- assertions ----
      case AT.CLASS_ASSERTION: return this._classAssertion(axiom);
      case AT.OBJECT_PROPERTY_ASSERTION: return this._objectPropertyAssertion(axiom);
      case AT.NEGATIVE_OBJECT_PROPERTY_ASSERTION: return this._negativeObjectPropertyAssertion(axiom);
      case AT.DATA_PROPERTY_ASSERTION: return this._dataPropertyAssertion(axiom);
      case AT.NEGATIVE_DATA_PROPERTY_ASSERTION: return this._negativeDataPropertyAssertion(axiom);
      case AT.SAME_INDIVIDUAL: return this._sameIndividual(axiom);
      case AT.DIFFERENT_INDIVIDUALS: return this._differentIndividuals(axiom);

      // ---- object properties ----
      case AT.SUB_OBJECT_PROPERTY_OF: return this._subObjectPropertyOf(axiom);
      case AT.SUB_PROPERTY_CHAIN_OF: return this._subPropertyChainOf(axiom);
      case AT.EQUIVALENT_OBJECT_PROPERTIES: return this._equivalentObjectProperties(axiom);
      case AT.DISJOINT_OBJECT_PROPERTIES: return this._disjointObjectProperties(axiom);
      case AT.INVERSE_OBJECT_PROPERTIES: return this._inverseObjectProperties(axiom);
      case AT.OBJECT_PROPERTY_DOMAIN: return this._objectPropertyDomain(axiom);
      case AT.OBJECT_PROPERTY_RANGE: return this._objectPropertyRange(axiom);
      case AT.FUNCTIONAL_OBJECT_PROPERTY:
        return this.reasoner.isFunctional(axiom.property);
      case AT.INVERSE_FUNCTIONAL_OBJECT_PROPERTY:
        return this.reasoner.isInverseFunctional(axiom.property);
      case AT.SYMMETRIC_OBJECT_PROPERTY:
        return this.reasoner.isSymmetric(axiom.property);
      case AT.ASYMMETRIC_OBJECT_PROPERTY:
        return this.reasoner.isAsymmetric(axiom.property);
      case AT.TRANSITIVE_OBJECT_PROPERTY:
        return this.reasoner.isTransitive(axiom.property);
      case AT.REFLEXIVE_OBJECT_PROPERTY:
        return this.reasoner.isReflexive(axiom.property);
      case AT.IRREFLEXIVE_OBJECT_PROPERTY:
        return this.reasoner.isIrreflexive(axiom.property);

      // ---- data properties ----
      case AT.SUB_DATA_PROPERTY_OF: return this._subDataPropertyOf(axiom);
      case AT.EQUIVALENT_DATA_PROPERTIES: return this._equivalentDataProperties(axiom);
      case AT.DISJOINT_DATA_PROPERTIES: return this._disjointDataProperties(axiom);
      case AT.DATA_PROPERTY_DOMAIN: return this._dataPropertyDomain(axiom);
      case AT.DATA_PROPERTY_RANGE: return this._dataPropertyRange(axiom);
      case AT.FUNCTIONAL_DATA_PROPERTY:
        return this.reasoner.isFunctionalDataProperty(axiom.property);

      // ---- class axioms ----
      case AT.SUBCLASS_OF: return this._subClassOf(axiom);
      case AT.EQUIVALENT_CLASSES: return this._equivalentClasses(axiom);
      case AT.DISJOINT_CLASSES: return this._disjointClasses(axiom);
      case AT.DISJOINT_UNION: return this._disjointUnion(axiom);

      // ---- datatypes / keys / rules ----
      case AT.DATATYPE_DEFINITION: return this._datatypeDefinition(axiom);
      case AT.HAS_KEY: return this._hasKey(axiom);
      case 'SWRLRule':
        throw new Error('Entailment checking for SWRL rules is not supported.');

      default:
        throw new Error(`EntailmentChecker: unsupported axiom type '${type}'.`);
    }
  }

  // ---- assertions ----------------------------------------------------------

  /** `C(i)`. Anonymous subjects are buffered for the roll-up. */
  _classAssertion(axiom) {
    const ind = axiom.individual;
    if (isAnonymousIndividual(ind)) {
      this.anonymousIndividualAxioms.add(axiom);
      return true; // checked afterwards by rolling up
    }
    return this.reasoner.hasType(ind, axiom.classExpression, false);
  }

  /** `R(i, j)`. */
  _objectPropertyAssertion(axiom) {
    if (isAnonymousIndividual(axiom.subject) || isAnonymousIndividual(axiom.object)) {
      this.anonymousIndividualAxioms.add(axiom);
      return true;
    }
    return this.reasoner.hasObjectPropertyRelationship(
      axiom.subject, axiom.property, axiom.object);
  }

  /** `¬R(i, j)` ≡ `i : ¬∃R.{j}`. */
  _negativeObjectPropertyAssertion(axiom) {
    const E = this.factory;
    // OWL 2 Syntax §11.2: negative assertions must not mention anonymous individuals.
    if (isAnonymousIndividual(axiom.subject) || isAnonymousIndividual(axiom.object)) {
      throw new Error(
        'NegativeObjectPropertyAssertion axioms are not allowed to be used with anonymous '
        + `individuals (see OWL 2 Syntax Sec 11.2) but the axiom ${axiom} contains an `
        + 'anonymous subject or object.');
    }
    const hasValue = E.objectHasValue(axiom.property, axiom.object);
    return this.reasoner.hasType(axiom.subject, E.objectComplementOf(hasValue), false);
  }

  /** `dp(i, v)` ≡ `i : ∃dp.{v}`. */
  _dataPropertyAssertion(axiom) {
    const E = this.factory;
    if (isAnonymousIndividual(axiom.subject)) {
      this.anonymousIndividualAxioms.add(axiom);
      return true;
    }
    const hasValue = E.dataHasValue(axiom.property, E.assertionLiteral(axiom));
    return this.reasoner.hasType(axiom.subject, hasValue, false);
  }

  /** `¬dp(i, v)` ≡ `i : ¬∃dp.{v}`. */
  _negativeDataPropertyAssertion(axiom) {
    const E = this.factory;
    if (isAnonymousIndividual(axiom.subject)) {
      throw new Error(
        'NegativeDataPropertyAssertion axioms are not allowed to be used with anonymous '
        + `individuals (see OWL 2 Syntax Sec 11.2) and the subject ${axiom.subject} of `
        + `the axiom ${axiom} is anonymous.`);
    }
    const hasValue = E.dataHasValue(axiom.property, E.assertionLiteral(axiom));
    return this.reasoner.hasType(axiom.subject, E.objectComplementOf(hasValue), false);
  }

  /** `SameIndividual(i1 … in)` — pairwise `isSameIndividual` against the first. */
  _sameIndividual(axiom) {
    const individuals = axiom.individuals;
    for (const i of individuals) {
      if (isAnonymousIndividual(i)) {
        throw new Error(
          'SameIndividual axioms are not allowed to be used with anonymous individuals '
          + `(see OWL 2 Syntax Sec 11.2) but the axiom ${axiom} contains an anonymous individual.`);
      }
    }
    if (individuals.length === 0) return true;
    const first = individuals[0];
    for (let i = 1; i < individuals.length; i++) {
      if (!this.reasoner.isSameIndividual(first, individuals[i])) return false;
    }
    return true;
  }

  /** `DifferentIndividuals(i1 … in)` — pairwise `i : ¬{j}`. */
  _differentIndividuals(axiom) {
    const E = this.factory;
    const list = axiom.individuals;
    for (const i of list) {
      if (isAnonymousIndividual(i)) {
        throw new Error(
          'DifferentIndividuals axioms are not allowed to be used with anonymous '
          + `individuals (see OWL 2 Syntax Sec 11.2) but the axiom ${axiom} contains an `
          + 'anonymous individual.');
      }
    }
    for (let i = 0; i < list.length - 1; i++) {
      for (let j = i + 1; j < list.length; j++) {
        const notOneOf = E.objectComplementOf(E.objectOneOf([list[j]]));
        if (!this.reasoner.hasType(list[i], notOneOf, false)) return false;
      }
    }
    return true;
  }

  // ---- object properties ---------------------------------------------------

  /** `Domain(R, C)` ≡ `∃R.⊤ ⊑ C`. */
  _objectPropertyDomain(axiom) {
    const E = this.factory;
    return this.reasoner.isSubClassOf(
      E.objectSomeValuesFrom(axiom.property, E.owlThing()), axiom.domain);
  }

  /** `Range(R, C)` ≡ `⊤ ⊑ ∀R.C`. */
  _objectPropertyRange(axiom) {
    const E = this.factory;
    return this.reasoner.isSubClassOf(
      E.owlThing(), E.objectAllValuesFrom(axiom.property, axiom.range));
  }

  /** `InverseObjectProperties(P1, P2)` ≡ `P1⁻ ≡ P2`. */
  _inverseObjectProperties(axiom) {
    const E = this.factory;
    // protege-js names the fields property1/property2; OWL API uses
    // getFirstProperty()/getSecondProperty().
    const first = axiom.firstProperty !== undefined ? axiom.firstProperty : axiom.property1;
    const second = axiom.secondProperty !== undefined ? axiom.secondProperty : axiom.property2;
    const inverseOfFirst = E.inversePropertyOf(first);
    return this.reasoner.isSubObjectPropertyExpressionOf(inverseOfFirst, second)
      && this.reasoner.isSubObjectPropertyExpressionOf(second, inverseOfFirst);
  }

  /** `EquivalentObjectProperties(P1 … Pn)` — P1 against each of the rest, both ways. */
  _equivalentObjectProperties(axiom) {
    const props = axiom.properties;
    if (props.length === 0) return true;
    const first = props[0];
    for (let i = 1; i < props.length; i++) {
      if (!this.reasoner.isSubObjectPropertyExpressionOf(first, props[i])
        || !this.reasoner.isSubObjectPropertyExpressionOf(props[i], first)) return false;
    }
    return true;
  }

  _subObjectPropertyOf(axiom) {
    return this.reasoner.isSubObjectPropertyExpressionOf(axiom.subProperty, axiom.superProperty);
  }

  /** `SubObjectPropertyOf(chain P1∘…∘Pn, S)`. */
  _subPropertyChainOf(axiom) {
    return this.reasoner.isSubObjectPropertyExpressionOf(axiom.propertyChain, axiom.superProperty);
  }

  _disjointObjectProperties(axiom) {
    const props = axiom.properties;
    for (let i = 0; i < props.length - 1; i++) {
      for (let j = i + 1; j < props.length; j++) {
        if (!this.reasoner.isDisjointObjectProperty(props[i], props[j])) return false;
      }
    }
    return true;
  }

  // ---- data properties -----------------------------------------------------

  /** `Domain(dp, C)` ≡ `∃dp.⊤ ⊑ C`. */
  _dataPropertyDomain(axiom) {
    const E = this.factory;
    return this.reasoner.isSubClassOf(
      E.dataSomeValuesFrom(axiom.property, E.topDatatype()), axiom.domain);
  }

  /** `Range(dp, dr)` ≡ `⊤ ⊑ ∀dp.dr`. */
  _dataPropertyRange(axiom) {
    const E = this.factory;
    return this.reasoner.isSubClassOf(
      E.owlThing(), E.dataAllValuesFrom(axiom.property, axiom.range));
  }

  _equivalentDataProperties(axiom) {
    const props = axiom.properties;
    if (props.length === 0) return true;
    const first = props[0];
    for (let i = 1; i < props.length; i++) {
      if (!this.reasoner.isSubDataPropertyOf(first, props[i])
        || !this.reasoner.isSubDataPropertyOf(props[i], first)) return false;
    }
    return true;
  }

  _subDataPropertyOf(axiom) {
    return this.reasoner.isSubDataPropertyOf(axiom.subProperty, axiom.superProperty);
  }

  /**
   * `DisjointDataProperties(dp1 … dpn)`: every pair must be disjoint.
   *
   * DEVIATION from HermiT: HermiT spells the pairwise test out as
   * `∃dpi.⊤ ⊓ ∃dpj.⊤ ⊓ (≤1 owl:topDataProperty)` and calls `isSatisfiable`.
   * That formulation cannot survive normalization — `OWLNormalization` rejects
   * `owl:topDataProperty` inside a cardinality restriction — so HermiT throws on
   * every `DisjointDataProperties` entailment query. We delegate to
   * `Reasoner.isDisjointDataProperty`, which expresses the same constraint
   * (a single individual sharing one data value between both properties) without
   * mentioning `owl:topDataProperty`.
   */
  _disjointDataProperties(axiom) {
    const props = axiom.properties;
    for (let i = 0; i < props.length - 1; i++) {
      for (let j = i + 1; j < props.length; j++) {
        if (!this.reasoner.isDisjointDataProperty(props[i], props[j])) return false;
      }
    }
    return true;
  }

  // ---- class axioms --------------------------------------------------------

  _subClassOf(axiom) {
    return this.reasoner.isSubClassOf(axiom.subClass, axiom.superClass);
  }

  _equivalentClasses(axiom) {
    const ces = axiom.classExpressions;
    if (ces.length === 0) return true;
    const first = ces[0];
    for (let i = 1; i < ces.length; i++) {
      if (!this.reasoner.isSubClassOf(first, ces[i])
        || !this.reasoner.isSubClassOf(ces[i], first)) return false;
    }
    return true;
  }

  /** `DisjointClasses(C1 … Cn)`: pairwise `Ci ⊑ ¬Cj`. */
  _disjointClasses(axiom) {
    const E = this.factory;
    const classes = axiom.classExpressions;
    for (let i = 0; i < classes.length - 1; i++) {
      for (let j = i + 1; j < classes.length; j++) {
        if (!this.reasoner.isSubClassOf(classes[i], E.objectComplementOf(classes[j]))) return false;
      }
    }
    return true;
  }

  /**
   * `DisjointUnion(C, C1 … Cn)` ≡
   *   `(¬C ⊔ C1 ⊔ … ⊔ Cn) ⊓ (¬(C1 ⊔ … ⊔ Cn) ⊔ C) ⊓ ⋀_{i<j} (¬Ci ⊔ ¬Cj)`.
   * Entailed iff the complement of that conjunction is unsatisfiable.
   */
  _disjointUnion(axiom) {
    const E = this.factory;
    const c = axiom.owlClass;
    const descs = axiom.classExpressions;

    const incl1 = E.objectUnionOf([...descs, E.objectComplementOf(c)]);
    const incl2 = E.objectUnionOf([E.objectComplementOf(E.objectUnionOf(descs)), c]);

    const conjuncts = [incl1, incl2];
    for (let i = 0; i < descs.length - 1; i++) {
      for (let j = i + 1; j < descs.length; j++) {
        conjuncts.push(E.objectUnionOf([
          E.objectComplementOf(descs[i]),
          E.objectComplementOf(descs[j])
        ]));
      }
    }
    const entailmentDesc = E.objectIntersectionOf(conjuncts);
    return !this.reasoner.isSatisfiable(E.objectComplementOf(entailmentDesc));
  }

  // ---- datatype definitions ------------------------------------------------

  /**
   * `DatatypeDefinition(dt, dr)`: introduce a fresh data property and a fresh
   * anonymous individual asserted to have a value in `(¬dr ⊓ dt) ⊔ (¬dt ⊓ dr)`.
   * The definition is entailed iff that symmetric difference is empty, i.e. the
   * resulting tableau is unsatisfiable.
   */
  _datatypeDefinition(axiom) {
    const E = this.factory;
    this.reasoner.throwInconsistentOntologyExceptionIfNecessary();
    if (!this.reasoner.isConsistent()) return true;
    if (!this.reasoner.dlOntology.hasDatatypes) return false;

    const freshIndividual = E.anonymousIndividual('fresh-individual');
    const freshDataProperty = E.dataProperty('fresh-data-property');
    const dataRange = axiom.dataRange;
    const dt = axiom.datatype;
    const dr1 = E.dataIntersectionOf([E.dataComplementOf(dataRange), dt]);
    const dr2 = E.dataIntersectionOf([E.dataComplementOf(dt), dataRange]);
    const union = E.dataUnionOf([dr1, dr2]);
    const c = E.dataSomeValuesFrom(freshDataProperty, union);
    const ax = E.classAssertion(c, freshIndividual);

    const tableau = this.reasoner.getTableau(ax);
    const result = tableau.isSatisfiable({
      loadPermanentABox: true,
      loadAdditionalABox: true,
      reasoningTaskDescription: `isAxiomEntailed(${axiom})`
    });
    tableau.clearAdditionalDLOntology();
    return !result;
  }

  // ---- keys ----------------------------------------------------------------

  /**
   * `HasKey(CE, p1 … pn)`: build two fresh named individuals that agree on
   * every key property and assert they are different. The key is entailed iff
   * that is unsatisfiable.
   */
  _hasKey(axiom) {
    const E = this.factory;
    this.reasoner.throwFreshEntityExceptionIfNecessary([axiom]);
    this.reasoner.throwInconsistentOntologyExceptionIfNecessary();
    if (!this.reasoner.isConsistent()) return true;

    const individualA = E.namedIndividual('internal:named-fresh-individual-A');
    const individualB = E.namedIndividual('internal:named-fresh-individual-B');
    const axioms = [
      E.classAssertion(axiom.classExpression, individualA),
      E.classAssertion(axiom.classExpression, individualB)
    ];

    // HermiT's OWL API axiom exposes getObjectPropertyExpressions() and
    // getDataPropertyExpressions() separately; our `hasKey` factory stores a
    // single mixed `propertyExpressions` array, so partition it here.
    const objectPropertyExpressions = axiom.objectPropertyExpressions
      || (axiom.propertyExpressions || []).filter(p => !E.isDataProperty(p));
    const dataPropertyExpressions = axiom.dataPropertyExpressions
      || (axiom.propertyExpressions || []).filter(p => E.isDataProperty(p));

    let i = 0;
    for (const p of objectPropertyExpressions) {
      const tmp = E.namedIndividual(`internal:named-fresh-individual-${i}`);
      axioms.push(E.objectPropertyAssertion(p, individualA, tmp));
      axioms.push(E.objectPropertyAssertion(p, individualB, tmp));
      i++;
    }
    const anonymousConstantsDatatype = E.datatype(IRI_ANONYMOUS_CONSTANTS);
    for (const p of dataPropertyExpressions) {
      const constant = E.literal(`internal:constant-${i}`, anonymousConstantsDatatype);
      axioms.push(E.dataPropertyAssertion(p, individualA, constant));
      axioms.push(E.dataPropertyAssertion(p, individualB, constant));
      i++;
    }
    axioms.push(E.differentIndividuals([individualA, individualB]));

    const tableau = this.reasoner.getTableau(axioms);
    const result = tableau.isSatisfiable({
      loadPermanentABox: true,
      loadAdditionalABox: true,
      reasoningTaskDescription: `isAxiomEntailed(${axiom})`
    });
    tableau.clearAdditionalDLOntology();
    return !result;
  }
}

// ===========================================================================
// AnonymousIndividualForestBuilder
// ===========================================================================

/**
 * Turns a set of axioms mentioning anonymous individuals into an equivalent set
 * of axioms over named individuals only, by "rolling up" each tree of anonymous
 * individuals into a class expression.
 *
 * OWL 2 Syntax §11.2 requires the anonymous individuals of an entailment query
 * to form a forest in which
 *   • each pair of anonymous individuals is connected by at most one object
 *     property assertion,
 *   • each root has at most one object property assertion to a named individual,
 *   • there are no cycles.
 * Anything else is rejected with an error.
 */
class AnonymousIndividualForestBuilder {
  /** @param {typeof import('../owl/OWLExpressions')} factory */
  constructor(factory) {
    this.factory = factory;
    /** Named individuals that occur in the axioms (informational). */
    this.namedNodes = new Set();
    /** Every anonymous individual that occurs in the axioms. */
    this.nodes = new Set();
    /** key → the individual object it came from (all the maps below are keyed). */
    this.individualsByKey = new Map();
    /** Undirected adjacency of the forest: key(anon) → Set<key(anon)>. */
    this.edges = new Map();
    /** key(anon) → Map<key(named), Set<objectPropertyExpression>>. */
    this.specialOPEdges = new Map();
    /** key(anon) → Set<classExpression> (HermiT's `nodelLabels`, typo intact). */
    this.nodelLabels = new Map();
    /** edgeKey(sub, obj) → the *named* object property, in subject→object direction. */
    this.edgeOPLabels = new Map();
    /** Roll-ups that became class assertions on a named individual. */
    this.anonIndAxioms = new Set();
    /** Roll-ups with no named anchor: `⊤ ⊑ ¬C`, must make the KB inconsistent. */
    this.anonNoNamedIndAxioms = new Set();
  }

  /**
   * @param {Iterable<object>} axioms
   */
  constructConceptsForAnonymousIndividuals(axioms) {
    const E = this.factory;

    // 1. Build the labelled forest.
    for (const ax of axioms) this._visitForestAxiom(ax);

    // 2. Split into components and pick a root for each.
    const components = this._getComponents();
    const componentsToRoots = this._findSuitableRoots(components);

    // 3. Read off the rolled-up concepts.
    for (const rootKey of componentsToRoots.values()) {
      const root = this._individualForKey(rootKey);
      const special = this.specialOPEdges.get(rootKey);
      if (special === undefined) {
        // No named neighbour: roll up into a concept that must be non-empty in
        // every model, expressed as `⊤ ⊑ ¬C` (adding it must clash).
        const c = this._getClassExpressionFor(rootKey, null);
        this.anonNoNamedIndAxioms.add(E.subclassOf(E.owlThing(), E.objectComplementOf(c)));
      } else {
        // Exactly one named neighbour with exactly one property — roll up into
        // a class assertion on that individual.
        if (special.size !== 1) {
          throw new Error(
            'Internal error: the anonymous individuals were decided to form a valid '
            + 'forest, but actually they do not.');
        }
        const [namedKey, ops] = [...special.entries()][0];
        if (ops.size !== 1) {
          throw new Error(
            'Internal error: the anonymous individuals were decided to form a valid '
            + 'forest, but actually they do not.');
        }
        // The recorded property points named → anonymous, so the roll-up needs
        // its inverse.
        const op = E.inversePropertyOf([...ops][0]);
        const c = this._getClassExpressionFor(rootKey, null);
        this.anonIndAxioms.add(
          E.classAssertion(E.objectSomeValuesFrom(op, c), this._individualForKey(namedKey)));
      }
    }
  }

  /** @returns {Set<object>} */
  getAnonIndAxioms() { return this.anonIndAxioms; }
  /** @returns {Set<object>} */
  getAnonNoNamedIndAxioms() { return this.anonNoNamedIndAxioms; }

  // ---- forest construction -------------------------------------------------

  _visitForestAxiom(axiom) {
    const E = this.factory;
    const AT = E.AxiomType;
    switch (axiomTypeOf(axiom)) {
      case AT.CLASS_ASSERTION: {
        if (E.isOWLThing(axiom.classExpression)) return;
        const node = axiom.individual;
        const key = this._register(node);
        if (!isAnonymousIndividual(node)) {
          this.namedNodes.add(node);
          return;
        }
        this.nodes.add(node);
        this._addLabel(key, axiom.classExpression);
        return;
      }

      case AT.OBJECT_PROPERTY_ASSERTION: {
        const subAnon = isAnonymousIndividual(axiom.subject);
        const objAnon = isAnonymousIndividual(axiom.object);
        let sub = axiom.subject;
        let obj = axiom.object;
        let ope = axiom.property;

        if (!subAnon && !objAnon) return; // not interesting for the forest

        if (subAnon !== objAnon) {
          // Exactly one anonymous: normalise so `sub` is the anonymous one and
          // the property points named → anonymous.
          if (!subAnon) {
            const tmp = sub; sub = obj; obj = tmp;
            ope = E.inversePropertyOf(ope);
          }
          const namedKey = this._register(obj);
          const unnamedKey = this._register(sub);
          this.namedNodes.add(obj);
          this.nodes.add(sub);

          let byNamed = this.specialOPEdges.get(unnamedKey);
          if (byNamed === undefined) {
            byNamed = new Map();
            this.specialOPEdges.set(unnamedKey, byNamed);
          }
          // DEVIATION: HermiT replaced the whole inner map when `named` was a
          // new key, discarding earlier named neighbours. Merge instead.
          let ops = byNamed.get(namedKey);
          if (ops === undefined) {
            ops = new Set();
            byNamed.set(namedKey, ops);
          }
          ops.add(ope);
          return;
        }

        // Both anonymous.
        let op;
        if (E.isAnonymousProperty(ope)) {
          // `R⁻(x, y)` ≡ `R(y, x)`: flip the pair so the label is the named
          // property in subject→object direction.
          op = E.namedPropertyOf(ope);
          const tmp = sub; sub = obj; obj = tmp;
        } else {
          op = ope;
        }
        const subKey = this._register(sub);
        const objKey = this._register(obj);
        this.nodes.add(sub);
        this.nodes.add(obj);

        const forward = this.edges.get(subKey);
        const backward = this.edges.get(objKey);
        if ((forward !== undefined && forward.has(objKey))
          || (backward !== undefined && backward.has(subKey))) {
          throw new Error(
            'Invalid input ontology: there are two object property assertions for the '
            + 'same anonymous individuals, which is not allowed (see OWL 2 Syntax Sec 11.2).');
        }
        if (forward === undefined) this.edges.set(subKey, new Set([objKey]));
        else forward.add(objKey);
        if (backward === undefined) this.edges.set(objKey, new Set([subKey]));
        else backward.add(subKey);
        this.edgeOPLabels.set(edgeKey(sub, obj), op);
        return;
      }

      case AT.DATA_PROPERTY_ASSERTION: {
        if (!isAnonymousIndividual(axiom.subject)) return;
        const sub = axiom.subject;
        this.nodes.add(sub);
        const c = E.dataHasValue(axiom.property, E.assertionLiteral(axiom));
        this._addLabel(this._register(sub), c);
        return;
      }

      default:
        // Every other axiom type is a no-op for the forest, exactly as in HermiT.
        return;
    }
  }

  _addLabel(nodeKey, classExpression) {
    let labels = this.nodelLabels.get(nodeKey);
    if (labels === undefined) {
      labels = new Set();
      this.nodelLabels.set(nodeKey, labels);
    }
    labels.add(classExpression);
  }

  /** Records an individual under its key and returns the key. */
  _register(ind) {
    const key = individualKey(ind);
    if (!this.individualsByKey.has(key)) this.individualsByKey.set(key, ind);
    return key;
  }

  /** The individual object recorded for a key. */
  _individualForKey(key) {
    const ind = this.individualsByKey.get(key);
    if (ind === undefined) {
      throw new Error(`Internal error: no individual recorded for key '${key}'.`);
    }
    return ind;
  }

  // ---- roll-up -------------------------------------------------------------

  /**
   * The class expression describing the subtree rooted at `nodeKey`, excluding
   * the branch back to `predecessorKey`.
   *
   * @param {string} nodeKey
   * @param {string|null} predecessorKey
   */
  _getClassExpressionFor(nodeKey, predecessorKey) {
    const E = this.factory;
    const successors = this.edges.get(nodeKey);
    const children = successors === undefined
      ? []
      : [...successors].filter(k => k !== predecessorKey);

    const concepts = [];

    // DEVIATION: HermiT omitted the node's own labels on the non-leaf branch.
    const labels = this.nodelLabels.get(nodeKey);
    if (labels !== undefined) {
      for (const l of labels) concepts.push(l);
    }

    for (const successorKey of children) {
      const op = this._edgeProperty(nodeKey, successorKey);
      concepts.push(E.objectSomeValuesFrom(op, this._getClassExpressionFor(successorKey, nodeKey)));
    }

    if (concepts.length === 0) return E.owlThing();
    if (concepts.length === 1) return concepts[0];
    return E.objectIntersectionOf(concepts);
  }

  /**
   * The object property expression to use when rolling up from `nodeKey` to
   * `successorKey`. The label is stored in subject→object direction, so
   * traversing an edge backwards requires the inverse.
   */
  _edgeProperty(nodeKey, successorKey) {
    const E = this.factory;
    const node = this._individualForKey(nodeKey);
    const successor = this._individualForKey(successorKey);

    const forward = this.edgeOPLabels.get(edgeKey(node, successor));
    if (forward !== undefined) return forward;
    const backward = this.edgeOPLabels.get(edgeKey(successor, node));
    if (backward !== undefined) return E.objectInverseOf(backward); // DEVIATION: HermiT omitted the inverse.
    throw new Error(
      'Internal error: some edge in the forest of anonymous individuals has no edge '
      + 'label although it should.');
  }

  // ---- components / roots --------------------------------------------------

  /**
   * The connected components of the anonymous-individual graph.
   * @returns {Set<Set<string>>} component → set of node keys
   */
  _getComponents() {
    const components = new Set();
    if (this.nodes.size === 0) return components;

    const toProcess = new Set([...this.nodes].map(n => this._register(n)));
    while (toProcess.size > 0) {
      const currentComponent = new Set();
      // Nodes already placed in this component. In a forest the only visited
      // neighbour of a node is its predecessor (which we skip before queueing),
      // so reaching a visited node again means there is a cycle.
      //
      // DEVIATION: HermiT detects cycles by scanning the *pending* work queue,
      // which is empty by the time the closing edge is followed — so a genuine
      // cycle makes its `while (!workQueue.isEmpty())` loop run forever.
      const visited = new Set();
      /** @type {{first:string, second:string|null}[]} */
      const workQueue = [{ first: [...toProcess][0], second: null }];
      while (workQueue.length > 0) {
        const nodePlusPredecessor = workQueue.shift();
        if (visited.has(nodePlusPredecessor.first)) {
          throw new Error(
            'Invalid input ontology: the anonymous individuals cannot be arranged '
            + 'into a forest as required (cf. OWL 2 Structural Specification and '
            + 'Functional-Style Syntax, Sec. 11.2) because there is a cycle.');
        }
        visited.add(nodePlusPredecessor.first);
        currentComponent.add(nodePlusPredecessor.first);
        const successors = this.edges.get(nodePlusPredecessor.first);
        if (successors !== undefined) {
          for (const ind of successors) {
            if (nodePlusPredecessor.second === null || ind !== nodePlusPredecessor.second) {
              workQueue.push({ first: ind, second: nodePlusPredecessor.first });
            }
          }
        }
      }
      components.add(currentComponent);
      for (const k of currentComponent) toProcess.delete(k);
    }
    return components;
  }

  /**
   * Picks a root per component: prefer a node with exactly one named relation
   * (that allows rolling up into a class assertion), else any node with none.
   * @param {Set<Set<string>>} components
   * @returns {Map<Set<string>, string>}
   */
  _findSuitableRoots(components) {
    const componentsToRoots = new Map();
    for (const component of components) {
      let root = null;
      let rootWithOneNamedRelation = null;
      for (const ind of component) {
        const special = this.specialOPEdges.get(ind);
        if (special !== undefined) {
          if (special.size < 2) rootWithOneNamedRelation = ind;
        } else {
          root = ind;
        }
      }
      if (root === null && rootWithOneNamedRelation === null) {
        throw new Error(
          'Invalid input ontology: one of the trees in the forest of anonymous '
          + 'individuals has no root that satisfies the criteria on roots (cf. OWL 2 '
          + 'Structural Specification and Functional-Style Syntax, Sec. 11.2).');
      }
      componentsToRoots.set(component, rootWithOneNamedRelation !== null ? rootWithOneNamedRelation : root);
    }
    return componentsToRoots;
  }
}

module.exports = {
  EntailmentChecker,
  AnonymousIndividualForestBuilder,
  isAnonymousIndividual,
  axiomTypeOf,
  individualKey
};
