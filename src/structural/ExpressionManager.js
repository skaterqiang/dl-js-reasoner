'use strict';

// ---------------------------------------------------------------------------
// structural/ExpressionManager.js — NNF, complement-NNF and simplification for
// OWL 2 class expressions and data ranges.
//
// A direct port of org.semanticweb.HermiT.structural.ExpressionManager. The
// Java version uses six OWL API visitors; here they are six recursive functions
// dispatched on `exprType(e)`, which also lets them consume protege-js objects
// (same shapes, different classes).
//
//   getNNF(d)            — negation normal form: negations pushed to atoms.
//   getComplementNNF(d)  — NNF of ¬d, computed without building the complement.
//   getSimplified(d)     — algebraic simplification (Thing/Nothing absorption,
//                          HasValue → SomeValuesFrom∘OneOf, ExactCard → Min⊓Max,
//                          MinCard 1 → SomeValuesFrom, MaxCard 0 → AllValuesFrom¬,
//                          double-negation elimination, n-ary flattening).
// ---------------------------------------------------------------------------

const E = require('../owl/OWLExpressions');

const {
  ClassExpressionType: T,
  exprType, isOWLThing, isOWLNothing, isTopDatatype, isBottomDataRange,
  operandOf, operandsOf, cardinalityFiller, structuralKey
} = E;

// ===========================================================================
// NNF
// ===========================================================================

function getNNF(d) {
  if (d === null || d === undefined) return d;
  switch (exprType(d)) {
    case T.OWL_CLASS:
    case T.DATATYPE:
    case T.OBJECT_ONE_OF:
    case T.DATA_ONE_OF:
    case T.DATA_HAS_VALUE:
      return d;

    case T.OBJECT_INTERSECTION_OF:
      return E.objectIntersectionOf(operandsOf(d).map(getNNF));
    case T.OBJECT_UNION_OF:
      return E.objectUnionOf(operandsOf(d).map(getNNF));
    case T.OBJECT_COMPLEMENT_OF:
      return getComplementNNF(operandOf(d));

    case T.OBJECT_SOME_VALUES_FROM:
      return E.objectSomeValuesFrom(d.property, getNNF(d.filler));
    case T.OBJECT_ALL_VALUES_FROM:
      return E.objectAllValuesFrom(d.property, getNNF(d.filler));
    case T.OBJECT_HAS_VALUE:
      return E.objectHasValue(d.property, d.value !== undefined ? d.value : d.filler);
    case T.OBJECT_HAS_SELF:
      return E.objectHasSelf(d.property);

    case T.OBJECT_MIN_CARDINALITY:
      return E.objectMinCardinality(d.cardinality, d.property, getNNF(cardinalityFiller(d, false)));
    case T.OBJECT_MAX_CARDINALITY:
      return E.objectMaxCardinality(d.cardinality, d.property, getNNF(cardinalityFiller(d, false)));
    case T.OBJECT_EXACT_CARDINALITY:
      return E.objectExactCardinality(d.cardinality, d.property, getNNF(cardinalityFiller(d, false)));

    case T.DATA_SOME_VALUES_FROM:
      return E.dataSomeValuesFrom(d.property, getDataRangeNNF(d.filler));
    case T.DATA_ALL_VALUES_FROM:
      return E.dataAllValuesFrom(d.property, getDataRangeNNF(d.filler));
    case T.DATA_MIN_CARDINALITY:
      return E.dataMinCardinality(d.cardinality, d.property, getDataRangeNNF(cardinalityFiller(d, true)));
    case T.DATA_MAX_CARDINALITY:
      return E.dataMaxCardinality(d.cardinality, d.property, getDataRangeNNF(cardinalityFiller(d, true)));
    case T.DATA_EXACT_CARDINALITY:
      return E.dataExactCardinality(d.cardinality, d.property, getDataRangeNNF(cardinalityFiller(d, true)));

    default:
      return d;
  }
}

function getDataRangeNNF(dr) {
  if (dr === null || dr === undefined) return dr;
  switch (exprType(dr)) {
    case T.DATATYPE:
    case T.DATA_ONE_OF:
    case T.DATATYPE_RESTRICTION:
      return dr;
    case T.DATA_COMPLEMENT_OF:
      return getDataRangeComplementNNF(operandOf(dr));
    case T.DATA_INTERSECTION_OF:
      return E.dataIntersectionOf(operandsOf(dr).map(getDataRangeNNF));
    case T.DATA_UNION_OF:
      return E.dataUnionOf(operandsOf(dr).map(getDataRangeNNF));
    default:
      return dr;
  }
}

// ===========================================================================
// Complement NNF
// ===========================================================================

function getComplementNNF(d) {
  if (d === null || d === undefined) return d;
  switch (exprType(d)) {
    case T.OWL_CLASS:
      if (isOWLThing(d)) return E.owlNothing();
      if (isOWLNothing(d)) return E.owlThing();
      return E.objectComplementOf(d);

    case T.OBJECT_INTERSECTION_OF:
      return E.objectUnionOf(operandsOf(d).map(getComplementNNF));
    case T.OBJECT_UNION_OF:
      return E.objectIntersectionOf(operandsOf(d).map(getComplementNNF));
    case T.OBJECT_COMPLEMENT_OF:
      return getNNF(operandOf(d));
    case T.OBJECT_ONE_OF:
      return E.objectComplementOf(d);

    case T.OBJECT_SOME_VALUES_FROM:
      return E.objectAllValuesFrom(d.property, getComplementNNF(d.filler));
    case T.OBJECT_ALL_VALUES_FROM:
      return E.objectSomeValuesFrom(d.property, getComplementNNF(d.filler));
    case T.OBJECT_HAS_VALUE:
      return E.objectComplementOf(getNNF(d));
    case T.OBJECT_HAS_SELF:
      return E.objectComplementOf(getNNF(d));

    case T.OBJECT_MIN_CARDINALITY: {
      if (d.cardinality === 0) return E.owlNothing();
      const filler = getNNF(cardinalityFiller(d, false));
      return E.objectMaxCardinality(d.cardinality - 1, d.property, filler);
    }
    case T.OBJECT_MAX_CARDINALITY:
      return E.objectMinCardinality(d.cardinality + 1, d.property, getNNF(cardinalityFiller(d, false)));
    case T.OBJECT_EXACT_CARDINALITY: {
      const filler = getNNF(cardinalityFiller(d, false));
      if (d.cardinality === 0) return E.objectMinCardinality(1, d.property, filler);
      return E.objectUnionOf([
        E.objectMaxCardinality(d.cardinality - 1, d.property, filler),
        E.objectMinCardinality(d.cardinality + 1, d.property, filler)
      ]);
    }

    case T.DATA_SOME_VALUES_FROM:
      return E.dataAllValuesFrom(d.property, getDataRangeComplementNNF(d.filler));
    case T.DATA_ALL_VALUES_FROM:
      return E.dataSomeValuesFrom(d.property, getDataRangeComplementNNF(d.filler));
    case T.DATA_HAS_VALUE:
      return E.objectComplementOf(d);

    case T.DATA_MIN_CARDINALITY: {
      if (d.cardinality === 0) return E.owlNothing();
      const filler = getDataRangeNNF(cardinalityFiller(d, true));
      return E.dataMaxCardinality(d.cardinality - 1, d.property, filler);
    }
    case T.DATA_MAX_CARDINALITY:
      return E.dataMinCardinality(d.cardinality + 1, d.property, getDataRangeNNF(cardinalityFiller(d, true)));
    case T.DATA_EXACT_CARDINALITY: {
      const filler = getDataRangeNNF(cardinalityFiller(d, true));
      if (d.cardinality === 0) return E.dataMinCardinality(1, d.property, filler);
      return E.objectUnionOf([
        E.dataMaxCardinality(d.cardinality - 1, d.property, filler),
        E.dataMinCardinality(d.cardinality + 1, d.property, filler)
      ]);
    }

    default:
      return E.objectComplementOf(getNNF(d));
  }
}

function getDataRangeComplementNNF(dr) {
  if (dr === null || dr === undefined) return dr;
  switch (exprType(dr)) {
    case T.DATATYPE:
    case T.DATA_ONE_OF:
    case T.DATATYPE_RESTRICTION:
      return E.dataComplementOf(dr);
    case T.DATA_COMPLEMENT_OF:
      return getDataRangeNNF(operandOf(dr));
    case T.DATA_INTERSECTION_OF:
      return E.dataUnionOf(operandsOf(dr).map(getDataRangeComplementNNF));
    case T.DATA_UNION_OF:
      return E.dataIntersectionOf(operandsOf(dr).map(getDataRangeComplementNNF));
    default:
      return E.dataComplementOf(dr);
  }
}

// ===========================================================================
// Simplification
// ===========================================================================

function getSimplified(d) {
  if (d === null || d === undefined) return d;
  switch (exprType(d)) {
    case T.OWL_CLASS:
    case T.OBJECT_ONE_OF:
      return d;

    case T.OBJECT_INTERSECTION_OF: {
      const conjuncts = [];
      for (const op of operandsOf(d)) {
        const s = getSimplified(op);
        if (isOWLThing(s)) continue;
        if (isOWLNothing(s)) return E.owlNothing();
        if (exprType(s) === T.OBJECT_INTERSECTION_OF) conjuncts.push(...operandsOf(s));
        else conjuncts.push(s);
      }
      return E.objectIntersectionOf(conjuncts);
    }
    case T.OBJECT_UNION_OF: {
      const disjuncts = [];
      for (const op of operandsOf(d)) {
        const s = getSimplified(op);
        if (isOWLThing(s)) return E.owlThing();
        if (isOWLNothing(s)) continue;
        if (exprType(s) === T.OBJECT_UNION_OF) disjuncts.push(...operandsOf(s));
        else disjuncts.push(s);
      }
      return E.objectUnionOf(disjuncts);
    }
    case T.OBJECT_COMPLEMENT_OF: {
      const s = getSimplified(operandOf(d));
      if (isOWLThing(s)) return E.owlNothing();
      if (isOWLNothing(s)) return E.owlThing();
      if (exprType(s) === T.OBJECT_COMPLEMENT_OF) return operandOf(s);
      return E.objectComplementOf(s);
    }

    case T.OBJECT_SOME_VALUES_FROM: {
      const filler = getSimplified(d.filler);
      return isOWLNothing(filler) ? E.owlNothing() : E.objectSomeValuesFrom(d.property, filler);
    }
    case T.OBJECT_ALL_VALUES_FROM: {
      const filler = getSimplified(d.filler);
      return isOWLThing(filler) ? E.owlThing() : E.objectAllValuesFrom(d.property, filler);
    }
    case T.OBJECT_HAS_VALUE:
      return E.objectSomeValuesFrom(d.property, E.objectOneOf([d.value !== undefined ? d.value : d.filler]));
    case T.OBJECT_HAS_SELF:
      return E.objectHasSelf(d.property);

    case T.OBJECT_MIN_CARDINALITY: {
      const filler = getSimplified(cardinalityFiller(d, false));
      if (d.cardinality <= 0) return E.owlThing();
      if (isOWLNothing(filler)) return E.owlNothing();
      if (d.cardinality === 1) return E.objectSomeValuesFrom(d.property, filler);
      return E.objectMinCardinality(d.cardinality, d.property, filler);
    }
    case T.OBJECT_MAX_CARDINALITY: {
      const filler = getSimplified(cardinalityFiller(d, false));
      if (isOWLNothing(filler)) return E.owlThing();
      if (d.cardinality <= 0) return E.objectAllValuesFrom(d.property, E.objectComplementOf(filler));
      return E.objectMaxCardinality(d.cardinality, d.property, filler);
    }
    case T.OBJECT_EXACT_CARDINALITY: {
      const filler = getSimplified(cardinalityFiller(d, false));
      if (d.cardinality < 0) return E.owlNothing();
      if (d.cardinality === 0) return E.objectAllValuesFrom(d.property, E.objectComplementOf(filler));
      if (isOWLNothing(filler)) return E.owlNothing();
      return E.objectIntersectionOf([
        E.objectMinCardinality(d.cardinality, d.property, filler),
        E.objectMaxCardinality(d.cardinality, d.property, filler)
      ]);
    }

    case T.DATA_SOME_VALUES_FROM: {
      const filler = getDataRangeSimplified(d.filler);
      return isBottomDataRange(filler) ? E.owlNothing() : E.dataSomeValuesFrom(d.property, filler);
    }
    case T.DATA_ALL_VALUES_FROM: {
      const filler = getDataRangeSimplified(d.filler);
      return isTopDatatype(filler) ? E.owlThing() : E.dataAllValuesFrom(d.property, filler);
    }
    case T.DATA_HAS_VALUE:
      return E.dataSomeValuesFrom(d.property, E.dataOneOf([E.literal(d.value !== undefined ? d.value : d.filler)]));

    case T.DATA_MIN_CARDINALITY: {
      const filler = getDataRangeSimplified(cardinalityFiller(d, true));
      if (d.cardinality <= 0) return E.owlThing();
      if (isBottomDataRange(filler)) return E.owlNothing();
      if (d.cardinality === 1) return E.dataSomeValuesFrom(d.property, filler);
      return E.dataMinCardinality(d.cardinality, d.property, filler);
    }
    case T.DATA_MAX_CARDINALITY: {
      const filler = getDataRangeSimplified(cardinalityFiller(d, true));
      if (isBottomDataRange(filler)) return E.owlThing();
      if (d.cardinality <= 0) return E.dataAllValuesFrom(d.property, E.dataComplementOf(filler));
      return E.dataMaxCardinality(d.cardinality, d.property, filler);
    }
    case T.DATA_EXACT_CARDINALITY: {
      const filler = getDataRangeSimplified(cardinalityFiller(d, true));
      if (d.cardinality < 0) return E.owlNothing();
      if (d.cardinality === 0) return E.dataAllValuesFrom(d.property, E.dataComplementOf(filler));
      if (isBottomDataRange(filler)) return E.owlNothing();
      return E.objectIntersectionOf([
        E.dataMinCardinality(d.cardinality, d.property, filler),
        E.dataMaxCardinality(d.cardinality, d.property, filler)
      ]);
    }

    default:
      return d;
  }
}

function getDataRangeSimplified(dr) {
  if (dr === null || dr === undefined) return dr;
  switch (exprType(dr)) {
    case T.DATATYPE:
    case T.DATA_ONE_OF:
    case T.DATATYPE_RESTRICTION:
      return dr;
    case T.DATA_COMPLEMENT_OF: {
      const s = getDataRangeSimplified(operandOf(dr));
      if (exprType(s) === T.DATA_COMPLEMENT_OF) return operandOf(s);
      return E.dataComplementOf(s);
    }
    case T.DATA_INTERSECTION_OF: {
      const conjuncts = [];
      for (const op of operandsOf(dr)) {
        const s = getDataRangeSimplified(op);
        if (isTopDatatype(s)) continue;
        if (exprType(s) === T.DATA_INTERSECTION_OF) conjuncts.push(...operandsOf(s));
        else conjuncts.push(s);
      }
      return E.dataIntersectionOf(conjuncts);
    }
    case T.DATA_UNION_OF: {
      const disjuncts = [];
      for (const op of operandsOf(dr)) {
        const s = getDataRangeSimplified(op);
        if (isTopDatatype(s)) return E.topDatatype();
        if (exprType(s) === T.DATA_UNION_OF) disjuncts.push(...operandsOf(s));
        else disjuncts.push(s);
      }
      return E.dataUnionOf(disjuncts);
    }
    default:
      return dr;
  }
}

// ===========================================================================
// Convenience: the two composites HermiT uses everywhere.
// ===========================================================================

/** NNF of the simplified form — HermiT's `positive(description)`. */
function positive(d) { return getNNF(getSimplified(d)); }
/** Complement-NNF of the simplified form — HermiT's `negative(description)`. */
function negative(d) { return getComplementNNF(getSimplified(d)); }

/** True when `d` is a data range (not a class expression). */
function isDataRange(d) {
  const t = exprType(d);
  return t === T.DATATYPE || t === T.DATA_ONE_OF || t === T.DATATYPE_RESTRICTION
    || t === T.DATA_COMPLEMENT_OF || t === T.DATA_INTERSECTION_OF || t === T.DATA_UNION_OF;
}

module.exports = {
  getNNF, getComplementNNF, getSimplified,
  getDataRangeNNF, getDataRangeComplementNNF, getDataRangeSimplified,
  positive, negative, isDataRange, structuralKey
};
