'use strict';

// ---------------------------------------------------------------------------
// structural/RuleNormalizer.js — SWRL rule normalization.
//
// Port of OWLNormalization.RuleNormalizer and OWLNormalization.Rule2FactConverter.
//
// Two jobs:
//   1. A rule with an EMPTY body is really a set of facts, so it is converted
//      directly into ClassAssertion / ObjectPropertyAssertion / ... axioms
//      (Rule2FactConverter).
//   2. A rule with a body is split into one rule per head atom (Lloyd-Topor),
//      every non-atomic class expression / data range in an atom is replaced by
//      a fresh named class or datatype plus a defining inclusion, individuals
//      are replaced by variables constrained by `ObjectOneOf({ind})` atoms, and
//      sameAs/differentFrom atoms are used to canonicalise variables.
//
// The normalized atoms are plain objects with the same shape as protege-js's
// SWRL atoms (`src/model/SWRL.js`), so this module has no dependency on it.
// ---------------------------------------------------------------------------

const E = require('../owl/OWLExpressions');
const EM = require('./ExpressionManager');
const { DisjunctiveRule } = require('./OWLAxioms');

const SWRLAtomType = Object.freeze({
  CLASS: 'ClassAtom',
  OBJECT_PROPERTY: 'ObjectPropertyAtom',
  DATA_PROPERTY: 'DataPropertyAtom',
  SAME_AS: 'SameAsAtom',
  DIFFERENT_FROM: 'DifferentFromAtom',
  DATA_RANGE: 'DataRangeAtom',
  BUILTIN: 'BuiltInAtom'
});

/** A SWRL variable. `name` is the short form, e.g. `x` for `?x`. */
class SWRLVariable {
  constructor(name) { this.name = String(name).replace(/^\?/, ''); }
  toString() { return `?${this.name}`; }
}

const classAtom = (classExpression, arg) =>
  _atom({ type: SWRLAtomType.CLASS, classExpression, arg });
const objectPropertyAtom = (property, arg1, arg2) =>
  _atom({ type: SWRLAtomType.OBJECT_PROPERTY, property, arg1, arg2 });
const dataPropertyAtom = (property, arg1, arg2) =>
  _atom({ type: SWRLAtomType.DATA_PROPERTY, property, arg1, arg2 });
const sameAsAtom = (arg1, arg2) =>
  _atom({ type: SWRLAtomType.SAME_AS, arg1, arg2 });
const differentFromAtom = (arg1, arg2) =>
  _atom({ type: SWRLAtomType.DIFFERENT_FROM, arg1, arg2 });
const dataRangeAtom = (dataRange, arg) =>
  _atom({ type: SWRLAtomType.DATA_RANGE, dataRange, arg });

/** Attach a readable `toString` so normalized atoms can be printed/debugged. */
function _atom(a) {
  a.toString = function () {
    switch (this.type) {
      case SWRLAtomType.CLASS: return `${this.classExpression}(${this.arg})`;
      case SWRLAtomType.DATA_RANGE: return `${this.dataRange}(${this.arg})`;
      case SWRLAtomType.OBJECT_PROPERTY:
      case SWRLAtomType.DATA_PROPERTY:
        return `${this.property}(${this.arg1},${this.arg2})`;
      case SWRLAtomType.SAME_AS: return `sameAs(${this.arg1},${this.arg2})`;
      case SWRLAtomType.DIFFERENT_FROM: return `differentFrom(${this.arg1},${this.arg2})`;
      default: return `${this.type}(${JSON.stringify(Object.keys(this))})`;
    }
  };
  return a;
}

/**
 * Is `arg` a SWRL variable?
 *
 * Three shapes occur in practice:
 *   1. this module's own `SWRLVariable` — caught by `instanceof`;
 *   2. a hand-built object explicitly tagged `{ type: 'SWRLVariable', name }`;
 *   3. **protege-js' `SWRLVariable`, which carries only `{ iri }` and NO type
 *      tag whatsoever.**
 *
 * Case 3 is what makes this non-trivial. It has to be told apart from the
 * other things that can legally appear in an argument position:
 *   - `OWLNamedIndividual`      → `{ iri, entityType }`
 *   - `OWLAnonymousIndividual`  → `{ nodeId }`
 *   - `SWRLIndividualArgument`  → `{ individual }`
 *   - `SWRLLiteralArgument`     → `{ literal }`
 * So a variable is "has an `iri`, and is none of those".
 *
 * Getting this wrong is silent and nasty: an unrecognized variable falls
 * through to `individualOf` and is treated as a NAMED individual, so it gets
 * rewritten into an `ObjectOneOf` nominal that nothing ever asserts. The rule
 * then simply never fires and no error is raised.
 */
function isVariable(arg) {
  if (!arg || typeof arg !== 'object') return false;
  if (arg instanceof SWRLVariable) return true;
  if (arg.type === 'SWRLVariable') return true;
  if (typeof arg.iri === 'undefined') return false;
  return arg.entityType === undefined
    && arg.nodeId === undefined
    && typeof arg.individual === 'undefined'
    && typeof arg.literal === 'undefined';
}

/**
 * The variable's name, used as the key for `variableRepresentative`.
 *
 * protege-js variables have no `name`, only an `iri`, so fall back to the IRI
 * string — it is unique per variable, which is all the key needs to be.
 */
function variableName(arg) { return isVariable(arg) ? (arg.name || String(arg.iri || arg)) : null; }
/** The individual of an argument that is not a variable, else null. */
function individualOf(arg) {
  if (isVariable(arg)) return null;
  if (arg && typeof arg.individual !== 'undefined') return arg.individual; // SWRLIndividualArgument
  return arg;
}
function literalOf(arg) {
  if (arg && typeof arg.literal !== 'undefined') return arg.literal; // SWRLLiteralArgument
  return arg;
}
function atomType(atom) { return atom.type; }

// ===========================================================================
// Shared helpers
// ===========================================================================

function isSimple(d) {
  const t = E.exprType(d);
  if (t === E.ClassExpressionType.OWL_CLASS) return true;
  return t === E.ClassExpressionType.OBJECT_COMPLEMENT_OF && E.exprType(E.operandOf(d)) === E.ClassExpressionType.OWL_CLASS;
}

function isAnonymousIndividual(ind) {
  if (!ind) return false;
  if (typeof ind.isAnonymous === 'function') return !!ind.isAnonymous();
  return ind.nodeId !== undefined;
}

// ===========================================================================
// Rule2FactConverter — rules with an empty body become facts.
// ===========================================================================

class Rule2FactConverter {
  /**
   * @param {import('./OWLNormalization').OWLNormalization} normalization
   * @param {object[][]} newInclusions worklist of class-expression disjunctions
   */
  constructor(normalization, newInclusions) {
    this.normalization = normalization;
    this.axioms = normalization.axioms;
    this.newInclusions = newInclusions;
    this.freshDataProperties = 0;
    this.freshIndividuals = 0;
  }

  getFreshIndividual() {
    const ind = E.namedIndividual(`internal:nom#swrlfact${this.freshIndividuals++}`);
    this.axioms.namedIndividuals.add(ind);
    return ind;
  }

  getFreshDataProperty() {
    return E.dataProperty(`internal:freshDP#${++this.freshDataProperties}`);
  }

  addFact(fact) { this.axioms.facts.push(fact); }

  convert(atom) {
    switch (atomType(atom)) {
      case SWRLAtomType.CLASS: {
        const ind = individualOf(atom.arg);
        if (ind === null) {
          throw new Error(`A SWRL rule contains a head atom ${atom} with a variable that does not occur in the body.`);
        }
        if (isAnonymousIndividual(ind)) this._throwAnon(atom);
        if (!isSimple(atom.classExpression)) {
          const { definition, alreadyExists } = this.normalization.getDefinitionFor(atom.classExpression);
          if (!alreadyExists) {
            this.newInclusions.push([this.normalization.negative(definition), atom.classExpression]);
          }
          this.addFact(E.classAssertion(definition, ind));
        } else {
          this.addFact(E.classAssertion(atom.classExpression, ind));
        }
        return;
      }
      case SWRLAtomType.DATA_RANGE: {
        const ind = individualOf(atom.arg);
        if (ind === null) {
          throw new Error(`A SWRL rule contains a head atom ${atom} with a variable that does not occur in the body.`);
        }
        // dr(literal) :- becomes
        //   ClassAssertion(DataSomeValuesFrom(freshDP, DataOneOf(literal)), freshIndividual)
        //   ⊤ ⊑ ∀freshDP.dr
        const lit = E.literal(literalOf(atom.arg));
        const freshIndividual = this.getFreshIndividual();
        const freshDP = this.getFreshDataProperty();
        const some = E.dataSomeValuesFrom(freshDP, E.dataOneOf([lit]));
        const { definition, alreadyExists } = this.normalization.getDefinitionFor(some);
        if (!alreadyExists) {
          this.newInclusions.push([this.normalization.negative(definition), some]);
        }
        this.addFact(E.classAssertion(definition, freshIndividual));
        this.newInclusions.push([E.dataAllValuesFrom(freshDP, atom.dataRange)]);
        return;
      }
      case SWRLAtomType.OBJECT_PROPERTY: {
        const first = individualOf(atom.arg1);
        const second = individualOf(atom.arg2);
        if (first === null || second === null) {
          throw new Error(`A SWRL rule contains a head atom ${atom} with a variable that does not occur in the body.`);
        }
        if (isAnonymousIndividual(first) || isAnonymousIndividual(second)) this._throwAnon(atom);
        const ope = atom.property;
        if (E.isAnonymousProperty(ope)) {
          this.addFact(E.objectPropertyAssertion(E.namedPropertyOf(ope), second, first));
        } else {
          this.addFact(E.objectPropertyAssertion(ope, first, second));
        }
        return;
      }
      case SWRLAtomType.DATA_PROPERTY: {
        const ind = individualOf(atom.arg1);
        if (ind === null || isVariable(atom.arg2)) {
          throw new Error(`A SWRL rule contains a head atom ${atom} with a variable that does not occur in the body.`);
        }
        if (isAnonymousIndividual(ind)) this._throwAnon(atom);
        this.addFact(E.dataPropertyAssertion(atom.property, ind, E.literal(literalOf(atom.arg2))));
        return;
      }
      case SWRLAtomType.BUILTIN:
        throw new Error(`Error: A rule uses built-in atoms (${atom}), but built-in atoms are not supported yet.`);
      case SWRLAtomType.SAME_AS: {
        const inds = new Set();
        for (const arg of [atom.arg1, atom.arg2]) {
          const ind = individualOf(arg);
          if (ind === null) {
            throw new Error(`A SWRL rule contains a head atom ${atom} with a variable that does not occur in the body.`);
          }
          if (isAnonymousIndividual(ind)) this._throwAnon(atom);
          inds.add(ind);
        }
        this.addFact(E.sameIndividual([...inds]));
        return;
      }
      case SWRLAtomType.DIFFERENT_FROM: {
        const inds = new Set();
        for (const arg of [atom.arg1, atom.arg2]) {
          const ind = individualOf(arg);
          if (ind === null) {
            throw new Error(`A SWRL rule contains a head atom ${atom} with a variable that does not occur in the body.`);
          }
          if (isAnonymousIndividual(ind)) this._throwAnon(atom);
          inds.add(ind);
        }
        this.addFact(E.differentIndividuals([...inds]));
        return;
      }
      default:
        throw new Error(`Unsupported SWRL head atom: ${atom}`);
    }
  }

  _throwAnon(atom) {
    throw new Error(`A SWRL rule contains a fact (${atom}) with an anonymous individual, which is not allowed.`);
  }
}

// ===========================================================================
// RuleNormalizer — Lloyd-Topor splitting + atom normalization.
// ===========================================================================

class RuleNormalizer {
  /**
   * @param {import('./OWLNormalization').OWLNormalization} normalization
   * @param {object[][]} classExpressionInclusions worklist shared with the
   *        class-expression normalizer, so definitions introduced here are
   *        themselves normalized.
   * @param {object[][]} dataRangeInclusions worklist for data-range inclusions.
   */
  constructor(normalization, classExpressionInclusions, dataRangeInclusions) {
    this.normalization = normalization;
    this.axioms = normalization.axioms;
    this.classExpressionInclusions = classExpressionInclusions;
    this.dataRangeInclusions = dataRangeInclusions;
    this.newVariableIndex = 0;
  }

  /**
   * Normalize one SWRL rule, pushing the results into `axioms.rules`.
   * @param {{body:object[], head:object[]}} rule
   */
  normalize(rule) {
    // Process head atoms one-by-one, thereby breaking up the head conjunction.
    for (const headAtom of rule.head) {
      const state = {
        bodyAtoms: rule.body.slice(),
        headAtoms: [headAtom],
        normalizedBodyAtoms: new Set(),
        normalizedHeadAtoms: new Set(),
        variableRepresentative: new Map(),
        individualsToVariables: new Map(),
        bodyDataRangeVariables: new Set(),
        headDataRangeVariables: new Set()
      };

      // First process sameAs atoms in the body to set up variable canonicalisation.
      const remainingBody = [];
      for (const atom of state.bodyAtoms) {
        if (atomType(atom) === SWRLAtomType.SAME_AS) {
          const v1 = this._getVariableFor(state, atom.arg1);
          const arg2 = atom.arg2;
          if (isVariable(arg2)) {
            state.variableRepresentative.set(variableName(arg2), v1);
          } else {
            const ind = individualOf(arg2);
            if (isAnonymousIndividual(ind)) {
              throw new Error('Internal error: Rules with anonymous individuals are not supported.');
            }
            state.individualsToVariables.set(E.atomKey(ind), v1);
            state.bodyAtoms.push(classAtom(E.objectOneOf([ind]), v1));
          }
        } else {
          remainingBody.push(atom);
        }
      }
      state.bodyAtoms = remainingBody;

      // Head atoms first: processing them may add body atoms.
      state.isPositive = true;
      while (state.headAtoms.length > 0) this._processAtom(state, state.headAtoms.shift());

      // Then body atoms.
      state.isPositive = false;
      while (state.bodyAtoms.length > 0) this._processAtom(state, state.bodyAtoms.shift());

      for (const v of state.headDataRangeVariables) {
        if (!state.bodyDataRangeVariables.has(v)) {
          throw new Error('A SWRL rule contains data range variables in the head, but not in the body, and this is not supported.');
        }
      }

      this.axioms.rules.push(new DisjunctiveRule(
        [...state.normalizedBodyAtoms], [...state.normalizedHeadAtoms]));
    }
  }

  _processAtom(state, atom) {
    switch (atomType(atom)) {
      case SWRLAtomType.CLASS: {
        const c = EM.getNNF(EM.getSimplified(atom.classExpression));
        const variable = this._getVariableFor(state, atom.arg);
        if (state.isPositive) {
          if (E.exprType(c) === E.ClassExpressionType.OWL_CLASS) {
            state.normalizedHeadAtoms.add(classAtom(c, variable));
          } else {
            const { definition, alreadyExists } = this.normalization.getClassFor(atom.classExpression);
            if (!alreadyExists) {
              this.classExpressionInclusions.push(
                [this.normalization.negative(definition), atom.classExpression]);
            }
            state.normalizedHeadAtoms.add(classAtom(definition, variable));
          }
        } else if (E.exprType(c) === E.ClassExpressionType.OWL_CLASS) {
          state.normalizedBodyAtoms.add(classAtom(c, variable));
        } else {
          const { definition, alreadyExists } = this.normalization.getClassFor(atom.classExpression);
          if (!alreadyExists) {
            this.classExpressionInclusions.push(
              [this.normalization.negative(atom.classExpression), definition]);
          }
          state.normalizedBodyAtoms.add(classAtom(definition, variable));
        }
        return;
      }

      case SWRLAtomType.DATA_RANGE: {
        const argument = atom.arg;
        if (!isVariable(argument)) {
          throw new Error('A SWRL rule contains a data range with an argument that is not a literal, and such rules are not supported.');
        }
        let dr = atom.dataRange;
        if (!state.isPositive) dr = E.dataComplementOf(dr);
        // NOTE: HermiT's `ExpressionManager` overloads `getNNF`/`getSimplified`
        // for `OWLDataRange`, so `visit(SWRLDataRangeAtom)` dispatches to the
        // *data-range* visitors. The class-expression visitors have no case for
        // DataIntersectionOf / DataUnionOf / DataComplementOf and would return
        // the node untouched, leaving a raw connective in the normalized atom
        // that `OWLClausification.DataRangeConverter.convertDataRange` then
        // rejects with "invalid normal form". Use the data-range variants.
        dr = EM.getDataRangeNNF(EM.getDataRangeSimplified(dr));
        const t = E.exprType(dr);
        if (t === E.ClassExpressionType.DATA_INTERSECTION_OF || t === E.ClassExpressionType.DATA_UNION_OF) {
          const { definition, alreadyExists } = this.normalization.getDefinitionForDataRange(dr);
          if (!alreadyExists) {
            this.dataRangeInclusions.push([this.normalization.negativeDataRange(definition), dr]);
          }
          dr = definition;
        }
        state.normalizedHeadAtoms.add(dataRangeAtom(dr, argument));
        state.headDataRangeVariables.add(variableName(argument));
        return;
      }

      case SWRLAtomType.OBJECT_PROPERTY: {
        const ope = atom.property;
        const op = E.namedPropertyOf(ope);
        let variable1;
        let variable2;
        if (E.isAnonymousProperty(ope)) {
          variable1 = this._getVariableFor(state, atom.arg2);
          variable2 = this._getVariableFor(state, atom.arg1);
        } else {
          variable1 = this._getVariableFor(state, atom.arg1);
          variable2 = this._getVariableFor(state, atom.arg2);
        }
        const newAtom = objectPropertyAtom(op, variable1, variable2);
        if (state.isPositive) state.normalizedHeadAtoms.add(newAtom);
        else state.normalizedBodyAtoms.add(newAtom);
        this.axioms.objectProperties.add(op);
        this.axioms.objectPropertiesOccurringInOWLAxioms.add(op);
        return;
      }

      case SWRLAtomType.DATA_PROPERTY: {
        const dp = atom.property;
        const variable1 = this._getVariableFor(state, atom.arg1);
        const argument2 = atom.arg2;
        if (isVariable(argument2)) {
          const variable2 = this._getVariableFor(state, argument2);
          if (state.isPositive) {
            state.normalizedHeadAtoms.add(dataPropertyAtom(dp, variable1, variable2));
            state.headDataRangeVariables.add(variable2.name);
          } else if (state.bodyDataRangeVariables.has(variable2.name)) {
            // The same data variable already occurs in the body: introduce a
            // fresh one and require the two to differ (HermiT's encoding of
            // "at most one value per data property atom in the body").
            const fresh = this._getFreshVariable();
            state.normalizedBodyAtoms.add(dataPropertyAtom(dp, variable1, fresh));
            state.normalizedHeadAtoms.add(differentFromAtom(variable2, fresh));
          } else {
            state.bodyDataRangeVariables.add(variable2.name);
            state.normalizedBodyAtoms.add(dataPropertyAtom(dp, variable1, variable2));
          }
        } else {
          const lit = E.literal(literalOf(argument2));
          const newAtom = classAtom(E.dataHasValue(dp, lit), variable1);
          if (state.isPositive) state.headAtoms.push(newAtom);
          else state.bodyAtoms.push(newAtom);
        }
        this.axioms.dataProperties.add(dp);
        return;
      }

      case SWRLAtomType.BUILTIN:
        throw new Error(`A SWRL rule uses a built-in atom (${atom}), but built-in atoms are not supported yet.`);

      case SWRLAtomType.SAME_AS:
        if (state.isPositive) {
          state.normalizedHeadAtoms.add(sameAsAtom(
            this._getVariableFor(state, atom.arg1), this._getVariableFor(state, atom.arg2)));
        } else {
          throw new Error('Internal error: this SameAsAtom should have been processed earlier.');
        }
        return;

      case SWRLAtomType.DIFFERENT_FROM:
        if (state.isPositive) {
          state.normalizedHeadAtoms.add(differentFromAtom(
            this._getVariableFor(state, atom.arg1), this._getVariableFor(state, atom.arg2)));
        } else {
          // ¬differentFrom(x,y) in the body is sameAs(x,y) in the head.
          state.normalizedHeadAtoms.add(sameAsAtom(
            this._getVariableFor(state, atom.arg1), this._getVariableFor(state, atom.arg2)));
        }
        return;

      default:
        throw new Error(`Unsupported SWRL atom: ${atom}`);
    }
  }

  _getVariableFor(state, term) {
    let variable;
    if (isVariable(term)) {
      variable = term instanceof SWRLVariable ? term : new SWRLVariable(variableName(term));
    } else {
      const ind = individualOf(term);
      if (isAnonymousIndividual(ind)) {
        throw new Error('Internal error: Rules with anonymous individuals are not supported.');
      }
      variable = state.individualsToVariables.get(E.atomKey(ind));
      if (!variable) {
        variable = this._getFreshVariable();
        state.individualsToVariables.set(E.atomKey(ind), variable);
        state.bodyAtoms.push(classAtom(E.objectOneOf([ind]), variable));
      }
    }
    const representative = state.variableRepresentative.get(variable.name);
    return representative || variable;
  }

  _getFreshVariable() {
    return new SWRLVariable(`internal:swrl#${this.newVariableIndex++}`);
  }
}

module.exports = {
  RuleNormalizer, Rule2FactConverter, SWRLVariable, SWRLAtomType,
  classAtom, objectPropertyAtom, dataPropertyAtom, sameAsAtom,
  differentFromAtom, dataRangeAtom, isVariable, variableName, individualOf, literalOf
};
