'use strict';

// ---------------------------------------------------------------------------
// model/Term.js — the terms that atoms are built from.
//
// Mirrors org.semanticweb.HermiT.model.{Term,Variable,Individual,Constant}.
// A Term is one of:
//   • Variable   — a placeholder bound during clause matching (X, Y, Z, ...)
//   • Individual — a ground nominal (a named individual or an anonymous tree node)
//   • Constant   — a ground data value (a literal: lexical form + datatype)
//
// Terms are interned so that identity (===) can be used for comparison, which
// is the same performance trick HermiT uses throughout model/.
// ---------------------------------------------------------------------------

const TERM_KIND = Object.freeze({
  VARIABLE: 'Variable',
  INDIVIDUAL: 'Individual',
  CONSTANT: 'Constant'
});

/** Abstract base. */
class Term {
  constructor(kind) {
    this.kind = kind;
  }
  isVariable() { return this.kind === TERM_KIND.VARIABLE; }
  isIndividual() { return this.kind === TERM_KIND.INDIVIDUAL; }
  isConstant() { return this.kind === TERM_KIND.CONSTANT; }
  /** The argument as a Variable, or null. Mirrors Atom.getArgumentVariable. */
  getArgumentVariable() { return this.isVariable() ? this : null; }
}

// ---- Variable ---------------------------------------------------------------

class Variable extends Term {
  constructor(name) {
    super(TERM_KIND.VARIABLE);
    this.name = name;
  }
  toString() { return this.name; }
}

const _variables = new Map();
/** Interned Variable factory (mirrors Variable.create). */
function createVariable(name) {
  let v = _variables.get(name);
  if (!v) {
    v = new Variable(name);
    _variables.set(name, v);
  }
  return v;
}

// Standard variables used by the clausifier.
const X = createVariable('X');
const Y = createVariable('Y');
const Z = createVariable('Z');

// ---- Individual -------------------------------------------------------------

class Individual extends Term {
  constructor(iri) {
    super(TERM_KIND.INDIVIDUAL);
    this.iri = iri; // string IRI (or internal node id for anonymous individuals)
  }
  /**
   * Anonymous individuals (OWLAnonymousIndividual) get an internal IRI and
   * become NI nodes rather than named nodes — keys must not apply to them.
   * Mirrors Individual.isAnonymous.
   */
  isAnonymous() { return this.iri.startsWith(ANONYMOUS_INDIVIDUAL_PREFIX); }
  toString() { return `<${this.iri}>`; }
}

const ANONYMOUS_INDIVIDUAL_PREFIX = 'internal:anonymous#';
const ANONYMOUS_CONSTANT_DATATYPE = 'internal:anonymous-constants';

const _individuals = new Map();
function createIndividual(iri) {
  let i = _individuals.get(iri);
  if (!i) {
    i = new Individual(iri);
    _individuals.set(iri, i);
  }
  return i;
}

/** Interned anonymous individual (mirrors Individual.createAnonymous). */
function createAnonymousIndividual(id) {
  return createIndividual(ANONYMOUS_INDIVIDUAL_PREFIX + id);
}

// ---- Constant ---------------------------------------------------------------

class Constant extends Term {
  /**
   * @param {string} lexicalValue
   * @param {string} datatypeIRI  e.g. 'http://www.w3.org/2001/XMLSchema#integer'
   */
  constructor(lexicalValue, datatypeIRI) {
    super(TERM_KIND.CONSTANT);
    this.lexicalValue = String(lexicalValue);
    this.datatypeIRI = datatypeIRI || null;
  }
  /**
   * Anonymous constants carry no concrete value (HermiT uses them for
   * ObjectHasValue/DataHasValue fillers whose value is unknown); they are not
   * given a ConstantEnumeration assertion.
   */
  isAnonymous() { return this.datatypeIRI === ANONYMOUS_CONSTANT_DATATYPE; }
  toString() {
    return this.datatypeIRI
      ? `"${this.lexicalValue}"^^<${this.datatypeIRI}>`
      : `"${this.lexicalValue}"`;
  }
}

const _constants = new Map();
function createConstant(lexicalValue, datatypeIRI) {
  const key = `${lexicalValue}\u0000${datatypeIRI || ''}`;
  let c = _constants.get(key);
  if (!c) {
    c = new Constant(lexicalValue, datatypeIRI);
    _constants.set(key, c);
  }
  return c;
}

/** Interned anonymous constant (mirrors Constant.createAnonymous). */
function createAnonymousConstant(id) {
  return createConstant(id, ANONYMOUS_CONSTANT_DATATYPE);
}

module.exports = {
  TERM_KIND,
  Term,
  Variable,
  Individual,
  Constant,
  createVariable,
  createIndividual,
  createAnonymousIndividual,
  createConstant,
  createAnonymousConstant,
  ANONYMOUS_INDIVIDUAL_PREFIX,
  ANONYMOUS_CONSTANT_DATATYPE,
  X,
  Y,
  Z
};
