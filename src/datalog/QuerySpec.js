'use strict';

// ---------------------------------------------------------------------------
// datalog/QuerySpec.js — build a conjunctive query from a readable spec.
//
// This module has NO counterpart in HermiT. It exists because the raw
// `ConjunctiveQuery` constructor takes DL-layer objects:
//
//   new ConjunctiveQuery(engine,
//     [createAtom(internAtomicRole(EX + 'R', false), createVariable('X'),
//                                            createIndividual(EX + 'a'))],
//     [createVariable('X')]);
//
// That is precise but verbose, and it forces callers to know which interner to
// use for which predicate kind and whether a role is a data role. This file
// turns a plain-object spec into exactly that pair of arrays, so the everyday
// call becomes
//
//   buildQuerySpec({
//     select: ['?X'],
//     where: [{ objectProperty: EX + 'R', subject: '?X', object: EX + 'a' }]
//   })
//
// === Spec shape ==============================================================
//
//   {
//     select: [term, ...],      // the answer columns; defaults to every
//                               // variable in `where`, in first-appearance order
//     where:  [atomSpec, ...]   // the body conjunction
//   }
//
// An `atomSpec` is a plain object with exactly one KEY naming the atom kind and
// the remaining keys naming its arguments:
//
//   { class: iri, arg }                       →  C(t)
//   { datatype: iri, arg }                    →  DT(t)      (binds a constant)
//   { objectProperty: iri, subject, object }  →  R(s, o)
//   { dataProperty: iri, subject, value }     →  dp(s, v)
//   { differentFrom: [t1, t2] }               →  t1 ≉ t2
//
// An object property may be written in inverse form with
// `{ inverseObjectProperty: iri, subject, object }`, which yields `R⁻(s,o)`.
// `ConjunctiveQuery` normalizes that to `R(o,s)` before matching, so it works
// even though the extension tables only ever store atomic roles.
//
// `{ datatype: iri, arg }` matches the concrete nodes whose datatype is `iri`.
// Note that the datatype is only *asserted* of a constant when the ontology
// says so — a `DataPropertyRange` or a `DatatypeDefinition`. Without one, the
// ABox stores the constant but no datatype tuple, and the atom matches nothing.
//
// **`sameAs` is NOT supported** and throws: an equality assertion is consumed by
// node merging, so `=` tuples never reach an extension table and such an atom
// could only ever return an empty answer set, silently. Sameness shows up
// instead as answers collapsing onto one representative — inspect that with
// `DatalogEngine.getEquivalenceClass` / `getRepresentative`.
//
// === Terms ===================================================================
//
// Every argument position accepts:
//   • a string starting with `?`   → a Variable named after the `?`
//   • any other string             → an Individual with that IRI
//   • `{ variable: name }`         → a Variable
//   • `{ individual: iri }`        → an Individual
//   • `{ literal: v, datatype? , lang? }` → a Constant
//   • an OWLLiteral / protege-js literal    → a Constant
//   • an existing `Term`           → passed through untouched
//
// Literals become `Constant`s using exactly the conversion the clausifier uses
// for asserted literals (`OWLClausification.convertLiteral`), including the
// `'value@lang'` lexical form for language-tagged literals. Getting this wrong
// would make a literal in a query never match the same literal in the ABox, so
// the two paths are deliberately kept identical.
// ---------------------------------------------------------------------------

const E = require('../owl/OWLExpressions');
const P = require('../model/DLPredicate');
const { createAtom } = require('../model/Atom');
const {
  Term,
  createVariable,
  createIndividual,
  createConstant,
  createAnonymousIndividual
} = require('../model/Term');

// ===========================================================================
// Term coercion
// ===========================================================================

/**
 * Coerce a spec value into a `Term`.
 *
 * @param {*} value
 * @returns {Term}
 * @throws {Error} if the value is not a recognizable term shape.
 */
function toTerm(value) {
  if (value === null || value === undefined) {
    throw new Error('A query term cannot be null or undefined.');
  }
  // Already a DL-layer term.
  if (value instanceof Term) return value;
  // Explicit wrappers.
  if (typeof value === 'object') {
    if (typeof value.variable === 'string') return createVariable(value.variable);
    if (typeof value.individual === 'string') return createIndividual(value.individual);
    if (typeof value.anonymousIndividual === 'string') {
      return createAnonymousIndividual(value.anonymousIndividual);
    }
    if (value.literal !== undefined) return literalToTerm(value);
    // An OWLLiteral / protege-js literal handed over directly.
    if (value.lexicalValue !== undefined) return literalToTerm(value);
  }
  if (typeof value === 'string') {
    if (value.startsWith('?')) return createVariable(value.slice(1));
    return createIndividual(value);
  }
  throw new Error(`Cannot interpret ${JSON.stringify(value)} as a query term.`);
}

/**
 * An OWL literal (or `{ literal, datatype, lang }` spec) → the `Constant` the
 * clausifier would have produced for it.
 *
 * Mirrors `OWLClausification.convertLiteral` exactly: a language-tagged literal,
 * and a literal explicitly typed `rdf:PlainLiteral`, both get the lexical form
 * `"<value>@<lang>"` (with an empty lang when there is none). Every other
 * literal keeps its lexical form and its datatype IRI.
 *
 * The two paths MUST agree, or a literal written in a query would never match
 * the same literal asserted in the ABox — silently, with no error.
 */
function literalToTerm(value) {
  // `{ literal, datatype, lang }` is this module's own spelling; anything else
  // (an OWLLiteral, a protege-js literal) goes straight through `E.literal`,
  // which normalizes both.
  const lit = value.literal !== undefined
    ? E.literal(value.literal, value.datatype, value.lang)
    : E.literal(value);
  if (lit.isRDFPlainLiteral()) {
    return createConstant(`${lit.lexicalValue}@${lit.lang || ''}`, E.IRI_RDF_PLAIN_LITERAL);
  }
  return createConstant(lit.lexicalValue, lit.getDatatypeIRI());
}

/** A Variable, or null if the term is ground. */
function asVariable(term) {
  return term.isVariable() ? term : null;
}

// ===========================================================================
// Atom construction
// ===========================================================================

/** The recognized atom-spec keys, in the order they are probed. */
const ATOM_KINDS = Object.freeze([
  'class', 'datatype', 'objectProperty', 'inverseObjectProperty',
  'dataProperty', 'differentFrom'
]);

/**
 * The datatype predicate the clausifier would have produced for a plain
 * datatype IRI, so a `{ datatype }` query atom matches the tuples the ABox
 * actually stores.
 *
 * This mirrors `OWLClausification._convertDatatype`:
 *   • `rdfs:Literal`            → the `RDFS_LITERAL` internal datatype
 *   • `internal:defdata#…`      → an `InternalDatatype`
 *   • anything else             → `DatatypeRestriction(iri, [])`
 *
 * A user-defined datatype (`DatatypeDefinition`) is clausified to an
 * `InternalDatatype` whose name depends on the whole ontology, so it cannot be
 * named from an IRI alone; query it through the data property that ranges over
 * it instead. Getting the predicate kind wrong here would make the atom match
 * nothing — silently — which is exactly the failure this function prevents.
 */
function datatypePredicate(iri) {
  if (iri === P.IRI_LITERAL) return P.RDFS_LITERAL;
  if (iri.startsWith('internal:defdata#')) return P.internInternalDatatype(iri);
  return P.internDatatypeRestriction(iri, []);
}

/**
 * Build one `Atom` from an atom spec.
 *
 * @param {object} spec
 * @returns {Atom}
 */
function toAtom(spec) {
  if (spec instanceof Object && spec.dlPredicate) return spec; // already an Atom

  if (typeof spec.class === 'string') {
    return createAtom(P.internAtomicConcept(spec.class), toTerm(spec.arg));
  }
  if (typeof spec.datatype === 'string') {
    return createAtom(datatypePredicate(spec.datatype), toTerm(spec.arg));
  }
  if (typeof spec.objectProperty === 'string') {
    return createAtom(P.internAtomicRole(spec.objectProperty, false),
      toTerm(spec.subject), toTerm(spec.object));
  }
  if (typeof spec.inverseObjectProperty === 'string') {
    const role = P.internAtomicRole(spec.inverseObjectProperty, false);
    return createAtom(P.internInverseRole(role), toTerm(spec.subject), toTerm(spec.object));
  }
  if (typeof spec.dataProperty === 'string') {
    return createAtom(P.internAtomicRole(spec.dataProperty, true),
      toTerm(spec.subject), toTerm(spec.value));
  }
  if (Array.isArray(spec.sameAs)) {
    // `EQUALITY` is deliberately NOT a supported query atom. In the tableau an
    // equality assertion is consumed by the merging manager
    // (`ExtensionManager._addTuple` routes it to `mergeNodes`), so an `=` tuple
    // is NEVER stored in an extension table and a `sameAs` atom could only ever
    // match nothing — silently. HermiT behaves identically. Sameness is instead
    // resolved by merging: two individuals that are `sameAs` share one canonical
    // node, so they already collapse to a single answer. To inspect that
    // collapse use `DatalogEngine.getEquivalenceClass` / `getRepresentative`, or
    // `Reasoner.getSameIndividuals`.
    throw new Error(
      'A `sameAs` atom cannot be used in a query body: equality is resolved by '
      + 'node merging, so `=` tuples are never stored and the atom would match '
      + 'nothing. Use getEquivalenceClass/getRepresentative (or '
      + 'Reasoner.getSameIndividuals) to inspect merged individuals.');
  }
  if (Array.isArray(spec.differentFrom)) {
    return createAtom(P.INEQUALITY, toTerm(spec.differentFrom[0]), toTerm(spec.differentFrom[1]));
  }
  throw new Error(
    `Unrecognized query atom spec: ${JSON.stringify(spec)}. `
    + `Expected one of ${ATOM_KINDS.join(', ')}.`);
}

/**
 * Compile a query spec into the pair `ConjunctiveQuery` wants.
 *
 * @param {{select?: Array, where: Array}} spec
 * @returns {{queryAtoms: Atom[], answerTerms: Term[]}}
 * @throws {Error} on a malformed spec.
 */
function buildQuerySpec(spec) {
  if (!spec || !Array.isArray(spec.where)) {
    throw new Error('A query spec needs a `where` array of atom specs.');
  }
  if (spec.where.length === 0) {
    throw new Error('A query spec needs at least one atom in `where`.');
  }
  const queryAtoms = spec.where.map(toAtom);

  let answerTerms;
  if (Array.isArray(spec.select)) {
    answerTerms = spec.select.map(toTerm);
  } else {
    // No `select`: answer with every variable in the body, in first-appearance
    // order. That is the SPARQL `SELECT *` convention and the sensible default.
    answerTerms = [];
    const seen = new Set();
    for (const atom of queryAtoms) {
      for (let i = 0; i < atom.getArity(); i++) {
        const v = asVariable(atom.getArgument(i));
        if (v && !seen.has(v)) { seen.add(v); answerTerms.push(v); }
      }
    }
  }
  return { queryAtoms, answerTerms };
}

/**
 * Render a spec (or an already-built atom list) the way it would be printed in
 * a textbook: `q(?X, ?Y) ← R(?X, ?Y) ∧ A(?X)`.
 */
function querySpecToString(queryAtoms, answerTerms) {
  const head = (answerTerms || []).map(String).join(', ');
  const body = (queryAtoms || []).map(String).join(' ∧ ');
  return `q(${head}) ← ${body}`;
}

module.exports = {
  buildQuerySpec,
  toAtom,
  toTerm,
  literalToTerm,
  querySpecToString,
  ATOM_KINDS
};
