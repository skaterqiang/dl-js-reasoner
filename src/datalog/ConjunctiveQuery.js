'use strict';

// ---------------------------------------------------------------------------
// datalog/ConjunctiveQuery.js — evaluate a conjunctive query against a
// materialised ABox.
//
// Mirrors org.semanticweb.HermiT.datalog.{ConjunctiveQuery,QueryResultCollector}.
//
// === What a conjunctive query is =============================================
//
//   q(X) ← A₁(t̄₁) ∧ … ∧ Aₙ(t̄ₙ)
//
// The body is a conjunction of atoms over variables and ground terms; the
// answer terms say which of them to report. An answer is one binding of the
// answer terms that makes every body atom true simultaneously.
//
// === How this port evaluates it ==============================================
//
// HermiT turns the query into a DL-clause with an empty head, compiles it with
// `DLClauseEvaluator.ConjunctionCompiler` into a chain of `Worker` bytecode
// objects, and runs that program. The compilation is purely a performance
// device — its observable behaviour is "match the conjunction against the
// extension tables and report each complete binding".
//
// This port already has that matcher: `DLClauseEvaluator._match` in
// `tableau/HyperresolutionManager.js` is a direct recursive join over the same
// extension tables, written as an interpreter instead of a compiler. So the
// query evaluator here SUBCLASSES it and overrides only `_deriveHeads` — the
// single hook where a complete binding is in hand. Everything else (join order,
// ground-term resolution, inverse-role handling, tuple-activity filtering) is
// inherited unchanged, which keeps query semantics identical to clause
// semantics by construction.
//
// Two deliberate differences from the inherited matcher:
//   • the body is joined from atom 0, not from a pre-bound "delta" atom — a
//     query has no delta tuple to trigger it, so `evaluate` starts the join
//     directly (HermiT achieves this with `OneEmptyTupleRetrieval`, a retrieval
//     that yields exactly one empty tuple);
//   • the head is reported to a collector instead of being added to the
//     extension.
// ---------------------------------------------------------------------------

const { DLClauseEvaluator, BodyAtomsSwapper, isPredicateWithExtension, normalizeAtom } =
  require('../tableau/HyperresolutionManager');
const { Variable } = require('../model/Term');
const { createDLClause } = require('../model/DLClause');

// ===========================================================================
// QueryResultCollector
// ===========================================================================

/**
 * Receives one call per answer. Mirrors the HermiT interface of the same name.
 *
 * Implement `processResult(conjunctiveQuery, result)`. `result` is an array of
 * Terms with the same length and order as the query's answer terms; it is
 * FRESHLY allocated per answer, so a collector may keep it.
 */
class QueryResultCollector {
  processResult(_conjunctiveQuery, _result) {
    throw new Error('QueryResultCollector.processResult must be implemented.');
  }
}

/**
 * Collects answers into an array. The everyday collector.
 *
 * Answers are de-duplicated: the same binding can be reached more than once
 * when two distinct extension tuples denote the same canonical nodes, and a
 * query result is a SET of answers, not a multiset.
 */
class CollectingQueryResultCollector extends QueryResultCollector {
  constructor() {
    super();
    /** @type {Term[][]} */
    this.results = [];
    this._seen = new Set();
  }

  processResult(_conjunctiveQuery, result) {
    const key = result.map(termKey).join('\u0000');
    if (this._seen.has(key)) return;
    this._seen.add(key);
    this.results.push(result);
  }

  /** Number of distinct answers. */
  get size() { return this.results.length; }

  /**
   * Answers as arrays of IRI strings / literal strings — the shape that is easy
   * to assert on and to serialise.
   */
  toArrayOfStrings() { return this.results.map((r) => r.map(termToString)); }
}

function termKey(term) {
  return term === null || term === undefined ? '\u0001null' : `${term.kind}:${term.toString()}`;
}

function termToString(term) {
  if (term === null || term === undefined) return null;
  if (term.isIndividual()) return term.iri;
  return term.toString();
}

// ===========================================================================
// QueryEvaluator — the DLClauseEvaluator subclass that reports bindings
// ===========================================================================

/**
 * A join over the query body that calls `collector.processResult` for each
 * complete binding.
 *
 * The constructor signature follows `DLClauseEvaluator`'s, with the head
 * clauses replaced by the answer terms and the collector.
 */
class QueryEvaluator extends DLClauseEvaluator {
  /**
   * @param {object} tableau the materialised tableau
   * @param {Atom[]} bodyAtoms the query body, already join-ordered
   * @param {Term[]} answerTerms what to report per binding
   * @param {DatalogEngine} engine supplies the node→term map
   */
  constructor(tableau, bodyAtoms, answerTerms, engine) {
    // `headDLClauses` is only consumed by `_deriveHeads`, which this class
    // overrides, so an empty list is correct — but the base constructor walks it
    // to collect variables, so it must be an array.
    super(tableau, createDLClause([], bodyAtoms), []);
    this.answerTerms = answerTerms;
    this.engine = engine;
    this.collector = null;

    // Answer term → index in the values buffer, for the variable answers.
    // Ground answer terms are reported verbatim and need no binding.
    this.answerVariableIndexes = answerTerms.map((term) => (
      term instanceof Variable ? this.variableIndex.get(term) : -1
    ));
  }

  /** Run the join, reporting every complete binding to `collector`. */
  evaluate(collector) {
    this.collector = collector;
    try {
      // No delta atom: start the join at body atom 0 with nothing bound.
      const values = new Array(this.variables.length).fill(null);
      this._match(0, values, []);
    } finally {
      this.collector = null;
    }
  }

  /**
   * A complete binding is in hand. Report the answer terms.
   *
   * Overrides the head-derivation hook: instead of adding tuples to the
   * extension, translate bound nodes back to the terms that denote them.
   */
  _deriveHeads(values, _depSets) {
    if (this.collector === null) return;
    const result = new Array(this.answerTerms.length);
    for (let i = 0; i < this.answerTerms.length; i++) {
      const term = this.answerTerms[i];
      if (!(term instanceof Variable)) {
        // A ground answer term is its own answer, whatever the binding.
        result[i] = term;
        continue;
      }
      const index = this.answerVariableIndexes[i];
      const node = index === undefined || index === -1 ? null : values[index];
      if (node === null || node === undefined) return; // unbound ⇒ not an answer
      // Nodes are canonical; map back to the term that denotes them. A node with
      // no term (e.g. a node created for a term the query never mentioned)
      // cannot be reported, so this binding is dropped — same as HermiT, whose
      // `m_nodesToTerms.get(...)` would yield null there.
      const answerTerm = this.engine.getTermForNode(node);
      if (answerTerm === null) return;
      result[i] = answerTerm;
    }
    this.collector.processResult(this.conjunctiveQuery || null, result);
  }
}

// ===========================================================================
// ConjunctiveQuery
// ===========================================================================

class ConjunctiveQuery {
  /**
   * @param {DatalogEngine} datalogEngine
   * @param {Atom[]} queryAtoms the body conjunction
   * @param {Term[]} answerTerms one per answer column
   * @throws {Error} if the ontology is inconsistent, or an answer variable does
   *   not occur in the body.
   */
  constructor(datalogEngine, queryAtoms, answerTerms) {
    if (!datalogEngine || typeof datalogEngine.materialize !== 'function') {
      throw new Error('ConjunctiveQuery requires a DatalogEngine.');
    }
    // Mirrors HermiT: the constructor materialises eagerly and refuses to build a
    // query over an unsatisfiable ontology, because every answer would be
    // vacuous.
    if (!datalogEngine.materialize()) {
      throw new Error('The supplied DL ontology is unsatisfiable.');
    }
    if (!Array.isArray(queryAtoms) || queryAtoms.length === 0) {
      throw new Error('A conjunctive query needs at least one body atom.');
    }
    if (!Array.isArray(answerTerms)) {
      throw new Error('answerTerms must be an array of Terms.');
    }

    this.datalogEngine = datalogEngine;
    this.queryAtoms = queryAtoms;
    this.answerTerms = answerTerms;

    // DL-safety for answers: an answer variable that does not occur in the body
    // is unbound in every binding, so the query could never report anything.
    // HermiT gets this for free from its compiler (the variable simply has no
    // buffer slot); here it is an explicit check with a clearer message.
    const bodyVariables = new Set();
    for (const atom of queryAtoms) {
      for (let i = 0; i < atom.getArity(); i++) {
        const v = atom.getArgumentVariable(i);
        if (v) bodyVariables.add(v);
      }
    }
    for (const term of answerTerms) {
      if (term instanceof Variable && !bodyVariables.has(term)) {
        throw new Error(
          `Answer variable ${term.name} does not occur in the query body.`);
      }
    }

    // Join ordering. `BodyAtomsSwapper` implements HermiT's selectivity
    // heuristic (most-bound-variables-first), which keeps intermediate result
    // sets small. Wrapping the body in a headless clause lets us reuse it
    // verbatim: `getSwappedDLClause(0)` puts atom 0 first and orders the rest.
    //
    // Normalize inverse roles: the extension tables only ever store atomic
    // roles (`ExtensionManager._addTuple` swaps `R⁻(a,b)` into `R(b,a)`), so an
    // un-normalized `R⁻(X,Y)` atom could never match and would silently return
    // no answers. Clause bodies get this from the clausifier's `getRoleAtom`;
    // a query body is hand-built, so it must be done here.
    //
    // Atoms whose predicate has no extension (the node-ID ordering
    // pseudo-predicates) cannot be looked up in a table, so they are filtered
    // out — a query body should not contain them, but a hand-built one might.
    const extended = queryAtoms
      .filter((a) => isPredicateWithExtension(a.dlPredicate))
      .map(normalizeAtom);
    if (extended.length === 0) {
      throw new Error('The query body contains no atom with an extension.');
    }
    const swapper = new BodyAtomsSwapper(createDLClause([], extended));
    this.orderedBodyAtoms = swapper.getSwappedDLClause(0).bodyAtoms;

    this.evaluator = new QueryEvaluator(
      datalogEngine.tableau, this.orderedBodyAtoms, answerTerms, datalogEngine);
    this.evaluator.conjunctiveQuery = this;
  }

  // ---- accessors (mirror HermiT) -------------------------------------------

  getDatalogEngine() { return this.datalogEngine; }
  getNumberOfQueryAtoms() { return this.queryAtoms.length; }
  getQueryAtom(index) { return this.queryAtoms[index]; }
  getNumberOfAnswerTerms() { return this.answerTerms.length; }
  getAnswerTerm(index) { return this.answerTerms[index]; }

  /**
   * Evaluate the query, reporting each answer to `collector`.
   * @param {QueryResultCollector} collector
   */
  evaluate(collector) {
    if (!collector || typeof collector.processResult !== 'function') {
      throw new Error('evaluate requires a QueryResultCollector.');
    }
    this.evaluator.evaluate(collector);
  }

  /**
   * Convenience: evaluate and return the distinct answers.
   * @returns {Term[][]}
   */
  getAnswers() {
    const collector = new CollectingQueryResultCollector();
    this.evaluate(collector);
    return collector.results;
  }

  toString() {
    const head = this.answerTerms.map(String).join(', ');
    const body = this.queryAtoms.map(String).join(' ∧ ');
    return `q(${head}) ← ${body}`;
  }
}

module.exports = {
  ConjunctiveQuery,
  QueryResultCollector,
  CollectingQueryResultCollector,
  QueryEvaluator
};
