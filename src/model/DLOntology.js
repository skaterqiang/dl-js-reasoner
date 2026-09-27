'use strict';

// ---------------------------------------------------------------------------
// model/DLOntology.js — a clausified ontology: DL-clauses + ABox facts +
// signature + feature flags.
//
// Mirrors org.semanticweb.HermiT.model.DLOntology. The flags let the Reasoner
// pick cheaper strategies (isHorn → deterministic classification;
// hasInverseRoles → pairwise blocking; hasAtMostRestrictions → merging, ...).
// ---------------------------------------------------------------------------

const { AtomicConcept, AtomicRole, InverseRole, DatatypeRestriction } = require('./DLPredicate');
const { Individual, Constant } = require('./Term');

const INTERNAL_PREFIX = 'internal:';

function isInternalIRI(iri) {
  return typeof iri === 'string' && iri.startsWith(INTERNAL_PREFIX);
}

class DLOntology {
  /**
   * @param {object} opts
   * @param {string} [opts.ontologyIRI]
   * @param {DLClause[]} opts.dlClauses
   * @param {Atom[]} opts.positiveFacts   ground ABox facts that hold
   * @param {Atom[]} opts.negativeFacts   ground ABox facts that must not hold
   * @param {boolean} opts.hasInverseRoles
   * @param {boolean} opts.hasAtMostRestrictions
   * @param {boolean} opts.hasNominals
   * @param {boolean} opts.hasDatatypes
   * @param {boolean} opts.hasUnknownDatatypeRestrictions
   *
   * Optional EXPLICIT signature sets, mirroring HermiT's constructor. When
   * given they are MERGED with the signature derived from the clauses and
   * facts: an entity declared in the ontology but never used in an axiom still
   * has to appear in the signature, because classification and realisation
   * iterate over it.
   * @param {Set<AtomicConcept>} [opts.atomicConcepts]
   * @param {Set<AtomicRole>} [opts.atomicObjectRoles]
   * @param {Set<AtomicRole>} [opts.atomicDataRoles]
   * @param {Set<Role>} [opts.complexObjectRoles]
   * @param {Set<Individual>} [opts.individuals]
   * @param {Set<DatatypeRestriction>} [opts.allUnknownDatatypeRestrictions]
   * @param {Set<string>} [opts.definedDatatypesIRIs]
   */
  constructor(opts) {
    this.ontologyIRI = opts.ontologyIRI || null;
    this.dlClauses = [...new Set(opts.dlClauses || [])];
    this.positiveFacts = [...new Set(opts.positiveFacts || [])];
    this.negativeFacts = [...new Set(opts.negativeFacts || [])];
    this.hasInverseRoles = !!opts.hasInverseRoles;
    this.hasAtMostRestrictions = !!opts.hasAtMostRestrictions;
    this.hasNominals = !!opts.hasNominals;
    this.hasDatatypes = !!opts.hasDatatypes;
    this.hasUnknownDatatypeRestrictions = !!opts.hasUnknownDatatypeRestrictions;

    // ---- signature (collected from clauses + facts, then merged with any
    // ---- explicitly supplied sets) ----
    this.allAtomicConcepts = new Set(opts.atomicConcepts || []);
    this.allAtomicObjectRoles = new Set(opts.atomicObjectRoles || []);
    this.allAtomicDataRoles = new Set(opts.atomicDataRoles || []);
    this.allIndividuals = new Set(opts.individuals || []);
    this.allUnknownDatatypeRestrictions = new Set(opts.allUnknownDatatypeRestrictions || []);
    /**
     * Roles that are not simple (transitive, or containing a non-simple role
     * in a chain). HermiT uses this to decide which existential expansions may
     * reuse existing nodes.
     * @type {Set<Role>}
     */
    this.complexObjectRoles = new Set(opts.complexObjectRoles || []);
    /** IRIs of datatypes introduced by DatatypeDefinition axioms. @type {Set<string>} */
    this.definedDatatypesIRIs = new Set(opts.definedDatatypesIRIs || []);
    /** role → individual → Set<Constant> (ground data property assertions). */
    this.dataPropertyAssertions = new Map();

    this.isHorn = true;
    for (const clause of this.dlClauses) {
      if (clause.getHeadLength() > 1) this.isHorn = false;
      for (const atom of clause.bodyAtoms) this._addPredicate(atom.dlPredicate);
      for (const atom of clause.headAtoms) this._addPredicate(atom.dlPredicate);
    }
    for (const fact of this.positiveFacts) {
      this._addPredicate(fact.dlPredicate);
      this._indexFact(fact);
    }
    for (const fact of this.negativeFacts) this._addPredicate(fact.dlPredicate);

    this.numberOfExternalConcepts = 0;
    for (const c of this.allAtomicConcepts) {
      if (!isInternalIRI(c.iri)) this.numberOfExternalConcepts++;
    }
  }

  _addPredicate(p) {
    if (p instanceof AtomicConcept) {
      this.allAtomicConcepts.add(p);
    } else if (p instanceof AtomicRole) {
      if (p.isDataRole()) this.allAtomicDataRoles.add(p);
      else this.allAtomicObjectRoles.add(p);
    } else if (p instanceof InverseRole) {
      // inverse of an atomic role contributes the atomic role too
      if (p.inverseRole instanceof AtomicRole) this._addPredicate(p.inverseRole);
    } else if (p instanceof DatatypeRestriction) {
      this.allUnknownDatatypeRestrictions.add(p);
    }
    // AtLeastConcept / AtLeastDataRange embed roles & concepts:
    if (p.onRole) this._addPredicate(p.onRole);
    if (p.toConcept instanceof AtomicConcept) this.allAtomicConcepts.add(p.toConcept);
  }

  _indexFact(atom) {
    // Collect individuals and data property assertions.
    for (const t of atom.arguments) {
      if (t instanceof Individual) this.allIndividuals.add(t);
    }
    if (atom.getArity() === 2 && atom.dlPredicate instanceof AtomicRole && atom.dlPredicate.isDataRole()) {
      const [ind, val] = atom.arguments;
      if (ind instanceof Individual && val instanceof Constant) {
        let byInd = this.dataPropertyAssertions.get(atom.dlPredicate);
        if (!byInd) {
          byInd = new Map();
          this.dataPropertyAssertions.set(atom.dlPredicate, byInd);
        }
        let set = byInd.get(ind);
        if (!set) {
          set = new Set();
          byInd.set(ind, set);
        }
        set.add(val);
      }
    }
  }

  /**
   * Two forms, mirroring HermiT's overloaded `toString`:
   *
   *   - `toString()` — the short signature/flags summary this port shipped
   *     first. Unchanged.
   *   - `toString(prefixes)` — the full `Prefixes / Deterministic DL-clauses /
   *     Disjunctive DL-clauses / ABox / Statistics` dump that
   *     `--dump-clauses` prints.
   *
   * DIVERGENCE FROM HERMIT (deliberate, documented): HermiT threads `prefixes`
   * through `DLClause.toString(Prefixes)` and `Atom.toString(Prefixes)` so IRIs
   * inside clauses are abbreviated. This port's clause/atom renderers take no
   * arguments, so IRIs are printed in full; the supplied `prefixes` only drives
   * the `Prefixes: [...]` header. Passing an empty `Prefixes` (the CLI's `-N`
   * route) therefore yields an empty header.
   *
   * @param {import('../Prefixes').Prefixes} [prefixes]
   * @returns {string}
   */
  toString(prefixes) {
    if (prefixes === undefined || prefixes === null) {
      return [
        `DLOntology(${this.ontologyIRI || 'anonymous'})`,
        `  clauses: ${this.dlClauses.length}`,
        `  positive facts: ${this.positiveFacts.length}`,
        `  negative facts: ${this.negativeFacts.length}`,
        `  concepts: ${this.allAtomicConcepts.size}, object roles: ${this.allAtomicObjectRoles.size}, data roles: ${this.allAtomicDataRoles.size}, individuals: ${this.allIndividuals.size}, complex roles: ${this.complexObjectRoles.size}`,
        `  flags: horn=${this.isHorn} inverse=${this.hasInverseRoles} atMost=${this.hasAtMostRestrictions} nominals=${this.hasNominals} datatypes=${this.hasDatatypes}`
      ].join('\n');
    }

    const lines = [];
    lines.push('Prefixes: [');
    for (const [name, iri] of prefixes.getPrefixIRIsByPrefixName()) {
      lines.push(`  ${name} = <${iri}>`);
    }
    lines.push(']');

    lines.push('Deterministic DL-clauses: [');
    let numDeterministicClauses = 0;
    for (const dlClause of this.dlClauses) {
      if (dlClause.getHeadLength() <= 1) {
        numDeterministicClauses++;
        lines.push(`  ${dlClause}`);
      }
    }
    lines.push(']');

    lines.push('Disjunctive DL-clauses: [');
    let numNondeterministicClauses = 0;
    let numDisjunctions = 0;
    for (const dlClause of this.dlClauses) {
      if (dlClause.getHeadLength() > 1) {
        numNondeterministicClauses++;
        numDisjunctions += dlClause.getHeadLength();
        lines.push(`  ${dlClause}`);
      }
    }
    lines.push(']');

    lines.push('ABox: [');
    for (const atom of this.positiveFacts) lines.push(`  ${atom}`);
    for (const atom of this.negativeFacts) lines.push(`  !${atom}`);
    lines.push(']');

    lines.push('Statistics: [');
    lines.push(`  Number of deterministic clauses: ${numDeterministicClauses}`);
    lines.push(`  Number of nondeterministic clauses: ${numNondeterministicClauses}`);
    lines.push(`  Number of disjunctions: ${numDisjunctions}`);
    lines.push(`  Number of positive facts: ${this.positiveFacts.length}`);
    lines.push(`  Number of negative facts: ${this.negativeFacts.length}`);
    lines.push(']');
    return lines.join('\n');
  }

  /**
   * HermiT's `getStatistics()` — the clause/flag statistics block on its own.
   * @returns {string}
   */
  getStatistics() {
    let numDeterministicClauses = 0;
    let numNondeterministicClauses = 0;
    let numDisjunctions = 0;
    for (const dlClause of this.dlClauses) {
      if (dlClause.getHeadLength() <= 1) numDeterministicClauses++;
      else {
        numNondeterministicClauses++;
        numDisjunctions += dlClause.getHeadLength();
      }
    }
    return [
      'DL clauses statistics: [',
      `  Number of deterministic clauses: ${numDeterministicClauses}`,
      `  Number of nondeterministic clauses: ${numNondeterministicClauses}`,
      `  Overall number of disjunctions: ${numDisjunctions}`,
      `  Number of positive facts: ${this.positiveFacts.length}`,
      `  Number of negative facts: ${this.negativeFacts.length}`,
      `  Inverses: ${this.hasInverseRoles}`,
      `  At-Mosts: ${this.hasAtMostRestrictions}`,
      `  Datatypes: ${this.hasDatatypes}`,
      `  Nominals: ${this.hasNominals}`,
      `  Number of atomic concepts: ${this.allAtomicConcepts.size}`,
      `  Number of object properties: ${this.allAtomicObjectRoles.size}`,
      `  Number of data properties: ${this.allAtomicDataRoles.size}`,
      `  Number of individuals: ${this.allIndividuals.size}`,
      ']'
    ].join('\n');
  }

  /**
   * Whether `atomicRole` occurs anywhere in this ontology (clauses or facts).
   * HermiT's DLOntology.containsObjectRole — used by Tableau to decide whether
   * an additional ontology may be loaded incrementally.
   */
  containsObjectRole(atomicRole) {
    if (!(atomicRole instanceof AtomicRole) || atomicRole.isDataRole()) return false;
    if (this.allAtomicObjectRoles.has(atomicRole)) return true;
    for (const clause of this.dlClauses) {
      for (const atom of clause.bodyAtoms) if (_usesRole(atom.dlPredicate, atomicRole)) return true;
      for (const atom of clause.headAtoms) if (_usesRole(atom.dlPredicate, atomicRole)) return true;
    }
    for (const fact of this.positiveFacts) if (_usesRole(fact.dlPredicate, atomicRole)) return true;
    for (const fact of this.negativeFacts) if (_usesRole(fact.dlPredicate, atomicRole)) return true;
    return false;
  }

  /** Whether `atomicConcept` occurs anywhere in this ontology. */
  containsAtomicConcept(atomicConcept) {
    return this.allAtomicConcepts.has(atomicConcept);
  }

  /** Whether `individual` occurs in a fact of this ontology. */
  containsIndividual(individual) {
    return this.allIndividuals.has(individual);
  }

  /** Whether `atomicRole` (a data role) occurs anywhere in this ontology. */
  containsDataRole(atomicRole) {
    return this.allAtomicDataRoles.has(atomicRole);
  }

  // ---- HermiT-parity accessors ---------------------------------------------
  // The fields above are public, but HermiT exposes these as getters and the
  // hierarchy printers / CLI call them by name.

  /** @returns {?string} the ontology IRI, or null for an anonymous ontology */
  getOntologyIRI() { return this.ontologyIRI; }

  /** @returns {Set<AtomicConcept>} */
  getAllAtomicConcepts() { return this.allAtomicConcepts; }

  /** @returns {Set<AtomicRole>} object (not data) atomic roles */
  getAllAtomicObjectRoles() { return this.allAtomicObjectRoles; }

  /** @returns {Set<AtomicRole>} data atomic roles */
  getAllAtomicDataRoles() { return this.allAtomicDataRoles; }

  /** @returns {Set<Individual>} */
  getAllIndividuals() { return this.allIndividuals; }

  /** @returns {Set<Role>} non-simple object roles */
  getAllComplexObjectRoles() { return this.complexObjectRoles; }

  /** @returns {DLClause[]} */
  getDLClauses() { return this.dlClauses; }

  /** @returns {Atom[]} */
  getPositiveFacts() { return this.positiveFacts; }

  /** @returns {Atom[]} */
  getNegativeFacts() { return this.negativeFacts; }
}

function _usesRole(predicate, atomicRole) {
  if (predicate === atomicRole) return true;
  if (predicate instanceof InverseRole) return _usesRole(predicate.inverseRole, atomicRole);
  if (predicate.onRole) return _usesRole(predicate.onRole, atomicRole);
  return false;
}

module.exports = { DLOntology, isInternalIRI, INTERNAL_PREFIX };
