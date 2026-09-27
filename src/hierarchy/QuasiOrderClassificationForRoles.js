'use strict';
/**
 * Quasi-order classification specialised for ROLES (object properties).
 *
 * Port of `org.semanticweb.HermiT.hierarchy.QuasiOrderClassificationForRoles`.
 *
 * Roles are classified by proxying each role `R` as a fresh concept
 * `internal:prop#R ≡ ∃R.F` and then running ordinary concept classification
 * (see `Reasoner.classifyObjectProperties`). Two things make the plain
 * `QuasiOrderClassification` a poor fit for that encoding, and this subclass
 * fixes both:
 *
 *  1. **Told role subsumers are invisible to the base seeder.** The base
 *     `initialiseKnownSubsumptionsUsingToldSubsumers` only recognises clauses
 *     whose body AND head predicates are `AtomicConcept`s in `elements`. A role
 *     inclusion `R ⊑ S` clausifies to `R(X,Y) → S(X,Y)`, whose predicates are
 *     `AtomicRole`s — so the base class seeds NOTHING and every told role
 *     inclusion has to be rediscovered by an expensive tableau test. This
 *     override reads those clauses directly.
 *
 *  2. **Inverses come for free.** `R ⊑ S⁻` is logically equivalent to
 *     `R⁻ ⊑ S`, and more generally `R ⊑ S` implies `R⁻ ⊑ S⁻`. When the
 *     ontology uses inverses at all, every subsumption discovered for one role
 *     is mirrored onto the inverses, halving the number of tableau runs.
 *
 * Distinguishing the two clause shapes is purely syntactic. `getRoleAtom`
 * renders an inverse property `R⁻(X,Y)` as the atom `R(Y,X)` — arguments
 * SWAPPED, named role kept — so `InverseRole` never reaches the extension
 * tables. Consequently, for a 1-body/1-head role clause:
 *
 *   - body arg 0 === head arg 0  →  the clause is `R → S` (or `R⁻ → S⁻`),
 *                                   i.e. a DIRECT inclusion;
 *   - body arg 0 !== head arg 0  →  the clause is `R → S⁻` (or `R⁻ → S`),
 *                                   i.e. an inclusion against an INVERSE.
 *
 * Soundness note: seeding is an OPTIMISATION. A missed or skipped edge only
 * costs extra tableau runs; it can never produce a wrong hierarchy, because
 * every candidate pair is still confirmed by `doesSubsume` before it enters
 * `knownSubsumptions`. That is why the defensive `undefined` guards below skip
 * rather than throw.
 */

const { QuasiOrderClassification } = require('./QuasiOrderClassification');
const { AtomicRole } = require('../model/DLPredicate');

class QuasiOrderClassificationForRoles extends QuasiOrderClassification {
  /**
   * @param {object} tableau
   * @param {{elementClassified: (element: *) => void}} progressMonitor
   * @param {object} topElement     proxy concept for `owl:topObjectProperty`
   * @param {object} bottomElement  proxy concept for `owl:bottomObjectProperty`
   * @param {Set<object>} elements  the proxy concepts — `rolesForConcepts.keys()`
   * @param {boolean} hasInverses   whether the ontology uses inverse roles at all
   * @param {Map<object, object>} conceptsForRoles  Role → proxy AtomicConcept
   * @param {Map<object, object>} rolesForConcepts  proxy AtomicConcept → Role
   */
  constructor(tableau, progressMonitor, topElement, bottomElement, elements,
    hasInverses, conceptsForRoles, rolesForConcepts) {
    super(tableau, progressMonitor, topElement, bottomElement, elements);
    this.hasInverses = !!hasInverses;
    this.conceptsForRoles = conceptsForRoles;
    this.rolesForConcepts = rolesForConcepts;
  }

  /**
   * Seed the known graph from the told ROLE subsumers.
   *
   * Replaces (does not extend) the base implementation: in this tableau the
   * `elements` are internal proxy concepts, and no 1:1 clause relates two of
   * them directly, so the base scan would find nothing.
   */
  initialiseKnownSubsumptionsUsingToldSubsumers(dlClauses) {
    const clauses = dlClauses || this.tableau.getPermanentDLOntology().dlClauses;
    for (const dlClause of clauses) {
      if (dlClause.getHeadLength() !== 1 || dlClause.getBodyLength() !== 1) continue;

      const headPredicate = dlClause.getHeadAtom(0).dlPredicate;
      const bodyPredicate = dlClause.getBodyAtom(0).dlPredicate;
      if (!(headPredicate instanceof AtomicRole)) continue;
      if (!(bodyPredicate instanceof AtomicRole)) continue;
      if (!this.conceptsForRoles.has(headPredicate)) continue;
      if (!this.conceptsForRoles.has(bodyPredicate)) continue;

      const conceptForHeadRole = this.conceptsForRoles.get(headPredicate);
      const conceptForBodyRole = this.conceptsForRoles.get(bodyPredicate);

      if (dlClause.getBodyAtom(0).getArgument(0) !== dlClause.getHeadAtom(0).getArgument(0)) {
        // Swapped arguments → the clause is `R → S⁻` (equivalently `R⁻ → S`),
        // so the told subsumption is between R⁻ and S.
        const conceptForBodyInvRole = this.conceptsForRoles.get(bodyPredicate.getInverse());
        if (conceptForBodyInvRole !== undefined) {
          this.addKnownSubsumption(conceptForBodyInvRole, conceptForHeadRole);
        }
      } else {
        // Aligned arguments → the clause is `R → S` (equivalently `R⁻ → S⁻`).
        this.addKnownSubsumption(conceptForBodyRole, conceptForHeadRole);
      }
    }
  }

  /**
   * Record a proven subsumption, and mirror it onto the inverses.
   *
   * `R ⊑ S` implies `R⁻ ⊑ S⁻` (substituting `y,x` for `x,y`), so one tableau
   * run pays for two edges. The mirror is also what makes
   * `makeConceptUnsatisfiable` propagate correctly: marking `R` unsatisfiable
   * marks `R⁻` unsatisfiable too.
   */
  addKnownSubsumption(subConcept, superConcept) {
    super.addKnownSubsumption(subConcept, superConcept);
    if (!this.hasInverses) return;
    const mirrored = this._inversePair(subConcept, superConcept);
    if (mirrored === null) return;
    super.addKnownSubsumption(mirrored[0], mirrored[1]);
  }

  /** Record a still-possible subsumption, mirrored onto the inverses. */
  addPossibleSubsumption(subConcept, superConcept) {
    super.addPossibleSubsumption(subConcept, superConcept);
    if (!this.hasInverses) return;
    const mirrored = this._inversePair(subConcept, superConcept);
    if (mirrored === null) return;
    super.addPossibleSubsumption(mirrored[0], mirrored[1]);
  }

  /**
   * Map a proxy-concept pair onto the pair for their inverse roles.
   *
   * @returns {[object, object]|null} `[subForInverse, superForInverse]`, or null
   *          when either side has no proxy — which cannot happen while
   *          `hasInverses` is true, because `classifyObjectProperties` then
   *          enumerates every role's inverse. Skipping is sound (see the header
   *          note); throwing would turn a bookkeeping gap into a hard failure.
   * @private
   */
  _inversePair(subConcept, superConcept) {
    const subRole = this.rolesForConcepts.get(subConcept);
    const superRole = this.rolesForConcepts.get(superConcept);
    if (subRole === undefined || superRole === undefined) return null;
    const subForInverse = this.conceptsForRoles.get(subRole.getInverse());
    const superForInverse = this.conceptsForRoles.get(superRole.getInverse());
    if (subForInverse === undefined || superForInverse === undefined) return null;
    return [subForInverse, superForInverse];
  }

  // ---- Reasoning-task descriptions ----------------------------------------
  //
  // Reporting the internal proxy concepts (`internal:prop#…`) in progress and
  // monitor output is useless to a caller, so these describe the tests in terms
  // of the ROLES actually being classified.

  getSatTestDescription(atomicConcept) {
    return `isObjectRoleSatisfiable(${this._role(atomicConcept)})`;
  }

  getSubsumptionTestDescription(subConcept, superConcept) {
    return `isObjectRoleSubsumedBy(${this._role(subConcept)}, ${this._role(superConcept)})`;
  }

  getSubsumedByListTestDescription(subConcept, superConcepts) {
    const supers = superConcepts.map((c) => this._role(c));
    return `isObjectRoleSubsumedByList(${this._role(subConcept)}, [${supers.join(', ')}])`;
  }

  /**
   * The role a proxy concept stands for, falling back to the concept itself for
   * anything outside the proxy map (which would only be `owl:Thing`/`owl:Nothing`
   * if they ever reached a description).
   * @private
   */
  _role(atomicConcept) {
    const role = this.rolesForConcepts.get(atomicConcept);
    return role === undefined ? atomicConcept : role;
  }
}

module.exports = { QuasiOrderClassificationForRoles };
