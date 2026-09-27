'use strict';

// ---------------------------------------------------------------------------
// test/helpers.js — shared fixtures for the `node --test` suite.
//
// The smoke scripts under `scripts/` are exhaustive, hand-rolled assertion
// harnesses. This suite is the `node:test` front door: smaller, focused, and
// covering the regressions that were actually found and fixed. Both run under
// `npm test`.
// ---------------------------------------------------------------------------

const E = require('../src/owl/OWLExpressions');

const EX = 'http://example.org/test#';

const cls = (n) => E.owlClass(EX + n);
const op = (n) => E.objectProperty(EX + n);
const dp = (n) => E.dataProperty(EX + n);
const ind = (n) => E.namedIndividual(EX + n);
const dt = (n) => E.datatype(EX + n);

const AT = E.AxiomType;

const declaration = (entity) => ({ axiomType: AT.DECLARATION, entity });
const datatypeDefinition = (datatype, dataRange) =>
  ({ axiomType: AT.DATATYPE_DEFINITION, datatype, dataRange });
const dataPropertyRange = (property, range) =>
  ({ axiomType: AT.DATA_PROPERTY_RANGE, property, range });
const differentIndividuals = (individuals) =>
  E.differentIndividuals(individuals);

/**
 * A minimal protege-js-shaped ontology: `getAxioms()` returns an ARRAY.
 *
 * It is MUTABLE (`addAxiom`/`removeAxiom`) because HermiT's incremental API
 * treats the ontology as the source of truth — the OWL API mutates the
 * ontology first, then fires an `OWLOntologyChange` that the reasoner merely
 * buffers; `flush()` re-clausifies the already-updated ontology.
 */
function ontology(axioms, iri = EX + 'test') {
  const list = [...new Set(axioms)];
  return {
    getAxioms: () => list.slice(),
    getOntologyID: () => ({ ontologyIRI: iri }),
    addAxiom(ax) { if (!list.includes(ax)) list.push(ax); },
    removeAxiom(ax) { const i = list.indexOf(ax); if (i >= 0) list.splice(i, 1); },
    _axioms: list
  };
}

/**
 * A tableau monitor that records backjump distances.
 *
 * `Tableau.backtrackTo(n)` calls `backtrackToStarted(branchingPoint)` BEFORE
 * lowering `currentBranchingPoint`, so at that moment
 * `tableau.currentBranchingPoint` is still the level we jump FROM and
 * `branchingPoint.level` is the level we jump TO.
 *
 * Injected via `Configuration.monitor` — `Reasoner.createTableau` reads
 * `configuration.monitor || null` and, when a well-known monitor is also
 * selected via `tableauMonitorType`, forks the two with a
 * `TableauMonitorFork`; with the default `NONE` the custom monitor is used
 * verbatim.
 */
class BackjumpRecorder {
  constructor() {
    this.tableau = null;
    this.backtracks = [];
    this.maxSkipped = 0;
    this.branchingPointsPushed = 0;
  }

  setTableau(tableau) { this.tableau = tableau; }

  pushBranchingPointStarted() { this.branchingPointsPushed++; }

  backtrackToStarted(branchingPoint) {
    const from = this.tableau.currentBranchingPoint;
    const to = branchingPoint.level;
    const skipped = from - to;
    this.backtracks.push({ from, to, skipped });
    if (skipped > this.maxSkipped) this.maxSkipped = skipped;
  }
}

/** Build a reasoner plus its recorder in one call. */
function recordingReasoner(axioms, extraConfig) {
  const rec = new BackjumpRecorder();
  const { createReasoner } = require('../src/reasoner/Reasoner');
  const r = createReasoner(ontology(axioms),
    Object.assign({ monitor: rec }, extraConfig || {}));
  return { r, rec };
}

/**
 * Build a plain reasoner over `axioms` with optional configuration overrides.
 *
 * The caller owns disposal (`r.dispose()`), so tests can inspect the tableau
 * afterwards — which is what makes configuration options observable.
 */
function createR(onto, extraConfig) {
  const { createReasoner } = require('../src/reasoner/Reasoner');
  return createReasoner(onto, extraConfig || {});
}

/** Flatten a Node OR NodeSet to an array of IRI strings. */
function iris(nodeOrNodeSet) {
  const items = typeof nodeOrNodeSet.getFlattened === 'function'
    ? nodeOrNodeSet.getFlattened()
    : nodeOrNodeSet.getEntities();
  return [...items].map((x) => E.iriString(x)).sort();
}

module.exports = {
  E, AT, EX,
  cls, op, dp, ind, dt,
  declaration, datatypeDefinition, dataPropertyRange, differentIndividuals,
  ontology, BackjumpRecorder, recordingReasoner, createR, iris
};
