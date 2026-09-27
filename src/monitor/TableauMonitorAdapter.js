'use strict';

// ---------------------------------------------------------------------------
// monitor/TableauMonitorAdapter.js — no-op base for tableau observers.
//
// Mirrors org.semanticweb.HermiT.monitor.TableauMonitorAdapter, restricted to
// the subset of hooks this port's `Tableau` actually fires. HermiT's interface
// has ~52 methods; several belong to features that are not ported (validated
// blocking, description graphs, the DL-clause evaluator's per-match hooks, the
// interactive debugger). `Tableau` guards every call with
// `typeof monitor.<hook> === 'function'`, so a monitor only needs the hooks it
// uses — this adapter supplies all of them as no-ops so subclasses can override
// selectively.
//
// IMPORTANT: in this port `reasoningTaskDescription` is a plain STRING (e.g.
// `isInstanceOf(a, B)`), not HermiT's `ReasoningTaskDescription` object. There
// is no `getMessagePattern()` / `flipSatisfiabilityResult()`; monitors that want
// to group by task should key on the string itself.
// ---------------------------------------------------------------------------

class TableauMonitorAdapter {
  constructor() {
    /** @type {import('../tableau/Tableau').Tableau|null} */
    this.tableau = null;
  }

  setTableau(tableau) { this.tableau = tableau; }

  // ---- whole-run lifecycle --------------------------------------------------
  isSatisfiableStarted(_reasoningTaskDescription) {}
  isSatisfiableFinished(_reasoningTaskDescription, _result) {}
  tableauCleared() {}

  // ---- saturation loop ------------------------------------------------------
  saturateStarted() {}
  saturateFinished(_modelFound) {}
  iterationStarted() {}
  iterationFinished() {}

  // ---- extension table ------------------------------------------------------
  tupleAdded(_tuple) {}
  tupleRemoved(_tuple) {}

  // ---- nodes ----------------------------------------------------------------
  nodeCreated(_node) {}

  // ---- branching / backjumping ---------------------------------------------
  pushBranchingPointStarted(_branchingPoint) {}
  pushBranchingPointFinished(_branchingPoint) {}
  startNextBranchingPointStarted(_branchingPoint) {}
  startNextBranchingPointFinished(_branchingPoint) {}
  backtrackToStarted(_branchingPoint) {}
  backtrackToFinished(_branchingPoint) {}

  // ---- ground disjunctions --------------------------------------------------
  groundDisjunctionDerived(_groundDisjunction) {}
  processGroundDisjunctionStarted(_groundDisjunction) {}
  groundDisjunctionSatisfied(_groundDisjunction) {}
  processGroundDisjunctionFinished(_groundDisjunction) {}
  disjunctProcessingStarted(_groundDisjunction, _disjunct) {}
  disjunctProcessingFinished(_groundDisjunction, _disjunct) {}
}

module.exports = { TableauMonitorAdapter };
