'use strict';

// ---------------------------------------------------------------------------
// monitor/CountingMonitor.js — counts nodes, backtracks, clashes and time.
//
// Mirrors org.semanticweb.HermiT.monitor.CountingMonitor.
//
// Two scopes of measurement, exactly as in HermiT:
//   • per-test  — reset by `isSatisfiableStarted`, read via `getTime()`,
//                 `getNumberOfBacktrackings()`, `getNumberOfNodes()`, …
//   • overall   — accumulated by `isSatisfiableFinished`, read via
//                 `getOverallTime()`, `getOverallNumberOfBacktrackings()`, …
//
// Test records are grouped by the reasoning-task description STRING (HermiT
// groups by `ReasoningTaskDescription.getMessagePattern()`; this port passes a
// plain string, so the string itself is the pattern).
//
// Not ported: the validated-blocking counters (`getInitialModelSize`,
// `getInitiallyBlocked`, `getInitiallyInvalid`, `getNoValidations`,
// `getValidationTime`) and the datatype-checking counters
// (`getNumberDatatypesChecked`, `getDatatypeCheckingTime`). Those hooks
// (`blockingValidationStarted/Finished`, `datatypeCheckingStarted/Finished`)
// belong to `ValidatedBlocking` and `DatatypeChecker`, neither of which is
// ported, so the fields would always read 0. `possibleInstanceIsInstance/Not`
// belongs to `InstanceManager`, also not ported.
// ---------------------------------------------------------------------------

const { TableauMonitorAdapter } = require('./TableauMonitorAdapter');

/**
 * One finished reasoning task.
 * @typedef {{time: number, description: string, result: boolean}} TestRecord
 */

class CountingMonitor extends TableauMonitorAdapter {
  /**
   * @param {boolean} [countClashes] also count clashes. HermiT accumulates
   *   `m_overallNumberOfClashes` but never increments it (no `clashDetected`
   *   hook is wired in this port either), so it is counted here from the
   *   extension manager at the end of each test instead.
   */
  constructor(countClashes = true) {
    super();
    this.countClashes = countClashes;

    // ---- per-test ----
    this.problemStartTime = 0;
    this.time = 0;
    this.numberOfBacktrackings = 0;
    this.numberOfNodes = 0;
    this.numberOfBlockedNodes = 0;
    this.numberOfClashes = 0;
    this.reasoningTaskDescription = null;
    this.testResult = false;

    // ---- overall ----
    /** @type {Map<string, TestRecord[]>} */
    this.testRecords = new Map();
    this.overallTime = 0;
    this.overallNumberOfBacktrackings = 0;
    this.overallNumberOfNodes = 0;
    this.overallNumberOfBlockedNodes = 0;
    this.overallNumberOfTests = 0;
    this.overallNumberOfClashes = 0;
  }

  /** Zero every counter and drop all test records (HermiT's `reset()`). */
  reset() {
    this.problemStartTime = 0;
    this.time = 0;
    this.numberOfBacktrackings = 0;
    this.numberOfNodes = 0;
    this.numberOfBlockedNodes = 0;
    this.numberOfClashes = 0;
    this.reasoningTaskDescription = null;
    this.testResult = false;
    this.testRecords.clear();
    this.overallTime = 0;
    this.overallNumberOfBacktrackings = 0;
    this.overallNumberOfNodes = 0;
    this.overallNumberOfBlockedNodes = 0;
    this.overallNumberOfTests = 0;
    this.overallNumberOfClashes = 0;
  }

  // ---- hooks ----------------------------------------------------------------

  isSatisfiableStarted(reasoningTaskDescription) {
    this.testNo = (this.testNo || 0) + 1;
    this.reasoningTaskDescription = reasoningTaskDescription;
    this.overallNumberOfTests++;
    this.problemStartTime = Date.now();
    this.numberOfBacktrackings = 0;
    this.numberOfNodes = 0;
    this.numberOfBlockedNodes = 0;
    this.numberOfClashes = 0;
  }

  isSatisfiableFinished(_reasoningTaskDescription, result) {
    this.testResult = result;
    this.time = Date.now() - this.problemStartTime;

    const pattern = String(this.reasoningTaskDescription);
    let records = this.testRecords.get(pattern);
    if (!records) { records = []; this.testRecords.set(pattern, records); }
    records.push({ time: this.time, description: pattern, result: this.testResult });

    this.overallTime += this.time;
    this.overallNumberOfBacktrackings += this.numberOfBacktrackings;

    // HermiT: `m_tableau.getNumberOfNodesInTableau() - getNumberOfMergedOrPrunedNodes()`.
    const t = this.tableau;
    if (t) {
      this.numberOfNodes = (t.numberOfNodesInTableau || 0) - (t.numberOfMergedOrPrunedNodes || 0);
      this.numberOfBlockedNodes = this._countBlockedNodesWithWork(t);
      if (this.countClashes) this.numberOfClashes = this._countClashes(t);
    }
    this.overallNumberOfNodes += this.numberOfNodes;
    this.overallNumberOfBlockedNodes += this.numberOfBlockedNodes;
    this.overallNumberOfClashes += this.numberOfClashes;
  }

  backtrackToFinished(_branchingPoint) {
    this.numberOfBacktrackings++;
  }

  // ---- helpers --------------------------------------------------------------

  /**
   * Active, blocked nodes that still have unprocessed existentials — i.e. nodes
   * whose blocking is actually load-bearing. HermiT counts exactly these.
   *
   * Defensive throughout: a monitor is a DIAGNOSTIC component and must never be
   * able to break a reasoning run, so a missing or partially-initialised
   * tableau counts as zero rather than throwing.
   * @param {import('../tableau/Tableau').Tableau} tableau
   */
  _countBlockedNodesWithWork(tableau) {
    let count = 0;
    let node = tableau.firstTableauNode;
    while (node !== null && node !== undefined) {
      if (node.isActive() && node.isBlocked() && node.hasUnprocessedExistentials()) count++;
      node = node.nextTableauNode;
    }
    return count;
  }

  /**
   * Whether the finished run ended in a clash. `ExtensionManager.containsClash()`
   * is still meaningful after `isSatisfiable` returns (the tableau is only
   * cleared at the START of the next run), so this reads the final state.
   * @param {import('../tableau/Tableau').Tableau} tableau
   */
  _countClashes(tableau) {
    const em = tableau.extensionManager;
    return em && typeof em.containsClash === 'function' && em.containsClash() ? 1 : 0;
  }

  // ---- getters: test records ------------------------------------------------

  /** Every distinct reasoning-task description seen so far. */
  getUsedMessagePatterns() { return [...this.testRecords.keys()]; }

  /**
   * The slowest tests first.
   * @param {number} [limit] at most this many records
   * @param {string} [messagePattern] restrict to one task description
   * @returns {TestRecord[]}
   */
  getTimeSortedTestRecords(limit = Infinity, messagePattern = null) {
    let filtered = [];
    if (messagePattern === null || messagePattern === undefined) {
      for (const records of this.testRecords.values()) filtered.push(...records);
    } else {
      filtered = this.testRecords.get(String(messagePattern)) || [];
    }
    filtered = filtered.slice().sort((a, b) => b.time - a.time);
    const n = Math.min(limit, filtered.length);
    return filtered.slice(0, n);
  }

  // ---- getters: current test ------------------------------------------------

  getTime() { return this.time; }
  getNumberOfBacktrackings() { return this.numberOfBacktrackings; }
  getNumberOfNodes() { return this.numberOfNodes; }
  getNumberOfBlockedNodes() { return this.numberOfBlockedNodes; }
  getNumberOfClashes() { return this.numberOfClashes; }
  getTestDescription() { return String(this.reasoningTaskDescription); }
  getTestResult() { return this.testResult; }

  // ---- getters: overall -----------------------------------------------------

  getOverallTime() { return this.overallTime; }
  getOverallNumberOfBacktrackings() { return this.overallNumberOfBacktrackings; }
  getOverallNumberOfNodes() { return this.overallNumberOfNodes; }
  getOverallNumberOfBlockedNodes() { return this.overallNumberOfBlockedNodes; }
  getOverallNumberOfTests() { return this.overallNumberOfTests; }
  getOverallNumberOfClashes() { return this.overallNumberOfClashes; }

  /** Overall counters as a plain object — handy for assertions and logging. */
  getSummary() {
    return {
      tests: this.overallNumberOfTests,
      timeMs: this.overallTime,
      backtracks: this.overallNumberOfBacktrackings,
      nodes: this.overallNumberOfNodes,
      blockedNodes: this.overallNumberOfBlockedNodes,
      clashes: this.overallNumberOfClashes
    };
  }
}

module.exports = { CountingMonitor };
