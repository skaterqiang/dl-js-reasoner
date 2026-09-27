'use strict';

// ---------------------------------------------------------------------------
// monitor/Timer.js — prints progress and statistics while reasoning.
//
// Mirrors org.semanticweb.HermiT.monitor.Timer.
//
// Differences from HermiT:
//   • Output goes through an injectable `write`/`writeLine` pair rather than a
//     `PrintWriter`, so tests can capture it. Defaults to `process.stdout`.
//   • The "binary/ternary table size in kb" line is replaced by the tuple counts
//     of every extension table: this port keys tables by ARITY (a Map), not by
//     a fixed binary/ternary pair, and `ExtensionTable` has no `sizeInMemory()`.
//   • `reasoningTaskDescription` is a plain string here, so it is printed as-is.
// ---------------------------------------------------------------------------

const { TableauMonitorAdapter } = require('./TableauMonitorAdapter');

/** How often (ms) `iterationStarted` re-prints statistics during a long run. */
const STATUS_INTERVAL_MS = 30000;

class Timer extends TableauMonitorAdapter {
  /**
   * @param {object} [options]
   * @param {(text: string) => void} [options.write]   append without a newline
   * @param {(text: string) => void} [options.writeLine] append with a newline
   */
  constructor(options = {}) {
    super();
    const out = options.out || process.stdout;
    this.write = options.write || ((text) => { out.write(text); });
    this.writeLine = options.writeLine || ((text) => { out.write(text + '\n'); });

    this.problemStartTime = 0;
    this.lastStatusTime = 0;
    this.numberOfBacktrackings = 0;
    this.testNumber = 0;
  }

  /** Reset the per-run counters and start the clock (HermiT's `start()`). */
  start() {
    this.numberOfBacktrackings = 0;
    this.problemStartTime = Date.now();
    this.lastStatusTime = this.problemStartTime;
  }

  isSatisfiableStarted(reasoningTaskDescription) {
    this.write(`${reasoningTaskDescription} ...`);
    this.start();
  }

  isSatisfiableFinished(_reasoningTaskDescription, result) {
    this.writeLine(result ? 'YES' : 'NO');
    this.doStatistics();
  }

  iterationStarted() {
    if (Date.now() - this.lastStatusTime > STATUS_INTERVAL_MS) {
      if (this.lastStatusTime === this.problemStartTime) this.writeLine('');
      this.doStatistics();
      this.lastStatusTime = Date.now();
    }
  }

  saturateStarted() { this.testNumber++; }

  backtrackToFinished(_branchingPoint) { this.numberOfBacktrackings++; }

  /** Print the current run's statistics (HermiT's `doStatistics()`). */
  doStatistics() {
    const durationSoFar = Date.now() - this.problemStartTime;
    const t = this.tableau;

    this.write('    Test:   ');
    this._printPadded(this.testNumber, 7);
    this.write('  Duration:  ');
    this._printPadded(`${durationSoFar} ms`, 7);
    this.write('   Current branching point: ');
    this._printPadded(t ? t.getCurrentBranchingPointLevel() : 0, 7);
    if (this.numberOfBacktrackings > 0) {
      this.write('    Backtrackings: ');
      this.write(String(this.numberOfBacktrackings));
    }
    this.writeLine('');

    if (t) {
      this.write('    Nodes:  in tableau: ');
      this._printPadded(t.numberOfNodesInTableau, 7);
      this.write('    created: ');
      this._printPadded(t.numberOfNodeCreations, 7);
      if (t.numberOfMergedOrPrunedNodes > 0) {
        this.write('    merged/pruned: ');
        this.write(String(t.numberOfMergedOrPrunedNodes));
      }
      this.writeLine('');
    }

    if (t && t.statistics) {
      this.write('    Work:   iterations: ');
      this._printPadded(t.statistics.iterations, 7);
      this.write('    clauses fired: ');
      this._printPadded(t.statistics.clausesFired, 7);
      this.write('    backjumps: ');
      this.write(String(t.statistics.backjumps));
      this.writeLine('');
    }

    if (t && t.extensionManager && typeof t.extensionManager.getAllTables === 'function') {
      this.write('    Sizes:  ');
      const parts = [];
      for (const table of t.extensionManager.getAllTables()) {
        parts.push(`arity-${table.arity} table: ${table.size}`);
      }
      this.writeLine(parts.join('    '));
    }
    this.writeLine('');
  }

  /** Right-pad `value` to `padding` columns (HermiT's `printPadded`). */
  _printPadded(value, padding) {
    const s = String(value);
    this.write(s.length >= padding ? s : s + ' '.repeat(padding - s.length));
  }
}

module.exports = { Timer, STATUS_INTERVAL_MS };
