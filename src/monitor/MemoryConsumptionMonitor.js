'use strict';

// ---------------------------------------------------------------------------
// monitor/MemoryConsumptionMonitor.js — measures tableau expansion memory.
//
// Mirrors org.semanticweb.HermiT.monitor.MemoryConsumptionMonitor.
//
// HermiT reads exact byte sizes from its binary/ternary extension tables and
// the dependency-set pool (`sizeInMemory()/1024`, in KB). This port's
// `ExtensionTable` keys by ARITY (a Map), not a fixed binary/ternary pair, and
// has no `sizeInMemory()`; its `DependencySetFactory` is interned and immutable
// (no recyclable pool — see its header), so there is no pool to measure. The
// port therefore reports an ESTIMATE in BYTES:
//   • per extension table: `size * (arity + 1) * PER_CELL_BYTES` (each tuple
//     holds `arity` payload references plus the interned predicate/dependency
//     bookkeeping);
//   • dependency sets: `dependencySetFactory.numberOfSets * PER_SET_BYTES`
//     (distinct non-permanent sets handed out — the closest analogue of the
//     pool size HermiT reports).
// The shape of the API is HermiT's: current / average / max, and per-component
// getters. "Binary/ternary" map onto "the arity-2 / arity-3 tables" (both may
// be absent — an arity-k-only tableau reports 0 for the others, exactly as an
// EL ontology with no role assertions reports 0 in HermiT).
// ---------------------------------------------------------------------------

const { CountingMonitor } = require('./CountingMonitor');

/** Estimated bytes per (predicate-or-tuple-cell) reference. */
const PER_CELL_BYTES = 8;
/** Estimated bytes per distinct dependency set. */
const PER_SET_BYTES = 24;

class MemoryConsumptionMonitor extends CountingMonitor {
  constructor(countClashes = true) {
    super(countClashes);
    // ---- per-test ----
    this.binaryTableMem = 0;   // bytes
    this.ternaryTableMem = 0;  // bytes
    this.dependencySetsMem = 0; // bytes
    // ---- running sums (for the averages) ----
    this.sumBinaryTableMem = 0;
    this.sumTernaryTableMem = 0;
    this.sumDependencySetsMem = 0;
    this.maxMem = 0;
    this.memTestNumber = 0;
  }

  isSatisfiableStarted(reasoningTaskDescription) {
    super.isSatisfiableStarted(reasoningTaskDescription);
    this.memTestNumber++;
  }

  isSatisfiableFinished(reasoningTaskDescription, result) {
    super.isSatisfiableFinished(reasoningTaskDescription, result);
    const { binary, ternary, depSets } = this._measure();
    this.binaryTableMem = binary;
    this.ternaryTableMem = ternary;
    this.dependencySetsMem = depSets;
    this.sumBinaryTableMem += binary;
    this.sumTernaryTableMem += ternary;
    this.sumDependencySetsMem += depSets;
    const sum = binary + ternary + depSets;
    if (sum > this.maxMem) this.maxMem = sum;
  }

  reset() {
    super.reset();
    this.binaryTableMem = 0;
    this.ternaryTableMem = 0;
    this.dependencySetsMem = 0;
    this.sumBinaryTableMem = 0;
    this.sumTernaryTableMem = 0;
    this.sumDependencySetsMem = 0;
    this.maxMem = 0;
    this.memTestNumber = 0;
  }

  /**
   * Current tableau expansion memory use, as `{binary, ternary, depSets}` in
   * estimated bytes. `binary`/`ternary` keep HermiT's names for API parity, but
   * NOTE this port stores a role tuple as [predicate, from, to] in the ARITY-3
   * table (there is no arity-2 table), so `binary` is 0 in practice and the
   * memory lands in `ternary`. Prefer `getExtensionTableMemoryByArity(n)`.
   * Defensive: a monitor must never break a run, so a missing or
   * partially-initialised tableau reads as zero.
   */
  _measure() {
    const t = this.tableau;
    let binary = 0;
    let ternary = 0;
    let depSets = 0;
    if (t && t.extensionManager && typeof t.extensionManager.getAllTables === 'function') {
      for (const table of t.extensionManager.getAllTables()) {
        const bytes = (table.size || 0) * ((table.arity || 0) + 1) * PER_CELL_BYTES;
        if (table.arity === 2) binary += bytes;
        else if (table.arity === 3) ternary += bytes;
      }
    }
    const dsf = t && t.dependencySetFactory;
    if (dsf && typeof dsf.numberOfSets === 'number') {
      depSets = dsf.numberOfSets * PER_SET_BYTES;
    }
    return { binary, ternary, depSets };
  }

  /**
   * Estimated bytes held by the arity-`n` extension table right now. This is
   * the honest, arity-keyed view of the tableau expansion memory.
   * @param {number} arity
   */
  getExtensionTableMemoryByArity(arity) {
    const t = this.tableau;
    if (!(t && t.extensionManager && typeof t.extensionManager.getAllTables === 'function')) return 0;
    let bytes = 0;
    for (const table of t.extensionManager.getAllTables()) {
      if (table.arity === arity) bytes += (table.size || 0) * (arity + 1) * PER_CELL_BYTES;
    }
    return bytes;
  }

  // ---- getters: current test ------------------------------------------------

  getCurrentTableauExpansionMemoryUse() {
    return this.binaryTableMem + this.ternaryTableMem + this.dependencySetsMem;
  }
  getCurrentTableauExpansionBinaryTableSize() { return this.binaryTableMem; }
  getCurrentTableauExpansionTernaryTableSize() { return this.ternaryTableMem; }
  getCurrentTableauExpansionDependencySetsSize() { return this.dependencySetsMem; }

  // ---- getters: averages ----------------------------------------------------

  getAverageTableauExpansionMemoryUse() {
    if (this.memTestNumber === 0) return 0;
    return (this.sumBinaryTableMem + this.sumTernaryTableMem + this.sumDependencySetsMem) / this.memTestNumber;
  }
  getAverageTableauExpansionBinaryTableSize() {
    return this.memTestNumber === 0 ? 0 : this.sumBinaryTableMem / this.memTestNumber;
  }
  getAverageTableauExpansionTernaryTableSize() {
    return this.memTestNumber === 0 ? 0 : this.sumTernaryTableMem / this.memTestNumber;
  }
  getAverageTableauExpansionDependencySetsSize() {
    return this.memTestNumber === 0 ? 0 : this.sumDependencySetsMem / this.memTestNumber;
  }

  // ---- getters: peak --------------------------------------------------------

  getMaxTableauExpansionMemoryUse() { return this.maxMem; }
}

module.exports = { MemoryConsumptionMonitor, PER_CELL_BYTES, PER_SET_BYTES };
