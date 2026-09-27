'use strict';

// ---------------------------------------------------------------------------
// monitor/TableauMonitorFork.js — fan one monitor slot out to two monitors.
//
// Mirrors org.semanticweb.HermiT.monitor.TableauMonitorFork.
//
// HermiT hand-writes a forwarding method for each of the ~52 interface methods.
// Here the forwarding is generated from `TableauMonitorAdapter.prototype`, so it
// can never drift out of sync with the hook set: adding a hook to the adapter
// automatically makes the fork forward it.
//
// `Reasoner.createTableau` uses this to combine a well-known monitor selected by
// `Configuration.tableauMonitorType` with a user-supplied `configuration.monitor`
// — HermiT does exactly the same when both are present.
//
// A hook is only invoked on a delegate that actually defines it, matching the
// `typeof monitor.<hook> === 'function'` guards `Tableau` already uses. That
// lets a minimal user monitor (e.g. one implementing only `backtrackToStarted`)
// be forked with a full monitor without either side breaking.
// ---------------------------------------------------------------------------

const { TableauMonitorAdapter } = require('./TableauMonitorAdapter');

/**
 * Every hook name the adapter declares, excluding the constructor and
 * `setTableau` (which needs to record the tableau on the fork itself, not just
 * forward it — see below).
 */
const HOOK_NAMES = Object.getOwnPropertyNames(TableauMonitorAdapter.prototype)
  .filter((name) => name !== 'constructor' && name !== 'setTableau'
    && typeof TableauMonitorAdapter.prototype[name] === 'function');

class TableauMonitorFork extends TableauMonitorAdapter {
  /**
   * @param {object} first  monitor receiving every hook first
   * @param {object} second monitor receiving every hook second
   */
  constructor(first, second) {
    super();
    this.first = first;
    this.second = second;
  }
}

// Generate the forwarding methods.
for (const name of HOOK_NAMES) {
  TableauMonitorFork.prototype[name] = function forward(...args) {
    const f = this.first;
    const s = this.second;
    if (f && typeof f[name] === 'function') f[name](...args);
    if (s && typeof s[name] === 'function') s[name](...args);
  };
}

// `setTableau` records the tableau on the fork itself AND forwards it.
TableauMonitorFork.prototype.setTableau = function setTableau(tableau) {
  this.tableau = tableau;
  const f = this.first;
  const s = this.second;
  if (f && typeof f.setTableau === 'function') f.setTableau(tableau);
  if (s && typeof s.setTableau === 'function') s.setTableau(tableau);
};

module.exports = { TableauMonitorFork, HOOK_NAMES };
