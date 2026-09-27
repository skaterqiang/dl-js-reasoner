'use strict';

// ---------------------------------------------------------------------------
// test/monitor.test.js — the tableau monitor package.
//
// `TABLEAU_MONITOR_TYPE` is exported public API, so it must not be inert: each
// value has to install a real monitor. These tests drive the monitors through a
// real reasoner run (so the hook wiring in `Tableau` is exercised too) and check
// the counters against the values the backjump suite already establishes for the
// disjunction ladder.
//
// Reference numbers, PROBED (not assumed) for the ladder
//   A ⊑ B1⊔C1, B1 ⊑ B2⊑C2, B2 ⊑ B3⊔C3, each Ci ⊑ ⊥
// with NO class assertion, running isConsistent → isSatisfiable(A) →
// isEntailed(A⊑B3) → isEntailed(A⊑C1):
//   tests = 4      (isSatisfiable does NOT re-run isConsistent — it is cached —
//                   but the explicit isConsistent() call is its own test)
//   backtracks = 3 (all from isEntailed(A⊑B3); the model-finding queries and
//                   isEntailed(A⊑C1) add none)
//   clashes = 1    (the A⊑B3 test ends in a clash, which is why it is entailed)
// Note `CountingMonitor` counts `backtrackToFinished`, so these are backjumps
// that actually COMPLETED.
// ---------------------------------------------------------------------------

const test = require('node:test');
const assert = require('node:assert/strict');

const {
  cls, ind, declaration, ontology, iris
} = require('./helpers');
const E = require('../src/owl/OWLExpressions');

const subclassOf = E.subclassOf;
const { createReasoner } = require('../src/reasoner/Reasoner');
const {
  TableauMonitorAdapter,
  CountingMonitor,
  Timer,
  TimerWithPause,
  MemoryConsumptionMonitor,
  TableauMonitorFork,
  HOOK_NAMES
} = (() => {
  const adapter = require('../src/monitor/TableauMonitorAdapter');
  const counting = require('../src/monitor/CountingMonitor');
  const timer = require('../src/monitor/Timer');
  const timerWithPause = require('../src/monitor/TimerWithPause');
  const memory = require('../src/monitor/MemoryConsumptionMonitor');
  const fork = require('../src/monitor/TableauMonitorFork');
  return Object.assign({}, adapter, counting, timer, timerWithPause, memory, fork);
})();
const { TABLEAU_MONITOR_TYPE } = require('../src/Configuration');

/** The disjunction ladder — the one shape that reliably backtracks. */
function ladderAxioms() {
  const A = cls('A');
  const Bs = [1, 2, 3].map((i) => cls(`B${i}`));
  const Cs = [1, 2, 3].map((i) => cls(`C${i}`));
  return {
    A, Bs, Cs,
    axioms: [
      ...[A, ...Bs, ...Cs].map(declaration),
      subclassOf(A, E.objectUnionOf([Bs[0], Cs[0]])),
      subclassOf(Bs[0], E.objectUnionOf([Bs[1], Cs[1]])),
      subclassOf(Bs[1], E.objectUnionOf([Bs[2], Cs[2]])),
      subclassOf(Cs[0], E.owlNothing()),
      subclassOf(Cs[1], E.owlNothing()),
      subclassOf(Cs[2], E.owlNothing())
    ]
  };
}

/** Run the ladder queries that produce backtracks. */
function runLadder(r) {
  const { A, Bs, Cs } = ladderAxioms();
  r.isConsistent();
  r.isSatisfiable(A);
  const entailedB3 = r.isEntailed(subclassOf(A, Bs[2]));
  const entailedC1 = r.isEntailed(subclassOf(A, Cs[0]));
  return { entailedB3, entailedC1 };
}

// ===========================================================================

test('TableauMonitorAdapter: every hook is a callable no-op', () => {
  const m = new TableauMonitorAdapter();
  assert.equal(m.tableau, null, 'a fresh adapter has no tableau');
  // The adapter must declare each hook the Tableau can fire, so that a subclass
  // overriding one hook still satisfies the others.
  for (const hook of [
    'setTableau', 'isSatisfiableStarted', 'isSatisfiableFinished', 'tableauCleared',
    'saturateStarted', 'saturateFinished', 'iterationStarted', 'iterationFinished',
    'tupleAdded', 'tupleRemoved', 'nodeCreated',
    'pushBranchingPointStarted', 'pushBranchingPointFinished',
    'startNextBranchingPointStarted', 'startNextBranchingPointFinished',
    'backtrackToStarted', 'backtrackToFinished',
    'groundDisjunctionDerived', 'processGroundDisjunctionStarted',
    'groundDisjunctionSatisfied', 'processGroundDisjunctionFinished',
    'disjunctProcessingStarted', 'disjunctProcessingFinished'
  ]) {
    assert.equal(typeof m[hook], 'function', `missing hook ${hook}`);
    assert.doesNotThrow(() => m[hook]({}), `${hook} should be a no-op`);
  }
  const sentinel = { id: 1 };
  m.setTableau(sentinel);
  assert.equal(m.tableau, sentinel);
});

test('TableauMonitorFork forwards every adapter hook to both delegates', () => {
  assert.ok(HOOK_NAMES.length >= 20, 'the fork should generate a real hook set');
  assert.ok(!HOOK_NAMES.includes('constructor'));
  assert.ok(!HOOK_NAMES.includes('setTableau'), 'setTableau is bespoke, not generated');

  const calls = { first: [], second: [] };
  function recorder(name) {
    const rec = new TableauMonitorAdapter();
    for (const hook of HOOK_NAMES) {
      rec[hook] = (...args) => { calls[name].push([hook, args]); };
    }
    rec.setTableau = (t) => { calls[name].push(['setTableau', [t]]); };
    return rec;
  }

  const fork = new TableauMonitorFork(recorder('first'), recorder('second'));
  const tableau = { id: 'T' };
  fork.setTableau(tableau);
  // The fork records the tableau on itself too (the generated forwarder would not).
  assert.equal(fork.tableau, tableau);

  fork.backtrackToStarted({ level: 2 });
  fork.isSatisfiableFinished('task', true);

  for (const side of ['first', 'second']) {
    const hooks = calls[side].map((c) => c[0]);
    assert.deepEqual(hooks, ['setTableau', 'backtrackToStarted', 'isSatisfiableFinished']);
    assert.deepEqual(calls[side][1][1], [{ level: 2 }]);
    assert.deepEqual(calls[side][2][1], ['task', true]);
  }
});

test('TableauMonitorFork tolerates a delegate that implements only some hooks', () => {
  // `Tableau` guards every call with a typeof check, so a minimal user monitor
  // must be forkable with a full one without either side throwing.
  const minimal = { backtrackToStarted() { minimal.seen = (minimal.seen || 0) + 1; } };
  const full = new CountingMonitor();
  const fork = new TableauMonitorFork(full, minimal);

  assert.doesNotThrow(() => fork.setTableau({}));
  assert.doesNotThrow(() => fork.isSatisfiableStarted('task'));
  assert.doesNotThrow(() => fork.backtrackToStarted({ level: 0 }));
  assert.doesNotThrow(() => fork.backtrackToFinished({ level: 0 }));
  assert.doesNotThrow(() => fork.isSatisfiableFinished('task', true));
  assert.equal(minimal.seen, 1);
  assert.equal(full.getNumberOfBacktrackings(), 1);
});

test('CountingMonitor counts tests and backtracks over a real ladder run', () => {
  const { axioms } = ladderAxioms();
  const monitor = new CountingMonitor();
  const r = createReasoner(ontology(axioms), { monitor });
  try {
    const { entailedB3, entailedC1 } = runLadder(r);
    assert.equal(entailedB3, true);
    assert.equal(entailedC1, false);

    const summary = monitor.getSummary();
    assert.equal(summary.tests, 4, 'isConsistent + isSatisfiable + two entailments');
    assert.equal(summary.backtracks, 3, 'all backjumps come from isEntailed(A⊑B3)');
    assert.equal(summary.clashes, 1, 'the A⊑B3 test ends in a clash');
    assert.ok(summary.nodes > 0, 'nodes were counted');
    assert.ok(summary.timeMs >= 0);

    // Per-test counters reflect the LAST test only.
    assert.equal(monitor.getOverallNumberOfTests(), 4);
    assert.equal(monitor.getOverallNumberOfBacktrackings(), 3);
    assert.equal(monitor.getNumberOfBacktrackings(), 0,
      'the last test (A⊑C1) needed no backjump');
  } finally {
    r.dispose();
  }
});

test('CountingMonitor groups test records by reasoning-task description', () => {
  const { axioms } = ladderAxioms();
  const monitor = new CountingMonitor();
  const r = createReasoner(ontology(axioms), { monitor });
  try {
    runLadder(r);
    const patterns = monitor.getUsedMessagePatterns();
    assert.ok(patterns.length >= 1, 'at least one task description recorded');
    for (const p of patterns) assert.equal(typeof p, 'string');

    const all = monitor.getTimeSortedTestRecords();
    assert.equal(all.length, 4, 'one record per test');
    // Sorted slowest-first.
    for (let i = 1; i < all.length; i++) {
      assert.ok(all[i - 1].time >= all[i].time, 'records must be time-descending');
    }
    assert.equal(monitor.getTimeSortedTestRecords(1).length, 1, 'limit is honoured');
    for (const rec of all) {
      assert.equal(typeof rec.result, 'boolean');
      assert.ok(rec.description.length > 0);
    }
  } finally {
    r.dispose();
  }
});

test('CountingMonitor.reset() clears every counter', () => {
  const { axioms } = ladderAxioms();
  const monitor = new CountingMonitor();
  const r = createReasoner(ontology(axioms), { monitor });
  try {
    runLadder(r);
    assert.ok(monitor.getOverallNumberOfTests() > 0);
    monitor.reset();
    const s = monitor.getSummary();
    assert.deepEqual(s, {
      tests: 0, timeMs: 0, backtracks: 0, nodes: 0, blockedNodes: 0, clashes: 0
    });
    assert.deepEqual(monitor.getUsedMessagePatterns(), []);
    assert.deepEqual(monitor.getTimeSortedTestRecords(), []);
  } finally {
    r.dispose();
  }
});

test('CountingMonitor reports a clash for an unsatisfiable class', () => {
  // A ⊑ B ⊓ ¬B is inconsistent, so every test ends in a clash.
  const A = cls('A'); const B = cls('B');
  const monitor = new CountingMonitor();
  const r = createReasoner(ontology([
    declaration(A), declaration(B),
    subclassOf(A, B),
    subclassOf(A, E.objectComplementOf(B)),
    E.classAssertion(A, ind('a'))
  ]), { monitor });
  try {
    assert.equal(r.isConsistent(), false);
    assert.ok(monitor.getOverallNumberOfClashes() >= 1, 'a clash was counted');
  } finally {
    r.dispose();
  }
});

test('Timer writes a report through the injected sink', () => {
  // `doStatistics` emits its fields with `write` and only terminates lines with
  // `writeLine`, so BOTH sinks must be captured to see the report.
  const out = [];
  const monitor = new Timer({
    write: (t) => out.push(t),
    writeLine: (t) => out.push(t + '\n')
  });
  const { axioms } = ladderAxioms();
  const r = createReasoner(ontology(axioms), { monitor });
  try {
    r.isSatisfiable(cls('A'));
  } finally {
    r.dispose();
  }

  const report = out.join('');
  // `isSatisfiableStarted` writes "<task> ..." with no newline.
  assert.match(report, /\.\.\./, 'the task banner was written');
  // `isSatisfiableFinished` writes YES/NO then the statistics block.
  assert.match(report, /YES|NO/, 'the verdict was written');
  assert.match(report, /Test:/);
  assert.match(report, /Duration:/);
  assert.match(report, /Current branching point:/);
  assert.match(report, /Nodes:/);
  assert.match(report, /in tableau:/);
  assert.match(report, /Work:/);
  assert.match(report, /iterations:/);
  assert.match(report, /Sizes:/);
  assert.match(report, /arity-\d+ table: \d+/, 'extension-table sizes are reported');
  // `isSatisfiable` also runs `isConsistent` internally, so saturateStarted
  // fires twice.
  assert.equal(monitor.testNumber, 2);
});

test('Timer reports backtracks when the run backjumps', () => {
  const out = [];
  const monitor = new Timer({
    write: (t) => out.push(t),
    writeLine: (t) => out.push(t + '\n')
  });
  const { axioms, A, Bs } = ladderAxioms();
  const r = createReasoner(ontology(axioms), { monitor });
  try {
    r.isEntailed(subclassOf(A, Bs[2]));
  } finally {
    r.dispose();
  }
  const report = out.join('');
  assert.match(report, /Backtrackings: \d+/, 'backtracks are printed when non-zero');
  assert.ok(monitor.numberOfBacktrackings > 0);
});

test('REGRESSION: every TABLEAU_MONITOR_TYPE installs a working monitor', () => {
  // `TABLEAU_MONITOR_TYPE` is exported public API. Before the monitor package
  // existed, every value other than NONE was inert: `createTableau` ignored it
  // and used `configuration.monitor || null`. Setting TIMING must now actually
  // produce output, and the DEBUGGER_* values must install a CountingMonitor
  // rather than silently doing nothing.
  const { axioms, A } = ladderAxioms();

  // NONE stays silent.
  {
    const lines = [];
    const custom = { isSatisfiableFinished: () => lines.push('x') };
    const r = createReasoner(ontology(axioms), {
      tableauMonitorType: TABLEAU_MONITOR_TYPE.NONE,
      monitor: custom
    });
    try {
      r.isSatisfiable(A);
      // NONE means no well-known monitor, so the custom one is used verbatim —
      // NOT wrapped in a TableauMonitorFork.
      assert.equal(r.getTableau().tableauMonitor, custom,
        'NONE must not wrap the custom monitor in a fork');
    } finally { r.dispose(); }
    // Two hooks, because `isSatisfiable` also runs `isConsistent` internally.
    assert.deepEqual(lines, ['x', 'x'], 'NONE must not add a well-known monitor');
  }

  // TIMING prints.
  {
    const lines = [];
    const r = createReasoner(ontology(axioms), {
      tableauMonitorType: TABLEAU_MONITOR_TYPE.TIMING,
      monitorOptions: { write: () => {}, writeLine: (t) => lines.push(t) }
    });
    try { r.isSatisfiable(A); } finally { r.dispose(); }
    assert.ok(lines.length > 0, 'TIMING must produce a report');
    assert.ok(lines.some((l) => l === 'YES' || l === 'NO'));
  }

  // TIMING_WITH_PAUSE prints too. With a non-TTY stdin the pause is a no-op
  // (fs.readSync returns EOF immediately), so this run does not hang.
  {
    const lines = [];
    const r = createReasoner(ontology(axioms), {
      tableauMonitorType: TABLEAU_MONITOR_TYPE.TIMING_WITH_PAUSE,
      monitorOptions: { write: () => {}, writeLine: (t) => lines.push(t) }
    });
    try { r.isSatisfiable(A); } finally { r.dispose(); }
    assert.ok(lines.length > 0, 'TIMING_WITH_PAUSE must produce a report');
  }

  // DEBUGGER_* install a CountingMonitor.
  for (const type of [
    TABLEAU_MONITOR_TYPE.DEBUGGER_NO_HISTORY,
    TABLEAU_MONITOR_TYPE.DEBUGGER_HISTORY_ON
  ]) {
    const r = createReasoner(ontology(axioms), { tableauMonitorType: type });
    try {
      r.isSatisfiable(A);
      // `getTableau()` caches, so this is the monitor the run actually used.
      const t = r.getTableau();
      assert.ok(t.tableauMonitor instanceof CountingMonitor,
        `${type} must install a CountingMonitor`);
      // `isSatisfiable` also runs `isConsistent` internally: two tests, not one.
      assert.equal(t.tableauMonitor.getOverallNumberOfTests(), 2);
    } finally {
      r.dispose();
    }
  }

  // An unknown type is rejected rather than silently ignored.
  assert.throws(
    () => createReasoner(ontology(axioms), { tableauMonitorType: 'NOPE' }).isSatisfiable(A),
    /Unknown monitor type/
  );
});

test('REGRESSION: a well-known monitor and a custom monitor are forked together', () => {
  // HermiT combines `tableauMonitorType` with `configuration.monitor` via
  // TableauMonitorFork when both are present. Previously the custom monitor
  // WON outright and the well-known one was dropped.
  const { axioms, A, Bs } = ladderAxioms();
  const seen = [];
  const custom = {
    setTableau: () => seen.push('setTableau'),
    isSatisfiableStarted: () => seen.push('started'),
    backtrackToStarted: () => seen.push('backtrack'),
    isSatisfiableFinished: () => seen.push('finished')
  };
  const r = createReasoner(ontology(axioms), {
    tableauMonitorType: TABLEAU_MONITOR_TYPE.TIMING,
    monitorOptions: { write: () => {}, writeLine: () => {} },
    monitor: custom
  });
  try {
    const t = r.getTableau();
    assert.ok(t.tableauMonitor instanceof TableauMonitorFork, 'both monitors must be forked');
    assert.ok(t.tableauMonitor.first instanceof Timer);
    assert.equal(t.tableauMonitor.second, custom);

    r.isEntailed(subclassOf(A, Bs[2]));
    // `isEntailed` runs `isConsistent` first, then the real query — so the custom
    // monitor sees TWO started/finished pairs. The three backtracks all belong to
    // the second (the A⊑B3 query, which is entailed precisely because it clashes).
    assert.deepEqual(seen, [
      'setTableau',
      'started', 'finished',
      'started', 'backtrack', 'backtrack', 'backtrack', 'finished'
    ], 'the custom monitor still receives every hook through the fork');
  } finally {
    r.dispose();
  }
});

test('TimerWithPause pauses after each report via the injected wait hook', () => {
  const out = [];
  let waits = 0;
  const monitor = new TimerWithPause({
    write: (t) => out.push(t),
    writeLine: (t) => out.push(t + '\n'),
    wait: () => { waits++; }
  });
  const { axioms } = ladderAxioms();
  const r = createReasoner(ontology(axioms), { monitor });
  try {
    r.isSatisfiable(cls('A'));
  } finally {
    r.dispose();
  }
  const report = out.join('');
  // `doStatistics` runs once per `isSatisfiableFinished`; `isSatisfiable` also
  // runs `isConsistent` internally, so there are two reports and two pauses.
  assert.equal(monitor.testNumber, 2);
  assert.equal(waits, 2, 'a pause follows every statistics report');
  assert.equal(monitor.pauses, 2);
  assert.match(report, /Press something to continue\.\. /, 'the pause prompt is written');
});

test('TimerWithPause honours pause:false (no wait, no prompt)', () => {
  const out = [];
  let waits = 0;
  const monitor = new TimerWithPause({
    write: (t) => out.push(t),
    writeLine: (t) => out.push(t + '\n'),
    pause: false,
    wait: () => { waits++; }
  });
  const { axioms } = ladderAxioms();
  const r = createReasoner(ontology(axioms), { monitor });
  try {
    r.isSatisfiable(cls('A'));
  } finally {
    r.dispose();
  }
  assert.equal(waits, 0, 'pause:false disables the wait hook');
  assert.equal(monitor.pauses, 0);
  assert.doesNotMatch(out.join(''), /Press something/, 'no prompt when paused off');
});

test('the monitor package is reachable from the public index', () => {
  const api = require('../src/index');
  assert.equal(typeof api.CountingMonitor, 'function');
  assert.equal(typeof api.Timer, 'function');
  assert.equal(typeof api.TimerWithPause, 'function');
  assert.equal(typeof api.MemoryConsumptionMonitor, 'function');
  assert.equal(typeof api.TableauMonitorAdapter, 'function');
  assert.equal(typeof api.TableauMonitorFork, 'function');
  assert.ok(api.TABLEAU_MONITOR_TYPE.TIMING);
  // The exported enum values must all be real, selectable options.
  assert.deepEqual(Object.keys(api.TABLEAU_MONITOR_TYPE).sort(), [
    'DEBUGGER_HISTORY_ON', 'DEBUGGER_NO_HISTORY', 'NONE', 'TIMING', 'TIMING_WITH_PAUSE'
  ]);
});

test('a CountingMonitor works on a Horn ontology that never backtracks', () => {
  const A = cls('A'); const B = cls('B'); const C = cls('C');
  const monitor = new CountingMonitor();
  const r = createReasoner(ontology([
    declaration(A), declaration(B), declaration(C),
    subclassOf(A, B), subclassOf(B, C),
    E.classAssertion(A, ind('a'))
  ]), { monitor });
  try {
    assert.equal(r.isConsistent(), true);
    // `getTypes` already returns a NodeSet; `iris` flattens it.
    assert.deepEqual(
      iris(r.getTypes(ind('a'), false)).filter((i) => i.startsWith('http://example.org/test#')),
      ['http://example.org/test#A', 'http://example.org/test#B', 'http://example.org/test#C']
    );
    assert.equal(monitor.getOverallNumberOfBacktrackings(), 0, 'Horn never backjumps');
    // NOTE: clashes are NOT asserted to be zero here. `getTypes` triggers
    // classification, which probes `owlNothing` against each class — a probe that
    // legitimately ends in a clash. The claim of this test is the absence of
    // BACKTRACKING, which is what distinguishes a Horn ontology.
    assert.ok(monitor.getOverallNumberOfTests() >= 1);
  } finally {
    r.dispose();
  }
});

// ===========================================================================
// MemoryConsumptionMonitor
// ===========================================================================

test('MemoryConsumptionMonitor measures tableau expansion memory per test', () => {
  const { axioms, A, Bs } = ladderAxioms();
  const monitor = new MemoryConsumptionMonitor();
  const r = createReasoner(ontology(axioms), { monitor });
  try {
    r.isEntailed(subclassOf(A, Bs[2]));
    // It is a CountingMonitor: the inherited counters work too.
    assert.ok(monitor.getOverallNumberOfTests() >= 1);
    // Memory getters return numbers (bytes), never negative.
    const cur = monitor.getCurrentTableauExpansionMemoryUse();
    assert.ok(typeof cur === 'number' && cur >= 0);
    assert.equal(cur,
      monitor.getCurrentTableauExpansionBinaryTableSize() +
      monitor.getCurrentTableauExpansionTernaryTableSize() +
      monitor.getCurrentTableauExpansionDependencySetsSize(),
      'current total is the sum of its components');
    // The peak is at least the last reading; averages are consistent with sums.
    assert.ok(monitor.getMaxTableauExpansionMemoryUse() >= cur);
    assert.ok(monitor.getAverageTableauExpansionMemoryUse() >= 0);
  } finally {
    r.dispose();
  }
});

test('MemoryConsumptionMonitor reports non-zero memory for a role-assertion ontology', () => {
  // An ontology with a role assertion materialises tuples, so the total memory
  // use must be positive. NOTE: this port stores a role tuple as
  // [predicate, from, to] in the ARITY-3 table (there is no arity-2 table), so
  // the component assertion is about the TOTAL, not HermiT's binary split.
  const A = cls('A');
  const R = E.objectProperty('http://example.org/test#R');
  const a = ind('a'); const b = ind('b');
  const monitor = new MemoryConsumptionMonitor();
  const r = createReasoner(ontology([
    declaration(A), declaration(R), declaration(a), declaration(b),
    E.objectPropertyAssertion(R, a, b)
  ]), { monitor });
  try {
    r.isConsistent();
    assert.ok(monitor.getCurrentTableauExpansionMemoryUse() > 0,
      'a role assertion fills some extension table');
    assert.ok(monitor.getCurrentTableauExpansionTernaryTableSize() > 0,
      'role tuples live in the arity-3 table');
  } finally {
    r.dispose();
  }
});

test('MemoryConsumptionMonitor averages over zero tests are zero and reset() clears it', () => {
  const monitor = new MemoryConsumptionMonitor();
  assert.equal(monitor.getAverageTableauExpansionMemoryUse(), 0);
  assert.equal(monitor.getAverageTableauExpansionBinaryTableSize(), 0);
  assert.equal(monitor.getMaxTableauExpansionMemoryUse(), 0);

  const { axioms, A } = ladderAxioms();
  const r = createReasoner(ontology(axioms), { monitor });
  try {
    r.isSatisfiable(A);
    assert.ok(monitor.memTestNumber >= 1);
  } finally {
    r.dispose();
  }
  monitor.reset();
  assert.equal(monitor.getCurrentTableauExpansionMemoryUse(), 0);
  assert.equal(monitor.getMaxTableauExpansionMemoryUse(), 0);
  assert.equal(monitor.memTestNumber, 0);
  assert.equal(monitor.getAverageTableauExpansionMemoryUse(), 0);
  // And the inherited CountingMonitor state is reset too.
  assert.equal(monitor.getOverallNumberOfTests(), 0);
});
