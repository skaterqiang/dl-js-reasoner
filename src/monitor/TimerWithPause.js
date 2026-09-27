'use strict';

// ---------------------------------------------------------------------------
// monitor/TimerWithPause.js — `Timer` that pauses for input after each report.
//
// Mirrors org.semanticweb.HermiT.monitor.TimerWithPause.
//
// HermiT's version blocks on `System.in.readLine()` after every `doStatistics()`.
// There is no `readline` equivalent that blocks synchronously in Node, but a
// blocking read on stdin IS available as `fs.readSync(0, ...)`: it suspends the
// event loop until bytes arrive (or EOF). That is exactly the Java semantics —
// the tableau cannot advance while the user is reading the report.
//
// The pause is gated on interactivity: it only happens when stdin is a real
// terminal (`process.stdin.isTTY`). Under a pipe, a file, `node --test`, or any
// automated runner stdin is not a TTY (or, when it is, the runner owns the input
// stream), so the monitor degrades to the plain `Timer` and never hangs a batch
// run. A byte already sitting in the OS input queue is also discarded rather than
// treated as the user's keypress, so a leaked newline cannot "answer" the prompt.
//
// The pause is opt-out via `options.pause === false`, and the injected
// `options.wait` hook replaces the read entirely so tests can count the pauses
// without touching a real terminal.
// ---------------------------------------------------------------------------

const fs = require('fs');
const { Timer } = require('./Timer');

class TimerWithPause extends Timer {
  /**
   * @param {object} [options] forwarded to {@link Timer}; plus:
   * @param {boolean} [options.pause=true] set false to disable the pause
   * @param {() => void} [options.wait] replaces the blocking stdin read
   */
  constructor(options = {}) {
    super(options);
    this.pause = options.pause !== false;
    this._wait = options.wait || null;
    /** Number of pauses performed (read or hook call). Useful for tests. */
    this.pauses = 0;
  }

  doStatistics() {
    super.doStatistics();
    if (!this.pause) return;
    // Only an explicit `wait` hook, or a genuinely interactive terminal, pauses.
    const interactive = this._wait !== null ||
      (typeof process !== 'undefined' && process.stdin && process.stdin.isTTY === true);
    if (!interactive) return;
    this.write('Press something to continue.. ');
    this.pauses++;
    if (this._wait) {
      this._wait();
      return;
    }
    this._blockingReadLine();
  }

  /**
   * Block until a newline (or EOF) on stdin. Mirrors the Java
   * `m_in.readLine()` inside a try/catch that swallows IO errors — a closed or
   * non-readable stdin must not crash the reasoner. A byte already queued is
   * skipped, so a stray newline buffered before the prompt does not answer it.
   */
  _blockingReadLine() {
    const chunk = Buffer.alloc(1);
    // Discard anything already waiting in the OS input queue.
    if (process.stdin && typeof process.stdin.readableLength === 'number' &&
        process.stdin.readableLength > 0) {
      try { process.stdin.read(process.stdin.readableLength); } catch (_e) { /* ignore */ }
    }
    for (;;) {
      let n = 0;
      try {
        n = fs.readSync(0, chunk, 0, 1, null);
      } catch (_e) {
        return; // stdin not readable (e.g. no fd 0) — behave like EOF
      }
      if (n === 0 || chunk[0] === 10 /* \n */) return; // EOF or newline
    }
  }
}

module.exports = { TimerWithPause };
