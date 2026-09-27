'use strict';

/**
 * src/cli/Writer.js — the `java.io.PrintWriter` stand-in.
 *
 * HermiT's CLI and hierarchy printers all take a `PrintWriter`. JavaScript has
 * no such type, so this module supplies a minimal duck-typed equivalent with
 * the two methods the ported code actually calls (`print`, `println`) plus
 * `flush()`.
 *
 * Three concrete sinks are provided:
 *
 *   - {@link StringWriter}  — accumulates into a string (tests, `dumpHierarchies`)
 *   - {@link StreamWriter}  — writes to any Node writable stream (`process.stdout`)
 *   - {@link FileWriter}    — appends to an open file descriptor
 *
 * Anything exposing `print(s)` and `println(s)` is accepted by the printers, so
 * callers may substitute their own sink.
 */

const fs = require('fs');

/** Base class: implements `println` in terms of `print`. */
class Writer {
  /**
   * Write a string with no line terminator.
   * @param {string} s
   */
  print(s) {
    throw new Error('Writer.print must be implemented.');
  }

  /**
   * Write a string followed by the platform line separator.
   * @param {string} [s]
   */
  println(s = '') {
    this.print(`${s}\n`);
  }

  /** Flush any buffering. A no-op for unbuffered sinks. */
  flush() {}

  /** Close the sink. A no-op unless the writer owns a resource. */
  close() {}
}

/** A {@link Writer} that accumulates everything into a string. */
class StringWriter extends Writer {
  constructor() {
    super();
    /** @type {string[]} */
    this._parts = [];
  }

  print(s) {
    this._parts.push(String(s));
  }

  /** Everything written so far. */
  toString() {
    return this._parts.join('');
  }

  /** Discard the accumulated text. */
  reset() {
    this._parts.length = 0;
  }
}

/**
 * A {@link Writer} over a Node writable stream.
 *
 * `write`/`end` are called on the stream, so `process.stdout`, an
 * `fs.WriteStream` and a test double all work.
 */
class StreamWriter extends Writer {
  /**
   * @param {{write: function(string): void, end?: function(): void}} stream
   */
  constructor(stream) {
    super();
    if (stream === null || stream === undefined || typeof stream.write !== 'function') {
      throw new Error('StreamWriter requires a stream with a write(string) method.');
    }
    this.stream = stream;
  }

  print(s) {
    this.stream.write(String(s));
  }

  flush() {
    // Node streams buffer internally; nothing to do.
  }

  close() {
    if (typeof this.stream.end === 'function') this.stream.end();
  }
}

/**
 * A {@link Writer} that appends to a file, opened eagerly so that an unwritable
 * path fails at construction time (HermiT's `FileOutputStream` behaviour).
 */
class FileWriter extends Writer {
  /**
   * @param {string} filePath
   */
  constructor(filePath) {
    super();
    this.filePath = filePath;
    try {
      this.fd = fs.openSync(filePath, 'w');
    } catch (e) {
      if (e && (e.code === 'EACCES' || e.code === 'EPERM' || e.code === 'EROFS')) {
        throw new Error(`unable to write to ${filePath}`);
      }
      throw new Error(`unable to open ${filePath} for writing`);
    }
  }

  print(s) {
    fs.writeSync(this.fd, String(s));
  }

  flush() {
    try { fs.fsyncSync(this.fd); } catch { /* not all platforms/streams support it */ }
  }

  close() {
    if (this.fd !== null && this.fd !== undefined) {
      try { fs.closeSync(this.fd); } catch { /* already closed */ }
      this.fd = null;
    }
  }
}

/**
 * Open a writer for a CLI `--output` style argument.
 *
 * `'-'` (and `null`/`undefined`) mean stdout, matching HermiT's convention.
 *
 * @param {?string} filePath
 * @param {{write: function(string): void}} [stdout] defaults to `process.stdout`
 * @returns {Writer}
 */
function openWriter(filePath, stdout = process.stdout) {
  if (filePath === null || filePath === undefined || filePath === '-') {
    return new StreamWriter(stdout);
  }
  return new FileWriter(filePath);
}

module.exports = {
  Writer,
  StringWriter,
  StreamWriter,
  FileWriter,
  openWriter
};
