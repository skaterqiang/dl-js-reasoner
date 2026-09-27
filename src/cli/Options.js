'use strict';
/**
 * src/cli/Options.js — the option table, its help formatting, and a getopt
 * implementation.
 *
 * Port of the `enum Arg`, `class Option`, `Option.formatOptionHelp`,
 * `Option.formatOptionsString` and `Option.breakLines` members of
 * `org.semanticweb.HermiT.cli.CommandLine`, plus a hand-rolled replacement for
 * `gnu.getopt.Getopt` (there is no JS equivalent worth depending on).
 *
 * The option codes mirror HermiT's `k*` constants exactly: single-character
 * options use their character code, long-only options use 1000+.
 */

/** `enum Arg` — whether an option takes a value. */
const Arg = Object.freeze({
  NONE: 'NONE',
  OPTIONAL: 'OPTIONAL',
  REQUIRED: 'REQUIRED'
});

/** Long-only option codes (HermiT's `k*` constants). */
const OptionCode = Object.freeze({
  kTime: 1000,
  kDumpClauses: 1001,
  kDumpRoleBox: 1002,
  kDirectBlock: 1003,
  kBlockStrategy: 1004,
  kBlockCache: 1005,
  kExpansion: 1006,
  kBase: 1007,
  kParser: 1008,
  kDefaultPrefix: 1009,
  kDumpPrefixes: 1010,
  kTaxonomy: 1011,
  kIgnoreUnsupportedDatatypes: 1012,
  kPremise: 1013,
  kConclusion: 1014,
  kNoInconsistentException: 1015
});

/** Option group headings, in display order. */
const OptionGroup = Object.freeze({
  kMisc: 'Miscellaneous',
  kActions: 'Actions',
  kParsing: 'Parsing and loading',
  kPrefixes: 'Prefix name and IRI',
  kAlgorithm: 'Algorithm settings (expert users only!)',
  kInternals: 'Internals and debugging (unstable)'
});

/**
 * One command-line option.
 *
 * HermiT has two constructors (no-argument and with-argument); this port uses
 * one signature with an optional `arg`/`metavar` pair.
 */
class Option {
  /**
   * @param {number|string} optChar a single character, or an {@link OptionCode}
   * @param {?string} longStr the long name WITHOUT the leading `--`
   * @param {?string} group an {@link OptionGroup} value, or null to continue
   *        the previous group without printing a new heading
   * @param {string} help one-line help text (wrapped by {@link breakLines})
   * @param {{arg?: string, metavar?: string}} [opts] `arg` is an {@link Arg}
   *        value (default `NONE`); `metavar` names the value in help output
   */
  constructor(optChar, longStr, group, help, opts = {}) {
    this.optChar = typeof optChar === 'string' ? optChar.codePointAt(0) : optChar;
    /** The character itself, for options that have one. @type {?string} */
    this.optCharString = typeof optChar === 'string' ? optChar : null;
    this.longStr = longStr || null;
    this.group = group === undefined ? null : group;
    this.arg = opts.arg || Arg.NONE;
    this.metavar = opts.metavar || null;
    this.help = help;
  }

  /** `--long`, `--long[=META]` or `--long=META`. */
  getLongOptExampleStr() {
    if (this.longStr === null || this.longStr === '') return '';
    if (this.arg === Arg.NONE) return `--${this.longStr}`;
    if (this.arg === Arg.OPTIONAL) return `--${this.longStr}[=${this.metavar}]`;
    return `--${this.longStr}=${this.metavar}`;
  }

  /** True iff this option can be given as `-X`. */
  hasShortForm() { return this.optChar < 256; }
}

/**
 * The full option table, in the order HermiT declares it (which is also the
 * order the help text is printed in).
 *
 * @type {Option[]}
 */
const options = [
  // ---- meta ----
  new Option('h', 'help', OptionGroup.kMisc, 'display this help and exit'),
  new Option('V', 'version', OptionGroup.kMisc, 'display version information and exit'),
  new Option('v', 'verbose', OptionGroup.kMisc, 'increase verbosity by AMOUNT levels (default 1)',
    { arg: Arg.OPTIONAL, metavar: 'AMOUNT' }),
  new Option('q', 'quiet', OptionGroup.kMisc, 'decrease verbosity by AMOUNT levels (default 1)',
    { arg: Arg.OPTIONAL, metavar: 'AMOUNT' }),
  new Option('o', 'output', OptionGroup.kMisc, 'write output to FILE',
    { arg: Arg.REQUIRED, metavar: 'FILE' }),
  new Option(OptionCode.kPremise, 'premise', OptionGroup.kMisc, 'set the premise ontology to PREMISE',
    { arg: Arg.REQUIRED, metavar: 'PREMISE' }),
  new Option(OptionCode.kConclusion, 'conclusion', OptionGroup.kMisc, 'set the conclusion ontology to CONCLUSION',
    { arg: Arg.REQUIRED, metavar: 'CONCLUSION' }),

  // ---- actions ----
  new Option('l', 'load', OptionGroup.kActions, 'parse and preprocess ontologies (default action)'),
  new Option('c', 'classify', OptionGroup.kActions, 'classify the classes of the ontology, optionally writing taxonomy to a file if -o (--output) is used'),
  new Option('O', 'classifyOPs', OptionGroup.kActions, 'classify the object properties of the ontology, optionally writing taxonomy to a file if -o (--output) is used'),
  new Option('D', 'classifyDPs', OptionGroup.kActions, 'classify the data properties of the ontology, optionally writing taxonomy to a file if -o (--output) is used'),
  new Option('P', 'prettyPrint', OptionGroup.kActions, 'when writing the classified hierarchy to a file, create a proper ontology and nicely indent the axioms according to their level in the hierarchy'),
  new Option('k', 'consistency', OptionGroup.kActions, 'check satisfiability of CLASS (default owl:Thing)',
    { arg: Arg.OPTIONAL, metavar: 'CLASS' }),
  new Option('d', 'direct', OptionGroup.kActions, 'restrict next subs/supers call to only direct sub/superclasses'),
  new Option('s', 'subs', OptionGroup.kActions, 'output classes subsumed by CLASS (or only direct subs if following --direct)',
    { arg: Arg.REQUIRED, metavar: 'CLASS' }),
  new Option('S', 'supers', OptionGroup.kActions, 'output classes subsuming CLASS (or only direct supers if following --direct)',
    { arg: Arg.REQUIRED, metavar: 'CLASS' }),
  new Option('e', 'equivalents', OptionGroup.kActions, 'output classes equivalent to CLASS',
    { arg: Arg.REQUIRED, metavar: 'CLASS' }),
  new Option('U', 'unsatisfiable', OptionGroup.kActions, 'output unsatisfiable classes (equivalent to --equivalents=owl:Nothing)'),
  new Option(OptionCode.kDumpPrefixes, 'print-prefixes', OptionGroup.kActions, 'output prefix names available for use in identifiers'),
  new Option('E', 'checkEntailment', OptionGroup.kActions, 'check whether the premise (option premise) ontology entails the conclusion ontology (option conclusion)'),

  // ---- prefixes ----
  new Option('N', 'no-prefixes', OptionGroup.kPrefixes, 'do not abbreviate or expand identifiers using prefixes defined in input ontology'),
  new Option('p', 'prefix', OptionGroup.kPrefixes, 'use PN as an abbreviation for IRI in identifiers',
    { arg: Arg.REQUIRED, metavar: 'PN=IRI' }),
  new Option(OptionCode.kDefaultPrefix, 'prefix', OptionGroup.kPrefixes, 'use IRI as the default identifier prefix',
    { arg: Arg.REQUIRED, metavar: 'IRI' }),

  // ---- base URI ----
  new Option(OptionCode.kBase, 'base', OptionGroup.kParsing, 'resolve relative ontology IRIs against BASE (default the current directory)',
    { arg: Arg.REQUIRED, metavar: 'BASE' }),

  // ---- algorithm tweaks ----
  new Option(OptionCode.kDirectBlock, 'block-match', OptionGroup.kAlgorithm, "identify blocked nodes with TYPE blocking; supported values are 'single', 'pairwise', and 'optimal' (default 'optimal')",
    { arg: Arg.REQUIRED, metavar: 'TYPE' }),
  new Option(OptionCode.kBlockStrategy, 'block-strategy', OptionGroup.kAlgorithm, "use TYPE as blocking strategy; supported values are 'ancestor', 'anywhere', 'core', and 'optimal' (default 'optimal')",
    { arg: Arg.REQUIRED, metavar: 'TYPE' }),
  new Option(OptionCode.kBlockCache, 'blockersCache', OptionGroup.kAlgorithm, 'cache blocking nodes for use in later tests; not possible with nominals or core blocking'),
  new Option(OptionCode.kIgnoreUnsupportedDatatypes, 'ignoreUnsupportedDatatypes', OptionGroup.kAlgorithm, 'ignore unsupported datatypes'),
  new Option(OptionCode.kExpansion, 'expansion-strategy', OptionGroup.kAlgorithm, "use TYPE as existential expansion strategy; supported values are 'el', 'creation', and 'reuse'",
    { arg: Arg.REQUIRED, metavar: 'TYPE' }),
  new Option(OptionCode.kNoInconsistentException, 'noInconsistentException', OptionGroup.kAlgorithm, 'do not throw an exception for an inconsistent ontology'),

  // ---- internals ----
  new Option(OptionCode.kDumpClauses, 'dump-clauses', OptionGroup.kInternals, 'output DL-clauses to FILE (default stdout)',
    { arg: Arg.OPTIONAL, metavar: 'FILE' })
];

/**
 * Wrap `str` to `lineWidth`, indenting continuation lines by `indent` spaces.
 *
 * Port of `Option.breakLines`. Java uses `BreakIterator.getLineInstance()`,
 * whose spans are a word PLUS any whitespace that follows it, and the width
 * test is applied to the whole span before it is appended. This port rebuilds
 * those same spans with a regex; splitting words and whitespace apart instead
 * would let a trailing space slip past the width test and emit `lineWidth + 1`
 * character lines.
 *
 * @param {string} str
 * @param {number} lineWidth
 * @param {number} indent
 * @returns {string}
 */
function breakLines(str, lineWidth, indent) {
  const pad = ' '.repeat(indent);
  const spans = String(str).match(/\S+\s*|\s+/g) || [];
  let out = '';
  let curLinePos = indent;
  for (const span of spans) {
    if (curLinePos + span.length > lineWidth) {
      out += `\n${pad}`;
      curLinePos = indent;
    }
    out += span;
    curLinePos += span.length;
  }
  return out;
}

/**
 * The grouped, column-aligned help text for the option table.
 *
 * Port of `Option.formatOptionHelp`.
 *
 * DIVERGENCE: HermiT declares `String curGroup=null;` and then assigns it
 * inside `if (o.group!=null)` WITHOUT ever comparing against the previous
 * value — so the group heading is re-emitted before every single option and
 * `--help` runs to ~150 lines. The dead variable makes the intent obvious; this
 * port prints a heading only when the group actually changes.
 *
 * @param {Option[]} [opts]
 * @returns {string}
 */
function formatOptionHelp(opts = options) {
  let fieldWidth = 0;
  for (const o of opts) {
    const curWidth = o.getLongOptExampleStr().length;
    if (curWidth > fieldWidth) fieldWidth = curWidth;
  }
  const parts = [];
  let curGroup = null;
  for (const o of opts) {
    if (o.group !== null && o.group !== curGroup) {
      curGroup = o.group;
      parts.push(`\n${curGroup}:\n`);
    }
    if (o.hasShortForm()) {
      parts.push(`  -${o.optCharString}`);
      parts.push(o.longStr !== null && o.longStr !== '' ? ', ' : '  ');
    } else {
      parts.push('      ');
    }
    let fieldLeft = fieldWidth + 1;
    if (o.longStr !== null && o.longStr !== '') {
      const s = o.getLongOptExampleStr();
      parts.push(s);
      fieldLeft -= s.length;
    }
    parts.push(' '.repeat(Math.max(0, fieldLeft)));
    parts.push(breakLines(o.help, 80, 6 + fieldWidth + 1));
    parts.push('\n');
  }
  return parts.join('');
}

/**
 * The short-option spec string in `getopt(3)` format: `h` for no argument,
 * `v::` for an optional one, `o:` for a required one.
 *
 * Port of `Option.formatOptionsString`.
 *
 * @param {Option[]} [opts]
 * @returns {string}
 */
function formatOptionsString(opts = options) {
  let out = '';
  for (const o of opts) {
    if (!o.hasShortForm()) continue;
    out += o.optCharString;
    if (o.arg === Arg.REQUIRED) out += ':';
    else if (o.arg === Arg.OPTIONAL) out += '::';
  }
  return out;
}

// ===========================================================================
// getopt
// ===========================================================================

/**
 * A parsed option occurrence.
 * @typedef {{code: number, option: Option, value: ?string}} GetoptResult
 */

/**
 * Minimal GNU-getopt replacement.
 *
 * Supports:
 *   - `--`            end of options
 *   - `--long`        long option, no value
 *   - `--long=v`      long option with a value (also for OPTIONAL args)
 *   - `--long v`      long option with a REQUIRED value in the next argument
 *   - `--lon`         unambiguous abbreviation of a long option
 *   - `-abc`          cluster of short options taking no value
 *   - `-oFILE`/`-o F` short option with a REQUIRED value
 *   - `-k`            short option with an OPTIONAL value: never consumes the
 *                     next argument (matching GNU getopt's `-o::` behaviour)
 *
 * Non-option arguments are collected into {@link Getopt#operands}.
 */
class Getopt {
  /**
   * @param {string[]} argv the arguments AFTER the program name
   * @param {Option[]} [opts]
   */
  constructor(argv, opts = options) {
    this.argv = argv;
    this.options = opts;
    /** Long name → Option. Duplicate long names keep the FIRST declaration,
     *  so `--prefix=PN=IRI` wins over `--prefix=IRI` (HermiT has the same
     *  collision and resolves it the same way through `gnu.getopt`). */
    this.byLong = new Map();
    /** Short character → Option. */
    this.byShort = new Map();
    for (const o of opts) {
      if (o.longStr && !this.byLong.has(o.longStr)) this.byLong.set(o.longStr, o);
      if (o.hasShortForm() && !this.byShort.has(o.optCharString)) {
        this.byShort.set(o.optCharString, o);
      }
    }
    /** @type {GetoptResult[]} */
    this.parsed = [];
    /** @type {string[]} positional arguments */
    this.operands = [];
    /** @type {?string} the offending token, for error messages */
    this.optopt = null;
    this._parse();
  }

  _fail(message) {
    const e = new Error(message);
    e.optopt = this.optopt;
    throw e;
  }

  _parse() {
    let i = 0;
    while (i < this.argv.length) {
      const token = this.argv[i];
      if (token === '--') {
        for (let j = i + 1; j < this.argv.length; j++) this.operands.push(this.argv[j]);
        return;
      }
      if (token.startsWith('--')) {
        i = this._parseLong(token, i);
        continue;
      }
      if (token.length > 1 && token[0] === '-') {
        i = this._parseShortCluster(token, i);
        continue;
      }
      this.operands.push(token);
      i++;
    }
  }

  /** @returns {number} the next index to process */
  _parseLong(token, i) {
    const eq = token.indexOf('=');
    const name = eq === -1 ? token.substring(2) : token.substring(2, eq);
    const inlineValue = eq === -1 ? null : token.substring(eq + 1);
    this.optopt = token;

    const option = this._resolveLong(name);
    if (option === null) this._fail(`invalid option -- ${token}`);

    if (option.arg === Arg.NONE) {
      if (inlineValue !== null) this._fail(`option --${name} doesn't allow an argument`);
      this.parsed.push({ code: option.optChar, option, value: null });
      return i + 1;
    }
    if (inlineValue !== null) {
      this.parsed.push({ code: option.optChar, option, value: inlineValue });
      return i + 1;
    }
    if (option.arg === Arg.OPTIONAL) {
      // GNU getopt never treats the next argument as an optional value.
      this.parsed.push({ code: option.optChar, option, value: null });
      return i + 1;
    }
    if (i + 1 >= this.argv.length) this._fail(`option --${name} requires an argument`);
    this.parsed.push({ code: option.optChar, option, value: this.argv[i + 1] });
    return i + 2;
  }

  /** Exact match first, then unique-prefix abbreviation. */
  _resolveLong(name) {
    const exact = this.byLong.get(name);
    if (exact !== undefined) return exact;
    let match = null;
    for (const [longStr, option] of this.byLong) {
      if (longStr.startsWith(name)) {
        if (match !== null) return null; // ambiguous
        match = option;
      }
    }
    return match;
  }

  /** @returns {number} the next index to process */
  _parseShortCluster(token, i) {
    let nextIndex = i + 1;
    let c = 1;
    while (c < token.length) {
      const ch = token[c];
      this.optopt = ch;
      const option = this.byShort.get(ch);
      if (option === undefined) this._fail(`invalid option -- ${ch}`);
      if (option.arg === Arg.NONE) {
        this.parsed.push({ code: option.optChar, option, value: null });
        c++;
        continue;
      }
      // The rest of this token is the value, if any.
      const attached = c + 1 < token.length ? token.substring(c + 1) : null;
      if (attached !== null) {
        this.parsed.push({ code: option.optChar, option, value: attached });
        return nextIndex;
      }
      if (option.arg === Arg.OPTIONAL) {
        this.parsed.push({ code: option.optChar, option, value: null });
        return nextIndex;
      }
      if (i + 1 >= this.argv.length) this._fail(`option requires an argument -- ${ch}`);
      this.parsed.push({ code: option.optChar, option, value: this.argv[i + 1] });
      nextIndex = i + 2;
      return nextIndex;
    }
    return nextIndex;
  }
}

module.exports = {
  Arg,
  Option,
  OptionCode,
  OptionGroup,
  options,
  Getopt,
  breakLines,
  formatOptionHelp,
  formatOptionsString
};
