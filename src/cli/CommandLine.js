'use strict';
/**
 * src/cli/CommandLine.js — the command-line front end.
 *
 * Port of `org.semanticweb.HermiT.cli.CommandLine`.
 *
 * Usage:
 *
 *     node src/cli/CommandLine.js [OPTION]... ONTOLOGY...
 *
 * The structure follows HermiT closely: a table of {@link Option}s (see
 * `./Options.js`), a set of {@link Action} objects collected while parsing, and
 * a loop that loads each ontology, builds a {@link Reasoner} and runs every
 * action against it.
 *
 * ## Entry points
 *
 *   - {@link main} — parse `argv`, do the work, return a process exit code.
 *     All I/O goes through an injectable `io` object so tests can capture it.
 *   - {@link run} — the same, but throws on a usage error instead of printing
 *     the diagnostic and returning 1.
 *
 * ## Documented divergences from HermiT
 *
 *   1. **`SupersAction` honours `--direct`.** HermiT calls
 *      `getSuperClasses(owlClass, false)` in BOTH branches, so `-d -S X` prints
 *      all supers under a "Direct super-classes" heading. That is a bug; this
 *      port passes `!all` and the heading matches what is printed.
 *   2. **Sub/super/equivalent listings are sorted by IRI.** HermiT iterates
 *      `HashSet`s, so its order is unspecified. Sorting makes the CLI output
 *      reproducible; the SET of lines is identical.
 *   3. **Only local ontologies.** HermiT dereferences `http:` IRIs through the
 *      OWL API. This port resolves `file:` IRIs and plain paths against `--base`
 *      (default: the current directory) and reports a clear error for any other
 *      scheme rather than attempting a network fetch.
 *   4. **`--dump-clauses` prints full IRIs inside clauses.** See
 *      `DLOntology.toString(prefixes)`.
 *   5. **protege-js is an optional peer dependency.** When it is not installed
 *      the CLI fails with an actionable message instead of a bare
 *      `MODULE_NOT_FOUND` stack.
 */

const fs = require('fs');
const path = require('path');
const { URL } = require('url');

const E = require('../owl/OWLExpressions');
const { Prefixes } = require('../Prefixes');
const {
  Configuration,
  DIRECT_BLOCKING_TYPE,
  BLOCKING_STRATEGY_TYPE,
  BLOCKING_SIGNATURE_CACHE_TYPE,
  EXISTENTIAL_STRATEGY_TYPE,
  INFERENCE_TYPE
} = require('../Configuration');
const { Reasoner, REASONER_NAME, REASONER_VERSION } = require('../reasoner/Reasoner');
const { EntailmentChecker } = require('../reasoner/EntailmentChecker');
const { logicalAxiomsOf } = require('../structural/OWLNormalization');
const { Timer } = require('../monitor/Timer');
const { StringWriter, StreamWriter, openWriter } = require('./Writer');
const {
  Arg, OptionCode, options, Getopt, formatOptionHelp
} = require('./Options');

// ===========================================================================
// Errors and status output
// ===========================================================================

/**
 * A command-line usage error. HermiT's `UsageException extends
 * IllegalArgumentException`; here it extends `Error` and is caught by
 * {@link main}, which prints the message plus a pointer to `--help`.
 */
class UsageException extends Error {
  constructor(message) {
    super(message);
    this.name = 'UsageException';
  }
}

/**
 * Normalise an injected sink into a {@link Writer}.
 *
 * Callers may pass a `Writer` (which has `print`/`println`) or a bare Node
 * stream (which has `write`). Both are accepted so that `StringWriter` works in
 * tests and `process.stdout` works in production.
 *
 * @param {{println?: function(string): void, write?: function(string): void}} sink
 * @returns {import('./Writer').Writer}
 */
function toWriter(sink) {
  if (sink === null || sink === undefined) return new StreamWriter(process.stdout);
  if (typeof sink.println === 'function') return sink;
  if (typeof sink.write === 'function') return new StreamWriter(sink);
  throw new TypeError('an injected output sink must expose print/println or write.');
}

/** Verbosity levels, mirroring `CommandLine.StatusOutput`. */
const StatusLevel = Object.freeze({
  ALWAYS: 0,
  STATUS: 1,
  DETAIL: 2,
  DEBUG: 3
});

/**
 * Progress messages, written to stderr so they never pollute piped output.
 *
 * A message is printed iff `messageLevel <= this.level`.
 */
class StatusOutput {
  /**
   * @param {number} level
   * @param {{println?: function(string): void, write?: function(string): void}} [err]
   */
  constructor(level, err = process.stderr) {
    this.level = level;
    this.err = toWriter(err);
  }

  /** @param {number} inLevel @param {string} message */
  log(inLevel, message) {
    if (inLevel <= this.level) this.err.println(message);
  }
}

// ===========================================================================
// Static help text
// ===========================================================================

const usageString = 'Usage: dl-js-reasoner [OPTION]... ONTOLOGY...';

const helpHeader = [
  'Perform reasoning on each OWL ontology.',
  'Example: dl-js-reasoner -dsowl:Thing pizza.owl',
  '    (prints direct subclasses of owl:Thing within the pizza ontology)',
  'Example: dl-js-reasoner --premise=premise.ofn --conclusion=conclusion.ofn --checkEntailment',
  '    (checks whether the conclusion ontology is entailed by the premise ontology)',
  '',
  'Both relative and absolute ontology references can be used. Relative paths',
  'are resolved with respect to the current directory; this behavior can be',
  "changed with the '--base' option. Only local files and 'file:' IRIs are",
  'supported — remote HTTP IRIs are not dereferenced.',
  '',
  'Classes and properties are identified using functional-syntax-style',
  'identifiers: names not containing a colon are resolved against the',
  "ontology's default prefix; otherwise the portion of the name preceding the",
  'colon is treated as a prefix name. Use of prefixes can be controlled using',
  'the -p, -N, and --prefix options. Alternatively, classes and properties can',
  'be identified with full IRIs by enclosing the IRI in <angle brackets>.',
  '',
  'By default, ontologies are simply retrieved and parsed. For more',
  'interesting reasoning, set one of the -c/-k/-s/-S/-e/-U options.'
];

const footer = [
  `${REASONER_NAME} is a JavaScript port of HermiT.`,
  'Visit <https://github.com/hermit-reasoner/HermiT> for the original.'
];

const versionString = `${REASONER_NAME} ${REASONER_VERSION}`;

// ===========================================================================
// Actions
// ===========================================================================

/**
 * The action contract.
 *
 * @typedef {{run: function(Reasoner, StatusOutput, import('./Writer').Writer, boolean): void}} Action
 */

/** `--print-prefixes`: list the prefix names usable in identifiers. */
class DumpPrefixesAction {
  run(reasoner, status, output, ignoreOntologyPrefixes) {
    output.println('Prefixes:');
    for (const [name, iri] of reasoner.getPrefixes().getPrefixIRIsByPrefixName()) {
      output.println(`\t${name}\t${iri}`);
    }
    output.flush();
  }
}

/** `--dump-clauses[=FILE]`: print the clausified ontology. */
class DumpClausesAction {
  /**
   * @param {?string} fileName `null` → the shared `-o` output writer;
   *        `'-'` → stdout; anything else → that file.
   * @param {import('./Writer').Writer} [stdout]
   */
  constructor(fileName, stdout) {
    this.file = fileName === undefined ? null : fileName;
    this.stdout = stdout === undefined ? null : stdout;
  }

  run(reasoner, status, output, ignoreOntologyPrefixes) {
    let sink = output;
    let owned = false;
    if (this.file !== null) {
      if (this.file === '-') {
        sink = this.stdout || output;
      } else {
        try {
          sink = openWriter(this.file);
        } catch (e) {
          throw new UsageException(e && e.message ? e.message : `unable to open ${this.file}`);
        }
        owned = true;
      }
    }
    try {
      sink.println(reasoner.getDLOntology().toString(
        ignoreOntologyPrefixes ? new Prefixes() : reasoner.getPrefixes()));
      sink.flush();
    } finally {
      if (owned) sink.close();
    }
  }
}

/** `-c` / `-O` / `-D` (with `-P` for the pretty form). */
class ClassifyAction {
  /**
   * @param {boolean} classifyClasses
   * @param {boolean} classifyOPs
   * @param {boolean} classifyDPs
   * @param {boolean} prettyPrint
   * @param {?string} outputLocation only used for the status message
   */
  constructor(classifyClasses, classifyOPs, classifyDPs, prettyPrint, outputLocation) {
    this.classifyClasses = classifyClasses;
    this.classifyOPs = classifyOPs;
    this.classifyDPs = classifyDPs;
    this.prettyPrint = prettyPrint;
    this.outputLocation = outputLocation === undefined ? null : outputLocation;
  }

  run(reasoner, status, output, ignoreOntologyPrefixes) {
    const inferences = [];
    if (this.classifyClasses) inferences.push(INFERENCE_TYPE.CLASS_HIERARCHY);
    if (this.classifyOPs) inferences.push(INFERENCE_TYPE.OBJECT_PROPERTY_HIERARCHY);
    if (this.classifyDPs) inferences.push(INFERENCE_TYPE.DATA_PROPERTY_HIERARCHY);
    status.log(StatusLevel.DETAIL, 'Classifying...');
    reasoner.precomputeInferences(...inferences);
    if (output !== null && output !== undefined) {
      status.log(StatusLevel.DETAIL, this.outputLocation !== null
        ? `Writing results to ${this.outputLocation}`
        : 'Writing results...');
      if (this.prettyPrint) {
        reasoner.printHierarchies(output, this.classifyClasses, this.classifyOPs, this.classifyDPs);
      } else {
        reasoner.dumpHierarchies(output, this.classifyClasses, this.classifyOPs, this.classifyDPs);
      }
      output.flush();
    }
  }
}

/**
 * Shared by the four class-query actions: turn a command-line identifier into
 * an `OWLClass`, warning when it is not declared.
 *
 * @param {Reasoner} reasoner
 * @param {string} conceptName as given on the command line
 * @param {StatusOutput} status
 * @returns {{owlClass: object, conceptUri: string}}
 */
function resolveClass(reasoner, conceptName, status) {
  const prefixes = reasoner.getPrefixes();
  let conceptUri = prefixes.canBeExpanded(conceptName)
    ? prefixes.expandAbbreviatedIRI(conceptName)
    : conceptName;
  if (conceptUri.startsWith('<') && conceptUri.endsWith('>')) {
    conceptUri = conceptUri.substring(1, conceptUri.length - 1);
  }
  const owlClass = E.owlClass(conceptUri);
  if (!reasoner.isDefined(owlClass)) {
    status.log(StatusLevel.ALWAYS,
      `Warning: class '${conceptUri}' was not declared in the ontology.`);
  }
  return { owlClass, conceptUri };
}

/**
 * Render one entity IRI the way HermiT's query actions do.
 *
 * @param {Prefixes} prefixes
 * @param {string} iri
 * @param {boolean} ignoreOntologyPrefixes
 * @returns {string}
 */
function renderEntityIRI(prefixes, iri, ignoreOntologyPrefixes) {
  if (ignoreOntologyPrefixes) {
    return prefixes.canBeExpanded(iri) ? prefixes.expandAbbreviatedIRI(iri) : iri;
  }
  return prefixes.abbreviateIRI(iri);
}

/**
 * Collect every entity IRI in a `NodeSet`, sorted.
 *
 * DIVERGENCE: HermiT iterates a `HashSet` and so prints in an unspecified
 * order. Sorting makes the CLI output reproducible.
 *
 * @param {import('../reasoner/Node').NodeSet} nodeSet
 * @returns {string[]}
 */
function sortedIRIsOfNodeSet(nodeSet) {
  const iris = [];
  for (const node of nodeSet) {
    for (const entity of node) iris.push(E.iriString(entity));
  }
  return iris.sort();
}

/** `-k[=CLASS]`: is CLASS satisfiable? */
class SatisfiabilityAction {
  /** @param {string} conceptName */
  constructor(conceptName) {
    this.conceptName = conceptName;
  }

  run(reasoner, status, output, ignoreOntologyPrefixes) {
    status.log(StatusLevel.DETAIL, `Checking satisfiability of '${this.conceptName}'`);
    const { owlClass, conceptUri } = resolveClass(reasoner, this.conceptName, status);
    const result = reasoner.isSatisfiable(owlClass);
    output.println(`${this.conceptName}${result ? ' is satisfiable.' : ' is not satisfiable.'}`);
    output.flush();
  }
}

/** `-S CLASS`: classes subsuming CLASS. */
class SupersAction {
  /**
   * @param {string} conceptName
   * @param {boolean} getAll true → all supers, false → direct supers only
   */
  constructor(conceptName, getAll) {
    this.conceptName = conceptName;
    this.all = getAll;
  }

  run(reasoner, status, output, ignoreOntologyPrefixes) {
    status.log(StatusLevel.DETAIL, `Finding supers of '${this.conceptName}'`);
    const prefixes = reasoner.getPrefixes();
    const { owlClass } = resolveClass(reasoner, this.conceptName, status);
    // DIVERGENCE: HermiT passes `false` in both branches, so `--direct` is
    // silently ignored for supers. This port honours it.
    const classes = reasoner.getSuperClasses(owlClass, !this.all);
    output.println(this.all
      ? `All super-classes of '${this.conceptName}':`
      : `Direct super-classes of '${this.conceptName}':`);
    for (const iri of sortedIRIsOfNodeSet(classes)) {
      output.println(`\t${renderEntityIRI(prefixes, iri, ignoreOntologyPrefixes)}`);
    }
    output.flush();
  }
}

/** `-s CLASS`: classes subsumed by CLASS. */
class SubsAction {
  /**
   * @param {string} conceptName
   * @param {boolean} getAll
   */
  constructor(conceptName, getAll) {
    this.conceptName = conceptName;
    this.all = getAll;
  }

  run(reasoner, status, output, ignoreOntologyPrefixes) {
    status.log(StatusLevel.DETAIL, `Finding subs of '${this.conceptName}'`);
    const prefixes = reasoner.getPrefixes();
    const { owlClass } = resolveClass(reasoner, this.conceptName, status);
    const classes = reasoner.getSubClasses(owlClass, !this.all);
    output.println(this.all
      ? `All sub-classes of '${this.conceptName}':`
      : `Direct sub-classes of '${this.conceptName}':`);
    for (const iri of sortedIRIsOfNodeSet(classes)) {
      output.println(`\t${renderEntityIRI(prefixes, iri, ignoreOntologyPrefixes)}`);
    }
    output.flush();
  }
}

/** `-e CLASS` (and `-U`, which is `-e owl:Nothing`): classes ≡ CLASS. */
class EquivalentsAction {
  /** @param {string} conceptName */
  constructor(conceptName) {
    this.conceptName = conceptName;
  }

  run(reasoner, status, output, ignoreOntologyPrefixes) {
    status.log(StatusLevel.DETAIL, `Finding equivalents of '${this.conceptName}'`);
    const prefixes = reasoner.getPrefixes();
    const { owlClass } = resolveClass(reasoner, this.conceptName, status);
    const classes = reasoner.getEquivalentClasses(owlClass);
    output.println(ignoreOntologyPrefixes
      ? `Classes equivalent to '${this.conceptName}':`
      : `Classes equivalent to '${prefixes.abbreviateIRI(this.conceptName)}':`);
    const iris = [];
    for (const entity of classes) iris.push(E.iriString(entity));
    for (const iri of iris.sort()) {
      output.println(`\t${renderEntityIRI(prefixes, iri, ignoreOntologyPrefixes)}`);
    }
    output.flush();
  }
}

/** `-E` with `--conclusion=IRI`: does the loaded ontology entail the conclusion? */
class EntailsAction {
  /**
   * @param {Configuration} config
   * @param {string} conclusionIRI
   * @param {{loadOntology: function(string): object}} loader
   */
  constructor(config, conclusionIRI, loader) {
    this.config = config;
    this.conclusionIRI = conclusionIRI;
    this.loader = loader;
  }

  run(reasoner, status, output, ignoreOntologyPrefixes) {
    status.log(StatusLevel.DETAIL,
      'Checking whether the loaded ontology entails the conclusion ontology');
    const conclusions = this.loader(this.conclusionIRI);
    status.log(StatusLevel.DETAIL, 'Conclusion ontology loaded.');
    const checker = new EntailmentChecker(reasoner, E);
    const isEntailed = checker.entails(logicalAxiomsOf(conclusions));
    status.log(StatusLevel.DETAIL,
      `Conclusion ontology is ${isEntailed ? '' : 'not '}entailed.`);
    output.println(String(isEntailed));
    output.flush();
  }
}

// ===========================================================================
// Ontology loading
// ===========================================================================

/**
 * Require protege-js, or fail with an actionable message.
 *
 * protege-js is an OPTIONAL peer dependency of this package, so a bare
 * `MODULE_NOT_FOUND` stack would be unhelpful.
 *
 * @param {function(string): *} [requireFn] injectable for tests
 */
function loadProtegeModule(requireFn = require) {
  try {
    return requireFn('@skaterqiang/protege-js');
  } catch (e) {
    throw new UsageException(
      'the @skaterqiang/protege-js package is required to load ontologies but could not be '
      + `resolved (${e && e.message ? e.message.split('\n')[0] : e}). Install it with `
      + "'npm install @skaterqiang/protege-js', or import an ontology yourself and use the "
      + 'Reasoner API directly.');
  }
}

/**
 * Turn a command-line ontology reference into a local file path.
 *
 * Handles plain paths (absolute or relative to `baseDir`), `file:` IRIs, and
 * percent-encoded `file:` IRIs. Any other absolute URI is rejected: this port
 * does not dereference remote ontologies.
 *
 * @param {string} reference
 * @param {string} baseDir
 * @returns {string} an absolute path
 */
function resolveOntologyPath(reference, baseDir) {
  if (reference === null || reference === undefined || reference === '') {
    throw new UsageException('an empty ontology reference was given');
  }
  // Windows drive letters (`d:\...`) and POSIX absolute paths.
  if (path.isAbsolute(reference)) return path.resolve(reference);

  const schemeMatch = /^([A-Za-z][A-Za-z0-9+.-]*):/.exec(reference);
  if (schemeMatch !== null && schemeMatch[1].length > 1) {
    const scheme = schemeMatch[1].toLowerCase();
    if (scheme === 'file') {
      let parsed;
      try {
        parsed = new URL(reference);
      } catch {
        throw new UsageException(`'${reference}' is not a valid file IRI`);
      }
      let filePath;
      try {
        filePath = decodeURIComponent(parsed.pathname);
      } catch {
        filePath = parsed.pathname;
      }
      // `file:///d:/x` → `/d:/x` on Windows; drop the leading separator.
      if (process.platform === 'win32' && /^\/[A-Za-z]:/.test(filePath)) {
        filePath = filePath.substring(1);
      }
      return path.resolve(filePath);
    }
    throw new UsageException(
      `cannot load '${reference}': only local files and 'file:' IRIs are supported `
      + `(got scheme '${schemeMatch[1]}:')`);
  }
  return path.resolve(baseDir, reference);
}

/**
 * Build the ontology loader closure used by `main` and by `EntailsAction`.
 *
 * @param {{requireProtege?: function(string): *, followImports?: boolean, baseDir?: string}} env
 * @returns {function(string): object} reference → parsed ontology
 */
function createOntologyLoader(env = {}) {
  const protege = env.requireProtege
    ? env.requireProtege('@skaterqiang/protege-js')
    : loadProtegeModule();
  const loader = new protege.OntologyLoader();
  const followImports = env.followImports !== false;
  const baseDir = env.baseDir || process.cwd();
  return (reference) => {
    const resolved = resolveOntologyPath(reference, baseDir);
    if (!fs.existsSync(resolved)) {
      throw new UsageException(`unable to load '${reference}': no such file (${resolved})`);
    }
    try {
      return followImports
        ? loader.loadWithImports(resolved)
        : loader.loadFromFile(resolved);
    } catch (e) {
      if (e instanceof UsageException) throw e;
      throw new UsageException(
        `unable to parse '${resolved}': ${e && e.message ? e.message.split('\n')[0] : e}`);
    }
  };
}

// ===========================================================================
// Argument parsing
// ===========================================================================

/**
 * Everything {@link run} needs, produced by {@link parseArguments}.
 *
 * @typedef {{
 *   verbosity: number,
 *   ignoreOntologyPrefixes: boolean,
 *   outputLocation: ?string,
 *   defaultPrefix: ?string,
 *   prefixMappings: Map<string,string>,
 *   baseDir: string,
 *   configuration: Configuration,
 *   actions: Action[],
 *   ontologies: string[],
 *   conclusionIRI: ?string,
 *   exitEarly: ?number
 * }} CliPlan
 */

/**
 * Parse `argv` into a {@link CliPlan}.
 *
 * @param {string[]} argv arguments AFTER the program name
 * @param {{stdout?: {write: function(string): void}}} [io]
 * @returns {CliPlan}
 * @throws {UsageException}
 */
function parseArguments(argv, io = {}) {
  const stdout = toWriter(io.stdout || process.stdout);

  const plan = {
    verbosity: 1,
    ignoreOntologyPrefixes: false,
    outputLocation: null,
    defaultPrefix: null,
    prefixMappings: new Map(),
    baseDir: process.cwd(),
    configuration: new Configuration(),
    actions: [],
    ontologies: [],
    conclusionIRI: null,
    exitEarly: null
  };

  let classifyClasses = false;
  let classifyOPs = false;
  let classifyDPs = false;
  let prettyPrint = false;
  let doAll = true;

  let g;
  try {
    g = new Getopt(argv, options);
  } catch (e) {
    throw new UsageException(e.message);
  }

  for (const { code, option, value } of g.parsed) {
    switch (code) {
      // ---- meta ----
      case 'h'.codePointAt(0):
        printHelp(stdout);
        plan.exitEarly = 0;
        break;
      case 'V'.codePointAt(0): {
        stdout.println(versionString);
        for (const s of footer) stdout.println(s);
        plan.exitEarly = 0;
        break;
      }
      case 'v'.codePointAt(0): {
        if (value === null) plan.verbosity += 1;
        else plan.verbosity += parseVerbosityAmount(value, '--verbose');
        break;
      }
      case 'q'.codePointAt(0): {
        if (value === null) plan.verbosity -= 1;
        else plan.verbosity -= parseVerbosityAmount(value, '--quiet');
        break;
      }
      case 'o'.codePointAt(0): {
        if (value === null) throw new UsageException('--output requires an argument');
        if (value === '-') {
          plan.outputLocation = null;
        } else {
          plan.outputLocation = path.resolve(value);
        }
        break;
      }
      case OptionCode.kPremise: {
        if (value === null) throw new UsageException('--premise requires an IRI as argument');
        plan.ontologies.push(value);
        break;
      }
      case OptionCode.kConclusion: {
        if (value === null) throw new UsageException('--conclusion requires an IRI as argument');
        plan.conclusionIRI = value;
        break;
      }

      // ---- actions ----
      case 'l'.codePointAt(0):
        // `--load` is a no-op: loading happens regardless of what is asked.
        break;
      case 'c'.codePointAt(0): classifyClasses = true; break;
      case 'O'.codePointAt(0): classifyOPs = true; break;
      case 'D'.codePointAt(0): classifyDPs = true; break;
      case 'P'.codePointAt(0): prettyPrint = true; break;
      case 'k'.codePointAt(0): {
        plan.actions.push(new SatisfiabilityAction(
          value === null ? E.IRI_THING : value));
        break;
      }
      case 'd'.codePointAt(0): doAll = false; break;
      case 's'.codePointAt(0): {
        if (value === null) throw new UsageException('--subs requires an argument');
        plan.actions.push(new SubsAction(value, doAll));
        doAll = true;
        break;
      }
      case 'S'.codePointAt(0): {
        if (value === null) throw new UsageException('--supers requires an argument');
        plan.actions.push(new SupersAction(value, doAll));
        doAll = true;
        break;
      }
      case 'e'.codePointAt(0): {
        if (value === null) throw new UsageException('--equivalents requires an argument');
        plan.actions.push(new EquivalentsAction(value));
        break;
      }
      case 'U'.codePointAt(0):
        plan.actions.push(new EquivalentsAction(E.IRI_NOTHING));
        break;
      case 'E'.codePointAt(0):
        // HermiT only registers the action when a conclusion was given; the
        // check happens here because `--conclusion` may follow `-E`.
        break;
      case OptionCode.kDumpPrefixes:
        plan.actions.push(new DumpPrefixesAction());
        break;

      // ---- prefixes ----
      case 'N'.codePointAt(0): plan.ignoreOntologyPrefixes = true; break;
      case 'p'.codePointAt(0): {
        if (value === null) throw new UsageException('--prefix requires an argument');
        const eqIndex = value.indexOf('=');
        if (eqIndex === -1) {
          throw new UsageException(
            `the prefix declaration '${value}' is not of the form PN=IRI.`);
        }
        plan.prefixMappings.set(value.substring(0, eqIndex), value.substring(eqIndex + 1));
        break;
      }
      case OptionCode.kDefaultPrefix: {
        if (value === null) throw new UsageException('--prefix requires an argument');
        plan.defaultPrefix = value;
        break;
      }

      // ---- parsing ----
      case OptionCode.kBase: {
        if (value === null) throw new UsageException('--base requires an argument');
        plan.baseDir = resolveBaseDir(value);
        break;
      }

      // ---- algorithm ----
      case OptionCode.kDirectBlock:
        plan.configuration.directBlockingType = parseEnum(
          value, DIRECT_BLOCKING_TYPE,
          { pairwise: 'PAIR_WISE', single: 'SINGLE', optimal: 'OPTIMAL' },
          'direct blocking type', "'pairwise', 'single', and 'optimal'");
        break;
      case OptionCode.kBlockStrategy:
        plan.configuration.blockingStrategyType = parseEnum(
          value, BLOCKING_STRATEGY_TYPE,
          { anywhere: 'ANYWHERE', ancestor: 'ANCESTOR', core: 'SIMPLE_CORE', optimal: 'OPTIMAL' },
          'blocking strategy type', "'ancestor', 'anywhere', 'core', and 'optimal'");
        break;
      case OptionCode.kBlockCache:
        plan.configuration.blockingSignatureCacheType = BLOCKING_SIGNATURE_CACHE_TYPE.CACHED;
        break;
      case OptionCode.kIgnoreUnsupportedDatatypes:
        plan.configuration.ignoreUnsupportedDatatypes = true;
        break;
      case OptionCode.kExpansion:
        plan.configuration.existentialStrategyType = parseEnum(
          value, EXISTENTIAL_STRATEGY_TYPE,
          { creation: 'CREATION_ORDER', el: 'EL', reuse: 'INDIVIDUAL_REUSE' },
          'existential strategy type', "'creation', 'el', and 'reuse'");
        break;
      case OptionCode.kNoInconsistentException:
        plan.configuration.throwInconsistentOntologyException = false;
        break;

      // ---- internals ----
      case OptionCode.kDumpClauses:
        plan.actions.push(new DumpClausesAction(value, stdout));
        break;

      default:
        throw new UsageException(`invalid option -- ${option.longStr || String(code)}`);
    }
  }

  // `-E` is resolved after the whole command line is known, so that
  // `--conclusion` may appear after it (HermiT requires it before).
  if (hasOption(g, 'E')) {
    if (plan.conclusionIRI === null) {
      throw new UsageException('--checkEntailment requires a --conclusion=IRI');
    }
    plan.actions.push(new EntailsAction(plan.configuration, plan.conclusionIRI, null));
  }

  for (const operand of g.operands) plan.ontologies.push(operand);

  if (classifyClasses || classifyOPs || classifyDPs) {
    plan.actions.push(new ClassifyAction(
      classifyClasses, classifyOPs, classifyDPs, prettyPrint, plan.outputLocation));
  }

  return plan;
}

/** True iff the short option `ch` was given. */
function hasOption(getopt, ch) {
  const code = ch.codePointAt(0);
  return getopt.parsed.some((p) => p.code === code);
}

/** Parse a `--verbose=N` / `--quiet=N` amount. */
function parseVerbosityAmount(value, optionName) {
  if (!/^[+-]?\d+$/.test(value.trim())) {
    throw new UsageException(`argument to ${optionName} must be a number`);
  }
  return parseInt(value.trim(), 10);
}

/**
 * Map a command-line keyword onto a frozen-enum value.
 *
 * @param {?string} value
 * @param {object} enumObject e.g. `DIRECT_BLOCKING_TYPE`
 * @param {Object<string,string>} keywords lower-case keyword → enum key
 * @param {string} what e.g. `'direct blocking type'`
 * @param {string} supported e.g. `"'pairwise', 'single', and 'optimal'"`
 */
function parseEnum(value, enumObject, keywords, what, supported) {
  const key = value === null ? null : keywords[String(value).toLowerCase()];
  if (key === undefined || key === null) {
    throw new UsageException(`unknown ${what} '${value}'; supported values are ${supported}`);
  }
  return enumObject[key];
}

/**
 * Resolve a `--base` argument to a directory.
 *
 * Accepts a plain directory path or a `file:` IRI. HermiT takes a `URI`; this
 * port only needs the directory that relative ontology references resolve
 * against.
 */
function resolveBaseDir(value) {
  if (/^file:/i.test(value)) {
    // Reuse the ontology resolver: it understands `file:` IRIs. Point it at a
    // dummy child and take the parent directory back off.
    return path.dirname(resolveOntologyPath(`${value.replace(/\/$/, '')}/__base__`, process.cwd()));
  }
  if (/^[A-Za-z][A-Za-z0-9+.-]*:/.test(value) && !/^[A-Za-z]:[\\/]/.test(value)) {
    throw new UsageException(`'${value}' is not a valid base URI.`);
  }
  return path.resolve(value);
}

// ===========================================================================
// Execution
// ===========================================================================

/**
 * Run a parsed plan.
 *
 * @param {CliPlan} plan
 * @param {{
 *   stdout?: {write: function(string): void},
 *   stderr?: {write: function(string): void},
 *   requireProtege?: function(string): *,
 *   followImports?: boolean
 * }} [io]
 * @returns {number} a process exit code
 * @throws {UsageException}
 */
function run(plan, io = {}) {
  if (plan.exitEarly !== null && plan.exitEarly !== undefined) return plan.exitEarly;

  const stderr = toWriter(io.stderr || process.stderr);
  const stdout = toWriter(io.stdout || process.stdout);
  const status = new StatusOutput(plan.verbosity, stderr);

  if (plan.verbosity > 3) {
    // `Timer` writes through `write`/`writeLine` callbacks; bind them to the
    // (possibly injected) stderr sink rather than to `process.stderr`.
    plan.configuration.monitor = new Timer({
      write: (text) => stderr.print(text),
      writeLine: (text) => stderr.println(text)
    });
  }

  // Route `Configuration.warningMonitor` messages to stderr at ALWAYS level.
  // Several options degrade rather than fail — `--blockersCache` (CACHED is not
  // implemented) and `--block-strategy=core` (core blocking is not implemented)
  // both fall back to an exact-but-different strategy. `BlockingStrategy.js`
  // documents that the caller "is never silently given something other than
  // what they asked for"; wiring the monitor here is what makes that true.
  if (typeof plan.configuration.warningMonitor !== 'function') {
    plan.configuration.warningMonitor = (message) => {
      status.log(StatusLevel.ALWAYS, `Warning: ${message}`);
    };
  }

  if (plan.ontologies.length === 0) {
    throw new UsageException('No ontologies given.');
  }

  const loader = createOntologyLoader({
    requireProtege: io.requireProtege,
    followImports: io.followImports,
    baseDir: plan.baseDir
  });

  // `EntailsAction` was constructed before the loader existed; wire it now.
  for (const action of plan.actions) {
    if (action instanceof EntailsAction && action.loader === null) action.loader = loader;
  }

  // `outputLocation === null` means stdout, which is already normalised into a
  // Writer above; anything else is a file path. HermiT opens the results file
  // while parsing `-o`; this port defers to here so the injected stdout sink is
  // available, but an unwritable path still yields a clean usage diagnostic.
  let output;
  let ownsOutput = false;
  if (plan.outputLocation === null) {
    output = stdout;
  } else {
    try {
      output = openWriter(plan.outputLocation);
      ownsOutput = true;
    } catch (e) {
      throw new UsageException(e && e.message ? e.message : `unable to open ${plan.outputLocation}`);
    }
  }
  try {
    for (const reference of plan.ontologies) {
      status.log(StatusLevel.DETAIL, `Processing ${reference}`);
      status.log(StatusLevel.DETAIL, `${plan.actions.length} actions`);
      try {
        let startTime = Date.now();
        const ontology = loader(reference);
        status.log(StatusLevel.DETAIL, `Ontology parsed in ${Date.now() - startTime} msec.`);

        startTime = Date.now();
        const reasoner = new Reasoner(ontology, plan.configuration.clone());
        applyPrefixOptions(reasoner.getPrefixes(), plan, status);
        status.log(StatusLevel.DETAIL, `Reasoner created in ${Date.now() - startTime} msec.`);

        for (const action of plan.actions) {
          status.log(StatusLevel.DETAIL, 'Doing action...');
          startTime = Date.now();
          action.run(reasoner, status, output, plan.ignoreOntologyPrefixes);
          status.log(StatusLevel.DETAIL,
            `...action completed in ${Date.now() - startTime} msec.`);
        }
      } catch (e) {
        if (e instanceof UsageException) throw e;
        stderr.println(`It all went pear-shaped: ${e && e.message ? e.message : e}`);
        if (plan.verbosity >= StatusLevel.DEBUG && e && e.stack) stderr.println(e.stack);
        return 1;
      }
    }
  } finally {
    output.flush();
    if (ownsOutput) output.close();
  }
  return 0;
}

/**
 * Apply `--prefix=IRI` and `-p PN=IRI` to the reasoner's prefix map.
 *
 * As in HermiT, a conflicting declaration is downgraded to a DETAIL-level
 * message rather than an error.
 */
function applyPrefixOptions(prefixes, plan, status) {
  if (plan.defaultPrefix !== null) {
    try {
      prefixes.declareDefaultPrefix(plan.defaultPrefix);
    } catch (e) {
      status.log(StatusLevel.DETAIL,
        `Default prefix ${plan.defaultPrefix} could not be registered because there is `
        + 'already a registered default prefix. ');
    }
  }
  for (const [name, iri] of plan.prefixMappings) {
    const prefixName = name.endsWith(':') ? name : `${name}:`;
    try {
      prefixes.declarePrefix(prefixName, iri);
    } catch (e) {
      status.log(StatusLevel.DETAIL,
        `Prefixname ${prefixName} could not be set to ${iri} because there is already a `
        + 'registered prefix name for the IRI. ');
    }
  }
}

/**
 * Parse `argv` and run, printing a usage diagnostic on a {@link UsageException}.
 *
 * @param {string[]} argv arguments AFTER the program name
 * @param {object} [io] see {@link run}
 * @returns {number} a process exit code
 */
function main(argv, io = {}) {
  const stderr = toWriter(io.stderr || process.stderr);
  try {
    return run(parseArguments(argv, io), io);
  } catch (e) {
    if (e instanceof UsageException) {
      stderr.println(e.message);
      stderr.println(usageString);
      stderr.println(`Try '${programName(io)} --help' for more information.`);
      return 1;
    }
    throw e;
  }
}

/** The program name used in the "try --help" hint. */
function programName(io) {
  return io.programName || 'dl-js-reasoner';
}

/**
 * Print the full help text to a writer. Exposed so `bin/` and tests can reuse
 * the exact same text `--help` prints.
 *
 * @param {{println?: function(string): void, write?: function(string): void}} [stdout]
 */
function printHelp(stdout = process.stdout) {
  const out = toWriter(stdout);
  out.println(usageString);
  for (const s of helpHeader) out.println(s);
  out.print(formatOptionHelp(options));
  for (const s of footer) out.println(s);
}

module.exports = {
  UsageException,
  StatusOutput,
  StatusLevel,
  toWriter,
  // actions
  DumpPrefixesAction,
  DumpClausesAction,
  ClassifyAction,
  SatisfiabilityAction,
  SupersAction,
  SubsAction,
  EquivalentsAction,
  EntailsAction,
  // helpers
  resolveClass,
  renderEntityIRI,
  sortedIRIsOfNodeSet,
  resolveOntologyPath,
  createOntologyLoader,
  loadProtegeModule,
  parseArguments,
  applyPrefixOptions,
  // entry points
  run,
  main,
  printHelp,
  // text
  usageString,
  helpHeader,
  footer,
  versionString,
  // re-exported for the bin wrapper
  Arg,
  StringWriter
};
