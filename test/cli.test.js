'use strict';

// ---------------------------------------------------------------------------
// test/cli.test.js — the command-line front end, at unit level.
//
// `scripts/smoke-cli.js` drives `main(argv, io)` end to end against the real
// sample ontologies; this suite covers the pieces that do not need an ontology
// at all, so that a getopt or option-table regression is reported precisely
// rather than as one of 333 smoke checks:
//
//   - `Getopt`: clustering, abbreviations, `--`, REQUIRED vs OPTIONAL arguments,
//     and the duplicate-long-name shadowing that HermiT shares.
//   - The option table: codes, groups, help rendering, the getopt spec string.
//   - `parseArguments`: the plan it builds, without loading anything.
//   - `resolveOntologyPath`: paths, file: IRIs, drive letters, remote schemes.
//   - `toWriter` / `StatusOutput`: sink normalisation and level filtering.
//   - `DLOntology.toString(prefixes)`: the HermiT dump overload.
//
// Every expected string here was read off actual output.
// ---------------------------------------------------------------------------

const test = require('node:test');
const assert = require('node:assert/strict');
const path = require('path');

const {
  Getopt, options, formatOptionsString, formatOptionHelp, breakLines,
  Arg, Option, OptionCode, OptionGroup
} = require('../src/cli/Options');
const {
  UsageException, StatusOutput, StatusLevel, toWriter, parseArguments,
  resolveOntologyPath, usageString, versionString, footer,
  SubsAction, SupersAction, ClassifyAction, SatisfiabilityAction,
  EquivalentsAction, EntailsAction, DumpClausesAction, DumpPrefixesAction
} = require('../src/cli/CommandLine');
const { StringWriter } = require('../src/cli/Writer');
const { Prefixes } = require('../src/Prefixes');
const {
  DIRECT_BLOCKING_TYPE, BLOCKING_STRATEGY_TYPE, BLOCKING_SIGNATURE_CACHE_TYPE,
  EXISTENTIAL_STRATEGY_TYPE
} = require('../src/Configuration');
const helpers = require('./helpers');

const DIR = path.resolve(__dirname, '../../protege-js/sample/ontologies');
const OGMS = path.join(DIR, 'ogms.owl');
const OBO = 'http://purl.obolibrary.org/obo/';
const OWL = 'http://www.w3.org/2002/07/owl#';

/** The option whose short form is `ch`. */
const byShort = (ch) => options.find((o) => o.optCharString === ch);
/** The option whose long form is `name` (first declaration wins). */
const byLong = (name) => options.find((o) => o.longStr === name);

// ===========================================================================
test('Getopt: short options', () => {
  const g = new Getopt(['-c', '-k', 'a.owl']);
  assert.deepEqual(g.parsed.map((p) => p.option.optCharString), ['c', 'k']);
  assert.deepEqual(g.operands, ['a.owl']);
  // `-k` takes an OPTIONAL argument, so GNU getopt never consumes the next one.
  assert.equal(g.parsed[1].value, null);
});

test('Getopt: a cluster of no-argument short options', () => {
  const g = new Getopt(['-cOPD']);
  assert.deepEqual(g.parsed.map((p) => p.option.optCharString), ['c', 'O', 'P', 'D']);
  assert.deepEqual(g.operands, []);
});

test('Getopt: a cluster ending in a REQUIRED-argument option takes the rest', () => {
  const g = new Getopt(['-dsowl:Thing']);
  assert.equal(g.parsed.length, 2);
  assert.equal(g.parsed[0].option.optCharString, 'd');
  assert.equal(g.parsed[1].option.optCharString, 's');
  assert.equal(g.parsed[1].value, 'owl:Thing');
});

test('Getopt: a REQUIRED-argument option also accepts a separate value', () => {
  const g = new Getopt(['-s', 'owl:Thing', 'a.owl']);
  assert.equal(g.parsed[0].value, 'owl:Thing');
  assert.deepEqual(g.operands, ['a.owl']);
});

test('Getopt: an OPTIONAL-argument option takes only an attached value', () => {
  assert.equal(new Getopt([`-k${OBO}X`]).parsed[0].value, `${OBO}X`);
  const detached = new Getopt(['-k', 'a.owl']);
  assert.equal(detached.parsed[0].value, null);
  assert.deepEqual(detached.operands, ['a.owl']);
});

test('Getopt: -vvv attaches "vv" as the optional argument', () => {
  const g = new Getopt(['-vvv']);
  assert.equal(g.parsed.length, 1);
  assert.equal(g.parsed[0].option.optCharString, 'v');
  assert.equal(g.parsed[0].value, 'vv');
});

test('Getopt: -- stops option parsing', () => {
  const g = new Getopt(['-k', '--', '-weird.owl', '-c']);
  assert.equal(g.parsed.length, 1);
  assert.deepEqual(g.operands, ['-weird.owl', '-c']);
});

test('Getopt: long options in both = and separate forms', () => {
  assert.equal(new Getopt(['--base=/x']).parsed[0].value, '/x');
  assert.equal(new Getopt(['--base', '/x']).parsed[0].value, '/x');
  assert.equal(new Getopt(['--classify']).parsed[0].value, null);
});

test('Getopt: unambiguous long abbreviations resolve', () => {
  // `--base` and `--premise`/`--conclusion` take REQUIRED arguments, so they are
  // probed with a value attached; the rest take none or an optional one.
  for (const [argv, longStr] of [[['--unsat'], 'unsatisfiable'], [['--load'], 'load'],
    [['--direct'], 'direct'], [['--base=/x'], 'base'], [['--print'], 'print-prefixes'],
    [['--dump'], 'dump-clauses'], [['--concl=c.owl'], 'conclusion'],
    [['--pretty'], 'prettyPrint'], [['--ignoreU'], 'ignoreUnsupportedDatatypes']]) {
    assert.equal(new Getopt(argv).parsed[0].option.longStr, longStr,
      `${argv[0]} should resolve to --${longStr}`);
  }
});

test('Getopt: an ambiguous abbreviation fails rather than guessing', () => {
  // `--clas` is a prefix of --classify, --classifyOPs and --classifyDPs.
  assert.throws(() => new Getopt(['--clas']), (e) => {
    assert.match(e.message, /^invalid option -- --clas$/);
    assert.equal(e.optopt, '--clas');
    return true;
  });
  assert.throws(() => new Getopt(['--class']), /invalid option -- --class/);
});

test('Getopt: an exact long name beats abbreviation matching', () => {
  assert.equal(new Getopt(['--classify']).parsed[0].option.longStr, 'classify');
});

test('Getopt: unknown options fail with the offending token', () => {
  assert.throws(() => new Getopt(['-Z']), (e) => {
    assert.equal(e.message, 'invalid option -- Z');
    assert.equal(e.optopt, 'Z');
    return true;
  });
  assert.throws(() => new Getopt(['--nonsense']), (e) => {
    assert.equal(e.message, 'invalid option -- --nonsense');
    assert.equal(e.optopt, '--nonsense');
    return true;
  });
});

test('Getopt: a value on a no-argument option fails', () => {
  assert.throws(() => new Getopt(['--classify=1']),
    /option --classify doesn't allow an argument/);
});

test('Getopt: a missing REQUIRED argument fails', () => {
  assert.throws(() => new Getopt(['--output']), /option --output requires an argument/);
  assert.throws(() => new Getopt(['--premise']), /option --premise requires an argument/);
  assert.throws(() => new Getopt(['-o']), /option requires an argument -- o/);
});

test('Getopt: an empty optional value is distinguishable from no value', () => {
  assert.equal(new Getopt(['--consistency=']).parsed[0].value, '');
  assert.equal(new Getopt(['--consistency']).parsed[0].value, null);
});

test('Getopt: a bare "-" and a bare "--x" that is not an option', () => {
  assert.deepEqual(new Getopt(['-']).operands, ['-']);
  // `--` alone is the terminator, not an operand.
  assert.deepEqual(new Getopt(['--']).operands, []);
});

test('Getopt: duplicate long names keep the FIRST declaration', () => {
  // Both `-p` (PN=IRI) and kDefaultPrefix (IRI) declare longStr 'prefix'.
  // HermiT has the identical collision at CommandLine.java:417-418, so
  // `--prefix=IRI` is unreachable by long name in both implementations.
  const g = new Getopt(['--prefix', OBO]);
  assert.equal(g.parsed[0].option.optCharString, 'p');
  assert.equal(g.parsed[0].option.metavar, 'PN=IRI');
  assert.equal(new Getopt([]).byLong.get('prefix').metavar, 'PN=IRI');
});

test('Getopt: exposes the parsed codes and the option objects', () => {
  const g = new Getopt(['-c']);
  assert.equal(g.parsed[0].code, 'c'.codePointAt(0));
  assert.equal(g.parsed[0].option, byShort('c'));
});

// ===========================================================================
test('option table: 31 options, each with a group and help text', () => {
  assert.equal(options.length, 31);
  for (const o of options) {
    assert.ok(typeof o.help === 'string' && o.help.length > 0, `${o.longStr} has no help`);
    assert.ok(typeof o.group === 'string' && o.group.length > 0, `${o.longStr} has no group`);
    assert.ok(Object.values(Arg).includes(o.arg), `${o.longStr} has a bad arg`);
  }
});

test('option table: Arg has exactly HermiT\'s three values', () => {
  assert.deepEqual(Object.keys(Arg).sort(), ['NONE', 'OPTIONAL', 'REQUIRED']);
});

test('option table: long-only options use HermiT\'s k* codes (1000+)', () => {
  const longOnly = options.filter((o) => !o.hasShortForm());
  assert.ok(longOnly.length > 0);
  for (const o of longOnly) {
    assert.ok(o.optChar >= 1000, `${o.longStr} has code ${o.optChar}`);
  }
  assert.equal(OptionCode.kPremise, 1013);
  assert.equal(OptionCode.kDumpClauses, 1001);
});

test('option table: short options are all ASCII', () => {
  for (const o of options.filter((x) => x.hasShortForm())) {
    assert.ok(o.optChar < 256);
    assert.equal(o.optCharString.length, 1);
  }
});

test('option table: groups appear in HermiT\'s display order', () => {
  const seen = [];
  for (const o of options) {
    if (seen.length === 0 || seen[seen.length - 1] !== o.group) seen.push(o.group);
  }
  assert.deepEqual(seen, [
    OptionGroup.kMisc, OptionGroup.kActions, OptionGroup.kPrefixes,
    OptionGroup.kParsing, OptionGroup.kAlgorithm, OptionGroup.kInternals
  ]);
});

test('option table: getLongOptExampleStr renders all three argument kinds', () => {
  assert.equal(byLong('classify').getLongOptExampleStr(), '--classify');
  assert.equal(byLong('base').getLongOptExampleStr(), '--base=BASE');
  assert.equal(byLong('consistency').getLongOptExampleStr(), '--consistency[=CLASS]');
  assert.equal(byLong('dump-clauses').getLongOptExampleStr(), '--dump-clauses[=FILE]');
  assert.equal(byLong('prefix').getLongOptExampleStr(), '--prefix=PN=IRI');
});

test('option table: an option with no long name renders an empty example', () => {
  const bare = new Option('x', null, null, 'help');
  assert.equal(bare.getLongOptExampleStr(), '');
});

test('option table: every metavar implies an argument', () => {
  for (const o of options) {
    if (o.metavar !== null) assert.notEqual(o.arg, Arg.NONE, `${o.longStr}`);
  }
});

test('formatOptionsString reproduces the getopt(3) spec', () => {
  assert.equal(formatOptionsString(options), 'hVv::q::o:lcODPk::ds:S:e:UENp:');
  assert.ok(formatOptionsString(options).includes('k::'), 'OPTIONAL uses two colons');
  assert.ok(formatOptionsString(options).includes('o:'), 'REQUIRED uses one colon');
  assert.ok(!formatOptionsString(options).includes('-'), 'long-only options are omitted');
});

test('formatOptionsString skips long-only options', () => {
  const spec = formatOptionsString(options);
  for (const o of options.filter((x) => !x.hasShortForm())) {
    assert.ok(!spec.includes(String.fromCharCode(o.optChar)));
  }
});

// ===========================================================================
test('formatOptionHelp prints each group heading exactly once', () => {
  // DIVERGENCE FROM HERMIT: HermiT's `formatOptionHelp` assigns `curGroup`
  // without ever comparing it, so it re-emits the heading before every option
  // and `--help` runs to ~150 lines. This port emits it on change only.
  const help = formatOptionHelp(options);
  for (const g of Object.values(OptionGroup)) {
    assert.equal(help.split(`\n${g}:\n`).length - 1, 1, `${g} heading count`);
  }
});

test('formatOptionHelp stays within 80 columns', () => {
  const help = formatOptionHelp(options);
  for (const line of help.split('\n')) {
    assert.ok(line.length <= 80, `${line.length} chars: ${JSON.stringify(line)}`);
  }
  // ...and actually uses the width, so a regression to over-wrapping is caught.
  assert.ok(Math.max(...help.split('\n').map((l) => l.length)) > 75);
});

test('formatOptionHelp lists every long option', () => {
  const help = formatOptionHelp(options);
  for (const o of options.filter((x) => x.longStr)) {
    assert.ok(help.includes(o.getLongOptExampleStr()), o.getLongOptExampleStr());
  }
});

test('formatOptionHelp aligns the help column', () => {
  const help = formatOptionHelp(options);
  const fieldWidth = Math.max(...options.map((o) => o.getLongOptExampleStr().length));
  const column = 6 + fieldWidth + 1;
  const wrapped = help.split('\n').filter((l) => l.startsWith(' '.repeat(column)) && l.trim() !== '');
  assert.ok(wrapped.length > 0);
});

test('formatOptionHelp accepts a custom option list', () => {
  // fieldWidth is 7 (`--zebra`), so the help column starts at 6 + 7 + 1 = 14 and
  // exactly one space separates the option from its help text.
  const help = formatOptionHelp([new Option('z', 'zebra', 'Animals', 'a zebra')]);
  assert.equal(help, '\nAnimals:\n  -z, --zebra a zebra\n');
  assert.equal(help.split('\n')[2].indexOf('a zebra'), 14);
});

test('formatOptionHelp pads a long-only option into the same column', () => {
  const help = formatOptionHelp([
    new Option('z', 'zebra', 'Animals', 'striped'),
    new Option(1000, 'aardvarkish', 'Animals', 'long-nosed')
  ]);
  const rows = help.split('\n').filter((l) => l.includes('striped') || l.includes('long-nosed'));
  assert.equal(rows.length, 2);
  // Both help texts start at the same column: 6 + len('--aardvarkish') + 1.
  const column = 6 + '--aardvarkish'.length + 1;
  assert.equal(rows[0].indexOf('striped'), column);
  assert.equal(rows[1].indexOf('long-nosed'), column);
});

// ===========================================================================
test('breakLines honours lineWidth and indent', () => {
  const out = breakLines('alpha beta gamma delta epsilon zeta eta', 20, 4);
  for (const line of out.split('\n')) assert.ok(line.length <= 20);
  for (const line of out.split('\n').slice(1)) assert.ok(line.startsWith('    '));
});

test('breakLines leaves text that already fits alone', () => {
  assert.equal(breakLines('one two', 80, 0), 'one two');
  assert.equal(breakLines('', 80, 0), '');
});

test('breakLines counts a trailing space against the width, as Java does', () => {
  // Java's BreakIterator spans are word+following-whitespace and the whole span
  // is width-tested. Splitting words from whitespace instead would let a
  // trailing space slip past and emit lineWidth+1 character lines.
  const out = breakLines('aaa bbb ccc', 7, 0);
  for (const line of out.split('\n')) assert.ok(line.length <= 7);
  assert.ok(out.includes('\n'), 'the text should not fit on one line');
});

test('breakLines emits an over-long word whole instead of splitting it', () => {
  // Java's BreakIterator yields the word as one span; the width test fails, so a
  // break is emitted and the word is placed on its own indented line. Nothing is
  // ever chopped mid-word, and the loop always terminates.
  assert.equal(breakLines('supercalifragilistic', 5, 2), '\n  supercalifragilistic');
  assert.equal(breakLines('supercalifragilistic', 5, 0), '\nsupercalifragilistic');
});

// ===========================================================================
test('toWriter passes a Writer through unchanged', () => {
  const w = new StringWriter();
  assert.equal(toWriter(w), w);
});

test('toWriter adapts a stream-like object', () => {
  const chunks = [];
  const w = toWriter({ write: (s) => chunks.push(s) });
  w.print('a');
  w.println('b');
  assert.deepEqual(chunks, ['a', 'b\n']);
});

test('toWriter rejects a sink it cannot use', () => {
  assert.throws(() => toWriter({}), TypeError);
  assert.throws(() => toWriter(42), TypeError);
});

test('toWriter defaults to a StreamWriter over process.stdout', () => {
  const w = toWriter(null);
  assert.equal(typeof w.println, 'function');
});

test('StatusOutput filters by level', () => {
  const err = new StringWriter();
  const s = new StatusOutput(StatusLevel.STATUS, err);
  s.log(StatusLevel.ALWAYS, 'always');
  s.log(StatusLevel.STATUS, 'status');
  s.log(StatusLevel.DETAIL, 'detail');
  s.log(StatusLevel.DEBUG, 'debug');
  assert.equal(err.toString(), 'always\nstatus\n');
});

test('StatusOutput at ALWAYS level prints only ALWAYS messages', () => {
  const err = new StringWriter();
  const s = new StatusOutput(StatusLevel.ALWAYS, err);
  s.log(StatusLevel.ALWAYS, 'shown');
  s.log(StatusLevel.STATUS, 'hidden');
  assert.equal(err.toString(), 'shown\n');
});

test('StatusLevel ordering matches HermiT', () => {
  assert.ok(StatusLevel.ALWAYS < StatusLevel.STATUS);
  assert.ok(StatusLevel.STATUS < StatusLevel.DETAIL);
  assert.ok(StatusLevel.DETAIL < StatusLevel.DEBUG);
});

// ===========================================================================
test('resolveOntologyPath keeps an absolute path', () => {
  assert.equal(resolveOntologyPath(OGMS, DIR), OGMS);
});

test('resolveOntologyPath joins a relative name onto the base', () => {
  assert.equal(resolveOntologyPath('ogms.owl', DIR), OGMS);
  assert.equal(resolveOntologyPath('./ogms.owl', DIR), OGMS);
  assert.equal(resolveOntologyPath('../ontologies/ogms.owl', DIR), OGMS);
});

test('resolveOntologyPath decodes a file: IRI', () => {
  const iri = `file:///${OGMS.replace(/\\/g, '/')}`;
  assert.equal(resolveOntologyPath(iri, DIR), OGMS);
});

test('resolveOntologyPath percent-decodes a file: IRI', () => {
  const iri = `file:///${OGMS.replace(/\\/g, '/').split('/').map(encodeURIComponent).join('/')}`;
  assert.equal(resolveOntologyPath(iri, DIR), OGMS);
});

test('resolveOntologyPath does not mistake a drive letter for a scheme', () => {
  const p = 'D:\\ontologies\\x.owl';
  assert.equal(resolveOntologyPath(p, DIR), path.resolve(p));
});

test('resolveOntologyPath rejects an empty reference', () => {
  for (const bad of ['', null, undefined]) {
    assert.throws(() => resolveOntologyPath(bad, DIR), UsageException);
  }
});

test('resolveOntologyPath rejects a remote scheme and names it', () => {
  assert.throws(() => resolveOntologyPath('http://example.org/x.owl', DIR), (e) => {
    assert.ok(e instanceof UsageException);
    assert.match(e.message, /only local files and 'file:' IRIs are supported/);
    assert.match(e.message, /got scheme 'http:'/);
    return true;
  });
  assert.throws(() => resolveOntologyPath('https://example.org/x.owl', DIR),
    /got scheme 'https:'/);
});

test('resolveOntologyPath resolves a degenerate file: IRI to the drive root', () => {
  // WHATWG URL parsing makes `file://` the root of the current drive rather than
  // an error, so the caller gets a path that simply will not exist. The failure
  // then comes from the file check in `run`, not from here.
  const resolved = resolveOntologyPath('file://', DIR);
  assert.ok(path.isAbsolute(resolved));
  assert.equal(resolved, path.parse(resolved).root);
  assert.equal(resolveOntologyPath('file:/x.owl', DIR), path.join(path.parse(DIR).root, 'x.owl'));
});

test('resolveOntologyPath rejects a file: IRI that is not a URL at all', () => {
  assert.throws(() => resolveOntologyPath('file://%zz', DIR), (e) => {
    assert.ok(e instanceof UsageException);
    assert.match(e.message, /is not a valid file IRI/);
    return true;
  });
});

// ===========================================================================
test('parseArguments builds an empty plan by default', () => {
  const p = parseArguments([OGMS]);
  assert.deepEqual(p.ontologies, [OGMS]);
  assert.deepEqual(p.actions, []);
  assert.equal(p.verbosity, 1);
  assert.equal(p.outputLocation, null);
  assert.equal(p.baseDir, process.cwd());
  assert.equal(p.ignoreOntologyPrefixes, false);
  assert.equal(p.defaultPrefix, null);
  assert.equal(p.conclusionIRI, null);
  assert.equal(p.exitEarly, null);
  assert.equal(p.prefixMappings.size, 0);
});

test('parseArguments collects several ontologies in order', () => {
  const p = parseArguments(['a.owl', 'b.owl', 'c.owl']);
  assert.deepEqual(p.ontologies, ['a.owl', 'b.owl', 'c.owl']);
});

test('parseArguments: -h and -V exit early without an ontology', () => {
  assert.equal(parseArguments(['--help']).exitEarly, 0);
  assert.equal(parseArguments(['--version']).exitEarly, 0);
  assert.equal(parseArguments(['-h']).exitEarly, 0);
  assert.equal(parseArguments(['-V']).exitEarly, 0);
});

test('parseArguments: -v/-q adjust the verbosity', () => {
  assert.equal(parseArguments(['-v', OGMS]).verbosity, 2);
  assert.equal(parseArguments(['-v', '-v', OGMS]).verbosity, 3);
  assert.equal(parseArguments(['-v2', OGMS]).verbosity, 3);
  assert.equal(parseArguments(['--verbose=2', OGMS]).verbosity, 3);
  assert.equal(parseArguments(['-q', OGMS]).verbosity, 0);
  assert.equal(parseArguments(['-q', '-q', OGMS]).verbosity, -1);
  assert.equal(parseArguments(['-v', '-q', OGMS]).verbosity, 1);
});

test('parseArguments: a non-numeric verbosity amount is a usage error', () => {
  assert.throws(() => parseArguments(['--verbose=x', OGMS]), (e) => {
    assert.ok(e instanceof UsageException);
    assert.equal(e.message, 'argument to --verbose must be a number');
    return true;
  });
  assert.throws(() => parseArguments(['--quiet=y', OGMS]),
    /argument to --quiet must be a number/);
  assert.throws(() => parseArguments(['-vvv', OGMS]),
    /argument to --verbose must be a number/);
});

test('parseArguments: -o resolves to an absolute path, -o - means stdout', () => {
  assert.equal(parseArguments(['-o', 'out.txt', OGMS]).outputLocation,
    path.resolve('out.txt'));
  assert.equal(parseArguments(['-o', '-', OGMS]).outputLocation, null);
  assert.equal(parseArguments(['--output=-', OGMS]).outputLocation, null);
});

test('parseArguments: --base sets the resolution directory', () => {
  assert.equal(parseArguments(['--base', DIR, 'ogms.owl']).baseDir, path.resolve(DIR));
  assert.deepEqual(parseArguments([`--base=${DIR}`, 'ogms.owl']).ontologies, ['ogms.owl']);
});

test('parseArguments: -N and -p', () => {
  const p = parseArguments(['-N', '-p', `obo=${OBO}`, OGMS]);
  assert.equal(p.ignoreOntologyPrefixes, true);
  assert.deepEqual([...p.prefixMappings], [['obo', OBO]]);
});

test('parseArguments: a malformed -p is a usage error', () => {
  assert.throws(() => parseArguments(['-p', 'bogus', OGMS]), (e) => {
    assert.ok(e instanceof UsageException);
    assert.equal(e.message, "the prefix declaration 'bogus' is not of the form PN=IRI.");
    return true;
  });
});

test('parseArguments: -d applies only to the NEXT subs/supers', () => {
  const p = parseArguments(['-d', '-s', 'A', '-s', 'B', OGMS]);
  const subs = p.actions.filter((a) => a instanceof SubsAction);
  assert.equal(subs.length, 2);
  assert.equal(subs[0].all, false);
  assert.equal(subs[1].all, true);
  assert.deepEqual(subs.map((a) => a.conceptName), ['A', 'B']);

  const q = parseArguments(['-d', '-S', 'A', '-S', 'B', OGMS]);
  const supers = q.actions.filter((a) => a instanceof SupersAction);
  assert.equal(supers[0].all, false);
  assert.equal(supers[1].all, true);
});

test('parseArguments: -cODP collapse into ONE ClassifyAction', () => {
  const p = parseArguments(['-c', '-O', '-D', '-P', OGMS]);
  const classify = p.actions.filter((a) => a instanceof ClassifyAction);
  assert.equal(classify.length, 1);
  assert.equal(classify[0].classifyClasses, true);
  assert.equal(classify[0].classifyOPs, true);
  assert.equal(classify[0].classifyDPs, true);
  assert.equal(classify[0].prettyPrint, true);
});

test('parseArguments: -P alone registers no action', () => {
  assert.deepEqual(parseArguments(['-P', OGMS]).actions, []);
  assert.deepEqual(parseArguments(['-d', OGMS]).actions, []);
  assert.deepEqual(parseArguments(['-N', OGMS]).actions, []);
});

test('parseArguments: the ClassifyAction is appended LAST', () => {
  const p = parseArguments(['-c', '-k', OGMS]);
  assert.ok(p.actions[0] instanceof SatisfiabilityAction);
  assert.ok(p.actions[p.actions.length - 1] instanceof ClassifyAction);
});

test('parseArguments: -U is sugar for --equivalents=owl:Nothing', () => {
  const p = parseArguments(['-U', OGMS]);
  assert.equal(p.actions.length, 1);
  assert.ok(p.actions[0] instanceof EquivalentsAction);
  assert.equal(p.actions[0].conceptName, `${OWL}Nothing`);
});

test('parseArguments: -k defaults to owl:Thing and keeps an attached argument', () => {
  assert.equal(parseArguments(['-k', OGMS]).actions[0].conceptName, `${OWL}Thing`);
  assert.equal(parseArguments([`-k${OBO}X`, OGMS]).actions[0].conceptName, `${OBO}X`);
  assert.equal(parseArguments([`--consistency=${OBO}X`, OGMS]).actions[0].conceptName,
    `${OBO}X`);
});

test('parseArguments: -s/-S/-e/-l build the right action types', () => {
  assert.ok(parseArguments(['-s', 'A', OGMS]).actions[0] instanceof SubsAction);
  assert.ok(parseArguments(['-S', 'A', OGMS]).actions[0] instanceof SupersAction);
  assert.ok(parseArguments(['-e', 'A', OGMS]).actions[0] instanceof EquivalentsAction);
  assert.deepEqual(parseArguments(['-l', OGMS]).actions, []);
  assert.ok(parseArguments(['--dump-clauses=-', OGMS]).actions[0] instanceof DumpClausesAction);
  assert.ok(parseArguments(['--print-prefixes', OGMS]).actions[0] instanceof DumpPrefixesAction);
});

test('parseArguments: -s/-S/-e need an argument', () => {
  for (const opt of ['--subs', '--supers', '--equivalents']) {
    assert.throws(() => parseArguments([opt]), UsageException);
  }
});

test('parseArguments: -E needs --conclusion', () => {
  assert.throws(() => parseArguments(['-E', OGMS]), (e) => {
    assert.ok(e instanceof UsageException);
    assert.equal(e.message, '--checkEntailment requires a --conclusion=IRI');
    return true;
  });
});

test('parseArguments: -E records the conclusion and builds an EntailsAction', () => {
  const p = parseArguments(['--premise', 'p.owl', '--conclusion', 'c.owl', '-E']);
  assert.equal(p.conclusionIRI, 'c.owl');
  assert.ok(p.actions.some((a) => a instanceof EntailsAction));
  // DIVERGENCE FROM HERMIT: -E may appear BEFORE --conclusion, because the
  // action is only materialised after the getopt loop finishes.
  const q = parseArguments(['-E', '--premise', 'p.owl', '--conclusion', 'c.owl']);
  assert.ok(q.actions.some((a) => a instanceof EntailsAction));
});

test('parseArguments: algorithm options reach the Configuration', () => {
  const p = parseArguments(['--block-match=pairwise', '--block-strategy=core',
    '--expansion-strategy=el', '--blockersCache', '--ignoreUnsupportedDatatypes',
    '--noInconsistentException', OGMS]);
  assert.equal(p.configuration.directBlockingType, DIRECT_BLOCKING_TYPE.PAIR_WISE);
  assert.equal(p.configuration.blockingStrategyType, BLOCKING_STRATEGY_TYPE.SIMPLE_CORE);
  assert.equal(p.configuration.existentialStrategyType, EXISTENTIAL_STRATEGY_TYPE.EL);
  assert.equal(p.configuration.blockingSignatureCacheType,
    BLOCKING_SIGNATURE_CACHE_TYPE.CACHED);
  assert.equal(p.configuration.ignoreUnsupportedDatatypes, true);
  assert.equal(p.configuration.throwInconsistentOntologyException, false);
});

test('parseArguments: enum keywords are case-insensitive', () => {
  const p = parseArguments(['--block-match=OPTIMAL', '--block-strategy=Anywhere',
    '--expansion-strategy=REUSE', OGMS]);
  assert.equal(p.configuration.directBlockingType, DIRECT_BLOCKING_TYPE.OPTIMAL);
  assert.equal(p.configuration.blockingStrategyType, BLOCKING_STRATEGY_TYPE.ANYWHERE);
  assert.equal(p.configuration.existentialStrategyType,
    EXISTENTIAL_STRATEGY_TYPE.INDIVIDUAL_REUSE);
});

test('parseArguments: every enum keyword maps to a real Configuration value', () => {
  const blocking = { single: 'SINGLE', pairwise: 'PAIR_WISE', optimal: 'OPTIMAL' };
  for (const [kw, key] of Object.entries(blocking)) {
    assert.equal(parseArguments([`--block-match=${kw}`, OGMS]).configuration.directBlockingType,
      DIRECT_BLOCKING_TYPE[key]);
  }
  const strategy = { ancestor: 'ANCESTOR', anywhere: 'ANYWHERE', core: 'SIMPLE_CORE',
    optimal: 'OPTIMAL' };
  for (const [kw, key] of Object.entries(strategy)) {
    assert.equal(parseArguments([`--block-strategy=${kw}`, OGMS]).configuration.blockingStrategyType,
      BLOCKING_STRATEGY_TYPE[key]);
  }
  const expansion = { creation: 'CREATION_ORDER', el: 'EL', reuse: 'INDIVIDUAL_REUSE' };
  for (const [kw, key] of Object.entries(expansion)) {
    assert.equal(parseArguments([`--expansion-strategy=${kw}`, OGMS]).configuration.existentialStrategyType,
      EXISTENTIAL_STRATEGY_TYPE[key]);
  }
});

test('parseArguments: a bad enum value is a usage error listing the choices', () => {
  assert.throws(() => parseArguments(['--block-match=bogus', OGMS]), (e) => {
    assert.ok(e instanceof UsageException);
    assert.equal(e.message, "unknown direct blocking type 'bogus'; supported values are "
      + "'pairwise', 'single', and 'optimal'");
    return true;
  });
  assert.throws(() => parseArguments(['--block-strategy=bogus', OGMS]),
    /unknown blocking strategy type 'bogus'/);
  assert.throws(() => parseArguments(['--expansion-strategy=bogus', OGMS]),
    /unknown existential strategy type 'bogus'/);
});

test('parseArguments: the default configuration matches Configuration\'s own', () => {
  const { Configuration } = require('../src/Configuration');
  const p = parseArguments([OGMS]);
  const fresh = new Configuration();
  for (const field of ['directBlockingType', 'blockingStrategyType',
    'existentialStrategyType', 'blockingSignatureCacheType',
    'ignoreUnsupportedDatatypes', 'throwInconsistentOntologyException']) {
    assert.equal(p.configuration[field], fresh[field], field);
  }
});

test('parseArguments: getopt failures surface as UsageException with a message', () => {
  for (const argv of [['-Z', OGMS], ['--nonsense', OGMS], ['--class', OGMS],
    ['-p', 'bogus', OGMS], ['--output']]) {
    assert.throws(() => parseArguments(argv), UsageException, JSON.stringify(argv));
  }
});

// ===========================================================================
test('static help text', () => {
  assert.equal(usageString, 'Usage: dl-js-reasoner [OPTION]... ONTOLOGY...');
  // The version is read from package.json (single source of truth), so assert
  // the DERIVATION rather than a literal — a hardcoded expectation here would
  // silently rot on the next version bump. Mirrors HermiT reading
  // `getPackage().getImplementationVersion()` out of the JAR manifest.
  const { REASONER_NAME, REASONER_VERSION } = require('../src/index');
  assert.equal(REASONER_VERSION, require('../package.json').version);
  assert.equal(versionString, `${REASONER_NAME} ${REASONER_VERSION}`);
  assert.match(versionString, /^DL-JS-REASONER \d+\.\d+\.\d+$/);
  // `footer` is an ARRAY of lines (printed with one `println` each), not a string.
  assert.ok(Array.isArray(footer));
  assert.equal(footer.length, 2);
  assert.ok(footer[0].includes('JavaScript port of HermiT'));
  assert.ok(footer[1].includes('https://github.com/hermit-reasoner/HermiT'));
});

test('REASONER_VERSION is package.json\'s version, not a duplicate literal', () => {
  const { REASONER_VERSION, REASONER_NAME } = require('../src/index');
  assert.equal(REASONER_NAME, 'DL-JS-REASONER');
  assert.equal(REASONER_VERSION, require('../package.json').version);
  assert.match(REASONER_VERSION, /^\d+\.\d+\.\d+$/);
});

test('UsageException carries its name for the bin wrapper', () => {
  const e = new UsageException('boom');
  assert.equal(e.name, 'UsageException');
  assert.equal(e.message, 'boom');
  assert.ok(e instanceof Error);
});

// ===========================================================================
// DLOntology.toString — the overload `--dump-clauses` prints through.
// ===========================================================================

test('DLOntology.toString() with no argument is the short summary', () => {
  const { E, cls, declaration, ontology, createR } = helpers;
  const A = cls('A');
  const B = cls('B');
  const r = createR(ontology([declaration(A), declaration(B), E.subclassOf(A, B)],
    'http://example.org/test'));
  r.isConsistent();
  try {
    assert.equal(r.getDLOntology().toString(), [
      'DLOntology(http://example.org/test)',
      '  clauses: 1',
      '  positive facts: 0',
      '  negative facts: 0',
      '  concepts: 2, object roles: 0, data roles: 0, individuals: 0, complex roles: 0',
      '  flags: horn=true inverse=false atMost=false nominals=false datatypes=false'
    ].join('\n'));
  } finally {
    r.dispose();
  }
});

test('DLOntology.toString(prefixes) is the HermiT five-section dump', () => {
  const { E, cls, declaration, ontology, createR } = helpers;
  const A = cls('A');
  const B = cls('B');
  const r = createR(ontology([declaration(A), declaration(B), E.subclassOf(A, B)],
    'http://example.org/test'));
  r.isConsistent();
  try {
    const dump = r.getDLOntology().toString(r.getPrefixes());
    assert.equal(dump, [
      'Prefixes: [',
      '  rdf: = <http://www.w3.org/1999/02/22-rdf-syntax-ns#>',
      '  rdfs: = <http://www.w3.org/2000/01/rdf-schema#>',
      '  owl: = <http://www.w3.org/2002/07/owl#>',
      '  xsd: = <http://www.w3.org/2001/XMLSchema#>',
      '  swrl: = <http://www.w3.org/2003/11/swrl#>',
      '  swrlb: = <http://www.w3.org/2003/11/swrlb#>',
      '  swrlx: = <http://www.w3.org/2003/11/swrlx#>',
      '  ruleml: = <http://www.w3.org/2003/11/ruleml#>',
      '  def: = <internal:def#>',
      '  defdata: = <internal:defdata#>',
      '  nnq: = <internal:nnq#>',
      '  all: = <internal:all#>',
      '  prop: = <internal:prop#>',
      '  nam: = <internal:nam#>',
      '  : = <http://example.org/test#>',
      ']',
      'Deterministic DL-clauses: [',
      '  http://example.org/test#B(X) :- http://example.org/test#A(X)',
      ']',
      'Disjunctive DL-clauses: [',
      ']',
      'ABox: [',
      ']',
      'Statistics: [',
      '  Number of deterministic clauses: 1',
      '  Number of nondeterministic clauses: 0',
      '  Number of disjunctions: 0',
      '  Number of positive facts: 0',
      '  Number of negative facts: 0',
      ']'
    ].join('\n'));
  } finally {
    r.dispose();
  }
});

test('DLOntology.toString(prefixes) does NOT abbreviate IRIs inside clauses', () => {
  // DIVERGENCE FROM HERMIT: HermiT threads `prefixes` through
  // `DLClause.toString(Prefixes)` and `Atom.toString(Prefixes)`. This port's
  // clause/atom renderers take no arguments, so only the `Prefixes: [...]`
  // header is affected — which is why `-N` yields an empty header but identical
  // clause bodies.
  const { E, cls, declaration, ontology, createR } = helpers;
  const A = cls('A');
  const B = cls('B');
  const r = createR(ontology([declaration(A), declaration(B), E.subclassOf(A, B)],
    'http://example.org/test'));
  r.isConsistent();
  try {
    const dlo = r.getDLOntology();
    const withPrefixes = dlo.toString(r.getPrefixes());
    const without = dlo.toString(new Prefixes());
    assert.equal(without.split('\n')[0], 'Prefixes: [');
    assert.equal(without.split('\n')[1], ']');
    // Everything after the header is byte-identical.
    assert.equal(without.slice(without.indexOf('Deterministic')),
      withPrefixes.slice(withPrefixes.indexOf('Deterministic')));
    assert.ok(without.includes('http://example.org/test#B(X)'));
  } finally {
    r.dispose();
  }
});

test('the reasoner\'s prefixes include the semantic-web set and a default', () => {
  const { cls, declaration, ontology, createR } = helpers;
  const A = cls('A');
  const r = createR(ontology([declaration(A)], 'http://example.org/test'));
  r.isConsistent();
  try {
    const map = new Map(r.getPrefixes().getPrefixIRIsByPrefixName());
    assert.equal(map.get('owl:'), 'http://www.w3.org/2002/07/owl#');
    assert.equal(map.get('rdf:'), 'http://www.w3.org/1999/02/22-rdf-syntax-ns#');
    assert.equal(map.get(':'), 'http://example.org/test#');
    // The internal prefixes HermiT uses for generated names are declared too.
    for (const name of ['def:', 'defdata:', 'nnq:', 'all:', 'prop:', 'nam:']) {
      assert.ok(map.has(name), `${name} is missing`);
      assert.ok(map.get(name).startsWith('internal:'), `${name} = ${map.get(name)}`);
    }
  } finally {
    r.dispose();
  }
});
