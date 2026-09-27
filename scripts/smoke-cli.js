'use strict';

// ---------------------------------------------------------------------------
// scripts/smoke-cli.js — the command-line front end, end to end.
//
// `test/cli.test.js` is the focused `node:test` suite (getopt, the option table,
// path resolution). This script is the broad one: it drives
// `CommandLine.main(argv, io)` IN-PROCESS against the real sample ontologies
// shipped with protege-js, capturing stdout/stderr into `StringWriter`s.
// Nothing is spawned, so there are no shell-quoting or pipe-killing hazards —
// and every assertion below was read off actual output, not guessed.
//
// Sections:
//   1. Meta: --help, --version, no ontology, unknown/ambiguous options, bad
//      enum values, bad verbosity amounts.
//   2. Actions on real ontologies: -k, -c, -cP, -O, -D, -s, -dS, -e, -U, -l.
//   3. Output routing: -o FILE, -o -, --dump-clauses (all three forms).
//   4. Prefixes and identifier forms: --print-prefixes, -p PN=IRI, -N, <…>.
//   5. Ontology resolution: --base, file: IRIs, --, missing files, remote IRIs,
//      several ontologies in one invocation.
//   6. Entailment: --premise/--conclusion/-E with positive AND negative controls.
//   7. Verbosity: -q silences, --verbose=2 emits DETAIL, -v -v -v emits DEBUG.
//   8. Algorithm options reach the Configuration (and still classify correctly).
//   9. Plan introspection, determinism, and the option table itself.
//
// Run with:  node scripts/smoke-cli.js
// ---------------------------------------------------------------------------

const fs = require('fs');
const os = require('os');
const path = require('path');

const { CommandLine, CliWriter, CliOptions, REASONER_NAME, REASONER_VERSION } = require('../src/index');
const {
  DIRECT_BLOCKING_TYPE, BLOCKING_STRATEGY_TYPE, BLOCKING_SIGNATURE_CACHE_TYPE,
  EXISTENTIAL_STRATEGY_TYPE
} = require('../src/Configuration');

const {
  main, parseArguments, resolveOntologyPath, UsageException,
  SubsAction, ClassifyAction, SatisfiabilityAction, EquivalentsAction
} = CommandLine;
const { StringWriter } = CliWriter;
const { options, formatOptionsString, formatOptionHelp, Arg } = CliOptions;

const DIR = path.resolve(__dirname, '../../protege-js/sample/ontologies');
const BFO = path.join(DIR, 'bfo.owl');
const OGMS = path.join(DIR, 'ogms.owl');
const RO = path.join(DIR, 'ro-core.owl');
const IAO = path.join(DIR, 'iao.owl');
const OBO = 'http://purl.obolibrary.org/obo/';
const OWL = 'http://www.w3.org/2002/07/owl#';

let failures = 0;
let checks = 0;

function check(name, actual, expected) {
  checks++;
  const a = JSON.stringify(actual);
  const e = JSON.stringify(expected);
  const ok = a === e;
  if (!ok) failures++;
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}${ok ? '' : `  (got ${a}, expected ${e})`}`);
}
function checkTrue(name, actual) { check(name, Boolean(actual), true); }
function section(title) { console.log(`\n=== ${title} ===`); }

/**
 * Run the CLI in-process.
 * @param {string[]} argv arguments AFTER the program name
 * @returns {{code: number, out: string, err: string}}
 */
function cli(argv) {
  const out = new StringWriter();
  const err = new StringWriter();
  const code = main(argv, { stdout: out, stderr: err });
  return { code, out: out.toString(), err: err.toString() };
}

/** Non-empty lines of `text`. */
function lines(text) { return text.split('\n').filter((l) => l !== ''); }

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'dljs-smoke-cli-'));
const tmpFile = (name) => path.join(tmp, name);
function writeTmp(name, content) {
  const f = tmpFile(name);
  fs.writeFileSync(f, content);
  return f;
}

// Two fixtures used by several sections. Both use FULL IRIs: protege-js'
// functional-syntax parser only expands a prefixed name when the colon index is
// > 0, so the empty default prefix (`:Local`) is left literal.
const UNSAT_OFN = writeTmp('unsat.ofn', [
  'Ontology(',
  `Declaration(Class(<${OBO}OGMS_0000073>))`,
  `SubClassOf(<${OBO}OGMS_0000073> ObjectIntersectionOf(<${OBO}BFO_0000002>`
    + ` ObjectComplementOf(<${OBO}BFO_0000002>)))`,
  ')'
].join('\n'));

const DPEX = 'http://example.org/dp#';
const DP_OFN = writeTmp('dp.ofn', [
  'Ontology(<http://example.org/dp>',
  `Declaration(DataProperty(<${DPEX}hasName>))`,
  `Declaration(DataProperty(<${DPEX}hasFirstName>))`,
  `Declaration(DataProperty(<${DPEX}hasAge>))`,
  `Declaration(DataProperty(<${DPEX}hasLabel>))`,
  `SubDataPropertyOf(<${DPEX}hasFirstName> <${DPEX}hasName>)`,
  `SubDataPropertyOf(<${DPEX}hasAge> owl:topDataProperty)`,
  `EquivalentDataProperties(<${DPEX}hasName> <${DPEX}hasLabel>)`,
  ')'
].join('\n'));

// ===========================================================================
section('1. meta options');
// ===========================================================================

const HELP = cli(['--help']);
check('1.1 --help exits 0', HELP.code, 0);
checkTrue('1.2 --help starts with the usage line',
  HELP.out.startsWith('Usage: dl-js-reasoner [OPTION]... ONTOLOGY...\n'));
checkTrue('1.3 --help keeps HermiT\'s own -dsowl:Thing example',
  HELP.out.includes('Example: dl-js-reasoner -dsowl:Thing pizza.owl'));
checkTrue('1.4 --help documents the entailment example',
  HELP.out.includes('--premise=premise.ofn --conclusion=conclusion.ofn --checkEntailment'));
checkTrue('1.5 --help documents that remote IRIs are NOT dereferenced',
  HELP.out.includes("Only local files and 'file:' IRIs are"));
checkTrue('1.6 --help prints all six group headings',
  ['Miscellaneous:', 'Actions:', 'Prefix name and IRI:', 'Parsing and loading:',
    'Algorithm settings (expert users only!):', 'Internals and debugging (unstable):']
    .every((g) => HELP.out.includes(`\n${g}\n`)));
checkTrue('1.7 --help prints each group heading EXACTLY once',
  ['Miscellaneous:', 'Actions:', 'Prefix name and IRI:', 'Parsing and loading:']
    .every((g) => HELP.out.split(`\n${g}\n`).length === 2));
checkTrue('1.8 --help lists every long option',
  options.filter((o) => o.longStr).every((o) => HELP.out.includes(o.getLongOptExampleStr())));
checkTrue('1.9 --help ends with the footer',
  HELP.out.endsWith('Visit <https://github.com/hermit-reasoner/HermiT> for the original.\n'));
checkTrue('1.10 --help writes nothing to stderr', HELP.err === '');
checkTrue('1.11 --help is compact (HermiT repeats every heading; we do not)',
  lines(HELP.out).length < 120);

check('1.12 -h is the same as --help', cli(['-h']).out, HELP.out);

const VERSION = cli(['--version']);
check('1.13 --version exits 0', VERSION.code, 0);
check('1.14 --version prints exactly three lines', lines(VERSION.out).length, 3);
check('1.15 --version prints name and version', lines(VERSION.out)[0],
  `${REASONER_NAME} ${REASONER_VERSION}`);
check('1.16 --version prints the port attribution', lines(VERSION.out)[1],
  'DL-JS-REASONER is a JavaScript port of HermiT.');
checkTrue('1.17 --version does not need an ontology', VERSION.err === '');

const NOARGS = cli([]);
check('1.18 no ontologies exits 1', NOARGS.code, 1);
check('1.19 no ontologies writes nothing to stdout', NOARGS.out, '');
check('1.20 no ontologies prints message + usage + hint', NOARGS.err,
  'No ontologies given.\nUsage: dl-js-reasoner [OPTION]... ONTOLOGY...\n'
  + "Try 'dl-js-reasoner --help' for more information.\n");

{
  const r = cli(['-Z', OGMS]);
  check('1.21 unknown short option exits 1', r.code, 1);
  checkTrue('1.22 unknown short option names the character',
    r.err.startsWith('invalid option -- Z\n'));
}
{
  const r = cli(['--nonsense', OGMS]);
  check('1.23 unknown long option exits 1', r.code, 1);
  checkTrue('1.24 unknown long option names the token',
    r.err.startsWith('invalid option -- --nonsense\n'));
}
{
  // `--class` is a prefix of both --classify and --classifyOPs.
  const r = cli(['--class', OGMS]);
  check('1.25 ambiguous long abbreviation exits 1', r.code, 1);
  checkTrue('1.26 an ambiguous abbreviation is refused, not guessed',
    r.err.startsWith('invalid option -- --class\n'));
}
{
  // An UNAMBIGUOUS abbreviation is accepted, exactly as GNU getopt allows.
  // `--unsat` matches `--unsatisfiable` alone; `--clas` (1.25) matches three.
  const r = cli(['--unsat', OGMS]);
  check('1.27 unambiguous abbreviation --unsat resolves to --unsatisfiable', r.code, 0);
  check('1.28 --unsat lists owl:Nothing', lines(r.out),
    ["Classes equivalent to 'owl:Nothing':", '\towl:Nothing']);
}
{
  const r = cli(['--block-match=bogus', OGMS]);
  check('1.29 a bad --block-match value exits 1', r.code, 1);
  checkTrue('1.30 a bad --block-match value lists the supported ones',
    r.err.startsWith("unknown direct blocking type 'bogus'; supported values are "
      + "'pairwise', 'single', and 'optimal'\n"));
}
{
  const r = cli(['--verbose=x', OGMS]);
  check('1.31 a non-numeric --verbose exits 1', r.code, 1);
  checkTrue('1.32 a non-numeric --verbose says so',
    r.err.startsWith('argument to --verbose must be a number\n'));
}
{
  const r = cli(['--quiet=y', OGMS]);
  check('1.33 a non-numeric --quiet exits 1', r.code, 1);
  checkTrue('1.34 a non-numeric --quiet says so',
    r.err.startsWith('argument to --quiet must be a number\n'));
}
{
  const r = cli(['-E', BFO]);
  check('1.35 -E without --conclusion exits 1', r.code, 1);
  checkTrue('1.36 -E without --conclusion says so',
    r.err.startsWith('--checkEntailment requires a --conclusion=IRI\n'));
}
{
  const r = cli(['--output']);
  check('1.37 --output without an argument exits 1', r.code, 1);
  checkTrue('1.38 --output without an argument is caught by getopt',
    r.err.startsWith('option --output requires an argument\n'));
}
{
  const r = cli(['--classify=1', OGMS]);
  check('1.39 a value on a no-argument option exits 1', r.code, 1);
  checkTrue('1.40 a value on a no-argument option says so',
    r.err.startsWith("option --classify doesn't allow an argument\n"));
}

// ===========================================================================
section('2. actions on real ontologies');
// ===========================================================================

check('2.1 bare -k exits 0', cli(['-k', OGMS]).code, 0);
check('2.2 bare -k defaults to owl:Thing', cli(['-k', OGMS]).out,
  `${OWL}Thing is satisfiable.\n`);
check('2.3 -kCLASS (attached) names a declared ogms class',
  cli([`-k${OBO}OGMS_0000073`, OGMS]).out, `${OBO}OGMS_0000073 is satisfiable.\n`);
check('2.4 --consistency=CLASS (long, = form) agrees with -kCLASS',
  cli([`--consistency=${OBO}OGMS_0000073`, OGMS]).out,
  `${OBO}OGMS_0000073 is satisfiable.\n`);

{
  // GNU getopt NEVER consumes the next argv element for an OPTIONAL argument,
  // so `-k X` leaves X as an ontology operand. HermiT's own help example
  // (`-dsowl:Thing`) shows the attached form is the intended one.
  const r = cli(['-k', BFO, OGMS]);
  check('2.5 `-k FILE` treats FILE as a second ontology (GNU semantics)', r.code, 0);
  check('2.6 `-k FILE` therefore answers for owl:Thing twice', lines(r.out).length, 2);
  const iri = cli(['-k', `${OBO}OGMS_0000073`, OGMS]);
  checkTrue('2.6b a detached `-k <IRI>` is refused as a remote IRI, not read as an argument',
    iri.code === 1 && iri.err.startsWith(`cannot load '${OBO}OGMS_0000073':`));
}

{
  const r = cli([`-k${OBO}OGMS_0000073`, UNSAT_OFN]);
  check('2.7 -k on an unsatisfiable class exits 0', r.code, 0);
  check('2.8 the unsatisfiable class is reported as such', r.out,
    `${OBO}OGMS_0000073 is not satisfiable.\n`);
}
{
  const r = cli(['-U', UNSAT_OFN]);
  check('2.9 -U exits 0', r.code, 0);
  check('2.10 -U lists the unsatisfiable class and owl:Nothing', lines(r.out),
    ["Classes equivalent to 'owl:Nothing':",
      `\t<${OBO}OGMS_0000073>`,
      '\towl:Nothing']);
}
{
  // A NEGATIVE CONTROL for 2.9: ogms.owl has no unsatisfiable classes, so -U
  // must list owl:Nothing alone.
  const r = cli(['-U', OGMS]);
  check('2.11 -U on a consistent ontology exits 0', r.code, 0);
  check('2.12 -U lists only owl:Nothing when nothing is unsatisfiable', lines(r.out),
    ["Classes equivalent to 'owl:Nothing':", '\towl:Nothing']);
}

{
  const r = cli(['-khttp://example.org/NotDeclared', OGMS]);
  check('2.13 -k on an undeclared class still exits 0', r.code, 0);
  check('2.14 an unconstrained class is satisfiable', r.out,
    'http://example.org/NotDeclared is satisfiable.\n');
  check('2.15 an undeclared class warns on stderr at ALWAYS level', r.err,
    "Warning: class 'http://example.org/NotDeclared' was not declared in the ontology.\n");
}

const FLAT = cli(['-c', '-o', '-', OGMS]);
check('2.16 -c -o - exits 0', FLAT.code, 0);
checkTrue('2.17 -c dumps a substantial taxonomy', lines(FLAT.out).length > 150);
check('2.18 the first dumped axiom is the top of the ogms hierarchy', lines(FLAT.out)[0],
  `SubClassOf( <${OBO}BFO_0000002> <${OBO}BFO_0000001> )`);
checkTrue('2.19 every dumped line is a flat FSS class axiom',
  lines(FLAT.out).every((l) => l.startsWith('SubClassOf( <')
    || l.startsWith('EquivalentClasses( <')));
checkTrue('2.20 the flat dump uses full angle-bracket IRIs throughout',
  lines(FLAT.out).every((l) => !/[a-z]+:[A-Za-z]/.test(l)));

{
  // Without -o the taxonomy still goes to stdout (HermiT does the same).
  const r = cli(['-c', OGMS]);
  check('2.21 -c without -o exits 0', r.code, 0);
  check('2.22 -c without -o writes the taxonomy to stdout', r.out, FLAT.out);
}

const PRETTY = cli(['-cP', '-o', '-', OGMS]);
check('2.23 -cP exits 0', PRETTY.code, 0);
check('2.24 -cP opens with a default Prefix declaration', lines(PRETTY.out)[0],
  'Prefix(:=<http://purl.obolibrary.org/obo/ogms.owl#>)');
check('2.25 -cP opens an Ontology frame', lines(PRETTY.out)[1],
  'Ontology(<http://purl.obolibrary.org/obo/ogms.owl#>');
check('2.26 -cP closes the Ontology frame',
  lines(PRETTY.out)[lines(PRETTY.out).length - 1], ')');
check('2.27 -cP puts owl:Thing at the root', lines(PRETTY.out)[2],
  `  SubClassOf( <${OBO}BFO_0000001> owl:Thing )`
  + ` Declaration( Class( <${OBO}BFO_0000001> ) )`);
check('2.28 -cP indents one level deeper', lines(PRETTY.out)[3],
  `    SubClassOf( <${OBO}BFO_0000002> <${OBO}BFO_0000001> )`
  + ` Declaration( Class( <${OBO}BFO_0000002> ) )`);
checkTrue('2.29 the pretty form wraps the flat one (more lines)',
  lines(PRETTY.out).length > lines(FLAT.out).length);

{
  const r = cli(['-O', '-o', '-', RO]);
  check('2.30 -O on ro-core exits 0', r.code, 0);
  checkTrue('2.31 -O dumps role axioms', lines(r.out).length > 30);
  checkTrue('2.32 -O emits SubObjectPropertyOf / EquivalentObjectProperties only',
    lines(r.out).every((l) => l.startsWith('SubObjectPropertyOf( ')
      || l.startsWith('EquivalentObjectProperties( ')));
  checkTrue('2.33 -O renders inverses as ObjectInverseOf( ... )',
    r.out.includes('ObjectInverseOf( <'));
  checkTrue('2.34 -O dumps NO class axioms', !r.out.includes('SubClassOf('));
}

{
  // -cO is a CLUSTER of -c and -O, so both hierarchies are dumped.
  const r = cli(['-cO', '-o', '-', RO]);
  check('2.35 -cO exits 0', r.code, 0);
  checkTrue('2.36 -cO dumps the class hierarchy', r.out.includes('SubClassOf( <'));
  checkTrue('2.37 -cO also dumps the role hierarchy',
    r.out.includes('SubObjectPropertyOf( '));
}

{
  // iao.owl declares data properties but asserts no data-property hierarchy, so
  // -D on it is legitimately EMPTY. The fixture below is the positive control.
  const empty = cli(['-D', '-o', '-', IAO]);
  check('2.38 -D on iao exits 0', empty.code, 0);
  check('2.39 -D on an ontology with no DP hierarchy prints nothing', empty.out, '\n');

  const r = cli(['-D', '-o', '-', DP_OFN]);
  check('2.40 -D on a DP-hierarchy fixture exits 0', r.code, 0);
  check('2.41 -D dumps the equivalent pair and the sub-property', lines(r.out),
    [`EquivalentDataProperties( <${DPEX}hasLabel> <${DPEX}hasName> )`,
      `SubDataPropertyOf( <${DPEX}hasFirstName> <${DPEX}hasLabel> )`]);
  checkTrue('2.42 -D omits the hasAge -> owl:topDataProperty edge (top is implicit)',
    !r.out.includes('hasAge'));
}

{
  const r = cli(['-DP', '-o', '-', DP_OFN]);
  check('2.43 -DP exits 0', r.code, 0);
  check('2.44 -DP derives the default prefix from the ontology IRI',
    lines(r.out)[0], `Prefix(:=<${DPEX}>)`);
  checkTrue('2.45 -DP abbreviates data properties against that prefix',
    r.out.includes('SubDataPropertyOf( :hasAge owl:topDataProperty )'));
  checkTrue('2.46 -DP nests hasFirstName under hasName',
    r.out.includes('    SubDataPropertyOf( :hasFirstName :hasName )'));
}

const SUBS = cli(['-s', `${OBO}BFO_0000001`, OGMS]);
check('2.47 -s exits 0', SUBS.code, 0);
check('2.48 -s uses the "All sub-classes" header', lines(SUBS.out)[0],
  `All sub-classes of '${OBO}BFO_0000001':`);
check('2.49 -s lists BFO_0000002 first (sorted by IRI)', lines(SUBS.out)[1],
  `\t<${OBO}BFO_0000002>`);
check('2.50 -s ends with owl:Nothing (a subclass of everything)',
  lines(SUBS.out)[lines(SUBS.out).length - 1], '\towl:Nothing');
checkTrue('2.51 every -s entry is tab-indented',
  lines(SUBS.out).slice(1).every((l) => l.startsWith('\t')));
checkTrue('2.52 -s lists the whole ogms class set', lines(SUBS.out).length === 183);

{
  const r = cli(['-ds', `${OBO}BFO_0000001`, OGMS]);
  check('2.53 -ds exits 0', r.code, 0);
  check('2.54 -ds uses the "Direct sub-classes" header', lines(r.out)[0],
    `Direct sub-classes of '${OBO}BFO_0000001':`);
  checkTrue('2.55 -ds lists strictly fewer classes than -s',
    lines(r.out).length < lines(SUBS.out).length);
  checkTrue('2.56 -ds still lists the direct child BFO_0000002',
    r.out.includes(`\t<${OBO}BFO_0000002>`));
  checkTrue('2.57 -ds drops the transitive descendant OGMS_0000073',
    !r.out.includes('OGMS_0000073'));
}

{
  const r = cli(['-dsowl:Thing', OGMS]);
  check('2.58 -dsowl:Thing (HermiT\'s documented example) exits 0', r.code, 0);
  check('2.59 -dsowl:Thing uses the abbreviated header', lines(r.out)[0],
    "Direct sub-classes of 'owl:Thing':");
  check('2.60 -dsowl:Thing lists the five ogms top-level classes',
    lines(r.out).length, 6);
  checkTrue('2.61 -dsowl:Thing includes BFO_0000001',
    r.out.includes(`\t<${OBO}BFO_0000001>`));
}

const SUPERS = cli(['-S', `${OBO}BFO_0000002`, OGMS]);
check('2.62 -S exits 0', SUPERS.code, 0);
check('2.63 -S uses the "All super-classes" header', lines(SUPERS.out)[0],
  `All super-classes of '${OBO}BFO_0000002':`);
check('2.64 -S lists BFO_0000001 and owl:Thing', lines(SUPERS.out).slice(1),
  [`\t<${OBO}BFO_0000001>`, '\towl:Thing']);

{
  // DIVERGENCE FROM HERMIT, asserted deliberately. HermiT calls
  // getSuperClasses(_, false) in BOTH branches, so -dS prints ALL supers under a
  // "Direct" heading. This port honours --direct.
  const r = cli(['-dS', `${OBO}BFO_0000002`, OGMS]);
  check('2.65 -dS exits 0', r.code, 0);
  check('2.66 -dS uses the "Direct super-classes" header', lines(r.out)[0],
    `Direct super-classes of '${OBO}BFO_0000002':`);
  check('2.67 -dS lists ONLY the direct super (HermiT would list owl:Thing too)',
    lines(r.out).slice(1), [`\t<${OBO}BFO_0000001>`]);
}

{
  const r = cli(['-e', `${OBO}BFO_0000001`, OGMS]);
  check('2.68 -e exits 0', r.code, 0);
  // The header abbreviates the raw name; with no matching ontology prefix the
  // functional-syntax form <IRI> comes back out.
  check('2.69 -e uses the "Classes equivalent to" header', lines(r.out)[0],
    `Classes equivalent to '<${OBO}BFO_0000001>':`);
  check('2.70 -e lists the class itself', lines(r.out).slice(1),
    [`\t<${OBO}BFO_0000001>`]);
}

check('2.71 -l exits 0', cli(['-l', OGMS]).code, 0);
check('2.72 -l is a no-op', cli(['-l', OGMS]).out, '');

{
  // Several actions in one invocation, run in command-line order.
  const r = cli(['-k', '-U', OGMS]);
  check('2.73 two actions exit 0', r.code, 0);
  check('2.74 the actions run in command-line order', lines(r.out),
    [`${OWL}Thing is satisfiable.`,
      "Classes equivalent to 'owl:Nothing':",
      '\towl:Nothing']);
}

// ===========================================================================
section('3. output routing');
// ===========================================================================

{
  const f = tmpFile('classify.txt');
  const r = cli(['-c', '-o', f, OGMS]);
  check('3.1 -o FILE exits 0', r.code, 0);
  check('3.2 -o FILE leaves stdout empty', r.out, '');
  check('3.3 the file holds exactly what -o - would print',
    fs.readFileSync(f, 'utf8'), FLAT.out);
}
{
  const f = tmpFile('pretty.txt');
  cli(['-cP', '-o', f, OGMS]);
  check('3.4 -cP -o FILE writes the pretty form',
    fs.readFileSync(f, 'utf8'), PRETTY.out);
}
{
  const f = tmpFile('missing-dir/x.txt');
  const r = cli(['-c', '-o', f, OGMS]);
  check('3.5 an unwritable -o exits 1', r.code, 1);
  checkTrue('3.6 an unwritable -o reports it without a stack trace',
    r.err.startsWith(`unable to open ${path.resolve(f)} for writing\n`)
    && !r.err.includes('\n    at '));
}
{
  // `-o -` and no `-o` at all both mean stdout.
  check('3.7 --output=- equals -o -', cli(['-c', '--output=-', OGMS]).out, FLAT.out);
}

const CLAUSES = cli(['--dump-clauses=-', OGMS]);
check('3.8 --dump-clauses=- exits 0', CLAUSES.code, 0);
checkTrue('3.9 the clause dump opens with the Prefixes block',
  CLAUSES.out.startsWith('Prefixes: [\n'));
checkTrue('3.10 the clause dump lists the standard prefixes',
  CLAUSES.out.includes('  owl: = <http://www.w3.org/2002/07/owl#>\n'));
checkTrue('3.11 the clause dump has the deterministic-clause block',
  CLAUSES.out.includes('Deterministic DL-clauses: [\n'));
checkTrue('3.12 the clause dump has the disjunctive block',
  CLAUSES.out.includes('Disjunctive DL-clauses: [\n'));
checkTrue('3.13 the clause dump has the ABox block', CLAUSES.out.includes('ABox: [\n'));
checkTrue('3.14 the clause dump ends with the Statistics block',
  CLAUSES.out.includes('Statistics: [\n'));
checkTrue('3.15 ogms reports 200 deterministic clauses',
  CLAUSES.out.includes('  Number of deterministic clauses: 200\n'));
checkTrue('3.16 ogms reports 0 nondeterministic clauses (it is Horn)',
  CLAUSES.out.includes('  Number of nondeterministic clauses: 0\n'));
checkTrue('3.17 ogms reports 17 positive facts',
  CLAUSES.out.includes('  Number of positive facts: 17\n'));
checkTrue('3.18 ogms reports 0 negative facts',
  CLAUSES.out.includes('  Number of negative facts: 0\n'));
check('3.19 --dump-clauses=- writes to stdout, not stderr', CLAUSES.err, '');

{
  const f = tmpFile('clauses.txt');
  const r = cli([`--dump-clauses=${f}`, OGMS]);
  check('3.20 --dump-clauses=FILE exits 0', r.code, 0);
  check('3.21 --dump-clauses=FILE leaves stdout empty', r.out, '');
  check('3.22 the file holds the same dump', fs.readFileSync(f, 'utf8'), CLAUSES.out);
}
{
  // A bare --dump-clauses has an OPTIONAL argument, so it falls back to the
  // shared -o sink (stdout here).
  const r = cli(['--dump-clauses', OGMS]);
  check('3.23 bare --dump-clauses exits 0', r.code, 0);
  check('3.24 bare --dump-clauses uses the -o sink', r.out, CLAUSES.out);
}
{
  const f = tmpFile('missing-dir/clauses.txt');
  const r = cli([`--dump-clauses=${f}`, OGMS]);
  check('3.25 an unwritable --dump-clauses target exits 1', r.code, 1);
  checkTrue('3.26 an unwritable --dump-clauses target reports it cleanly',
    r.err.startsWith('unable to open ') && !r.err.includes('\n    at '));
}
{
  // -N empties the dump's Prefixes header but leaves the clause bodies alone.
  const r = cli(['-N', '--dump-clauses=-', OGMS]);
  check('3.27 -N --dump-clauses exits 0', r.code, 0);
  checkTrue('3.28 -N empties the Prefixes header',
    r.out.startsWith('Prefixes: [\n]\n'));
  checkTrue('3.29 -N leaves the clause statistics untouched',
    r.out.includes('  Number of deterministic clauses: 200\n'));
}
{
  // DIVERGENCE: HermiT threads Prefixes into DLClause.toString/Atom.toString, so
  // clause bodies are abbreviated. This port's renderers take no arguments, so
  // bodies always carry full IRIs — with or without -N.
  const withP = CLAUSES.out;
  const withoutP = cli(['-N', '--dump-clauses=-', OGMS]).out;
  const bodyOf = (s) => s.slice(s.indexOf('Deterministic DL-clauses: ['));
  checkTrue('3.30 clause bodies are identical with and without -N (documented divergence)',
    bodyOf(withP).slice(0, 4000) === bodyOf(withoutP).slice(0, 4000));
}

// ===========================================================================
section('4. prefixes and identifier forms');
// ===========================================================================

{
  const r = cli(['--print-prefixes', OGMS]);
  check('4.1 --print-prefixes exits 0', r.code, 0);
  check('4.2 it prints the "Prefixes:" header first', lines(r.out)[0], 'Prefixes:');
  // The correct W3C namespace. HermiT's own Prefixes.java:54 registers the
  // typo'd `1999-02-22-rdf-syntax-ns#`; this port does not reproduce it, because
  // protege-js expands `rdf:` to the correct value.
  check('4.3 it lists rdf: (correct W3C namespace, NOT HermiT\'s typo)', lines(r.out)[1],
    '\trdf:\thttp://www.w3.org/1999/02/22-rdf-syntax-ns#');
  check('4.4 it lists owl:', lines(r.out)[3], '\towl:\thttp://www.w3.org/2002/07/owl#');
  checkTrue('4.5 it lists the ontology default prefix last (empty name)',
    lines(r.out)[lines(r.out).length - 1] === '\t:\thttp://purl.obolibrary.org/obo/ogms.owl#');
  checkTrue('4.6 every entry is tab-separated name/IRI',
    lines(r.out).slice(1).every((l) => /^\t[A-Za-z0-9-]*:\t\S+$/.test(l)));
}

{
  const r = cli(['-p', `obo=${OBO}`, '-e', `${OBO}BFO_0000001`, OGMS]);
  check('4.7 -p PN=IRI exits 0', r.code, 0);
  check('4.8 the header abbreviates with the declared prefix', lines(r.out)[0],
    "Classes equivalent to 'obo:BFO_0000001':");
  check('4.9 the entries are abbreviated too', lines(r.out).slice(1), ['\tobo:BFO_0000001']);
}
{
  const r = cli(['-p', `obo=${OBO}`, `-kobo:BFO_0000001`, OGMS]);
  check('4.10 a prefixed -k identifier exits 0', r.code, 0);
  check('4.11 the prefixed identifier resolves and is echoed verbatim', r.out,
    'obo:BFO_0000001 is satisfiable.\n');
}
{
  // `--prefix` resolves to the FIRST declaration with that long name, i.e. the
  // PN=IRI form — exactly as HermiT's gnu.getopt does with its duplicate entry.
  const r = cli(['--prefix', `obo=${OBO}`, `-kobo:BFO_0000001`, OGMS]);
  check('4.12 --prefix=PN=IRI is the long form of -p', r.code, 0);
  check('4.13 --prefix=PN=IRI abbreviates like -p', r.out,
    'obo:BFO_0000001 is satisfiable.\n');
}
{
  const r = cli(['-p', 'bogus', OGMS]);
  check('4.14 a malformed -p exits 1', r.code, 1);
  checkTrue('4.15 a malformed -p explains the expected form',
    r.err.startsWith("the prefix declaration 'bogus' is not of the form PN=IRI.\n"));
}
{
  const r = cli(['-p', `obo=${OBO}`, '-p', `obo=${OBO}`, OGMS]);
  check('4.16 a duplicate -p declaration exits 0', r.code, 0);
  checkTrue('4.17 a duplicate -p is reported at DETAIL level only (silent by default)',
    r.err === '');
}

const NOPREFIX = cli(['-N', '-s', `${OBO}BFO_0000001`, OGMS]);
check('4.18 -N exits 0', NOPREFIX.code, 0);
check('4.19 -N keeps the header verbatim', lines(NOPREFIX.out)[0],
  `All sub-classes of '${OBO}BFO_0000001':`);
check('4.20 -N prints bare IRIs (no angle brackets, no abbreviation)',
  lines(NOPREFIX.out)[1], `\t${OBO}BFO_0000002`);
check('4.21 -N expands owl:Nothing to its full IRI',
  lines(NOPREFIX.out)[lines(NOPREFIX.out).length - 1], `\t${OWL}Nothing`);
checkTrue('4.22 -N never emits an abbreviated name',
  !lines(NOPREFIX.out).slice(1).some((l) => /^\t[a-z]+:[A-Za-z]/.test(l)));

{
  const r = cli(['-N', '-U', OGMS]);
  check('4.23 -N -U exits 0', r.code, 0);
  check('4.24 -N expands the owl:Nothing header too', lines(r.out),
    [`Classes equivalent to '${OWL}Nothing':`, `\t${OWL}Nothing`]);
}

{
  const r = cli([`-k<${OBO}OGMS_0000073>`, OGMS]);
  check('4.25 an <angle-bracket> identifier exits 0', r.code, 0);
  check('4.26 the angle brackets are stripped for resolution but echoed verbatim',
    r.out, `<${OBO}OGMS_0000073> is satisfiable.\n`);
  checkTrue('4.27 no "not declared" warning for a real class',
    !r.err.includes('was not declared'));
}

// ===========================================================================
section('5. ontology resolution');
// ===========================================================================

check('5.1 --base + a relative name exits 0',
  cli(['--base', DIR, 'ogms.owl', '-k']).code, 0);
check('5.2 --base resolves the relative name to ogms.owl',
  cli(['--base', DIR, 'ogms.owl', '-k']).out, `${OWL}Thing is satisfiable.\n`);
checkTrue('5.3 --base works for the classify action too',
  cli(['--base', DIR, '-c', '-o', '-', 'bfo.owl']).out.includes('SubClassOf( <'));
checkTrue('5.4 --base=DIR (inline form) works the same',
  cli([`--base=${DIR}`, 'ogms.owl', '-k']).out === `${OWL}Thing is satisfiable.\n`);

{
  const iri = `file:///${OGMS.replace(/\\/g, '/')}`;
  check('5.5 a file: IRI exits 0', cli(['-k', iri]).code, 0);
  check('5.6 a file: IRI loads the ontology', cli(['-k', iri]).out,
    `${OWL}Thing is satisfiable.\n`);
  check('5.7 resolveOntologyPath decodes a file: IRI to the same path',
    resolveOntologyPath(iri, DIR), OGMS);
}

{
  const r = cli(['-k', 'http://example.org/remote.owl']);
  check('5.8 a remote IRI exits 1', r.code, 1);
  checkTrue('5.9 a remote IRI is refused with an explanation',
    r.err.startsWith("cannot load 'http://example.org/remote.owl': only local files "
      + "and 'file:' IRIs are supported (got scheme 'http:')\n"));
}
{
  const r = cli(['-k', 'https://example.org/remote.owl']);
  check('5.10 an https: IRI exits 1', r.code, 1);
  checkTrue('5.11 an https: IRI names its scheme', r.err.includes("(got scheme 'https:')"));
}
{
  const missing = tmpFile('definitely-missing.owl');
  const r = cli(['-k', missing]);
  check('5.12 a missing file exits 1', r.code, 1);
  checkTrue('5.13 a missing file reports both the reference and the resolved path',
    r.err.startsWith(`unable to load '${missing}': no such file (${missing})\n`));
}
{
  const r = cli(['-k', BFO, OGMS]);
  check('5.14 two ontologies in one invocation exit 0', r.code, 0);
  check('5.15 each ontology gets its own answer', lines(r.out).length, 2);
  checkTrue('5.16 both answers are the owl:Thing line',
    lines(r.out).every((l) => l === `${OWL}Thing is satisfiable.`));
}
{
  // --premise is just another way to name the ontology to load.
  const r = cli(['--premise', BFO, '-k']);
  check('5.17 --premise exits 0', r.code, 0);
  check('5.18 --premise loads bfo', r.out, `${OWL}Thing is satisfiable.\n`);
}
{
  const r = cli(['--premise']);
  check('5.19 --premise without an argument exits 1', r.code, 1);
  checkTrue('5.20 --premise without an argument is caught by getopt',
    r.err.startsWith('option --premise requires an argument\n'));
}
{
  // `--` stops option parsing, so a file whose name looks like an option loads.
  const weird = tmpFile('-weird.owl');
  fs.copyFileSync(OGMS, weird);
  const r = cli(['-k', '--', weird]);
  check('5.21 -- stops option parsing', r.code, 0);
  check('5.22 the operand after -- was loaded', r.out, `${OWL}Thing is satisfiable.\n`);
}
{
  const r = cli(['-k', tmpFile('missing.owl'), OGMS]);
  check('5.23 a failure on the FIRST ontology aborts the run', r.code, 1);
  checkTrue('5.24 the second ontology is never processed', !r.out.includes('satisfiable'));
}
{
  check('5.25 resolveOntologyPath keeps an absolute path', resolveOntologyPath(OGMS, DIR), OGMS);
  check('5.26 resolveOntologyPath joins a relative name onto the base',
    resolveOntologyPath('ogms.owl', DIR), OGMS);
  checkTrue('5.27 resolveOntologyPath rejects an empty reference',
    (() => {
      try { resolveOntologyPath('', DIR); return false; }
      catch (e) { return e instanceof UsageException; }
    })());
  checkTrue('5.28 resolveOntologyPath rejects a remote scheme',
    (() => {
      try { resolveOntologyPath('https://x/y.owl', DIR); return false; }
      catch (e) { return e instanceof UsageException; }
    })());
  checkTrue('5.29 a Windows drive letter is NOT mistaken for a URI scheme',
    resolveOntologyPath('D:\\ontologies\\x.owl', DIR) === path.resolve('D:\\ontologies\\x.owl'));
}
{
  // protege-js' OntologyLoader is LENIENT: a file it cannot recognise yields an
  // EMPTY ontology rather than an error. Asserted here so that any future move
  // to strict parsing is a deliberate one, not a silent regression.
  const junk = writeTmp('junk.owl', 'this is not an ontology at all }}}');
  const r = cli(['-k', junk]);
  check('5.30 an unrecognisable file loads as an empty ontology', r.code, 0);
  check('5.31 an empty ontology is still consistent', r.out,
    `${OWL}Thing is satisfiable.\n`);
  checkTrue('5.32 an empty ontology has no unsatisfiable classes',
    cli(['-U', junk]).out === "Classes equivalent to 'owl:Nothing':\n\towl:Nothing\n");
}

// ===========================================================================
section('6. entailment (--premise / --conclusion / -E)');
// ===========================================================================

// bfo.owl asserts BFO_0000002 SubClassOf BFO_0000001, so that direction is
// entailed and the reverse is not. Full IRIs only: protege-js' functional-syntax
// parser does not expand the EMPTY default prefix.
const ENTAILED = writeTmp('entailed.ofn',
  `Ontology(\nSubClassOf(<${OBO}BFO_0000002> <${OBO}BFO_0000001>)\n)`);
const NOT_ENTAILED = writeTmp('not-entailed.ofn',
  `Ontology(\nSubClassOf(<${OBO}BFO_0000001> <${OBO}BFO_0000002>)\n)`);
const BOTH = writeTmp('both.ofn', [
  'Ontology(',
  `SubClassOf(<${OBO}BFO_0000002> <${OBO}BFO_0000001>)`,
  `SubClassOf(<${OBO}BFO_0000003> <${OBO}BFO_0000001>)`,
  ')'
].join('\n'));
const MIXED = writeTmp('mixed.ofn', [
  'Ontology(',
  `SubClassOf(<${OBO}BFO_0000002> <${OBO}BFO_0000001>)`,
  `SubClassOf(<${OBO}BFO_0000001> <${OBO}BFO_0000002>)`,
  ')'
].join('\n'));

check('6.1 an entailed conclusion exits 0',
  cli([`--premise=${BFO}`, `--conclusion=${ENTAILED}`, '-E']).code, 0);
check('6.2 an entailed conclusion prints true',
  cli([`--premise=${BFO}`, `--conclusion=${ENTAILED}`, '-E']).out, 'true\n');
check('6.3 the reversed direction prints false (negative control)',
  cli([`--premise=${BFO}`, `--conclusion=${NOT_ENTAILED}`, '-E']).out, 'false\n');
check('6.4 a conclusion whose axioms are ALL entailed prints true',
  cli([`--premise=${BFO}`, `--conclusion=${BOTH}`, '-E']).out, 'true\n');
check('6.5 a conclusion with ONE non-entailed axiom prints false',
  cli([`--premise=${BFO}`, `--conclusion=${MIXED}`, '-E']).out, 'false\n');
check('6.6 -E may precede --conclusion (HermiT requires it after)',
  cli(['-E', `--premise=${BFO}`, `--conclusion=${ENTAILED}`]).out, 'true\n');
check('6.7 --checkEntailment is the long form of -E',
  cli([`--premise=${BFO}`, `--conclusion=${ENTAILED}`, '--checkEntailment']).out, 'true\n');
check('6.8 the premise may be a positional operand instead of --premise',
  cli([BFO, `--conclusion=${ENTAILED}`, '-E']).out, 'true\n');
{
  const r = cli([`--premise=${BFO}`, '--conclusion', tmpFile('gone.ofn'), '-E']);
  check('6.9 a missing conclusion file exits 1', r.code, 1);
  checkTrue('6.10 a missing conclusion file says "no such file"',
    r.err.includes('no such file'));
}
{
  // -E runs per ontology, so two premises give two answers.
  const r = cli([`--conclusion=${ENTAILED}`, '-E', BFO, OGMS]);
  check('6.11 -E over two premises exits 0', r.code, 0);
  check('6.12 bfo entails it and ogms (which imports bfo) entails it too',
    lines(r.out), ['true', 'true']);
}
{
  const r = cli(['-v', '-v', `--premise=${BFO}`, `--conclusion=${NOT_ENTAILED}`, '-E']);
  check('6.13 -E at DETAIL verbosity exits 0', r.code, 0);
  checkTrue('6.14 DETAIL reports the verdict on stderr',
    r.err.includes('Conclusion ontology is not entailed.'));
  check('6.15 the verdict still goes to stdout', r.out, 'false\n');
}

// ===========================================================================
section('7. verbosity');
// ===========================================================================

check('7.1 -q exits 0', cli(['-q', '-k', OGMS]).code, 0);
check('7.2 -q silences stderr entirely', cli(['-q', '-k', OGMS]).err, '');
checkTrue('7.3 -q leaves the answer on stdout',
  cli(['-q', '-k', OGMS]).out.includes('is satisfiable.'));
check('7.4 the default verbosity prints no DETAIL lines', cli(['-k', OGMS]).err, '');
{
  // ALWAYS-level messages survive one -q but not two.
  checkTrue('7.5 one -q still shows the undeclared-class warning',
    cli(['-q', '-khttp://example.org/NotDeclared', OGMS]).err.includes('was not declared'));
  check('7.6 two -q silence even ALWAYS-level warnings',
    cli(['-q', '-q', '-khttp://example.org/NotDeclared', OGMS]).err, '');
  checkTrue('7.7 two -q still produce the answer',
    cli(['-q', '-q', '-khttp://example.org/NotDeclared', OGMS]).out
      .includes('is satisfiable.'));
}

const DETAIL = cli(['--verbose=2', '-k', OGMS]);
check('7.8 --verbose=2 exits 0', DETAIL.code, 0);
checkTrue('7.9 DETAIL reports the ontology being processed',
  DETAIL.err.startsWith(`Processing ${OGMS}\n`));
checkTrue('7.10 DETAIL reports the action count', DETAIL.err.includes('\n1 actions\n'));
checkTrue('7.11 DETAIL times the parse', /Ontology parsed in \d+ msec\.\n/.test(DETAIL.err));
checkTrue('7.12 DETAIL times the reasoner construction',
  /Reasoner created in \d+ msec\.\n/.test(DETAIL.err));
checkTrue('7.13 DETAIL announces each action', DETAIL.err.includes('Doing action...\n'));
checkTrue('7.14 DETAIL times each action',
  /\.\.\.action completed in \d+ msec\.\n/.test(DETAIL.err));
checkTrue('7.15 DETAIL names the satisfiability check',
  DETAIL.err.includes(`Checking satisfiability of '${OWL}Thing'`));
checkTrue('7.16 DETAIL does not enable the tableau monitor',
  !DETAIL.err.includes('Current branching point'));
checkTrue('7.17 DETAIL leaves the answer on stdout',
  DETAIL.out === `${OWL}Thing is satisfiable.\n`);

const DEBUG = cli(['-v', '-v', '-v', '-k', OGMS]);
check('7.18 -v -v -v exits 0', DEBUG.code, 0);
checkTrue('7.19 DEBUG includes everything DETAIL does',
  DEBUG.err.includes('Doing action...\n'));
checkTrue('7.20 DEBUG turns on the tableau monitor',
  DEBUG.err.includes('Current branching point'));
checkTrue('7.21 DEBUG reports the tableau statistics',
  DEBUG.err.includes('clauses fired:') && DEBUG.err.includes('backjumps:'));
checkTrue('7.22 DEBUG reports the satisfiability verdict',
  DEBUG.err.includes('isConceptSatisfiable(Thing) ...YES'));
checkTrue('7.23 DEBUG still leaves the answer on stdout',
  DEBUG.out === `${OWL}Thing is satisfiable.\n`);

{
  // GNU getopt ATTACHES an optional argument, so -vvv is -v with optarg "vv".
  const r = cli(['-vvv', '-k', OGMS]);
  check('7.24 -vvv is parsed as -v=vv and rejected', r.code, 1);
  checkTrue('7.25 -vvv reports the non-numeric amount',
    r.err.startsWith('argument to --verbose must be a number\n'));
}
{
  const r = cli(['-v2', '-k', OGMS]);
  check('7.26 -v2 is the attached form of --verbose=2', r.code, 0);
  checkTrue('7.27 -v2 reaches DETAIL level', r.err.includes('Doing action...\n'));
  checkTrue('7.28 -v2 does not reach DEBUG level', !r.err.includes('Current branching point'));
}
{
  const r = cli(['--verbose=+2', '-k', OGMS]);
  check('7.29 a signed amount is accepted', r.code, 0);
  checkTrue('7.30 --verbose=+2 reaches DETAIL level', r.err.includes('Doing action...\n'));
}
{
  const r = cli(['-v', '-q', '-k', OGMS]);
  check('7.31 -v -q cancel out', r.code, 0);
  check('7.32 -v -q is back to the default (silent) level', r.err, '');
}

// ===========================================================================
section('8. algorithm options reach the Configuration');
// ===========================================================================

{
  const p = parseArguments([
    '--block-match=pairwise', '--block-strategy=core', '--expansion-strategy=el',
    '--blockersCache', '--ignoreUnsupportedDatatypes', '--noInconsistentException', OGMS
  ]);
  check('8.1 --block-match=pairwise', p.configuration.directBlockingType,
    DIRECT_BLOCKING_TYPE.PAIR_WISE);
  check('8.2 --block-strategy=core maps to SIMPLE_CORE', p.configuration.blockingStrategyType,
    BLOCKING_STRATEGY_TYPE.SIMPLE_CORE);
  check('8.3 --expansion-strategy=el', p.configuration.existentialStrategyType,
    EXISTENTIAL_STRATEGY_TYPE.EL);
  check('8.4 --blockersCache', p.configuration.blockingSignatureCacheType,
    BLOCKING_SIGNATURE_CACHE_TYPE.CACHED);
  check('8.5 --ignoreUnsupportedDatatypes', p.configuration.ignoreUnsupportedDatatypes, true);
  check('8.6 --noInconsistentException',
    p.configuration.throwInconsistentOntologyException, false);
  check('8.7 the ontology is still registered', p.ontologies, [OGMS]);
}
{
  const p = parseArguments(['--block-match=single', '--block-strategy=ancestor',
    '--expansion-strategy=creation', OGMS]);
  check('8.8 --block-match=single', p.configuration.directBlockingType,
    DIRECT_BLOCKING_TYPE.SINGLE);
  check('8.9 --block-strategy=ancestor', p.configuration.blockingStrategyType,
    BLOCKING_STRATEGY_TYPE.ANCESTOR);
  check('8.10 --expansion-strategy=creation', p.configuration.existentialStrategyType,
    EXISTENTIAL_STRATEGY_TYPE.CREATION_ORDER);
}
{
  const p = parseArguments(['--block-match=OPTIMAL', '--block-strategy=Anywhere',
    '--expansion-strategy=REUSE', OGMS]);
  check('8.11 enum keywords are case-insensitive (--block-match)',
    p.configuration.directBlockingType, DIRECT_BLOCKING_TYPE.OPTIMAL);
  check('8.12 enum keywords are case-insensitive (--block-strategy)',
    p.configuration.blockingStrategyType, BLOCKING_STRATEGY_TYPE.ANYWHERE);
  check('8.13 --expansion-strategy=reuse maps to INDIVIDUAL_REUSE',
    p.configuration.existentialStrategyType, EXISTENTIAL_STRATEGY_TYPE.INDIVIDUAL_REUSE);
}
{
  // The defaults must match Configuration's own defaults.
  const p = parseArguments([OGMS]);
  const fresh = new (require('../src/Configuration').Configuration)();
  check('8.14 no algorithm options leaves directBlockingType at the default',
    p.configuration.directBlockingType, fresh.directBlockingType);
  check('8.15 no algorithm options leaves blockingStrategyType at the default',
    p.configuration.blockingStrategyType, fresh.blockingStrategyType);
  check('8.16 no algorithm options leaves existentialStrategyType at the default',
    p.configuration.existentialStrategyType, fresh.existentialStrategyType);
  check('8.17 no algorithm options leaves the blockers cache at the default',
    p.configuration.blockingSignatureCacheType, fresh.blockingSignatureCacheType);
  check('8.18 the default verbosity is 1', p.verbosity, 1);
  check('8.19 the default output location is stdout', p.outputLocation, null);
  check('8.20 the default base directory is the cwd', p.baseDir, process.cwd());
  check('8.21 no actions are registered by default', p.actions, []);
}
{
  const r = cli(['--block-strategy=bogus', OGMS]);
  check('8.22 a bad --block-strategy exits 1', r.code, 1);
  checkTrue('8.23 a bad --block-strategy lists the supported values',
    r.err.startsWith("unknown blocking strategy type 'bogus'; supported values are "
      + "'ancestor', 'anywhere', 'core', and 'optimal'\n"));
}
{
  const r = cli(['--expansion-strategy=bogus', OGMS]);
  check('8.24 a bad --expansion-strategy exits 1', r.code, 1);
  checkTrue('8.25 a bad --expansion-strategy lists the supported values',
    r.err.startsWith("unknown existential strategy type 'bogus'; supported values are "
      + "'creation', 'el', and 'reuse'\n"));
}
{
  // The options must actually change the reasoning path, not just the config:
  // pairwise blocking + ancestor strategy still classifies ogms identically.
  const r = cli(['--block-match=pairwise', '--block-strategy=ancestor', '-c', '-o', '-', OGMS]);
  check('8.26 non-default blocking still classifies ogms', r.code, 0);
  check('8.27 the taxonomy is IDENTICAL to the default configuration', r.out, FLAT.out);
}
{
  const r = cli(['--block-match=single', '--expansion-strategy=creation', '-k', OGMS]);
  check('8.28 single blocking + creation-order expansion still decides ogms', r.code, 0);
  check('8.29 the satisfiability answer is unchanged', r.out,
    `${OWL}Thing is satisfiable.\n`);
}
{
  // --blockersCache IS implemented in this port: CACHED installs the cache
  // silently (it is also the default), so it must NOT warn.
  const r = cli(['--blockersCache', '-k', OGMS]);
  check('8.30 --blockersCache still runs', r.code, 0);
  checkTrue('8.31 --blockersCache does not warn (CACHED is implemented)',
    !r.err.includes('not implemented'));
  check('8.32 --blockersCache emits no stderr', r.err, '');
  check('8.33 the answer is still produced', r.out, `${OWL}Thing is satisfiable.\n`);
}
{
  const r = cli(['--block-strategy=core', '-k', OGMS]);
  check('8.34 --block-strategy=core still runs', r.code, 0);
  checkTrue('8.35 core blocking warns that it degrades to ANYWHERE',
    r.err.includes('Blocking strategy SIMPLE_CORE is not implemented')
    && r.err.includes('falling back to ANYWHERE blocking'));
  check('8.36 the answer is unaffected by the degradation', r.out,
    `${OWL}Thing is satisfiable.\n`);
}
{
  // The DEFAULT configuration (OPTIMAL strategy, CACHED) must stay silent,
  // otherwise every `err === ''` assertion above would be meaningless.
  check('8.37 the default configuration emits no degradation warning',
    cli(['-k', OGMS]).err, '');
  check('8.38 --block-strategy=anywhere emits no warning either',
    cli(['--block-strategy=anywhere', '-k', OGMS]).err, '');
}

// ===========================================================================
section('9. plan introspection, determinism, and the option table');
// ===========================================================================

{
  const p = parseArguments(['-d', '-s', 'A', '-s', 'B', OGMS]);
  const subs = p.actions.filter((a) => a instanceof SubsAction);
  check('9.1 two -s actions were registered', subs.length, 2);
  check('9.2 -d applies only to the NEXT subs/supers call', subs[0].all, false);
  check('9.3 the following -s reverts to "all"', subs[1].all, true);
  check('9.4 the concept names are kept verbatim',
    subs.map((a) => a.conceptName), ['A', 'B']);
}
{
  const p = parseArguments(['-d', '-S', 'A', '-S', 'B', OGMS]);
  const supers = p.actions.filter((a) => a instanceof CommandLine.SupersAction);
  check('9.5 -d applies to -S too', supers[0].all, false);
  check('9.6 -d resets after -S', supers[1].all, true);
}
{
  const p = parseArguments(['-c', '-O', '-D', '-P', OGMS]);
  const classify = p.actions.filter((a) => a instanceof ClassifyAction);
  check('9.7 -cODP registers exactly ONE ClassifyAction', classify.length, 1);
  check('9.8 it classifies classes', classify[0].classifyClasses, true);
  check('9.9 it classifies object properties', classify[0].classifyOPs, true);
  check('9.10 it classifies data properties', classify[0].classifyDPs, true);
  check('9.11 it pretty-prints', classify[0].prettyPrint, true);
  check('9.12 -P alone registers no action', parseArguments(['-P', OGMS]).actions, []);
}
{
  const p = parseArguments(['-c', '-k', OGMS]);
  check('9.13 actions run in command-line order', p.actions[0] instanceof SatisfiabilityAction,
    true);
  checkTrue('9.14 the ClassifyAction is appended LAST (after the getopt loop)',
    p.actions[p.actions.length - 1] instanceof ClassifyAction);
}
{
  const p = parseArguments(['-U', OGMS]);
  check('9.15 -U registers one EquivalentsAction',
    p.actions.filter((a) => a instanceof EquivalentsAction).length, 1);
  check('9.16 -U is sugar for --equivalents=owl:Nothing', p.actions[0].conceptName,
    `${OWL}Nothing`);
}
{
  const p = parseArguments([`-k${OBO}X`, OGMS]);
  check('9.17 -kCLASS records the attached argument', p.actions[0].conceptName, `${OBO}X`);
  const q = parseArguments(['-k', OGMS]);
  check('9.18 bare -k defaults to owl:Thing', q.actions[0].conceptName, `${OWL}Thing`);
}
{
  const f = tmpFile('out.txt');
  const p = parseArguments(['-c', '-o', f, OGMS]);
  check('9.19 -o FILE is resolved to an absolute path', p.outputLocation, path.resolve(f));
  check('9.20 -o - means stdout', parseArguments(['-c', '-o', '-', OGMS]).outputLocation, null);
  checkTrue('9.21 the ClassifyAction carries the output location for its status message',
    p.actions[0].outputLocation === path.resolve(f));
}
{
  const p = parseArguments(['-N', '-p', `obo=${OBO}`, OGMS]);
  check('9.22 -N sets ignoreOntologyPrefixes', p.ignoreOntologyPrefixes, true);
  check('9.23 -p records the mapping', [...p.prefixMappings], [['obo', OBO]]);
}

{
  check('9.24 the flat taxonomy is byte-identical across runs',
    cli(['-c', '-o', '-', OGMS]).out === FLAT.out, true);
  check('9.25 the pretty taxonomy is byte-identical across runs',
    cli(['-cP', '-o', '-', OGMS]).out === PRETTY.out, true);
  check('9.26 the clause dump is byte-identical across runs',
    cli(['--dump-clauses=-', OGMS]).out === CLAUSES.out, true);
  check('9.27 -s listings are byte-identical across runs',
    cli(['-s', `${OBO}BFO_0000001`, OGMS]).out === SUBS.out, true);
  check('9.28 -N listings are byte-identical across runs',
    cli(['-N', '-s', `${OBO}BFO_0000001`, OGMS]).out === NOPREFIX.out, true);
}

checkTrue('9.29 the option table has all 31 HermiT options', options.length === 31);
checkTrue('9.30 every option has a help string',
  options.every((o) => typeof o.help === 'string' && o.help.length > 0));
checkTrue('9.31 every option belongs to a group',
  options.every((o) => typeof o.group === 'string' && o.group.length > 0));
checkTrue('9.32 every long option renders as --name / --name=META / --name[=META]',
  options.filter((o) => o.longStr).every((o) => {
    const s = o.getLongOptExampleStr();
    if (o.arg === Arg.NONE) return s === `--${o.longStr}`;
    if (o.arg === Arg.OPTIONAL) return s === `--${o.longStr}[=${o.metavar}]`;
    return s === `--${o.longStr}=${o.metavar}`;
  }));
checkTrue('9.33 every option with a metavar takes an argument',
  options.every((o) => o.metavar === null || o.arg !== Arg.NONE));
check('9.34 Arg has exactly HermiT\'s three values',
  Object.keys(Arg).sort().join(','), 'NONE,OPTIONAL,REQUIRED');
check('9.35 the getopt spec matches HermiT\'s option set',
  formatOptionsString(options), 'hVv::q::o:lcODPk::ds:S:e:UENp:');
checkTrue('9.36 the getopt spec marks REQUIRED args with one colon',
  formatOptionsString(options).includes('o:'));
checkTrue('9.37 the getopt spec marks OPTIONAL args with two colons',
  formatOptionsString(options).includes('k::'));
checkTrue('9.38 the getopt spec omits long-only options',
  !formatOptionsString(options).includes('-'));
checkTrue('9.39 formatOptionHelp emits each group heading once',
  ['Miscellaneous:', 'Actions:', 'Prefix name and IRI:', 'Parsing and loading:',
    'Algorithm settings (expert users only!):', 'Internals and debugging (unstable):']
    .map((g) => formatOptionHelp(options).split(`\n${g}\n`).length - 1)
    .every((n) => n === 1));
checkTrue('9.40 formatOptionHelp wraps long help text at 80 columns',
  formatOptionHelp(options).split('\n').every((l) => l.length <= 80));
checkTrue('9.41 formatOptionHelp actually uses the full width (not over-wrapped)',
  Math.max(...formatOptionHelp(options).split('\n').map((l) => l.length)) > 75);
checkTrue('9.42 breakLines never exceeds lineWidth',
  CliOptions.breakLines('alpha beta gamma delta epsilon zeta', 20, 4)
    .split('\n').every((l) => l.length <= 20));
checkTrue('9.43 breakLines indents continuation lines',
  CliOptions.breakLines('alpha beta gamma delta epsilon zeta', 20, 4)
    .split('\n').slice(1).every((l) => l.startsWith('    ')));
checkTrue('9.44 breakLines keeps single-space-separated words on one line when they fit',
  CliOptions.breakLines('one two', 80, 0) === 'one two');

// ===========================================================================
fs.rmSync(tmp, { recursive: true, force: true });

console.log(`\n${failures === 0 ? 'ALL PASS' : 'FAILURES'}: ${checks - failures}/${checks} checks passed`);
process.exit(failures === 0 ? 0 : 1);
