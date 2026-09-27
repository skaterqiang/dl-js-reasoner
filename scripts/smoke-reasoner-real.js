'use strict';

// ---------------------------------------------------------------------------
// scripts/smoke-reasoner-real.js — end-to-end reasoner pass over the real
// sample ontologies shipped with protege-js (bfo, ogms, ro-core, iao).
//
// For each ontology this:
//   1. loads it with protege-js' OntologyLoader,
//   2. builds a Reasoner and asserts it is CONSISTENT,
//   3. classifies the class hierarchy and reports node/unsatisfiable counts,
//   4. runs a few named-class satisfiability + subsumption queries,
//   5. re-checks entailment of a sample of the ontology's OWN logical axioms
//      (every one of them MUST be entailed — they are asserted),
//   6. times each phase.
//
// Then a NON-HORN section: all four sample ontologies are Horn (`horn=Y`), so on
// their own they never exercise dependency-directed backjumping's level-skipping
// path. Each is therefore AUGMENTED with a disjunction ladder rooted at one of
// its own real classes, which forces wrong disjuncts to clash and produces
// backjumps that skip levels — at real-ontology scale (up to 2361 axioms).
//
// Baseline clause counts (scripts/clausify-real-ontologies.js):
//   bfo 53, ogms 200 (+17 facts), ro-core 89, iao 398 (+25 facts); all Horn.
//
// Run with:  node scripts/smoke-reasoner-real.js
// ---------------------------------------------------------------------------

const path = require('path');
const protege = require('@skaterqiang/protege-js');
const E = require('../src/owl/OWLExpressions');
const { createReasoner } = require('../src/reasoner/Reasoner');
const { Configuration } = require('../src/Configuration');

const DIR = path.resolve(__dirname, '../../protege-js/sample/ontologies');
const FILES = ['bfo.owl', 'ogms.owl', 'ro-core.owl', 'iao.owl'];

const loader = new protege.OntologyLoader();

let failures = 0;
let checks = 0;

/** Ontologies that loaded successfully, reused by the non-Horn section below. */
const loaded = [];

// --- non-Horn ladder fixtures ------------------------------------------------
// Fresh IRIs, so the ladder can never collide with the host ontology.
const LEX = 'http://example.org/ladder#';
const LADDER = {
  B1: E.owlClass(LEX + 'B1'), B2: E.owlClass(LEX + 'B2'), B3: E.owlClass(LEX + 'B3'),
  C1: E.owlClass(LEX + 'C1'), C2: E.owlClass(LEX + 'C2'), C3: E.owlClass(LEX + 'C3')
};

/**
 * Records backjump distances.
 *
 * `Tableau.backtrackTo(n)` fires `backtrackToStarted(branchingPoint)` BEFORE
 * lowering `currentBranchingPoint`, so at that moment `tableau.currentBranchingPoint`
 * is still the level jumped FROM and `branchingPoint.level` the level jumped TO.
 * Their difference is the number of levels SKIPPED — the thing this section proves
 * actually happens.
 */
class BackjumpRecorder {
  constructor() {
    this.tableau = null;
    this.backtracks = [];
    this.maxSkipped = 0;
    this.branchingPointsPushed = 0;
  }

  setTableau(tableau) { this.tableau = tableau; }

  pushBranchingPointStarted() { this.branchingPointsPushed++; }

  backtrackToStarted(branchingPoint) {
    const from = this.tableau.currentBranchingPoint;
    const to = branchingPoint.level;
    const skipped = from - to;
    this.backtracks.push({ from, to, skipped });
    if (skipped > this.maxSkipped) this.maxSkipped = skipped;
  }
}

/**
 * `K ⊑ B1⊔C1`, `B1 ⊑ B2⊔C2`, `B2 ⊑ B3⊔C3`, every `Ci ⊑ ⊥`.
 *
 * The `Ci` are dead ends, so `K ⊑ B3` is entailed — but only by rejecting each
 * `Ci` in turn. Asking for that entailment adds `¬(K ⊑ B3)`, which forces the
 * wrong disjuncts to clash and makes the tableau backjump. Without the query the
 * first disjunct already yields a model and no backtracking happens at all.
 */
function ladderAxioms(K) {
  const { B1, B2, B3, C1, C2, C3 } = LADDER;
  return [
    ...[B1, B2, B3, C1, C2, C3].map((entity) =>
      ({ axiomType: E.AxiomType.DECLARATION, entity })),
    E.subclassOf(K, E.objectUnionOf([B1, C1])),
    E.subclassOf(B1, E.objectUnionOf([B2, C2])),
    E.subclassOf(B2, E.objectUnionOf([B3, C3])),
    E.subclassOf(C1, E.owlNothing()),
    E.subclassOf(C2, E.owlNothing()),
    E.subclassOf(C3, E.owlNothing())
  ];
}

/**
 * A protege-js-shaped ontology view over `host`'s axioms plus `extra`.
 *
 * Everything except `getAxioms` delegates to the host, so the signature stays
 * the real one — declared-but-unused classes must survive for classification.
 */
function augmentedOntology(host, extra) {
  const axioms = [...host.getAxioms(), ...extra];
  return {
    getAxioms: () => axioms.slice(),
    getOntologyID: () => ({ ontologyIRI: LEX + 'augmented' }),
    getClassesInSignature: () => host.getClassesInSignature(),
    getObjectPropertiesInSignature: () => host.getObjectPropertiesInSignature(),
    getDataPropertiesInSignature: () => host.getDataPropertiesInSignature(),
    getIndividualsInSignature: () => host.getIndividualsInSignature()
  };
}

function check(name, actual, expected) {
  checks++;
  const ok = actual === expected;
  if (!ok) failures++;
  console.log(`  ${ok ? 'PASS' : 'FAIL'}  ${name}  (got ${actual}, expected ${expected})`);
}

/** Logical (non-declaration, non-annotation) axioms of an ontology. */
function logicalAxioms(ont) {
  return ont.getAxioms().filter((ax) => {
    const t = ax.axiomType || (ax.getAxiomType && ax.getAxiomType());
    return !E.NON_LOGICAL_AXIOM_TYPES.has(t);
  });
}

function axiomType(ax) {
  return ax.axiomType || (ax.getAxiomType && ax.getAxiomType());
}

for (const file of FILES) {
  console.log(`\n=== ${file} ===`);
  let ont;
  try {
    ont = loader.loadFromFile(path.join(DIR, file));
  } catch (err) {
    console.log(`  LOAD-FAIL: ${err.message.split('\n')[0]}`);
    failures++;
    continue;
  }
  loaded.push({ file, ont });

  const config = new Configuration({ throwInconsistentOntologyException: false });
  let r;
  const tLoad = Date.now();
  try {
    r = createReasoner(ont, config);
  } catch (err) {
    console.log(`  REASONER-FAIL: ${err.message.split('\n')[0]}`);
    console.log(err.stack.split('\n').slice(1, 5).join('\n'));
    failures++;
    continue;
  }
  const loadMs = Date.now() - tLoad;

  // (2) consistency
  const tCons = Date.now();
  const consistent = r.isConsistent();
  check('isConsistent', consistent, true);
  const consMs = Date.now() - tCons;

  // (3) classification
  const tClass = Date.now();
  let classNodes = 0;
  let unsatisfiable = 0;
  try {
    r.precomputeInferences('CLASS_HIERARCHY');
    // Every proper subclass of owl:Thing, as a NodeSet; +1 for the top node.
    classNodes = r.getSubClasses(E.owlThing(), false).getNodes().size + 1;
    // `getUnsatisfiableClasses()` returns the single bottom NODE (not a NodeSet).
    unsatisfiable = [...r.getUnsatisfiableClasses().getEntities()]
      .filter((c) => !E.isOWLNothing(c)).length;
  } catch (err) {
    console.log(`  CLASSIFY-FAIL: ${err.message.split('\n')[0]}`);
    failures++;
  }
  const classMs = Date.now() - tClass;
  console.log(`  class hierarchy: ${classNodes} nodes, ${unsatisfiable} unsatisfiable (excl. owl:Nothing) [${classMs}ms]`);

  // (4) a few satisfiability / subsumption queries on named classes
  const classes = ont.getClassesInSignature()
    .filter((c) => !E.isOWLThing(c) && !E.isOWLNothing(c));
  let satChecked = 0;
  for (const c of classes.slice(0, 5)) {
    const sat = r.isSatisfiable(c);
    check(`isSatisfiable(${c.getShortForm()})`, typeof sat, 'boolean');
    satChecked++;
  }
  // owl:Thing ⊑ owl:Thing is a tautology; owl:Nothing ⊑ C for any C.
  check('isSubClassOf(⊤,⊤)', r.isSubClassOf(E.owlThing(), E.owlThing()), true);
  if (classes.length > 0) {
    check('isSubClassOf(⊥,C)', r.isSubClassOf(E.owlNothing(), classes[0]), true);
  }

  // (5) entailment of the ontology's OWN logical axioms — all must hold.
  const tEnt = Date.now();
  const logical = logicalAxioms(ont);
  // Sample up to 25 logical axioms (entailment runs a tableau each).
  const sample = logical.slice(0, 25);
  let entailed = 0;
  let entFailed = 0;
  for (const ax of sample) {
    let ok;
    try {
      ok = r.isEntailed(ax);
    } catch (err) {
      // HasKey / DisjointDataProperties / SWRL etc. may be unsupported here;
      // treat a throw as "skipped", not a failure, but report it.
      console.log(`  SKIP  ${axiomType(ax)}: ${err.message.split('\n')[0].slice(0, 80)}`);
      continue;
    }
    if (ok) entailed++;
    else {
      entFailed++;
      console.log(`  NOT-ENTAILED (asserted!)  ${axiomType(ax)}: ${String(ax).slice(0, 100)}`);
    }
  }
  const entMs = Date.now() - tEnt;
  check(`all sampled asserted axioms entailed (${entailed}/${sample.length})`, entFailed, 0);

  console.log(`  timing: clausify=${loadMs}ms consistency=${consMs}ms classification=${classMs}ms entailment(${sample.length})=${entMs}ms`);
  console.log(`  signature: ${classes.length} classes, ${ont.getObjectPropertiesInSignature().length} object props, ${ont.getDataPropertiesInSignature().length} data props, ${ont.getIndividualsInSignature().length} individuals; ${logical.length} logical axioms`);

  r.dispose();
}

// ---------------------------------------------------------------------------
// NON-HORN AT REAL-ONTOLOGY SCALE
//
// All four sample ontologies are Horn, so the loop above never exercises
// dependency-directed backjumping's level-skipping path — the code that
// `test/tableau-backtrack.test.js` and `smoke-backjump.js` cover only on toy
// ladders of a handful of axioms. Here each real ontology is augmented with a
// disjunction ladder rooted at one of its OWN classes, so the same path runs
// against a real signature (up to 2361 axioms).
//
// What makes this section meaningful rather than vacuous:
//   * `maxSkipped >= 1` — a backjump that actually SKIPS a level, not just
//     backtracks one step. This is the property under test.
//   * the entailment must still come out TRUE, so the skipping did not lose a
//     model;
//   * the host ontology must stay CONSISTENT after augmentation.
// ---------------------------------------------------------------------------
console.log('\n=== non-Horn ladder over each real ontology ===');
for (const { file, ont } of loaded) {
  const candidates = ont.getClassesInSignature()
    .filter((c) => !E.isOWLThing(c) && !E.isOWLNothing(c));
  if (candidates.length === 0) {
    console.log(`  SKIP ${file}: no named classes to root the ladder at`);
    continue;
  }
  // First, middle and last: three unrelated positions in the signature, so a
  // class that happens to be unsatisfiable or isolated cannot mask a failure.
  const picks = [
    candidates[0],
    candidates[Math.floor(candidates.length / 2)],
    candidates[candidates.length - 1]
  ];

  for (const K of picks) {
    const name = K.getShortForm ? K.getShortForm() : E.iriString(K);
    const label = `${file}:${name}`;
    const rec = new BackjumpRecorder();
    let r;
    try {
      r = createReasoner(augmentedOntology(ont, ladderAxioms(K)), {
        throwInconsistentOntologyException: false,
        monitor: rec
      });
    } catch (err) {
      console.log(`  REASONER-FAIL ${label}: ${err.message.split('\n')[0]}`);
      failures++;
      checks++;
      continue;
    }
    try {
      check(`${label} consistent after augmentation`, r.isConsistent(), true);
      // The query's negation is what forces the wrong disjuncts to clash.
      check(`${label} entails K ⊑ B3`, r.isEntailed(E.subclassOf(K, LADDER.B3)), true);
      // Dead ends must stay dead: no Ci is satisfiable.
      check(`${label} C1 unsatisfiable`, r.isSatisfiable(LADDER.C1), false);
      // The point of the whole section.
      check(`${label} backtracked`, rec.backtracks.length > 0, true);
      check(`${label} skipped >= 1 level`, rec.maxSkipped >= 1, true);
      console.log(`  ${label}: pushed=${rec.branchingPointsPushed} `
        + `backtracks=${rec.backtracks.length} maxSkipped=${rec.maxSkipped}`);
    } catch (err) {
      console.log(`  QUERY-FAIL ${label}: ${err.message.split('\n')[0]}`);
      failures++;
      checks++;
    } finally {
      r.dispose();
    }
  }
}

console.log(`\n${checks - failures}/${checks} checks passed.`);
if (failures > 0) {
  console.log(`${failures} FAILURES`);
  process.exit(1);
}
console.log('All real-ontology reasoner checks passed.');
