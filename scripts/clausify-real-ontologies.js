'use strict';

// ---------------------------------------------------------------------------
// scripts/clausify-real-ontologies.js — runs the full structural pipeline
// (normalize → inclusion-manager → clausify) over the real sample ontologies
// shipped with protege-js, and reports clause/fact/signature counts + flags.
// ---------------------------------------------------------------------------

const path = require('path');
const protege = require('@skaterqiang/protege-js');
const C = require('../src/structural/OWLClausification');

const DIR = path.resolve(__dirname, '../../protege-js/sample/ontologies');
const FILES = ['bfo.owl', 'ogms.owl', 'ro-core.owl', 'iao.owl'];

const loader = new protege.OntologyLoader();

function load(file) {
  return loader.loadFromFile(path.join(DIR, file));
}

let totalClauses = 0;
for (const file of FILES) {
  let ont;
  try {
    ont = load(file);
  } catch (err) {
    console.log(`${file.padEnd(14)} LOAD-FAIL: ${err.message.split('\n')[0]}`);
    continue;
  }
  const t0 = Date.now();
  let result;
  try {
    result = new C.OWLClausification().preprocessAndClausify(ont, { ontologyIRI: `urn:${file}` });
  } catch (err) {
    console.log(`${file.padEnd(14)} CLAUSIFY-FAIL: ${err.message.split('\n')[0]}`);
    console.log(err.stack.split('\n').slice(1, 5).join('\n'));
    continue;
  }
  const ms = Date.now() - t0;
  const o = result.dlOntology;
  totalClauses += o.dlClauses.length;
  console.log(
    `${file.padEnd(14)} clauses=${String(o.dlClauses.length).padStart(5)}`
    + ` +facts=${String(o.positiveFacts.length).padStart(4)}`
    + ` -facts=${String(o.negativeFacts.length).padStart(4)}`
    + ` | concepts=${String(o.allAtomicConcepts.size).padStart(4)}`
    + ` objRoles=${String(o.allAtomicObjectRoles.size).padStart(3)}`
    + ` dataRoles=${String(o.allAtomicDataRoles.size).padStart(3)}`
    + ` inds=${String(o.allIndividuals.size).padStart(3)}`
    + ` complexRoles=${String(o.complexObjectRoles.size).padStart(3)}`
    + ` | horn=${o.isHorn ? 'Y' : 'n'} inv=${o.hasInverseRoles ? 'Y' : 'n'}`
    + ` atMost=${o.hasAtMostRestrictions ? 'Y' : 'n'} nom=${o.hasNominals ? 'Y' : 'n'}`
    + ` dt=${o.hasDatatypes ? 'Y' : 'n'} | ${ms}ms`
  );
}
console.log(`\ntotal clauses: ${totalClauses}`);
