#!/usr/bin/env node
'use strict';
/**
 * bin/dl-js-reasoner.js — the executable entry point.
 *
 * Thin wrapper over `src/cli/CommandLine.js`: it strips the node/script prefix
 * from `process.argv`, runs {@link main} and exits with the returned code.
 *
 * All real work lives in `src/cli/CommandLine.js` so it can be driven
 * in-process by the test suite (no child processes, no shell quoting issues).
 */

const { main } = require('../src/cli/CommandLine');

process.exitCode = main(process.argv.slice(2));
