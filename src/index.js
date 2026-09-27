'use strict';

// ---------------------------------------------------------------------------
// src/index.js — public entry point for DL-JS-REASONER.
//
// A JavaScript port of HermiT's hypertableau reasoner. It consumes
// protege-js-shaped OWL axioms / class expressions (plain objects with
// `axiomType`, `type`, `entityType` fields), so an ontology parsed by
// protege-js can be handed straight to `createReasoner`.
//
// Typical use:
//
//   const protege = require('@skaterqiang/protege-js');
//   const { createReasoner, E } = require('dl-js-reasoner');
//
//   const ont = new protege.OntologyLoader().loadFromFile('pizza.owl');
//   const r = createReasoner(ont);
//   r.isConsistent();                                  // true
//   r.isSatisfiable(E.owlClass('http://...#MeatEater'));
//   r.isEntailed(E.subclassOf(A, B));
//   r.getSuperClasses(A, true).getFlattened();
//
// The reasoner is the OWL API's `OWLReasoner` in spirit: `isConsistent`,
// `isSatisfiable`, `isSubClassOf`, `getSuperClasses`/`getSubClasses`,
// `classifyClasses`, `hasType`/`getTypes`, `isSameIndividual`,
// `isEntailed`, plus property-characteristic and property-hierarchy queries.
// ---------------------------------------------------------------------------

const Reasoner = require('./reasoner/Reasoner');
const { Node, NodeSet } = require('./reasoner/Node');
const { EntailmentChecker } = require('./reasoner/EntailmentChecker');
const Configuration = require('./Configuration');
const { Prefixes } = require('./Prefixes');
const E = require('./owl/OWLExpressions');
const P = require('./model/DLPredicate');
const { DLOntology } = require('./model/DLOntology');
const { OWLClausification } = require('./structural/OWLClausification');
const {
  ReducedABoxOnlyClausification,
  INDIVIDUAL_AXIOM_TYPES,
  INCREMENTAL_CLASS_EXPRESSION_TYPES
} = require('./structural/ReducedABoxOnlyClausification');
const { Tableau } = require('./tableau/Tableau');
const { DatalogEngine, NullExistentialExpansionStrategy } = require('./datalog/DatalogEngine');
const {
  ConjunctiveQuery,
  QueryResultCollector,
  CollectingQueryResultCollector
} = require('./datalog/ConjunctiveQuery');
const { buildQuerySpec, toAtom, toTerm, querySpecToString } = require('./datalog/QuerySpec');
const { createAtom } = require('./model/Atom');
const {
  Term,
  Variable,
  Individual,
  Constant,
  createVariable,
  createIndividual,
  createConstant
} = require('./model/Term');
const { TableauMonitorAdapter } = require('./monitor/TableauMonitorAdapter');
const { CountingMonitor } = require('./monitor/CountingMonitor');
const { Timer } = require('./monitor/Timer');
const { TimerWithPause } = require('./monitor/TimerWithPause');
const { MemoryConsumptionMonitor } = require('./monitor/MemoryConsumptionMonitor');
const { TableauMonitorFork } = require('./monitor/TableauMonitorFork');
const { ProtegeAdapter, reasonerFor } = require('./adapter/protege');
const { HierarchyDumperFSS } = require('./hierarchy/HierarchyDumperFSS');
const { HierarchyPrinterFSS } = require('./hierarchy/HierarchyPrinterFSS');
const CommandLine = require('./cli/CommandLine');
const CliWriter = require('./cli/Writer');
const CliOptions = require('./cli/Options');

module.exports = {
  // ---- the reasoner façade (the thing almost everyone wants) ----------------
  Reasoner: Reasoner.Reasoner,
  createReasoner: Reasoner.createReasoner,
  createNonBufferingReasoner: Reasoner.createNonBufferingReasoner,
  InconsistentOntologyException: Reasoner.InconsistentOntologyException,
  FreshEntitiesException: Reasoner.FreshEntitiesException,
  EntailmentChecker,

  // ---- result containers ----------------------------------------------------
  Node,
  NodeSet,

  // ---- configuration --------------------------------------------------------
  Configuration: Configuration.Configuration,
  PrepareReasonerInferences: Configuration.PrepareReasonerInferences,
  FRESH_ENTITY_POLICY: Configuration.FRESH_ENTITY_POLICY,
  INFERENCE_TYPE: Configuration.INFERENCE_TYPE,
  INDIVIDUAL_NODE_SET_POLICY: Configuration.INDIVIDUAL_NODE_SET_POLICY,
  BLOCKING_STRATEGY_TYPE: Configuration.BLOCKING_STRATEGY_TYPE,
  BLOCKING_SIGNATURE_CACHE_TYPE: Configuration.BLOCKING_SIGNATURE_CACHE_TYPE,
  DIRECT_BLOCKING_TYPE: Configuration.DIRECT_BLOCKING_TYPE,
  EXISTENTIAL_STRATEGY_TYPE: Configuration.EXISTENTIAL_STRATEGY_TYPE,
  TABLEAU_MONITOR_TYPE: Configuration.TABLEAU_MONITOR_TYPE,
  Prefixes,

  // ---- OWL expression / axiom layer ----------------------------------------
  // `E` is the whole OWLExpressions module: entity + class-expression + axiom
  // factories, type registries (`AxiomType`, `EntityType`,
  // `ClassExpressionType`) and structural predicates. Re-exported flat too,
  // because `E.owlClass(...)` / `E.subclassOf(...)` are the everyday calls.
  E,
  OWLExpressions: E,
  AxiomType: E.AxiomType,
  EntityType: E.EntityType,
  ClassExpressionType: E.ClassExpressionType,
  NON_LOGICAL_AXIOM_TYPES: E.NON_LOGICAL_AXIOM_TYPES,

  // ---- DL model layer (advanced: build a DLOntology by hand) ----------------
  DLPredicate: P,
  DLOntology,
  OWLClausification,
  // Incremental ABox loading: `ReducedABoxOnlyClausification` translates
  // individual axioms into ground facts WITHOUT touching the TBox/RBox
  // clauses. The two frozen sets are the shape whitelists that
  // `Reasoner.canProcessPendingChangesIncrementally` gates on; they are
  // exported so callers can predict the flush mode before buffering a change.
  ReducedABoxOnlyClausification,
  INDIVIDUAL_AXIOM_TYPES,
  INCREMENTAL_CLASS_EXPRESSION_TYPES,
  Tableau,

  // ---- conjunctive query answering ------------------------------------------
  // `DatalogEngine` materialises the ABox; `ConjunctiveQuery` matches a
  // conjunction of atoms against it. The everyday route is the spec-based one
  // (`reasoner.query({ select, where })` / `adapter.query(...)`), which needs
  // none of the exports below — they are here for callers who want to build
  // atoms and terms by hand, or to subclass the collector.
  DatalogEngine,
  NullExistentialExpansionStrategy,
  ConjunctiveQuery,
  QueryResultCollector,
  CollectingQueryResultCollector,
  buildQuerySpec,
  toAtom,
  toTerm,
  querySpecToString,
  // Term / Atom factories, so a hand-built query needs no deep requires.
  createAtom,
  Term,
  Variable,
  Individual,
  Constant,
  createVariable,
  createIndividual,
  createConstant,

  // ---- tableau monitors -----------------------------------------------------
  // `TABLEAU_MONITOR_TYPE` selects one of these via `Configuration`; they are
  // exported so they can also be composed by hand (e.g. fork a `CountingMonitor`
  // with a custom one) or subclassed from `TableauMonitorAdapter`.
  TableauMonitorAdapter,
  CountingMonitor,
  Timer,
  TimerWithPause,
  MemoryConsumptionMonitor,
  TableauMonitorFork,

  // ---- protege-js interop ---------------------------------------------------
  ProtegeAdapter,
  /**
   * Convenience: `reasonerFor(ontology, configuration?)` builds a protege-js
   * adapter (which owns a {@link Reasoner}) for a protege-js `OWLOntology`.
   */
  reasonerFor,

  // ---- hierarchy printers (HermiT's FSS output) -----------------------------
  // `HierarchyDumperFSS` writes the flat `SubClassOf( <a> <b> )` form;
  // `HierarchyPrinterFSS` writes the indented, prefix-abbreviated functional
  // syntax document. Both take a `Writer` (see below). The everyday route is
  // `reasoner.dumpHierarchies(out, ...)` / `reasoner.printHierarchies(out, ...)`.
  HierarchyDumperFSS,
  HierarchyPrinterFSS,

  // ---- command-line interface -----------------------------------------------
  // `CommandLine.main(argv, io)` runs the whole CLI in-process and RETURNS an
  // exit code, so it is testable without spawning a child. `bin/dl-js-reasoner`
  // is a two-line wrapper over it.
  CommandLine,
  /** `{ Writer, StringWriter, StreamWriter, FileWriter, openWriter }` */
  CliWriter,
  /** `{ Arg, Option, OptionCode, OptionGroup, options, Getopt, formatOptionHelp, formatOptionsString, breakLines }` */
  CliOptions,

  // ---- metadata -------------------------------------------------------------
  REASONER_NAME: Reasoner.REASONER_NAME,
  REASONER_VERSION: Reasoner.REASONER_VERSION
};
