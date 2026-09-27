# Changelog

All notable changes to `dl-js-reasoner` are documented in this file.
The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added
- **Ported the blocking signature cache** (`src/blocking/BlockingSignatureCache.js`,
  `src/blocking/BlockingSignature.js`, `src/blocking/SetFactory.js`). HermiT's
  `BlockingSignatureCache` remembers the blocking labels ("signatures") of
  blocker nodes from completed models, so a later node whose signature matches a
  remembered one can be blocked immediately — a pure performance optimisation
  that never changes reasoning results. The faithful port internes labels
  through a `SetFactory` port (canonical sorted label sets with reference
  counting) and compares them by identity, exactly as HermiT compares
  `SetFactory`-interned sets with `==`. A signature-blocked node is recorded
  against the new `Node.SIGNATURE_CACHE_BLOCKER` sentinel. The cache is skipped
  when the ontology has nominals and is only consulted while no additional
  (query) ontology is in effect, matching HermiT's guards.
- `test/blocking-signature-cache.test.js` — 8 unit tests pinning the bucket
  hash (against Java's `String.hashCode`), the `SIGNATURE_CACHE_BLOCKER`
  sentinel, the add/contains/resize mechanics, label interning by identity, and
  the `canBeBlocked` / `NODE_TYPE` eligibility guards.

### Changed
- **`blockingSignatureCacheType` now defaults to `CACHED`** (matching HermiT),
  and `CACHED` is **honoured** rather than degrading to no cache. This removes
  the previous deviation in which the cache was unported and the default was
  `NOT_CACHED` to keep a stock `Configuration` warning-free. A core-strategy
  request (`SIMPLE_CORE`/`COMPLEX_CORE`) that degrades to `ANYWHERE` now
  installs the cache on that fallback, so only the single core-degradation
  warning fires (previously two warnings fired).
  methods). The class does not appear in HermiT's `known-test-failures.txt`
  (`org.semanticweb.HermiT.reasoner.*` has no entries there at all), so every
  assertion is a clean oracle. It is the only suite that drives the whole rule
  pipeline end to end: `SWRLRule → OWLNormalization._visitSWRLRule →
  RuleNormalizer → OWLClausification.RuleConverter → DLClause.getSafeVersion →
  HyperresolutionManager`. Since this port has no method overloading, rules are
  built from `src/structural/RuleNormalizer`'s own exported factories
  (`RN.classAtom`, `RN.objectPropertyAtom`, `RN.dataRangeAtom`,
  `new RN.SWRLVariable('x')`, …) rather than hand-rolled object literals, and
  `OWLNormalization._visitAxiom` detects them structurally via
  `Array.isArray(axiom.body) && Array.isArray(axiom.head)`. The file preserves
  four upstream oddities verbatim — `testRuleNonSimple`'s commented-out `s`
  assertion, `testNegativeBodyDataRange`'s `OWLClass C = …getOWLClass(NS + "B")`
  binding, `testRuleWithConstants2`'s single-`&` typo (which is *not*
  reproduced, since it would not compile here), and `testDiffrentFrom2`'s
  misspelling. It found defects 4–7 below; each of the four fixes was
  negative-controlled, and with any one disabled one or two of the 24 oracles
  fail.
- 10 unit tests in `test/datatype-constraints.test.js` pinning defects 5–7 below
  at the `DatatypeReasoning` level: `numericSubsumes` ranking the integer tower
  against `xsd:decimal`/`xsd:double` and ordering the twelve facet-derived
  subtypes by their value-space bounds; `constantMembership` deciding a CONCRETE
  value by magnitude (`25 ∈ xsd:int` even though `xsd:integer ⊄ xsd:int`);
  `isIntegerType` / `inIntegerBounds` including the three-valued refusal on
  unparsable and non-safe-integer inputs; a negative facet restriction that
  excludes the whole finite space clashing while one that leaves a survivor does
  not; and `enumerateFiniteSpace` skipping an opaque `InternalDatatype` positive
  and clamping `xsd:byte[0..300]` to `0..127`.
- `test/hermit-oracles-2.test.js` — 20 more **differential tests against
  HermiT's own JUnit oracles**, this time the *reasoner* ones: 8 ported verbatim
  from `org.semanticweb.HermiT.reasoner.ComplexConceptTest`, 8 from
  `org.semanticweb.HermiT.reasoner.OWLReasonerTest`, plus 4 regression tests
  pinning the third defect (see **Fixed**) at its source. Neither source class
  appears in HermiT's `known-test-failures.txt`, so every assertion is a clean
  oracle. The file reproduces `AbstractOntologyTest`'s `NS = "file:/c/test.owl#"`
  and its `SL` / `PL` / `TL` literal helpers, `AbstractReasonerTest`'s
  `assertABoxSatisfiable` / `assertSubsumedBy` / `assertSatisfiable` /
  `assertInstanceOf` (the last is `hasType(i, desc, false)`, NOT
  intersection-satisfiability), and `AbstractHermiTTest.assertContainsAll` —
  which is EXACT set equality, not a subset check. It also ports
  `OWLReasonerTest`'s two incremental oracles against the mutable-ontology mock,
  preserving HermiT's own upstream typo where `cDirect` is computed with
  `getSuperClasses(c, false)`. Both datatype oracles are load-bearing: with the
  `rdf:PlainLiteral` split disabled, exactly those two and the four regression
  tests fail while the other fourteen still pass.
- `test/hermit-oracles.test.js` — 27 **differential tests against HermiT's own
  JUnit oracles**, ported verbatim from `SimpleRolesTest` (4), `RIATest` (11),
  `ClausificationTest` (2) and `EntailmentTest` (10). Unlike every other test
  file, whose expectations were derived from the reference *source*, these come
  from the reference *test suite*, mirroring `AbstractReasonerTest`'s
  `assertSimple` / `assertRegular` / `assertEntails` helpers and matching the
  identical `Non-simple property '…'` and
  `The given property hierarchy is not regular` messages. Together with
  `hermit-oracles-2.test.js` and `hermit-oracles-3.test.js` this suite found all
  seven defects listed under **Fixed** below. Two oracles deliberately diverge
  and are
  documented in place: `ClausificationTest.testHasKeys` (HermiT's control file is
  stale — it is listed in `known-test-failures.txt`; our clause differs only in
  variable numbering) and `EntailmentTest.testValidBlankNodesWithNominals`
  (HermiT's `EntailmentChecker.visit(OWLObjectPropertyAssertionAxiom)` *replaces*
  rather than merges its per-anonymous-individual edge map, so its oracle depends
  on that bug; our merge is what OWL 2 Structural Specification §11.2 requires).
- 7 unit tests in `test/datatype-constraints.test.js` pinning the step-2 fix
  below at the `checkConstraintsSatisfiable` level: facet-free restrictions from
  disjoint groups clash, order-independently and mixed with `LiteralDataRange`;
  overlapping restrictions do not; facets are irrelevant to disjointness; an
  uninterpretable base datatype never clashes; the
  `internal:anonymous-constants` group is disjoint from every real one; and the
  boolean finite-space enumeration in step 4 — newly reachable now that
  `namedPos` includes restrictions — still behaves correctly.
- `LICENSE` — the full LGPL-3.0-or-later text (LGPL-3.0 plus the GPL-3.0 it
  incorporates), matching the `license` field in `package.json` and HermiT's
  own licensing.
- `.gitignore` and this `CHANGELOG.md` (release/packaging hygiene).
- `test/edge-cases.test.js` — 13 degenerate-input regression guards (empty and
  declaration-only ontologies, trivial subsumptions, `⊤ ⊑ ⊥` inconsistency,
  duplicate axioms, singleton/self-contradictory `differentIndividuals`,
  self-referential roles under functionality, functional/inverse-functional
  clashes, a 20-deep subclass chain, direct-vs-all `getTypes`, an empty-string
  literal, and querying a disposed reasoner). No defects were found while
  probing these; the guards pin the already-correct behaviour.

### Fixed
- **`RuleNormalizer` now dispatches data-range atoms to the data-range
  normalizers** (`structural/RuleNormalizer.js`: `_processAtom`,
  `case SWRLAtomType.DATA_RANGE`). HermiT's `ExpressionManager` *overloads*
  `getNNF` and `getSimplified` for `OWLDataRange`, so Java's
  `visit(SWRLDataRangeAtom)` reaches `DataRangeNNFVisitor` /
  `DataRangeSimplificationVisitor`. This port cannot overload, so the two
  families have distinct names (`getNNF`/`getSimplified` for class expressions,
  `getDataRangeNNF`/`getDataRangeSimplified` for data ranges) — and the
  `DATA_RANGE` case was calling the CLASS ones. Their switches have no
  `DATA_INTERSECTION_OF` / `DATA_UNION_OF` / `DATA_COMPLEMENT_OF` cases and fall
  through to `default: return d`, so a raw `DataIntersectionOf` survived into
  `OWLClausification.DataRangeConverter.convertDataRange`, which threw
  `Internal error: invalid normal form (convertDataRange(DataIntersectionOf(…)))`.
  The neighbouring CLASS case is correct and unchanged — it really does receive a
  class expression. Found by `RulesTest.testPositiveBodyDataRange` and
  `RulesTest.testNegativeBodyDataRange`.
- **`checkConstraintsSatisfiable` step 6 now consults EVERY negative predicate,
  not just `ConstantEnumeration`s** (`datatypes/DatatypeReasoning.js`). The step
  enumerates the finite positive space and keeps the first candidate no negative
  definitely excludes, but it filtered the negatives down to
  `ConstantEnumeration`s first. A negative `DatatypeRestriction` can exclude the
  whole space on its own — `xsd:integer[6..9]` with `¬xsd:integer[≥5]` and
  `¬xsd:decimal[≤10]` has no solution at all — yet the node was reported
  satisfiable, losing the clash and with it every conclusion the reference
  implementation draws from the alternative branch. The filter is now
  `negatives.every(p => !constantDefinitelySatisfies(c, p))`, a strict
  generalisation: for a `ConstantEnumeration` negative,
  `constantDefinitelySatisfies` reduces to exactly the old
  `p.constants.some(k => constantsEqual(k, c))` test. Undecidable negatives still
  KEEP the candidate, so the over-approximation continues to err towards
  "satisfiable" rather than inventing a clash. Found by
  `RulesTest.testNegDRInHead`.
- **Integer-derived XSD datatypes are now ranked, and a concrete value is
  decided by magnitude** (`datatypes/DatatypeReasoning.js`: new
  `INTEGER_BOUNDS` table, `xsdLocalName`, `inIntegerBounds`, `isIntegerType`,
  `_boundsOf`, `boundsContain`; rewritten `numericSubsumes`; extended
  `constantMembership`). `numericSubsumes`'s ranking function recognised only
  `xsd:integer` and names ending in `Integer`, returning −1 for all twelve
  facet-derived subtypes (`xsd:int`, `xsd:long`, `xsd:short`, `xsd:byte`,
  `xsd:nonNegativeInteger`, `xsd:positiveInteger`, `xsd:nonPositiveInteger`,
  `xsd:negativeInteger`, `xsd:unsignedInt`, `xsd:unsignedLong`,
  `xsd:unsignedShort`, `xsd:unsignedByte`). So
  `constantMembership("25"^^xsd:integer, xsd:int)` was `false` and no rule or
  restriction over a derived integer type ever fired. The bounds table is exactly
  the `minInclusive`/`maxInclusive` facets XSD 1.1 gives each type, so it adds no
  new semantics — it makes explicit what the datatype definitions already say
  (HermiT gets the same knowledge from its `datatypes/integer` handler family,
  which this port does not carry). `numericSubsumes` now ranks the whole integer
  family at one rung and orders same-rung types by bounds, while
  `constantMembership` additionally decides a CONCRETE constant by magnitude —
  a type-lattice question and a value question are different, and
  `xsd:integer ⊄ xsd:int` is correct even though `25 ∈ xsd:int`.
  `xsd:long`'s and `xsd:unsignedLong`'s extremes exceed
  `Number.MAX_SAFE_INTEGER` and are stored as the nearest doubles, which is
  harmless because `inIntegerBounds` refuses to decide any value that is not
  itself a safe integer. Found by `RulesTest.testRuleWithDatatypes2` and
  `RulesTest.testNegDRInHead`.
- **`enumerateFiniteSpace` now skips an opaque `InternalDatatype` positive
  instead of bailing out, and clamps to the base datatype's own value space**
  (`datatypes/DatatypeReasoning.js`). The function returned `null` whenever ANY
  positive was not a `LiteralDataRange` or `DatatypeRestriction` — in particular
  an opaque internal datatype such as `internal:defdata#0`, which normalization
  introduces for a complex data range. Step 7 then defaulted to "satisfiable",
  so `+xsd:integer[6..9] ; +internal:defdata#0 ; -xsd:decimal[maxInclusive "10"]`
  produced no clash and `hasType(a, B, false)` returned `false`. Constraints on
  one node are conjoined, so every positive can only NARROW the space: dropping
  an opaque one yields a superset of the real one, which is the safe direction
  for both callers — `checkConstraintsSatisfiable` may over-report satisfiable
  but never invents a clash, and `DatatypeManager._hasPerfectMatching` gets a
  space that is too large rather than too small. The same function now also
  clamps the facet bounds to the base datatype's range, so `xsd:byte[0..300]`
  enumerates `0..127` rather than offering candidates no value of the space can
  be. Found by `RulesTest.testPositiveBodyDataRange`.
- **`rdf:PlainLiteral` lexical forms are now split at their language tag**
  (`owl/OWLExpressions.js`: `literal()`). `rdf:PlainLiteral` carries its
  language tag *inside* the lexical form — `"abc@en-gb"` — and OWL API parses
  that out at construction time, so HermiT never sees the `@`. Three independent
  authorities agree on the rule: OWL API's
  `OWLDataFactoryInternalsImplNoCache.getOWLLiteral(String, OWLDatatype)` splits
  at `lastIndexOf('@')` and falls back to `xsd:string` when there is no
  separator; `OWLLiteral.getLiteral()`'s javadoc states that
  `"abc@"^^rdf:PlainLiteral` returns `"abc"`; and HermiT's own
  `RDFPlainLiteralDatatypeHandler.parseLiteral` performs the identical split,
  mapping an *empty* tag to a bare `String` — i.e. the `xsd:string` data value.
  Skipping the split left `lexicalValue === 'abc@'` with
  `isRDFPlainLiteral() === true`, so
  `OWLClausification.convertLiteral` appended a *second* separator and emitted
  `Constant("abc@@", rdf:PlainLiteral)` — a constant equal to neither `"abc"`
  nor `PL("abc","")`. That broke
  `ComplexConceptTest.testConceptWithDatatypes` and
  `OWLReasonerTest.testGetDataPropertyValues`, which each assert the two
  spellings denote ONE value. `QuerySpec.literalToTerm` and
  `Reasoner.constantToLiteral` needed no change: both key off
  `isRDFPlainLiteral()`, which is now correct. Note that HermiT builds against
  OWL API **4.2.8**, whose `OWLLiteralImplPlain.isRDFPlainLiteral()` returns
  `true` for a language-tagged literal (v5 returns `false` and reports
  `rdf:langString`); this port deliberately follows the v4 convention, which is
  also HermiT's internal `Constant(lex + "@" + lang, rdf:PlainLiteral)` spelling.
- **An untagged, untyped literal now defaults to `xsd:string`, not
  `rdf:PlainLiteral`** (`owl/OWLExpressions.js`: `literal()` and
  `OWLLiteral.getDatatypeIRI()`). OWL 2 Syntax §2.3 gives `"abc"` the datatype
  `xsd:string`, and OWL API's `getOWLLiteral(String)` builds it that way, so
  HermiT's `convertLiteral` reaches its `else` branch and emits
  `Constant.create("abc", xsd:string)`. The old default made `"test"` and
  `"test"^^xsd:string` two *different* constants, which broke
  `EntailmentTest.testBlankWithDTs3`. Language-tagged literals still map to
  `rdf:PlainLiteral`. This is a behavioural change, but no existing test or
  smoke check relied on the old default (every `literal()` call site passed an
  explicit datatype or language tag).
- **The disjoint-datatype clash now sees facet-free `DatatypeRestriction`s**
  (`datatypes/DatatypeReasoning.js`, new exported helper `datatypeIRIOf`).
  `checkConstraintsSatisfiable` step 2 filtered positives on `LiteralDataRange`,
  but `OWLClausification._convertDatatype` turns every bare datatype into a
  facet-free `DatatypeRestriction` (`xsd:string[]`) — exactly as HermiT does,
  which is why its `DatatypeChecker.DVariable.addDataRange` compares
  `getDatatypeURI()` on restrictions. The clash was consequently **unreachable
  from real input**: a concrete node carrying both `xsd:string[]` and
  `xsd:integer[]` was reported satisfiable, which made
  `EntailmentTest.testHasKey` answer `false` and reported a genuinely
  inconsistent ABox as consistent. Facets are still ignored here — disjointness
  is a property of the base value spaces — and an uninterpretable base datatype
  lands in `GROUP.OTHER`, for which `datatypesDisjoint` returns `false`, so the
  opaque restrictions handled by
  `applyUnknownDatatypeRestrictionSemantics` cannot manufacture a clash.

## [0.2.0]

### Added
- **Conjunctive query answering** (`src/datalog/`): `DatalogEngine`,
  `ConjunctiveQuery`, `QuerySpec`, wired into `Reasoner` (`answerQuery`,
  `answerQueryAsStrings`, `createConjunctiveQuery`, `getDatalogEngine`) and
  `ProtegeAdapter` (`query`, `answerQuery`, `createQuery`). The first four
  `test/datalog-query.test.js` tests are a direct port of HermiT's
  `DatalogEngineTest` oracles.
- **Command-line front end** (`src/cli/` + `bin/dl-js-reasoner.js`): a port of
  HermiT's `CommandLine`/`Options`/`Writer` with `Getopt` clustering,
  abbreviation and `--` handling, the 31-option table, `--dump-clauses`,
  hierarchy dumping/printing in functional-syntax style, and a
  `REASONER_VERSION` derived from `package.json`.
- **Blocking configuration honoured**: `createBlockingStrategy` selects
  `AnywhereBlocking`/`AncestorBlocking` per `BLOCKING_STRATEGY_TYPE`, all three
  `DIRECT_BLOCKING_TYPE` values are implemented, and unported choices
  (`SIMPLE_CORE`/`COMPLEX_CORE`, `CACHED`) degrade loudly via
  `configuration.warningMonitor` instead of being silently ignored.
- **Monitor package completed** (`src/monitor/`, 6 classes): `TimerWithPause`
  (TTY-gated pause) and `MemoryConsumptionMonitor` (estimated per-arity table
  memory) joined `TableauMonitorAdapter`, `CountingMonitor`, `Timer` and
  `TableauMonitorFork`; `Reasoner.createTableau` now selects and forks monitors
  exactly as HermiT does, and `Configuration.monitorOptions` configures them.
- **Façade accessors**: `Reasoner.getDataFactory()` (returns the interned
  `owl/OWLExpressions` factory module) and `getRootOntology()`, covered by
  `test/facade.test.js`.
- **Role classification** (`QuasiOrderClassificationForRoles`): object-property
  hierarchy with told-inclusion seeding and inverse mirroring.
- **Incremental ABox flush** (`ReducedABoxOnlyClausification`): `flush()`
  re-clausifies only the changed ABox when possible.
- **Caching**: per-individual realisation type cache, same-as equivalence-class
  cache with union-find, and `directSuperConceptNodesCache`, all reset by
  `clearInferenceCaches()`.

### Fixed
- **Datatype soundness**: a data range against its own negation now clashes
  (previously `R ∧ ¬R` could be reported satisfiable); three-valued
  `constantMembership` splits `null` (undecidable) in the only direction that
  cannot manufacture a spurious clash.
- `AtomicRole.getInverse()` special-cases TOP/BOTTOM object role (returns
  `this`), matching HermiT.
- Same-as/realisation cache flags are reset on incremental flush (previously
  orphaned from `clearInferenceCaches()`).

## [0.1.0]

### Added
- Initial port of HermiT's hypertableau to pure JavaScript: normalization and
  clausification, the tableau calculus (hyperresolution, existential expansion
  with `CreationOrder`/`IndividualReuse` strategies, anywhere/ancestor blocking
  with single/pairwise direct-blocking checkers, nominal introduction,
  merging, non-Horn backjumping with dependency sets and branching-point
  snapshots), class-hierarchy construction and classification, realisation,
  the entailment checker, `DatatypeDefinition` semantics, SWRL rule
  normalization (built-ins throw, matching HermiT), and the protege-js
  adapter/façade (`createReasoner`).

<!-- No remote repository is configured yet; add compare/tag links here once one exists. -->
