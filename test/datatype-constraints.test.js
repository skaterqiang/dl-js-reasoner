'use strict';

// ---------------------------------------------------------------------------
// test/datatype-constraints.test.js — unit tests for `checkConstraintsSatisfiable`.
//
// REGRESSION for a SOUNDNESS bug. A concrete node holds exactly ONE literal
// value, so `R(v)` and `¬R(v)` cannot both hold — for ANY data range `R`,
// whatever its value space is. No step of `checkConstraintsSatisfiable` used to
// detect that: step 1 (now step 2) compared two POSITIVE named datatypes, and
// every later step needs an enumeration or a finite value space. A positive
// datatype against its own negation therefore fell through to the final
// "default: satisfiable" branch.
//
// That was not merely incomplete — it made the reasoner accept a direct
// contradiction, and it is what caused `MyDT := xsd:string` to report
// `isEntailed(MyDT ≡ xsd:string) === false`: the symmetric-difference branch
// `(¬xsd:string ⊓ MyDT)` derives `xsd:string(v)` and `¬xsd:string(v)` on one
// node, which must clash.
//
// The fix needs no value-space knowledge, so it is sound for the OPAQUE
// predicates (`InternalDatatype`, unknown facet restrictions) that every later
// step has to over-approximate. The tests below pin both the new clash and the
// over-approximations that must NOT start clashing.
//
// A SECOND, MIRROR-IMAGE bug is also pinned here. Over-approximating an opaque
// predicate to "satisfies" is only safe in a POSITIVE test. Steps 3 and 4 (and
// `DatatypeManager._finiteSpace`) also use it NEGATIVELY — "if the candidate is
// in the negated range, reject it" — where a permissive `true` rejects EVERY
// candidate and reports the constraints unsatisfiable. That is a spurious clash,
// which is unsound in the opposite direction: it made
//   range(p) = {red,green},  range(p) = ¬MyDT,  MyDT := xsd:string[unknownFacet]
// report `isConsistent() === false` although nothing implies a contradiction.
// Membership is therefore THREE-VALUED (`constantMembership` → true/false/null),
// split two ways so `null` always keeps the candidate: `constantSatisfies`
// (positive) and `constantDefinitelySatisfies` (negative).
// ---------------------------------------------------------------------------

const test = require('node:test');
const assert = require('node:assert/strict');

const {
  checkConstraintsSatisfiable,
  constantMembership,
  constantSatisfies,
  constantDefinitelySatisfies,
  datatypesDisjoint,
  numericSubsumes,
  enumerateFiniteSpace,
  isIntegerType,
  inIntegerBounds
} = require('../src/datatypes/DatatypeReasoning');
const {
  internLiteralDataRange,
  internInternalDatatype,
  internDatatypeRestriction,
  internConstantEnumeration,
  LiteralDataRange,
  AtomicNegationDataRange
} = require('../src/model/DLPredicate');
const { Constant } = require('../src/model/Term');

const XSD = 'http://www.w3.org/2001/XMLSchema#';
const XS = internLiteralDataRange(XSD + 'string');
const XI = internLiteralDataRange(XSD + 'integer');
const XD = internLiteralDataRange(XSD + 'decimal');
const XB = internLiteralDataRange(XSD + 'boolean');

/** Shorthand for one constraint. */
const pos = (predicate) => ({ predicate, positive: true });
const neg = (predicate) => ({ predicate, positive: false });

// ===========================================================================
// The regression: a data range against its own negation
// ===========================================================================

test('REGRESSION: a data range and its own negation on one node clash', () => {
  for (const r of [XS, XI, XD, XB]) {
    const res = checkConstraintsSatisfiable([pos(r), neg(r)]);
    assert.equal(res.satisfiable, false, `${r} ∧ ¬${r} must be unsatisfiable`);
    assert.match(res.explanation, /its own negation/);
  }
});

test('REGRESSION: the clash does not depend on the constraint ORDER', () => {
  // A Set lookup must find the pair whichever way round they arrive.
  assert.equal(checkConstraintsSatisfiable([pos(XS), neg(XS)]).satisfiable, false);
  assert.equal(checkConstraintsSatisfiable([neg(XS), pos(XS)]).satisfiable, false);
});

test('REGRESSION: the clash fires even when other constraints are present', () => {
  const res = checkConstraintsSatisfiable([
    pos(XI),          // an unrelated positive
    pos(XS),
    neg(XD),          // an unrelated negative
    neg(XS)           // the contradiction
  ]);
  assert.equal(res.satisfiable, false);
});

test('REGRESSION: the clash works for an OPAQUE internal datatype', () => {
  // `InternalDatatype` is a defined datatype whose value space the reasoner
  // cannot inspect — `constantSatisfies` over-approximates it as "possibly
  // satisfies". The negation clash must still hold, because it is a property of
  // ONE node holding ONE value, not of the value space.
  const MyDT = internInternalDatatype('http://example.org/dt#MyDT');
  assert.equal(checkConstraintsSatisfiable([pos(MyDT), neg(MyDT)]).satisfiable, false);
});

test('REGRESSION: the clash works for an unknown facet restriction', () => {
  // `checkFacetValue` returns `null` for an unrecognised facet, so this
  // predicate's value space is unknown too — yet R ∧ ¬R is still a
  // contradiction, because step 1 needs no value-space knowledge at all.
  const odd = internDatatypeRestriction(XSD + 'string', [
    { facetIRI: XSD + 'someFutureFacet', lexicalValue: '1', datatypeIRI: XSD + 'integer' }
  ]);
  assert.equal(checkConstraintsSatisfiable([pos(odd), neg(odd)]).satisfiable, false);
});

// ===========================================================================
// Guards: the fix must NOT make anything else clash
// ===========================================================================

test('two DIFFERENT datatypes, one negated, do not clash', () => {
  // xsd:string ∧ ¬xsd:integer is perfectly satisfiable ("abc").
  assert.equal(checkConstraintsSatisfiable([pos(XS), neg(XI)]).satisfiable, true);
});

test('two positive datatypes from disjoint groups still clash via step 2', () => {
  const res = checkConstraintsSatisfiable([pos(XS), pos(XI)]);
  assert.equal(res.satisfiable, false);
  // The explanation must still name the disjointness, not the negation rule.
  assert.match(res.explanation, /disjoint datatypes/);
});

// ===========================================================================
// REGRESSION: step 2 must see FACET-FREE DatatypeRestrictions too.
//
// `OWLClausification._convertDatatype` turns a bare `xsd:string` into
// `internDatatypeRestriction(XSD+'string', [])` — a `DatatypeRestriction`, NOT
// a `LiteralDataRange` — exactly as HermiT does. Step 2 used to filter on
// `LiteralDataRange` alone, so the ONLY representation the real pipeline
// produces was invisible to it and the clash never fired. That is what made
// HermiT's `EntailmentTest.testHasKey` report `consistent: true`; see
// `test/hermit-oracles.test.js`.
// ===========================================================================

const XS_DR = internDatatypeRestriction(XSD + 'string', []);
const XI_DR = internDatatypeRestriction(XSD + 'integer', []);
const XD_DR = internDatatypeRestriction(XSD + 'decimal', []);

test('REGRESSION: two facet-free restrictions from disjoint groups clash', () => {
  const res = checkConstraintsSatisfiable([pos(XS_DR), pos(XI_DR)]);
  assert.equal(res.satisfiable, false);
  assert.match(res.explanation, /disjoint datatypes/);
});

test('REGRESSION: the clash is order-independent and mixes with LiteralDataRange', () => {
  assert.equal(checkConstraintsSatisfiable([pos(XI_DR), pos(XS_DR)]).satisfiable, false);
  // One side a restriction, the other a literal data range: still disjoint.
  assert.equal(checkConstraintsSatisfiable([pos(XS_DR), pos(XI)]).satisfiable, false);
  assert.equal(checkConstraintsSatisfiable([pos(XS), pos(XI_DR)]).satisfiable, false);
});

test('REGRESSION: overlapping facet-free restrictions do NOT clash', () => {
  // xsd:integer ⊆ xsd:decimal, so "5" witnesses the conjunction.
  assert.equal(checkConstraintsSatisfiable([pos(XI_DR), pos(XD_DR)]).satisfiable, true);
  assert.equal(checkConstraintsSatisfiable([pos(XS_DR)]).satisfiable, true);
});

test('REGRESSION: facets are irrelevant to step-2 disjointness', () => {
  // Disjointness is a property of the BASE value spaces: no string is an
  // integer whatever bounds are placed on either.
  const minLen = internDatatypeRestriction(XSD + 'string', [
    { facetIRI: XSD + 'minLength', lexicalValue: '1', datatypeIRI: XSD + 'integer' }
  ]);
  const maxFive = internDatatypeRestriction(XSD + 'integer', [
    { facetIRI: XSD + 'maxInclusive', lexicalValue: '5', datatypeIRI: XSD + 'integer' }
  ]);
  assert.equal(checkConstraintsSatisfiable([pos(minLen), pos(maxFive)]).satisfiable, false);
});

test('REGRESSION: an uninterpretable base datatype never clashes via step 2', () => {
  // `groupOf` returns GROUP.OTHER for an unknown IRI, and `datatypesDisjoint`
  // answers false for OTHER — so the opaque restrictions that
  // `applyUnknownDatatypeRestrictionSemantics` handles cannot manufacture a
  // clash here.
  const odd = internDatatypeRestriction('http://example.org/dt#MyDT', []);
  assert.equal(checkConstraintsSatisfiable([pos(odd), pos(XS_DR)]).satisfiable, true);
  assert.equal(checkConstraintsSatisfiable([pos(odd), pos(XI_DR)]).satisfiable, true);
});

test('REGRESSION: step 4 now enumerates a facet-free boolean restriction', () => {
  // A side effect of the step-2 fix, and a correct one: `namedPos` used to hold
  // only `LiteralDataRange`s, so the boolean finite-space enumeration in step 4
  // never saw the `xsd:boolean[]` the clausifier actually produces. Now
  // `bool[] ∧ ¬{true,false}` is properly reported unsatisfiable, while a single
  // excluded value still leaves a witness.
  const XB_DR = internDatatypeRestriction(XSD + 'boolean', []);
  const enumTF = internConstantEnumeration([
    new Constant('true', XSD + 'boolean'),
    new Constant('false', XSD + 'boolean')
  ]);
  const enumT = internConstantEnumeration([new Constant('true', XSD + 'boolean')]);
  assert.equal(checkConstraintsSatisfiable([pos(XB_DR)]).satisfiable, true);
  const res = checkConstraintsSatisfiable([pos(XB_DR), neg(enumTF)]);
  assert.equal(res.satisfiable, false);
  assert.match(res.explanation, /boolean value space exhausted/);
  assert.equal(checkConstraintsSatisfiable([pos(XB_DR), neg(enumT)]).satisfiable, true);
});

test('REGRESSION: the anonymous-constants group is disjoint from every real one', () => {
  // `internal:anonymous-constants` is its own GROUP, and `datatypesDisjoint`
  // makes it disjoint from all the real ones. In the live pipeline an anonymous
  // constant is a TERM (a witness value), never a data-range predicate, so this
  // combination is not reachable from normal input — it is pinned here purely to
  // document that step 2 honours the group rule for every spelling, and that a
  // future datatype added to `GROUP` cannot slip through unnoticed.
  const AC = 'internal:anonymous-constants';
  const anonDR = internDatatypeRestriction(AC, []);
  assert.equal(checkConstraintsSatisfiable([pos(anonDR), pos(XS_DR)]).satisfiable, false);
  assert.equal(checkConstraintsSatisfiable([pos(anonDR), pos(XI_DR)]).satisfiable, false);
  // The same IRI twice is never disjoint with itself.
  assert.equal(checkConstraintsSatisfiable([pos(anonDR), pos(anonDR)]).satisfiable, true);
});

test('a single positive datatype is satisfiable', () => {
  assert.equal(checkConstraintsSatisfiable([pos(XS)]).satisfiable, true);
});

test('a single negative datatype is satisfiable', () => {
  // ¬xsd:string alone leaves every non-string literal available.
  assert.equal(checkConstraintsSatisfiable([neg(XS)]).satisfiable, true);
});

test('an empty constraint set is satisfiable', () => {
  assert.equal(checkConstraintsSatisfiable([]).satisfiable, true);
});

test('two negatives of different datatypes do not clash', () => {
  assert.equal(checkConstraintsSatisfiable([neg(XS), neg(XI)]).satisfiable, true);
});

test('overlapping positive datatypes with an unrelated negative stay satisfiable', () => {
  // xsd:integer ∧ xsd:decimal overlap ("5"), and ¬xsd:string excludes nothing
  // they contain.
  assert.equal(checkConstraintsSatisfiable([pos(XI), pos(XD), neg(XS)]).satisfiable, true);
});

// ===========================================================================
// The interning identity the fix relies on
// ===========================================================================

test('interned data ranges are identical objects, so a Set lookup finds them', () => {
  // The fix compares predicates by identity (they are interned). Pin that,
  // because a future change to non-interned predicates would silently break it.
  assert.equal(internLiteralDataRange(XSD + 'string'), XS);
  assert.equal(XS.getNegation().dataRange, XS, '¬xsd:string wraps the same object');
  assert.ok(XS.getNegation() instanceof AtomicNegationDataRange);
  assert.ok(XS instanceof LiteralDataRange);
});

test('DatatypeManager unwraps a negation before calling this function', () => {
  // `_collectConstraints` stores `{predicate: pred.dataRange, positive: false}`
  // for an AtomicNegationDataRange, so the two sides really are the same object.
  const negation = XS.getNegation();
  const unwrapped = { predicate: negation.dataRange, positive: false };
  assert.equal(unwrapped.predicate, XS);
  assert.equal(checkConstraintsSatisfiable([pos(XS), unwrapped]).satisfiable, false);
});

// ===========================================================================
// Supporting primitives (unchanged behaviour, pinned for context)
// ===========================================================================

test('datatypesDisjoint separates different groups but not the same datatype', () => {
  assert.equal(datatypesDisjoint(XSD + 'string', XSD + 'integer'), true);
  assert.equal(datatypesDisjoint(XSD + 'string', XSD + 'string'), false);
  // An unknown datatype is assumed to overlap everything (safe).
  assert.equal(datatypesDisjoint(XSD + 'string', 'http://example.org/dt#MyDT'), false);
});

test('constantSatisfies still over-approximates opaque predicates', () => {
  const MyDT = internInternalDatatype('http://example.org/dt#MyDT');
  const c = new Constant('abc', XSD + 'string');
  // Over-approximate: "possibly satisfies", so it never causes a false clash.
  assert.equal(constantSatisfies(c, MyDT), true);
  assert.equal(constantSatisfies(c, XS), true);
  assert.equal(constantSatisfies(c, XI), false);
});

test('an enumeration excludes every listed value and nothing else', () => {
  const red = new Constant('red', XSD + 'string');
  const green = new Constant('green', XSD + 'string');
  const blue = new Constant('blue', XSD + 'string');
  const enumRG = internConstantEnumeration([red, green]);
  // {red,green} ∧ ¬{red,green} has no witness.
  assert.equal(checkConstraintsSatisfiable([pos(enumRG), neg(enumRG)]).satisfiable, false);
  // {red,green} ∧ ¬blue is satisfiable (pick red).
  const enumB = internConstantEnumeration([blue]);
  assert.equal(checkConstraintsSatisfiable([pos(enumRG), neg(enumB)]).satisfiable, true);
});

// ===========================================================================
// REGRESSION for the MIRROR-IMAGE bug: an undecidable predicate in a NEGATIVE
// position must not manufacture a clash.
// ===========================================================================

const RED = new Constant('red', XSD + 'string');
const GREEN = new Constant('green', XSD + 'string');
const ENUM_RG = internConstantEnumeration([RED, GREEN]);
const ENUM_R = internConstantEnumeration([RED]);

/** A facet `checkFacetValue` does not recognise, on a datatype that DOES match. */
const UNKNOWN_FACET_IRI = XSD + 'unknownFacet';
const ODD_STRING = internDatatypeRestriction(XSD + 'string', [
  { facetIRI: UNKNOWN_FACET_IRI, lexicalValue: '1', datatypeIRI: XSD + 'integer' }
]);
const OPAQUE_DT = internInternalDatatype('http://example.org/dt#Opaque');

test('REGRESSION: constantMembership is THREE-VALUED, and null means undecidable', () => {
  // Decidable predicates give a definite answer.
  assert.equal(constantMembership(RED, XS), true);
  assert.equal(constantMembership(RED, XI), false);
  assert.equal(constantMembership(RED, ENUM_RG), true);
  // Undecidable: an opaque internal datatype, and an unrecognised facet.
  assert.equal(constantMembership(RED, OPAQUE_DT), null);
  assert.equal(constantMembership(RED, ODD_STRING), null);
  // The two wrappers split `null` in OPPOSITE, always-candidate-keeping ways.
  assert.equal(constantSatisfies(RED, OPAQUE_DT), true, 'positive form: null := true');
  assert.equal(constantDefinitelySatisfies(RED, OPAQUE_DT), false, 'negative form: null := false');
  // Both agree with the definite answers.
  assert.equal(constantSatisfies(RED, XS), true);
  assert.equal(constantDefinitelySatisfies(RED, XS), true);
  assert.equal(constantSatisfies(RED, XI), false);
  assert.equal(constantDefinitelySatisfies(RED, XI), false);
});

test('REGRESSION: an opaque NEGATIVE does not exclude enumerated candidates', () => {
  // Step 3. {red,green}(v) ∧ ¬Opaque(v) is satisfiable unless Opaque contains
  // BOTH red and green, which is unknowable — so it must not clash.
  assert.equal(checkConstraintsSatisfiable([pos(ENUM_RG), neg(OPAQUE_DT)]).satisfiable, true);
  // Single-candidate enumeration: same reasoning.
  assert.equal(checkConstraintsSatisfiable([pos(ENUM_R), neg(OPAQUE_DT)]).satisfiable, true);
});

test('REGRESSION: an unknown facet in a NEGATIVE does not exclude candidates', () => {
  // Step 3 again, via a DatatypeRestriction whose base datatype DOES match.
  assert.equal(checkConstraintsSatisfiable([pos(ENUM_RG), neg(ODD_STRING)]).satisfiable, true);
});

test('REGRESSION: an opaque NEGATIVE does not exhaust the boolean space', () => {
  // Step 4. xsd:boolean(v) ∧ ¬Opaque(v): "true" or "false" works unless Opaque
  // holds both, which is unknowable.
  assert.equal(checkConstraintsSatisfiable([pos(XB), neg(OPAQUE_DT)]).satisfiable, true);
  assert.equal(checkConstraintsSatisfiable([pos(XB), neg(ODD_STRING)]).satisfiable, true);
});

test('the negative-position fix does NOT weaken decidable exclusions', () => {
  // A negative we CAN decide must still exclude every candidate.
  assert.equal(checkConstraintsSatisfiable([pos(ENUM_RG), neg(XS)]).satisfiable, false);
  assert.equal(checkConstraintsSatisfiable([pos(ENUM_R), neg(ENUM_R)]).satisfiable, false);
  assert.equal(checkConstraintsSatisfiable([pos(ENUM_RG), neg(ENUM_RG)]).satisfiable, false);
  // A decidable facet restriction still excludes what it really excludes.
  const minLen10 = internDatatypeRestriction(XSD + 'string', [
    { facetIRI: XSD + 'minLength', lexicalValue: '10', datatypeIRI: XSD + 'integer' }
  ]);
  const longEnum = internConstantEnumeration([
    new Constant('a-very-long-value', XSD + 'string')
  ]);
  // "a-very-long-value" IS ≥ 10 chars, so ¬string[minLength 10] excludes it.
  assert.equal(checkConstraintsSatisfiable([pos(longEnum), neg(minLen10)]).satisfiable, false);
  // "red" is NOT ≥ 10 chars, so it survives.
  assert.equal(checkConstraintsSatisfiable([pos(ENUM_RG), neg(minLen10)]).satisfiable, true);
});

test('a negated restriction still clashes with itself (step 1 is unaffected)', () => {
  // Step 1 fires on predicate IDENTITY and needs no value-space knowledge, so
  // making membership three-valued cannot weaken it.
  assert.equal(checkConstraintsSatisfiable([pos(ODD_STRING), neg(ODD_STRING)]).satisfiable, false);
  assert.equal(checkConstraintsSatisfiable([pos(OPAQUE_DT), neg(OPAQUE_DT)]).satisfiable, false);
});

test('a negation of a DECIDABLE range is still decided through the wrapper', () => {
  // AtomicNegationDataRange membership is the complement, and `null` must
  // propagate rather than collapse to a definite answer.
  const notString = XS.getNegation();
  assert.equal(constantMembership(RED, notString), false);
  assert.equal(constantDefinitelySatisfies(RED, notString), false);
  const notOpaque = OPAQUE_DT.getNegation();
  assert.equal(constantMembership(RED, notOpaque), null);
  assert.equal(constantDefinitelySatisfies(RED, notOpaque), false);
});

// ===========================================================================
// DEFECT 6 — integer-derived XSD datatypes and by-value membership.
//
// `numericSubsumes` used to rank only `xsd:integer` and names ending in
// `Integer`, so the twelve facet-derived subtypes (`xsd:int`, `xsd:short`,
// `xsd:byte`, `xsd:unsignedInt`, …) were unrankable. A concrete
// `"25"^^xsd:integer` was therefore judged OUTSIDE `xsd:int` and every rule or
// restriction naming a derived integer type silently failed to fire. The fix
// adds an `INTEGER_BOUNDS` table: `numericSubsumes` orders the integer family
// by bounds, and `constantMembership` falls back to by-value magnitude for a
// CONCRETE constant (25 ∈ xsd:int even though xsd:integer ⊄ xsd:int).
// ===========================================================================

const XINT = XSD + 'integer';
const XDEC = XSD + 'decimal';
const XDBL = XSD + 'double';
const XSTR = XSD + 'string';
const XINT_T = XSD + 'int';
const XSHORT = XSD + 'short';
const XBYTE = XSD + 'byte';
const XNNI = XSD + 'nonNegativeInteger';
const XPOSI = XSD + 'positiveInteger';

test('DEFECT 6: numericSubsumes ranks the integer tower against decimal/double', () => {
  assert.equal(numericSubsumes(XDEC, XINT), true);   // integer ⊆ decimal
  assert.equal(numericSubsumes(XINT, XDEC), false);
  assert.equal(numericSubsumes(XDBL, XINT), true);  // integer ⊆ double
  assert.equal(numericSubsumes(XINT, XDBL), false);
  assert.equal(numericSubsumes(XSTR, XINT), false); // disjoint groups
});

test('DEFECT 6: numericSubsumes orders derived integer types by their bounds', () => {
  assert.equal(numericSubsumes(XINT_T, XINT), false); // xsd:integer ⊄ xsd:int
  assert.equal(numericSubsumes(XINT, XINT_T), true);  // xsd:int ⊆ xsd:integer
  assert.equal(numericSubsumes(XINT_T, XSHORT), true);// short ⊆ int
  assert.equal(numericSubsumes(XSHORT, XINT_T), false);
  assert.equal(numericSubsumes(XSHORT, XBYTE), true); // byte ⊆ short
  assert.equal(numericSubsumes(XBYTE, XSHORT), false);
  assert.equal(numericSubsumes(XNNI, XPOSI), true);   // positiveInteger ⊆ nonNegativeInteger
  assert.equal(numericSubsumes(XPOSI, XNNI), false);
});

test('DEFECT 6: constantMembership decides a concrete value against a derived integer type', () => {
  const c25 = new Constant('25', XINT);
  assert.equal(constantMembership(c25, internLiteralDataRange(XINT_T)), true);
  assert.equal(constantMembership(c25, internLiteralDataRange(XBYTE)), true);
  assert.equal(constantMembership(new Constant('2.5', XDEC), internLiteralDataRange(XINT_T)), false);
  assert.equal(constantMembership(new Constant('-1', XINT), internLiteralDataRange(XNNI)), false);
  assert.equal(constantMembership(new Constant('0', XINT), internLiteralDataRange(XNNI)), true);
  assert.equal(constantMembership(new Constant('0', XINT), internLiteralDataRange(XPOSI)), false);
});

test('DEFECT 6: isIntegerType recognises the whole integer family', () => {
  assert.equal(isIntegerType(XINT), true);
  assert.equal(isIntegerType(XINT_T), true);
  assert.equal(isIntegerType(XBYTE), true);
  assert.equal(isIntegerType(XNNI), true);
  assert.equal(isIntegerType(XDEC), false);
  assert.equal(isIntegerType(XSTR), false);
});

test('DEFECT 6: inIntegerBounds is three-valued and refuses unsafe integers', () => {
  assert.equal(inIntegerBounds(new Constant('25', XINT), XINT_T), true);
  assert.equal(inIntegerBounds(new Constant('300', XINT), XBYTE), false);
  assert.equal(inIntegerBounds(new Constant('2.5', XDEC), XINT_T), false); // non-integer
  assert.equal(inIntegerBounds(new Constant('x', XSTR), XINT_T), null);    // unparsable
  assert.equal(inIntegerBounds(new Constant('25', XINT), XDEC), null);     // not an integer type
});

// ===========================================================================
// DEFECT 5 — a negative DatatypeRestriction must be consulted when filtering
// the finite positive space. Step 6 used to test only negative
// `ConstantEnumeration`s, so a negative facet restriction that excludes the
// whole space was ignored and an unsatisfiable node was reported satisfiable.
// ===========================================================================

const dr = (datatypeIRI, facets) => internDatatypeRestriction(datatypeIRI, facets);
const minInc = (v) => ({ facetIRI: XSD + 'minInclusive', lexicalValue: v, datatypeIRI: XINT });
const maxInc = (v) => ({ facetIRI: XSD + 'maxInclusive', lexicalValue: v, datatypeIRI: XINT });

test('DEFECT 5: a negative facet restriction that excludes the whole space clashes', () => {
  // xsd:integer[6..9] ∧ ¬xsd:integer[≥5] ∧ ¬xsd:decimal[≤10] has no solution:
  // every value 6..9 is both ≥5 and ≤10.
  const space = dr(XINT, [minInc('6'), maxInc('9')]);
  const notGe5 = dr(XINT, [minInc('5')]);
  const notLe10 = dr(XDEC, [maxInc('10')]);
  assert.equal(
    checkConstraintsSatisfiable([pos(space), neg(notGe5), neg(notLe10)]).satisfiable,
    false
  );
});

test('DEFECT 5: a negative facet restriction that leaves a survivor stays satisfiable', () => {
  // xsd:integer[6..9] ∧ ¬xsd:integer[≥8] still admits 6 and 7.
  const space = dr(XINT, [minInc('6'), maxInc('9')]);
  const notGe8 = dr(XINT, [minInc('8')]);
  assert.equal(
    checkConstraintsSatisfiable([pos(space), neg(notGe8)]).satisfiable,
    true
  );
});

// ===========================================================================
// DEFECT 7 — `enumerateFiniteSpace` must SKIP an opaque `InternalDatatype`
// positive rather than bail out. Positives conjoin, so dropping an opaque one
// yields a superset of the real space (the safe direction). Bailing out made
// `xsd:integer[6..9] ∧ internal:defdata#0 ∧ ¬xsd:decimal[≤10]` report
// "satisfiable" and lost the clash.
// ===========================================================================

test('DEFECT 7: enumerateFiniteSpace skips an opaque InternalDatatype positive', () => {
  const space = dr(XINT, [minInc('6'), maxInc('9')]);
  const opaque = internInternalDatatype('internal:defdata#0');
  const enumerated = enumerateFiniteSpace([space, opaque]);
  assert.ok(Array.isArray(enumerated), 'an opaque positive must not abort enumeration');
  assert.deepEqual(enumerated.map(c => c.lexicalValue), ['6', '7', '8', '9']);
});

test('DEFECT 7: the opaque-positive node still clashes through step 6', () => {
  const space = dr(XINT, [minInc('6'), maxInc('9')]);
  const opaque = internInternalDatatype('internal:defdata#0');
  const notLe10 = dr(XDEC, [maxInc('10')]);
  assert.equal(
    checkConstraintsSatisfiable([pos(space), pos(opaque), neg(notLe10)]).satisfiable,
    false
  );
});

test('DEFECT 7: enumerateFiniteSpace clamps to the base datatype value space', () => {
  // xsd:byte[0..300] is really 0..127; enumerating 128..300 would offer
  // candidates no value of the space can be.
  const space = dr(XBYTE, [minInc('0'), maxInc('300')]);
  const enumerated = enumerateFiniteSpace([space]);
  assert.ok(Array.isArray(enumerated));
  assert.equal(enumerated.length, 128); // 0..127 inclusive
});
