'use strict';

// ---------------------------------------------------------------------------
// datatypes/DatatypeReasoning.js — concrete-domain (datatype) constraint
// checking, a focused port of org.semanticweb.HermiT.datatypes.
//
// The tableau accumulates, per concrete node, a set of data-range constraints:
//   positive: the node's value MUST be in the range   ( DR(y) )
//   negative: the node's value must NOT be in the range ( ¬DR(y) )
//
// This module answers: is the conjunction satisfiable, and (if finite) what are
// the candidate values? The rules implemented:
//
//   1. A node holds ONE value, so a data range together with its own negation
//      is a contradiction — for ANY range, whatever its value space. This is
//      the only rule that needs no value-space knowledge, so it is the one that
//      stays sound for the opaque predicates (`InternalDatatype`, unknown facet
//      restrictions) that rules 2-6 have to over-approximate.
//   2. Named datatype value spaces are pairwise disjoint across datatype
//      "groups" (numeric vs. string vs. boolean vs. dateTime vs. binary...),
//      overlapping within the numeric group (integer ⊆ decimal ⊆ double).
//   3. ConstantEnumerations give explicit candidate sets.
//   4. Facet restrictions (min/maxInclusive/Exclusive, length, pattern...)
//      narrow a value space.
//   5. An infinite positive space can never be exhausted by finitely many
//      negative constraints → satisfiable.
//   6. A finite positive space is checked by enumeration.
//
// Rule 1 is load-bearing for `DatatypeDefinition` entailment: the symmetric
// difference `(¬dr ⊓ dt) ⊔ (dr ⊓ ¬dt)` derives `dr(v)` and `¬dr(v)` on one
// node, and without the clash a datatype would never be provable equal to the
// very range it is defined as.
//
// OVER-APPROXIMATION IS DIRECTIONAL. Where this port lacks value-space
// knowledge — a datatype DEFINED by an axiom (`InternalDatatype`), an
// unrecognised facet, an unrecognised predicate — membership is UNDECIDABLE,
// and `constantMembership` returns `null` rather than guessing. Each caller then
// resolves `null` in the only direction that cannot invent a clash:
//
//   positive test ("c must be in p")     → `constantSatisfies`           null := true
//   negative test ("c must NOT be in p") → `constantDefinitelySatisfies` null := false
//
// Both KEEP the candidate. Collapsing `null` to `true` unconditionally (the old
// two-valued `constantSatisfies`) is sound for the positive tests in rules 3-4
// but UNSOUND for their negative tests, where it rejects every candidate and
// reports the constraints unsatisfiable — a spurious clash, which is the wrong
// way round for a consistency check. `DatatypeManager._finiteSpace` has the same
// hazard: a space narrowed by an undecidable negative makes `_hasPerfectMatching`
// fail. Both now use the definite form.
// ---------------------------------------------------------------------------

const {
  LiteralDataRange,
  AtomicNegationDataRange,
  DatatypeRestriction,
  ConstantEnumeration,
  InternalDatatype,
  IRI_LITERAL,
  XSD,
  RDF
} = require('../model/DLPredicate');
const { Constant } = require('../model/Term');

// ---- datatype groups --------------------------------------------------------

const GROUP = {
  NUMERIC: 'numeric',
  STRING: 'string',
  BOOLEAN: 'boolean',
  DATETIME: 'datetime',
  BINARY: 'binary',
  ANONYMOUS_CONSTANTS: 'anonymous-constants',
  OTHER: 'other'
};

/**
 * The opaque datatype HermiT uses for fresh constants (e.g. the witness value
 * in `isSubDataPropertyOf`). Mirrors `DatatypeRegistry.AnonymousConstantsDatatypeHandler`:
 * every lexical form is a distinct value, disjoint from every other datatype.
 */
const IRI_ANONYMOUS_CONSTANTS = 'internal:anonymous-constants';

const NUMERIC_TYPES = new Set([
  XSD + 'integer', XSD + 'decimal', XSD + 'double', XSD + 'float',
  XSD + 'int', XSD + 'long', XSD + 'short', XSD + 'byte',
  XSD + 'nonNegativeInteger', XSD + 'positiveInteger',
  XSD + 'nonPositiveInteger', XSD + 'negativeInteger',
  XSD + 'unsignedInt', XSD + 'unsignedLong', XSD + 'unsignedShort', XSD + 'unsignedByte'
]);

const STRING_TYPES = new Set([
  XSD + 'string', XSD + 'normalizedString', XSD + 'token', XSD + 'language',
  XSD + 'Name', XSD + 'NCName', XSD + 'NMTOKEN', XSD + 'anyURI',
  RDF + 'PlainLiteral', RDF + 'XMLLiteral', XSD + 'anySimpleType'
]);

const DATETIME_TYPES = new Set([
  XSD + 'dateTime', XSD + 'dateTimeStamp', XSD + 'date', XSD + 'time',
  XSD + 'gYear', XSD + 'gYearMonth', XSD + 'gMonth', XSD + 'gMonthDay', XSD + 'gDay'
]);

const BINARY_TYPES = new Set([XSD + 'hexBinary', XSD + 'base64Binary']);

/**
 * The value-space bounds of the XSD datatypes derived from `xsd:integer` by
 * facet enumeration, keyed by local name. `null` means unbounded in that
 * direction. These are exactly the `minInclusive`/`maxInclusive` facets the
 * XSD 1.1 specification gives for each type, so this table adds no new
 * semantics — it makes explicit what the datatype definitions already say.
 *
 * HermiT gets the same knowledge from its `datatypes/integer` handler family
 * (`IntegerByteValueSpace`, `IntegerShortValueSpace`, …), each of which is a
 * bounded subrange of `IntegerValueSpace`. This port does not carry those
 * handlers, so without the table a concrete `"25"^^xsd:integer` is judged to
 * lie OUTSIDE `xsd:int` — `numericSubsumes` cannot rank a type it does not
 * know — and every rule or restriction whose data range names a derived
 * integer type silently fails to fire.
 *
 * `xsd:long`'s and `xsd:unsignedLong`'s extremes exceed
 * `Number.MAX_SAFE_INTEGER`; they are stored as the nearest doubles, which is
 * harmless because `inIntegerBounds` refuses to decide any value that is not
 * itself a safe integer (see below), and every safe integer is far inside both
 * ranges.
 */
const INTEGER_BOUNDS = new Map([
  ['long', [-9223372036854775808, 9223372036854775807]],
  ['int', [-2147483648, 2147483647]],
  ['short', [-32768, 32767]],
  ['byte', [-128, 127]],
  ['nonNegativeInteger', [0, null]],
  ['positiveInteger', [1, null]],
  ['nonPositiveInteger', [null, 0]],
  ['negativeInteger', [null, -1]],
  ['unsignedLong', [0, 18446744073709551615]],
  ['unsignedInt', [0, 4294967295]],
  ['unsignedShort', [0, 65535]],
  ['unsignedByte', [0, 255]]
]);

/** The local name of an `xsd:` datatype IRI, or `null` for anything else. */
function xsdLocalName(datatypeIRI) {
  return typeof datatypeIRI === 'string' && datatypeIRI.startsWith(XSD)
    ? datatypeIRI.substring(XSD.length)
    : null;
}

/**
 * Is the concrete numeric constant `c` inside the value space of the
 * integer-derived datatype `datatypeIRI`?
 *
 * Returns `null` — undecidable, so every caller keeps the candidate — when the
 * datatype has no entry in {@link INTEGER_BOUNDS}, when the lexical form does
 * not parse as a finite number, or when the value is an integer too large for
 * `Number` to represent exactly. A finite NON-integer is definitely outside
 * every integer-derived datatype, so that case returns `false`.
 *
 * @returns {boolean|null}
 */
function inIntegerBounds(c, datatypeIRI) {
  const local = xsdLocalName(datatypeIRI);
  const bounds = local === null ? undefined : INTEGER_BOUNDS.get(local);
  if (bounds === undefined) return null;
  const v = Number(c.lexicalValue);
  if (!Number.isFinite(v)) return null;
  if (!Number.isInteger(v)) return false;
  if (!Number.isSafeInteger(v)) return null;
  const lo = bounds[0], hi = bounds[1];
  if (lo !== null && v < lo) return false;
  if (hi !== null && v > hi) return false;
  return true;
}

/**
 * Is `datatypeIRI` an integer-valued datatype — `xsd:integer` itself or one of
 * the twelve facet-derived subtypes in {@link INTEGER_BOUNDS}? These are the
 * types whose value space can be enumerated one integer at a time.
 */
function isIntegerType(datatypeIRI) {
  return datatypeIRI === XSD + 'integer'
    || INTEGER_BOUNDS.has(xsdLocalName(datatypeIRI));
}

function groupOf(datatypeIRI) {
  if (NUMERIC_TYPES.has(datatypeIRI)) return GROUP.NUMERIC;
  if (STRING_TYPES.has(datatypeIRI)) return GROUP.STRING;
  if (DATETIME_TYPES.has(datatypeIRI)) return GROUP.DATETIME;
  if (BINARY_TYPES.has(datatypeIRI)) return GROUP.BINARY;
  if (datatypeIRI === XSD + 'boolean') return GROUP.BOOLEAN;
  if (datatypeIRI === IRI_ANONYMOUS_CONSTANTS) return GROUP.ANONYMOUS_CONSTANTS;
  return GROUP.OTHER;
}

/** Two named datatypes are disjoint iff they are in different known groups. */
function datatypesDisjoint(iri1, iri2) {
  if (iri1 === iri2) return false;
  if (iri1 === IRI_LITERAL || iri2 === IRI_LITERAL) return false;
  const g1 = groupOf(iri1), g2 = groupOf(iri2);
  // Anonymous constants are disjoint from every real datatype (and from each
  // other unless the lexical forms match, which `iri1 === iri2` cannot express
  // — callers compare full constants via `constantsEqual`).
  if (g1 === GROUP.ANONYMOUS_CONSTANTS || g2 === GROUP.ANONYMOUS_CONSTANTS) {
    return g1 !== g2;
  }
  if (g1 === GROUP.OTHER || g2 === GROUP.OTHER) return false; // unknown: assume overlap (safe)
  return g1 !== g2;
}

// ---- value parsing ----------------------------------------------------------

/** Parse a constant's lexical value into a JS value for comparison. */
function parseValue(constant) {
  const iri = constant.datatypeIRI;
  const lex = constant.lexicalValue;
  if (!iri || groupOf(iri) === GROUP.NUMERIC) {
    const n = Number(lex);
    return Number.isNaN(n) ? lex : n;
  }
  if (groupOf(iri) === GROUP.DATETIME) {
    const t = Date.parse(lex);
    return Number.isNaN(t) ? lex : t;
  }
  if (iri === XSD + 'boolean') return lex === 'true' || lex === '1';
  return lex;
}

/**
 * Are two constants the same value? (Cross-datatype numeric equality:
 * "5"^^xsd:integer ≡ "5.0"^^xsd:decimal.)
 */
function constantsEqual(c1, c2) {
  if (c1 === c2) return true;
  if (c1.datatypeIRI === c2.datatypeIRI && c1.lexicalValue === c2.lexicalValue) return true;
  const g1 = groupOf(c1.datatypeIRI), g2 = groupOf(c2.datatypeIRI);
  if (g1 !== g2) return false;
  return parseValue(c1) === parseValue(c2);
}

// ---- facet checking ---------------------------------------------------------

/**
 * Does `value` satisfy ONE facet restriction?
 *
 * THREE-VALUED: `true` / `false` when the facet is one this port understands,
 * `null` when it is not. `null` means "membership undecidable", and the caller
 * must over-approximate it in whichever direction is safe for it — see
 * `constantMembership`. Returning `true` here instead would be sound for a
 * positive test but UNSOUND for a negative one, where it would exclude a
 * candidate that might well lie outside the range and so manufacture a clash.
 */
function checkFacetValue(value, facetIRI, facetLex, datatypeIRI) {
  const XSF = XSD;
  const fv = parseValue(new Constant(facetLex, guessFacetDatatype(datatypeIRI)));
  const v = parseValue(new Constant(String(value), datatypeIRI));
  switch (facetIRI) {
    case XSF + 'minInclusive': return v >= fv;
    case XSF + 'minExclusive': return v > fv;
    case XSF + 'maxInclusive': return v <= fv;
    case XSF + 'maxExclusive': return v < fv;
    case XSF + 'length': return String(value).length === fv;
    case XSF + 'minLength': return String(value).length >= fv;
    case XSF + 'maxLength': return String(value).length <= fv;
    case XSF + 'pattern': return new RegExp(String(facetLex)).test(String(value));
    case XSF + 'totalDigits': return String(v).replace(/[-.]/g, '').replace(/^0+/, '').length <= fv;
    case XSF + 'fractionDigits': {
      const s = String(value);
      const dot = s.indexOf('.');
      return dot < 0 ? 0 <= fv : s.length - dot - 1 <= fv;
    }
    default: return null; // unknown facet: membership undecidable
  }
}

function guessFacetDatatype(datatypeIRI) {
  if (groupOf(datatypeIRI) === GROUP.NUMERIC) return XSD + 'decimal';
  if (groupOf(datatypeIRI) === GROUP.DATETIME) return XSD + 'dateTime';
  return XSD + 'string';
}

// ---- constraint objects -----------------------------------------------------

/**
 * A normalized constraint on one concrete node.
 * { predicate, positive: boolean }
 *
 * `normalizeConstraint` turns model predicates into a checkable form.
 */

/**
 * Does constant `c` lie in data-range predicate `p`?
 *
 * THREE-VALUED: `true`, `false`, or `null` for "undecidable". Undecidable arises
 * exactly where this port has no value-space knowledge: an `InternalDatatype` (a
 * datatype DEFINED by an axiom, opaque to the concrete domain), an unrecognised
 * facet, or an unrecognised predicate shape.
 *
 * Callers must split `null` in the direction that is safe for them, and the two
 * wrappers below do exactly that:
 *
 *   positive test (`c` must be in `p`)     → `constantSatisfies`,          null := true
 *   negative test (`c` must NOT be in `p`) → `constantDefinitelySatisfies`, null := false
 *
 * Both over-approximate towards KEEPING a candidate, so neither can manufacture
 * a clash out of missing knowledge. Using the positive form in a negative test
 * is the bug this guards against: it rejects every candidate and reports the
 * constraints unsatisfiable when they are merely undecidable.
 *
 * @returns {boolean|null}
 */
function constantMembership(c, p) {
  if (p instanceof LiteralDataRange) {
    if (p.isAlwaysTrue()) return true;
    if (!c.datatypeIRI) return p.iri === IRI_LITERAL;
    if (p.iri === c.datatypeIRI) return true;
    // numeric subsumption: integer ⊆ decimal ⊆ double
    if (groupOf(p.iri) === GROUP.NUMERIC && groupOf(c.datatypeIRI) === GROUP.NUMERIC) {
      if (numericSubsumes(p.iri, c.datatypeIRI)) return true;
      // `numericSubsumes` is a TYPE-lattice question and stays conservative: it
      // cannot rank the integer-derived datatypes (`xsd:int`, `xsd:short`, …)
      // against each other, and `xsd:integer ⊄ xsd:int` is correct anyway. But
      // here we have a CONCRETE value, so membership is decidable by magnitude
      // instead: 25 ∈ xsd:int even though xsd:integer ⊄ xsd:int. Without this
      // the base check fails and every facet-restricted range over a derived
      // integer type rejects all of its values.
      const byValue = inIntegerBounds(c, p.iri);
      if (byValue !== null) return byValue;
      return false;
    }
    if (p.iri === IRI_LITERAL) return true;
    return false;
  }
  if (p instanceof AtomicNegationDataRange) {
    const m = constantMembership(c, p.dataRange);
    return m === null ? null : !m;
  }
  if (p instanceof DatatypeRestriction) {
    const base = constantMembership(c, new LiteralDataRange(p.datatypeIRI));
    // A base-type mismatch is DEFINITE: the constant cannot be in the range.
    // (`base` is never null today — `LiteralDataRange` membership is decidable —
    // but propagating it keeps this correct if that ever changes.)
    if (base !== true) return base;
    // Every facet must hold. One definite failure decides it; otherwise a single
    // undecidable facet leaves the whole membership undecidable. A restriction
    // with no facets is just its base datatype, hence `true`.
    let undecided = false;
    for (const f of p.facets) {
      const v = checkFacetValue(c.lexicalValue, f.facetIRI, f.lexicalValue, p.datatypeIRI);
      if (v === false) return false;
      if (v === null) undecided = true;
    }
    return undecided ? null : true;
  }
  if (p instanceof ConstantEnumeration) {
    return p.constants.some(k => constantsEqual(k, c));
  }
  if (p instanceof InternalDatatype) {
    // A datatype DEFINED by an axiom is opaque to the concrete domain: this port
    // holds no value space for it, so membership of a concrete value is unknown.
    return null;
  }
  return null; // unrecognised predicate: membership unknown
}

/**
 * Positive over-approximation: does `c` POSSIBLY lie in `p`? `null` counts as
 * yes, so an opaque predicate never rejects a candidate it cannot judge.
 */
function constantSatisfies(c, p) {
  return constantMembership(c, p) !== false;
}

/**
 * Negative-safe form: does `c` DEFINITELY lie in `p`? `null` counts as no, so an
 * opaque predicate cannot exclude a candidate — which would be a spurious clash.
 * Use this, never `constantSatisfies`, wherever a NEGATIVE constraint is tested
 * against a candidate value.
 */
function constantDefinitelySatisfies(c, p) {
  return constantMembership(c, p) === true;
}

/**
 * Is every value of `sub` also a value of `sup`? (numeric tower only)
 *
 * The tower is `xsd:integer ⊆ xsd:decimal ⊆ xsd:float ⊆ xsd:double`, and the
 * twelve integer-derived datatypes of {@link INTEGER_BOUNDS} all sit at the
 * bottom rung. Two types on the SAME rung are ordered by their bounds, so
 * `xsd:short ⊆ xsd:int` holds while `xsd:int ⊆ xsd:short` does not, and
 * `xsd:positiveInteger ⊆ xsd:nonNegativeInteger` holds but not conversely.
 *
 * Anything that cannot be ranked returns `false`: this is a TYPE-lattice
 * question, so an unrankable pair is reported as non-subsuming rather than
 * guessed. Callers that hold a CONCRETE value can still decide membership by
 * magnitude — see {@link inIntegerBounds}.
 */
function numericSubsumes(sup, sub) {
  if (sup === sub) return true;
  const rank = (iri) => {
    if (iri === XSD + 'integer' || INTEGER_BOUNDS.has(xsdLocalName(iri))) return 0;
    if (iri === XSD + 'decimal') return 1;
    if (iri === XSD + 'float') return 2;
    if (iri === XSD + 'double') return 3;
    return -1;
  };
  const rs = rank(sup), rb = rank(sub);
  if (rs < 0 || rb < 0) return false;
  if (rb < rs) return true;   // strictly lower in the tower ⇒ a subset
  if (rb > rs) return false;
  // Same rung: both are integer-family types, so compare their bounds.
  return boundsContain(_boundsOf(sup), _boundsOf(sub));
}

/**
 * The `[min, max]` value-space bounds of an integer-family datatype IRI
 * (`null` for an unbounded side), or `null` when the type is not one.
 * `xsd:integer` itself is unbounded on both sides.
 */
function _boundsOf(datatypeIRI) {
  if (datatypeIRI === XSD + 'integer') return [null, null];
  const local = xsdLocalName(datatypeIRI);
  return local === null ? null : (INTEGER_BOUNDS.get(local) || null);
}

/** Are `inner`'s bounds contained in `outer`'s? `null` bounds mean "unknown". */
function boundsContain(outer, inner) {
  if (outer === null || inner === null) return false;
  // inner's lower bound must be at least outer's (outer unbounded ⇒ no constraint)
  if (outer[0] !== null && (inner[0] === null || inner[0] < outer[0])) return false;
  // inner's upper bound must be at most outer's
  if (outer[1] !== null && (inner[1] === null || inner[1] > outer[1])) return false;
  return true;
}

// ---- the satisfiability check ----------------------------------------------

/**
 * The datatype IRI a POSITIVE data-range predicate tests membership against, or
 * `null` when the predicate is not a (possibly facet-restricted) named datatype.
 *
 * `rdfs:Literal` maps to `null` rather than to its own IRI: it is the always-true
 * data range, and treating it as a datatype would make it "disjoint" from nothing
 * while adding a useless entry to every pairwise scan.
 */
function datatypeIRIOf(predicate) {
  if (predicate instanceof LiteralDataRange) {
    return predicate.isAlwaysTrue() ? null : predicate.iri;
  }
  if (predicate instanceof DatatypeRestriction) return predicate.datatypeIRI;
  return null;
}

/**
 * Decide whether a set of constraints on ONE concrete node is satisfiable.
 *
 * @param {Array<{predicate: DLPredicate, positive: boolean}>} constraints
 * @returns {{satisfiable: boolean, explanation: string|null}}
 */
function checkConstraintsSatisfiable(constraints) {
  const positives = constraints.filter(c => c.positive).map(c => c.predicate);
  const negatives = constraints.filter(c => !c.positive).map(c => c.predicate);

  // 1. A data range and its own negation on the same node → clash.
  //
  // A concrete node holds exactly ONE literal value, so `R(v)` and `¬R(v)`
  // cannot both hold no matter what `R`'s value space is. Deciding this needs
  // no knowledge of `R` at all, which is what makes it sound for the opaque
  // predicates (`InternalDatatype`, unknown facet restrictions) that every
  // later step has to over-approximate. Predicates are interned, so identity
  // suffices; `DatatypeManager._collectConstraints` has already unwrapped an
  // `AtomicNegationDataRange` to its underlying data range.
  const negativeSet = new Set(negatives);
  for (const p of positives) {
    if (negativeSet.has(p)) {
      return {
        satisfiable: false,
        explanation: `a data range and its own negation on the same node: ${p}`
      };
    }
  }

  // 2. Two positive named datatypes from disjoint groups → clash.
  //
  // `namedPos` covers BOTH spellings of a named datatype, because the pipeline
  // only ever produces the second one: `OWLClausification._convertDatatype`
  // turns a bare `xsd:string` into the FACET-FREE restriction `xsd:string[]`.
  // HermiT does the same, which is why its `DatatypeChecker.DVariable.addDataRange`
  // compares `getDatatypeURI()` on restrictions rather than on a separate
  // "literal data range" class. Filtering this step on `LiteralDataRange` alone
  // therefore made the clash UNREACHABLE from real input: a concrete node
  // carrying both `xsd:string[]` and `xsd:integer[]` was reported satisfiable,
  // which is what broke HermiT's `EntailmentTest.testHasKey`.
  //
  // Facets are deliberately ignored here — disjointness is a property of the
  // BASE value spaces, and `xsd:string[minLength 1]` ∧ `xsd:integer[max 5]` is
  // unsatisfiable for exactly the same reason. An uninterpretable base datatype
  // lands in `GROUP.OTHER`, for which `datatypesDisjoint` returns false, so the
  // opaque restrictions `applyUnknownDatatypeRestrictionSemantics` handles can
  // never manufacture a clash here.
  const namedPos = positives
    .map(p => ({ predicate: p, iri: datatypeIRIOf(p) }))
    .filter(x => x.iri !== null);
  for (let i = 0; i < namedPos.length; i++) {
    for (let j = i + 1; j < namedPos.length; j++) {
      if (datatypesDisjoint(namedPos[i].iri, namedPos[j].iri)) {
        return {
          satisfiable: false,
          explanation: `disjoint datatypes ${namedPos[i].iri} and ${namedPos[j].iri} on the same node`
        };
      }
    }
  }

  // 3. Positive enumeration: try each candidate against everything else.
  const enums = positives.filter(p => p instanceof ConstantEnumeration);
  if (enums.length > 0) {
    let candidates = enums[0].constants.slice();
    for (const e of enums.slice(1)) {
      candidates = candidates.filter(c1 => e.constants.some(c2 => constantsEqual(c1, c2)));
    }
    for (const c of candidates) {
      let ok = true;
      for (const p of positives) {
        if (p instanceof ConstantEnumeration) continue;
        if (!constantSatisfies(c, p)) { ok = false; break; }
      }
      if (ok) {
        for (const p of negatives) {
          // Negative test: only a DEFINITE membership excludes the candidate.
          if (constantDefinitelySatisfies(c, p)) { ok = false; break; }
        }
      }
      if (ok) return { satisfiable: true, explanation: null };
    }
    return {
      satisfiable: false,
      explanation: `no value in {${candidates.map(String).join(', ')}} satisfies all data-range constraints`
    };
  }

  // 4. Positive boolean datatype = finite space {true,false}: enumerate.
  const boolPos = namedPos.find(x => groupOf(x.iri) === GROUP.BOOLEAN);
  if (boolPos && positives.every(p => p instanceof LiteralDataRange || p instanceof DatatypeRestriction)) {
    for (const lex of ['true', 'false']) {
      const c = new Constant(lex, XSD + 'boolean');
      if (positives.every(p => constantSatisfies(c, p))
        && negatives.every(p => !constantDefinitelySatisfies(c, p))) {
        return { satisfiable: true, explanation: null };
      }
    }
    return { satisfiable: false, explanation: 'boolean value space exhausted' };
  }

  // 5. Facet-restricted numeric ranges can be empty (min > max).
  const facetPos = positives.filter(p => p instanceof DatatypeRestriction);
  for (const p of facetPos) {
    if (isEmptyFacetRange(p)) {
      return { satisfiable: false, explanation: `empty facet range ${p}` };
    }
  }
  // Multiple facet restrictions on the same numeric type: intersect bounds.
  const byType = new Map();
  for (const p of facetPos) {
    const list = byType.get(p.datatypeIRI) || [];
    list.push(p);
    byType.set(p.datatypeIRI, list);
  }
  for (const [iri, ps] of byType) {
    if (groupOf(iri) === GROUP.NUMERIC && isEmptyIntersection(ps)) {
      return { satisfiable: false, explanation: `empty intersection of facet ranges on ${iri}` };
    }
  }

  // 6. Negative constraints vs. the positive facet space: if the positive space
  //    is finite (bounded integers / bounded strings), enumerate it and keep the
  //    first value that NO negative constraint definitely excludes; otherwise an
  //    infinite space is never exhausted → satisfiable.
  //
  //    Every negative predicate kind has to be consulted here, not just
  //    `ConstantEnumeration`s. A negative `DatatypeRestriction` can exclude the
  //    whole space on its own — `xsd:integer[6..9]` together with
  //    `¬xsd:integer[≥5]` and `¬xsd:decimal[≤10]` has no solution at all — and
  //    filtering only enumerations reports that node as satisfiable, which loses
  //    the clash and with it every conclusion the reference implementation draws
  //    from the alternative branch. For a `ConstantEnumeration` negative,
  //    `constantDefinitelySatisfies` reduces to exactly the old
  //    `p.constants.some(k => constantsEqual(k, c))` test, so this is a strict
  //    generalisation. Undecidable negatives (`constantDefinitelySatisfies` →
  //    false) KEEP the candidate, so the over-approximation still errs towards
  //    "satisfiable" rather than inventing a clash.
  const finiteSpace = enumerateFiniteSpace(positives);
  if (finiteSpace) {
    for (const c of finiteSpace) {
      if (negatives.every(p => !constantDefinitelySatisfies(c, p))) {
        return { satisfiable: true, explanation: null };
      }
    }
    return { satisfiable: false, explanation: 'all values of the finite space are excluded by negative constraints' };
  }

  // 7. Default: infinite space (or opaque) → satisfiable.
  return { satisfiable: true, explanation: null };
}

function isEmptyFacetRange(p) {
  let min = null, minEx = false, max = null, maxEx = false;
  for (const f of p.facets) {
    const v = Number(f.lexicalValue);
    if (Number.isNaN(v)) continue;
    if (f.facetIRI === XSD + 'minInclusive') { if (min === null || v > min) { min = v; minEx = false; } }
    if (f.facetIRI === XSD + 'minExclusive') { if (min === null || v >= min) { min = v; minEx = true; } }
    if (f.facetIRI === XSD + 'maxInclusive') { if (max === null || v < max) { max = v; maxEx = false; } }
    if (f.facetIRI === XSD + 'maxExclusive') { if (max === null || v <= max) { max = v; maxEx = true; } }
  }
  if (min === null || max === null) return false;
  if (min > max) return true;
  if (min === max && (minEx || maxEx)) return true;
  return false;
}

function isEmptyIntersection(ps) {
  let min = -Infinity, minEx = false, max = Infinity, maxEx = false;
  for (const p of ps) {
    for (const f of p.facets) {
      const v = Number(f.lexicalValue);
      if (Number.isNaN(v)) continue;
      // A `minInclusive` bound only tightens the intersection when it is
      // STRICTLY greater than the current one. When `v === min` the existing
      // bound is already at least as strong — and if it came from a
      // `minExclusive` it is strictly stronger, so overwriting it with
      // `minEx = false` would WIDEN the range and lose a clash. Leaving it
      // alone is correct in both cases. (`maxExclusive` is symmetric and is
      // handled by the `v === max` branch below, which must set `maxEx`.)
      if (f.facetIRI === XSD + 'minInclusive') { if (v > min) { min = v; minEx = false; } }
      if (f.facetIRI === XSD + 'minExclusive') { if (v >= min) { min = v; minEx = true; } }
      if (f.facetIRI === XSD + 'maxInclusive') { if (v < max) { max = v; maxEx = false; } }
      if (f.facetIRI === XSD + 'maxExclusive') { if (v <= max) { max = v; maxEx = true; } }
    }
  }
  if (min > max) return true;
  if (min === max && (minEx || maxEx)) return true;
  return false;
}

/**
 * If the positive constraints define a small finite space, enumerate it.
 * Currently: bounded xsd:integer ranges (span ≤ 1024) and single-element
 * intersections. Returns Constant[] or null.
 *
 * Opaque positives (`InternalDatatype` — a datatype introduced by
 * normalization, whose value space this port does not carry) are SKIPPED rather
 * than causing a bail-out. Constraints on one node are conjoined, so every
 * positive can only NARROW the space: dropping one yields a superset of the
 * real one. That is the safe direction for both callers —
 * `checkConstraintsSatisfiable` may then report "satisfiable" too eagerly but
 * never invents a clash, and `DatatypeManager._hasPerfectMatching` gets a space
 * that is too large rather than too small (a too-small space is what makes it
 * fail and report a clash the constraints do not imply). Bailing out instead
 * loses real clashes: `xsd:integer[6..9] ∧ internal:defdata#0 ∧ ¬xsd:decimal[≤10]`
 * is unsatisfiable — every value 6..9 is definitely ≤ 10 — but with no
 * enumerated space the node is reported satisfiable and the alternative branch
 * of the disjunction that introduced `defdata#0` is never forced.
 */
function enumerateFiniteSpace(positives) {
  let min = null, max = null, isInt = false;
  let baseType = null;
  for (const p of positives) {
    if (p instanceof InternalDatatype) continue; // opaque: cannot widen the space
    if (p instanceof LiteralDataRange) {
      if (p.isAlwaysTrue()) continue;
      if (groupOf(p.iri) !== GROUP.NUMERIC) return null;
      baseType = p.iri;
      isInt = isIntegerType(p.iri);
    } else if (p instanceof DatatypeRestriction) {
      if (groupOf(p.datatypeIRI) !== GROUP.NUMERIC) return null;
      baseType = p.datatypeIRI;
      isInt = isIntegerType(p.datatypeIRI);
      for (const f of p.facets) {
        const v = Number(f.lexicalValue);
        if (Number.isNaN(v)) continue;
        if (f.facetIRI === XSD + 'minInclusive') min = min === null ? v : Math.max(min, v);
        if (f.facetIRI === XSD + 'minExclusive') min = min === null ? v + 1 : Math.max(min, v + 1);
        if (f.facetIRI === XSD + 'maxInclusive') max = max === null ? v : Math.min(max, v);
        if (f.facetIRI === XSD + 'maxExclusive') max = max === null ? v - 1 : Math.min(max, v - 1);
      }
    } else {
      return null; // unknown positive → don't enumerate
    }
  }
  if (!baseType || min === null || max === null) return null;
  if (!isInt) return null;
  // The base datatype's own value space narrows the facet bounds: `xsd:byte[0..300]`
  // is really `0..127`, and enumerating 128..300 would offer candidates that no
  // value of the space can be.
  const bounds = _boundsOf(baseType);
  if (bounds !== null) {
    if (bounds[0] !== null) min = Math.max(min, bounds[0]);
    if (bounds[1] !== null) max = Math.min(max, bounds[1]);
    if (min > max) return [];
  }
  if (max - min > 1024) return null;
  const out = [];
  for (let v = min; v <= max; v++) out.push(new Constant(String(v), XSD + 'integer'));
  return out;
}

module.exports = {
  GROUP,
  groupOf,
  datatypesDisjoint,
  constantsEqual,
  constantMembership,
  constantSatisfies,
  constantDefinitelySatisfies,
  parseValue,
  datatypeIRIOf,
  checkConstraintsSatisfiable,
  enumerateFiniteSpace,
  numericSubsumes,
  isIntegerType,
  inIntegerBounds,
  IRI_ANONYMOUS_CONSTANTS
};
