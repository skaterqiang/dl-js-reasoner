'use strict';
/**
 * IRI abbreviation / expansion.
 *
 * Port of `org.semanticweb.HermiT.Prefixes`.
 *
 * An IRI is printed either as `<full-iri>` or as `prefix-name:local-name`.
 * Prefix names always carry their trailing colon (e.g. `"owl:"`), exactly as in
 * HermiT, so that `abbreviateIRI` can concatenate without inserting one.
 *
 * The RDF namespace here deliberately uses the CORRECT W3C value
 * `1999/02/22-rdf-syntax-ns#`, matching `src/model/DLPredicate.js` and
 * protege-js, so that abbreviated IRIs round-trip against the rest of the
 * codebase.
 *
 * DIVERGENCE FROM HERMIT: HermiT's own `Prefixes.java:54` registers the typo'd
 * `1999-02-22-rdf-syntax-ns#` (hyphens instead of slashes). This port does not
 * reproduce that typo, because protege-js — the parser this port interoperates
 * with — expands `rdf:` to the correct namespace; copying HermiT's value would
 * make every `rdf:`-prefixed IRI fail to round-trip.
 */

const { RDF, RDFS, OWL, XSD } = require('./model/DLPredicate');

/** The well-known Semantic Web prefixes, keyed by prefix name (colon included). */
const SEMANTIC_WEB_PREFIXES = Object.freeze({
  'rdf:': RDF,
  'rdfs:': RDFS,
  'owl:': OWL,
  'xsd:': XSD,
  'swrl:': 'http://www.w3.org/2003/11/swrl#',
  'swrlb:': 'http://www.w3.org/2003/11/swrlb#',
  'swrlx:': 'http://www.w3.org/2003/11/swrlx#',
  'ruleml:': 'http://www.w3.org/2003/11/ruleml#'
});

// PN_CHARS_BASE / PN_CHARS from the SPARQL grammar, restricted to the BMP ranges
// that matter in practice. Used to decide whether a suffix can be printed bare.
const PN_CHARS_BASE = 'A-Za-z\\u00C0-\\u00D6\\u00D8-\\u00F6\\u00F8-\\u02FF\\u0370-\\u037D\\u037F-\\u1FFF\\u200C-\\u200D\\u2070-\\u218F\\u2C00-\\u2FEF\\u3001-\\uD7FF\\uF900-\\uFDCF\\uFDF0-\\uFFFD';
const PN_CHARS = `A-Za-z0-9_\\u002D\\u00B7\\u00C0-\\u00D6\\u00D8-\\u00F6\\u00F8-\\u02FF\\u0300-\\u036F\\u0370-\\u037D\\u037F-\\u1FFF\\u200C-\\u200D\\u203F-\\u2040\\u2070-\\u218F\\u2C00-\\u2FEF\\u3001-\\uD7FF\\uF900-\\uFDCF\\uFDF0-\\uFFFD`;
const LOCAL_NAME_CHECKER = new RegExp(
  `^([${PN_CHARS_BASE}]|_|[0-9])((([${PN_CHARS}]|[.])*([${PN_CHARS}]))?)$`);

/** Escape a literal string for use inside a RegExp. */
function quoteRegExp(s) {
  return s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

class Prefixes {
  constructor() {
    /** prefix name (with colon) → prefix IRI */
    this.prefixIRIsByPrefixName = new Map();
    /** prefix IRI → prefix name (with colon) */
    this.prefixNamesByPrefixIRI = new Map();
    /** @type {?RegExp} longest-prefix-first matcher, rebuilt on every declare */
    this.prefixIRIMatchingPattern = null;
  }

  _buildPrefixIRIMatchingPattern() {
    if (this.prefixNamesByPrefixIRI.size === 0) {
      this.prefixIRIMatchingPattern = null;
      return;
    }
    // Longest first, so `internal:nom#http://x#` wins over `internal:nom#`.
    const iris = [...this.prefixNamesByPrefixIRI.keys()]
      .sort((a, b) => b.length - a.length);
    this.prefixIRIMatchingPattern = new RegExp(
      `^(${iris.map(quoteRegExp).join('|')})`);
  }

  /**
   * @param {string} iri
   * @returns {string} `prefix:local` when possible, otherwise `<iri>`
   */
  abbreviateIRI(iri) {
    if (this.prefixIRIMatchingPattern !== null) {
      const m = this.prefixIRIMatchingPattern.exec(iri);
      if (m) {
        const localName = iri.substring(m[0].length);
        if (Prefixes.isValidLocalName(localName)) {
          return this.prefixNamesByPrefixIRI.get(m[0]) + localName;
        }
      }
    }
    return `<${iri}>`;
  }

  /**
   * Inverse of {@link abbreviateIRI}.
   * @param {string} abbreviation `<iri>` or `prefix:local`
   * @returns {string}
   */
  expandAbbreviatedIRI(abbreviation) {
    if (abbreviation.length > 0 && abbreviation.charAt(0) === '<') {
      if (abbreviation.charAt(abbreviation.length - 1) !== '>') {
        throw new Error(`The string '${abbreviation}' is not a valid abbreviation: IRIs must be enclosed in '<' and '>'.`);
      }
      return abbreviation.substring(1, abbreviation.length - 1);
    }
    const pos = abbreviation.indexOf(':');
    if (pos === -1) {
      throw new Error(`The abbreviation '${abbreviation}' is not valid (it does not contain a colon).`);
    }
    const prefix = abbreviation.substring(0, pos + 1);
    const prefixIRI = this.prefixIRIsByPrefixName.get(prefix);
    if (prefixIRI === undefined) {
      if (prefix === 'http:') {
        throw new Error(`The IRI '${abbreviation}' must be enclosed in '<' and '>' to be used as an abbreviation.`);
      }
      throw new Error(`The string '${prefix}' is not a registered prefix name.`);
    }
    return prefixIRI + abbreviation.substring(pos + 1);
  }

  canBeExpanded(iri) {
    if (iri.length > 0 && iri.charAt(0) === '<') return false;
    const pos = iri.indexOf(':');
    if (pos === -1) return false;
    return this.prefixIRIsByPrefixName.has(iri.substring(0, pos + 1));
  }

  /**
   * @param {string} prefixName must end with ':'
   * @param {string} prefixIRI
   * @returns {boolean} true iff the prefix name was NOT already registered
   */
  declarePrefix(prefixName, prefixIRI) {
    const isNew = this._declarePrefixRaw(prefixName, prefixIRI);
    this._buildPrefixIRIMatchingPattern();
    return isNew;
  }

  _declarePrefixRaw(prefixName, prefixIRI) {
    if (!prefixName.endsWith(':')) {
      throw new Error(`Prefix name '${prefixName}' should end with a colon character.`);
    }
    const existing = this.prefixNamesByPrefixIRI.get(prefixIRI);
    if (existing !== undefined && existing !== prefixName) {
      throw new Error(`The prefix IRI '${prefixIRI}' has already been associated with the prefix name '${existing}'.`);
    }
    this.prefixNamesByPrefixIRI.set(prefixIRI, prefixName);
    const previous = this.prefixIRIsByPrefixName.get(prefixName);
    this.prefixIRIsByPrefixName.set(prefixName, prefixIRI);
    return previous === undefined;
  }

  declareDefaultPrefix(defaultPrefixIRI) {
    return this.declarePrefix(':', defaultPrefixIRI);
  }

  getPrefixIRIsByPrefixName() {
    return new Map(this.prefixIRIsByPrefixName);
  }

  getPrefixIRI(prefixName) {
    return this.prefixIRIsByPrefixName.get(prefixName);
  }

  getPrefixName(prefixIRI) {
    return this.prefixNamesByPrefixIRI.get(prefixIRI);
  }

  /**
   * Register HermiT's internal prefixes, plus one `nom<i>:` prefix per named
   * individual IRI and one `anon<i>:` prefix per anonymous individual IRI.
   *
   * @param {Iterable<string>} individualIRIs
   * @param {Iterable<string>} anonIndividualIRIs
   * @returns {boolean} true iff any of these prefix names was already present
   */
  declareInternalPrefixes(individualIRIs, anonIndividualIRIs) {
    let containsPrefix = false;
    const declare = (name, iri) => {
      if (this._declarePrefixRaw(name, iri)) containsPrefix = true;
    };
    declare('def:', 'internal:def#');
    declare('defdata:', 'internal:defdata#');
    declare('nnq:', 'internal:nnq#');
    declare('all:', 'internal:all#');
    declare('prop:', 'internal:prop#');
    // NOTE: `swrl:` is deliberately NOT redeclared here — the Semantic Web
    // prefixes already own that name with a different IRI, and HermiT's
    // `declarePrefixRaw` would throw on the conflict.

    let i = 1;
    for (const iri of individualIRIs || []) {
      declare(`nom${i === 1 ? '' : i}:`, `internal:nom#${iri}`);
      i++;
    }
    let j = 1;
    for (const iri of anonIndividualIRIs || []) {
      declare(`anon${j === 1 ? '' : j}:`, `internal:anon#${iri}`);
      j++;
    }
    declare('nam:', 'internal:nam#');
    this._buildPrefixIRIMatchingPattern();
    return containsPrefix;
  }

  /** @returns {boolean} true iff any well-known prefix name was already present */
  declareSemanticWebPrefixes() {
    let containsPrefix = false;
    for (const [name, iri] of Object.entries(SEMANTIC_WEB_PREFIXES)) {
      if (this._declarePrefixRaw(name, iri)) containsPrefix = true;
    }
    this._buildPrefixIRIMatchingPattern();
    return containsPrefix;
  }

  /** @param {Prefixes|Map<string,string>} prefixes */
  addPrefixes(prefixes) {
    let containsPrefix = false;
    const entries = prefixes instanceof Prefixes
      ? prefixes.prefixIRIsByPrefixName.entries()
      : (prefixes instanceof Map ? prefixes.entries() : Object.entries(prefixes));
    for (const [name, iri] of entries) {
      if (this._declarePrefixRaw(name, iri)) containsPrefix = true;
    }
    this._buildPrefixIRIMatchingPattern();
    return containsPrefix;
  }

  toString() {
    const parts = [...this.prefixIRIsByPrefixName.entries()]
      .map(([name, iri]) => `${name}=${iri}`);
    return `{${parts.join(', ')}}`;
  }

  /** True for every IRI HermiT mints itself (starts with `internal:`). */
  static isInternalIRI(iri) {
    return typeof iri === 'string' && iri.startsWith('internal:');
  }

  static isValidLocalName(localName) {
    return LOCAL_NAME_CHECKER.test(localName);
  }
}

/** A Prefixes instance holding only the well-known Semantic Web prefixes. */
function getStandardPrefixes() {
  const p = new Prefixes();
  p.declareSemanticWebPrefixes();
  return p;
}

Prefixes.SEMANTIC_WEB_PREFIXES = SEMANTIC_WEB_PREFIXES;
Prefixes.isInternalIRI = Prefixes.isInternalIRI;

module.exports = { Prefixes, SEMANTIC_WEB_PREFIXES, getStandardPrefixes };
