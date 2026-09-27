'use strict';
/**
 * src/hierarchy/HierarchyPrinterFSS.js — nested, prefix-abbreviated
 * functional-syntax rendering of a hierarchy, wrapped in an `Ontology( ... )`
 * frame with its own `Prefix( ... )` declarations.
 *
 * Port of `org.semanticweb.HermiT.hierarchy.HierarchyPrinterFSS`.
 *
 * This is the `--classify --prettyPrint` output route. Where
 * {@link HierarchyDumperFSS} emits one flat axiom per line with full `<iri>`s,
 * this printer indents by depth, abbreviates IRIs against a synthesized prefix
 * map, and emits `Declaration( ... )` axioms for the entities it mentions.
 *
 * DIVERGENCE FROM HERMIT (deliberate, documented): the collected prefix IRIs
 * are sorted before being assigned `a1:`, `a2:`, ... names. HermiT gets this
 * for free from `TreeSet`; the port states it explicitly so the output is
 * reproducible.
 */

const { Prefixes } = require('../Prefixes');
const {
  AtomicRole,
  InverseRole,
  THING,
  NOTHING,
  TOP_OBJECT_ROLE,
  BOTTOM_OBJECT_ROLE,
  TOP_DATA_ROLE,
  BOTTOM_DATA_ROLE
} = require('../model/DLPredicate');

const OWL_PREFIX_IRI = Prefixes.SEMANTIC_WEB_PREFIXES['owl:'];

/** Java's `String.compareTo` — UTF-16 code-unit order, same as JS `<`/`>`. */
function compareStrings(a, b) {
  if (a === b) return 0;
  return a < b ? -1 : 1;
}

/**
 * `Hierarchy.IdentityTransformer` — the identity element transformer used to
 * re-sort a hierarchy without changing its elements.
 */
const IdentityTransformer = Object.freeze({
  transform: (element) => element,
  determineRepresentative: (oldRepresentative, newEquivalentElements) => (
    newEquivalentElements.has(oldRepresentative)
      ? oldRepresentative
      : [...newEquivalentElements][0])
});

/** `AtomicConceptComparator`: Nothing < Thing < everything else, then by IRI. */
function atomicConceptComparator(c1, c2) {
  const comparison = atomicConceptClass(c1) - atomicConceptClass(c2);
  if (comparison !== 0) return comparison;
  return compareStrings(c1.iri, c2.iri);
}

function atomicConceptClass(atomicConcept) {
  if (atomicConcept === NOTHING) return 0;
  if (atomicConcept === THING) return 1;
  return 2;
}

/**
 * `RoleComparator`: object bottom < object top < data bottom < data top <
 * everything else, then atomic before inverse, then by inner atomic IRI.
 *
 * Unlike {@link HierarchyDumperFSS}'s two separate role comparators, the pretty
 * printer uses one comparator spanning both role kinds, because it may print
 * object and data hierarchies into the same `Ontology( ... )` frame.
 */
function roleComparator(r1, r2) {
  const comparison = roleClass(r1) - roleClass(r2);
  if (comparison !== 0) return comparison;
  const direction = roleDirection(r1) - roleDirection(r2);
  if (direction !== 0) return direction;
  return compareStrings(innerAtomicRole(r1).iri, innerAtomicRole(r2).iri);
}

function roleClass(role) {
  if (role === BOTTOM_OBJECT_ROLE) return 0;
  if (role === TOP_OBJECT_ROLE) return 1;
  if (role === BOTTOM_DATA_ROLE) return 2;
  if (role === TOP_DATA_ROLE) return 3;
  return 4;
}

function innerAtomicRole(role) {
  return role instanceof InverseRole ? role.getInverse() : role;
}

function roleDirection(role) {
  return role instanceof AtomicRole ? 0 : 1;
}

class HierarchyPrinterFSS {
  /**
   * @param {{print: function(string): void, println: function(string=): void}} out
   * @param {string} defaultPrefixIRI normally `<ontologyIRI>#`
   */
  constructor(out, defaultPrefixIRI) {
    this.out = out;
    this.defaultPrefixIRI = defaultPrefixIRI;
    /** @type {Set<string>} */
    this.prefixIRIs = new Set();
    this.prefixIRIs.add(defaultPrefixIRI);
    this.prefixIRIs.add(OWL_PREFIX_IRI);
    /** @type {?Prefixes} built by {@link startPrinting} */
    this.prefixes = null;
  }

  /**
   * Collect the `...#` namespace of every class IRI so it can be abbreviated.
   *
   * Mirrors HermiT: only a `#` separator is recognised, so slash-namespaced
   * ontologies simply get no extra prefix and print as `<iri>`.
   *
   * @param {Iterable<{iri: string}>} atomicConcepts
   */
  loadAtomicConceptPrefixIRIs(atomicConcepts) {
    for (const atomicConcept of atomicConcepts) {
      this._loadPrefixIRI(atomicConcept.iri);
    }
  }

  /**
   * Collect the `...#` namespace of every role IRI.
   * @param {Iterable<{iri: string}>} atomicRoles
   */
  loadAtomicRolePrefixIRIs(atomicRoles) {
    for (const atomicRole of atomicRoles) {
      this._loadPrefixIRI(atomicRole.iri);
    }
  }

  _loadPrefixIRI(iri) {
    if (typeof iri !== 'string') return;
    const hashIndex = iri.indexOf('#');
    if (hashIndex === -1) return;
    const prefixIRI = iri.substring(0, hashIndex + 1);
    const localName = iri.substring(hashIndex + 1);
    if (Prefixes.isValidLocalName(localName)) this.prefixIRIs.add(prefixIRI);
  }

  /**
   * Build the prefix map and emit the `Prefix( ... )` declarations plus the
   * opening `Ontology(<iri>` line. Must be called before any `print*Hierarchy`.
   */
  startPrinting() {
    this.prefixes = new Prefixes();
    this.prefixes.declareDefaultPrefix(this.defaultPrefixIRI);
    // HermiT declares `owl:` unconditionally; that throws when the ontology's
    // own default prefix IRI IS the OWL namespace. Guarded here.
    if (this.prefixes.getPrefixName(OWL_PREFIX_IRI) === undefined) {
      this.prefixes.declarePrefix('owl:', OWL_PREFIX_IRI);
    }
    let index = 1;
    for (const prefixIRI of [...this.prefixIRIs].sort(compareStrings)) {
      if (prefixIRI !== this.defaultPrefixIRI && prefixIRI !== OWL_PREFIX_IRI) {
        this.prefixes.declarePrefix(`a${index++}:`, prefixIRI);
      }
    }
    for (const [name, iri] of this.prefixes.getPrefixIRIsByPrefixName()) {
      if (name !== 'owl:') this.out.println(`Prefix(${name}=<${iri}>)`);
    }
    this.out.println();
    this.out.println(`Ontology(<${this.prefixes.getPrefixIRI(':')}>`);
    this.out.println();
  }

  /**
   * Print the class hierarchy, indented by depth.
   * @param {import('./Hierarchy').Hierarchy} atomicConceptHierarchy
   */
  printAtomicConceptHierarchy(atomicConceptHierarchy) {
    const sortedHierarchy = atomicConceptHierarchy.transform(
      IdentityTransformer, atomicConceptComparator);
    const printer = new AtomicConceptPrinter(this, sortedHierarchy.getBottomNode());
    sortedHierarchy.traverseDepthFirst(printer);
    printer.printNode(0, sortedHierarchy.getBottomNode(), null, true);
  }

  /**
   * Print an object- or data-property hierarchy, indented by depth.
   *
   * @param {import('./Hierarchy').Hierarchy} roleHierarchy
   * @param {boolean} objectProperties true → `SubObjectPropertyOf` /
   *        `EquivalentObjectProperties`; false → the data-property analogues
   */
  printRoleHierarchy(roleHierarchy, objectProperties) {
    const sortedHierarchy = roleHierarchy.transform(IdentityTransformer, roleComparator);
    const printer = new RolePrinter(this, sortedHierarchy, objectProperties);
    sortedHierarchy.traverseDepthFirst(printer);
    printer.printNode(0, sortedHierarchy.getBottomNode(), null, true);
  }

  /** Close the `Ontology( ... )` frame. */
  endPrinting() {
    this.out.println();
    this.out.println(')');
    this.out.flush();
  }
}

/**
 * Shared body of `AtomicConceptPrinter.printNode` / `RolePrinter.printNode`:
 * indent, then join the non-empty fragments with single spaces.
 */
function printNodeLine(printer, level, fragments) {
  printer.out.print(' '.repeat(2 * level));
  printer.out.print(fragments.filter((f) => f !== null && f !== '').join(' '));
  printer.out.println();
}

/** `HierarchyPrinterFSS.AtomicConceptPrinter`. */
class AtomicConceptPrinter {
  constructor(owner, bottomNode) {
    this.owner = owner;
    this.bottomNode = bottomNode;
  }

  redirect() { return true; }

  visit(level, node, parentNode, firstVisit) {
    if (node !== this.bottomNode) this.printNode(level, node, parentNode, firstVisit);
  }

  printNode(level, node, parentNode, firstVisit) {
    const equivalences = node.getEquivalentElements();
    const printSubClassOf = parentNode !== null;
    const printEquivalences = firstVisit && equivalences.size > 1;
    let printDeclarations = false;
    if (firstVisit) {
      for (const atomicConcept of equivalences) {
        if (needsConceptDeclaration(atomicConcept)) { printDeclarations = true; break; }
      }
    }
    if (!printSubClassOf && !printEquivalences && !printDeclarations) return;

    const fragments = [];
    if (printSubClassOf) {
      fragments.push(`SubClassOf( ${this._print(node.getRepresentative())} `
        + `${this._print(parentNode.getRepresentative())} )`);
    }
    if (printEquivalences) {
      const parts = [...equivalences].map((c) => this._print(c));
      fragments.push(`EquivalentClasses(${parts.map((p) => ` ${p}`).join('')} )`);
    }
    if (printDeclarations) {
      for (const atomicConcept of equivalences) {
        if (needsConceptDeclaration(atomicConcept)) {
          fragments.push(`Declaration( Class( ${this._print(atomicConcept)} ) )`);
        }
      }
    }
    printNodeLine(this.owner, level, fragments);
  }

  _print(atomicConcept) {
    return this.owner.prefixes.abbreviateIRI(atomicConcept.iri);
  }
}

function needsConceptDeclaration(atomicConcept) {
  return atomicConcept !== NOTHING && atomicConcept !== THING;
}

/** `HierarchyPrinterFSS.RolePrinter`. */
class RolePrinter {
  constructor(owner, hierarchy, objectProperties) {
    this.owner = owner;
    this.hierarchy = hierarchy;
    this.objectProperties = objectProperties;
  }

  redirect() { return true; }

  visit(level, node, parentNode, firstVisit) {
    if (node !== this.hierarchy.getBottomNode()) {
      this.printNode(level, node, parentNode, firstVisit);
    }
  }

  printNode(level, node, parentNode, firstVisit) {
    const equivalences = node.getEquivalentElements();
    const printSubPropertyOf = parentNode !== null;
    const printEquivalences = firstVisit && equivalences.size > 1;
    let printDeclarations = false;
    if (firstVisit) {
      for (const role of equivalences) {
        if (needsRoleDeclaration(role)) { printDeclarations = true; break; }
      }
    }
    if (!printSubPropertyOf && !printEquivalences && !printDeclarations) return;

    const subKeyword = this.objectProperties ? 'SubObjectPropertyOf' : 'SubDataPropertyOf';
    const equivKeyword = this.objectProperties
      ? 'EquivalentObjectProperties' : 'EquivalentDataProperties';
    const entityKeyword = this.objectProperties ? 'ObjectProperty' : 'DataProperty';

    const fragments = [];
    if (printSubPropertyOf) {
      fragments.push(`${subKeyword}( ${this._print(node.getRepresentative())} `
        + `${this._print(parentNode.getRepresentative())} )`);
    }
    if (printEquivalences) {
      const parts = [...equivalences].map((r) => this._print(r));
      fragments.push(`${equivKeyword}(${parts.map((p) => ` ${p}`).join('')} )`);
    }
    if (printDeclarations) {
      for (const role of equivalences) {
        if (needsRoleDeclaration(role)) {
          fragments.push(`Declaration( ${entityKeyword}( ${this._print(role)} ) )`);
        }
      }
    }
    printNodeLine(this.owner, level, fragments);
  }

  _print(role) {
    if (role instanceof AtomicRole) return this.owner.prefixes.abbreviateIRI(role.iri);
    return `ObjectInverseOf( ${this._print(role.getInverse())} )`;
  }
}

function needsRoleDeclaration(role) {
  return role !== BOTTOM_OBJECT_ROLE
    && role !== TOP_OBJECT_ROLE
    && role !== BOTTOM_DATA_ROLE
    && role !== TOP_DATA_ROLE
    && role instanceof AtomicRole;
}

module.exports = {
  HierarchyPrinterFSS,
  AtomicConceptPrinter,
  RolePrinter,
  IdentityTransformer,
  atomicConceptComparator,
  roleComparator
};
