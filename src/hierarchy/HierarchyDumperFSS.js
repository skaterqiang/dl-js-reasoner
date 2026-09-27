'use strict';
/**
 * src/hierarchy/HierarchyDumperFSS.js — flat functional-syntax dump of a
 * hierarchy, as a set of `SubClassOf` / `EquivalentClasses` (and the role
 * analogues) axioms.
 *
 * Port of `org.semanticweb.HermiT.hierarchy.HierarchyDumperFSS`.
 *
 * This is the `--classify` (non-pretty) output route: one axiom per line, every
 * IRI in full `<...>` form, no prefixes, no nesting.
 *
 * DIVERGENCE FROM HERMIT (deliberate, documented): HermiT iterates
 * `getAllNodesSet()` and `getChildNodes()` over `HashSet`s, so its line order is
 * unspecified. This port sorts both by the same comparator used for the
 * equivalence classes, so the dump is byte-reproducible across runs. The SET of
 * lines emitted is identical.
 */

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

/** Java's `String.compareTo` — UTF-16 code-unit order, same as JS `<`/`>`. */
function compareStrings(a, b) {
  if (a === b) return 0;
  return a < b ? -1 : 1;
}

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
 * `ObjectRoleComparator`: bottom < top < everything else, then atomic before
 * inverse, then by the inner atomic role's IRI.
 */
function objectRoleComparator(r1, r2) {
  const comparison = objectRoleClass(r1) - objectRoleClass(r2);
  if (comparison !== 0) return comparison;
  const direction = roleDirection(r1) - roleDirection(r2);
  if (direction !== 0) return direction;
  return compareStrings(innerAtomicRole(r1).iri, innerAtomicRole(r2).iri);
}

function objectRoleClass(role) {
  if (role === BOTTOM_OBJECT_ROLE) return 0;
  if (role === TOP_OBJECT_ROLE) return 1;
  return 2;
}

/** `DataRoleComparator`: bottom < top < everything else, then by IRI. */
function dataRoleComparator(r1, r2) {
  const comparison = dataRoleClass(r1) - dataRoleClass(r2);
  if (comparison !== 0) return comparison;
  return compareStrings(r1.iri, r2.iri);
}

function dataRoleClass(atomicRole) {
  if (atomicRole === BOTTOM_DATA_ROLE) return 0;
  if (atomicRole === TOP_DATA_ROLE) return 1;
  return 2;
}

/** The `AtomicRole` an `InverseRole` wraps; identity for an `AtomicRole`. */
function innerAtomicRole(role) {
  return role instanceof InverseRole ? role.getInverse() : role;
}

/** Atomic roles sort before their inverses. */
function roleDirection(role) {
  return role instanceof AtomicRole ? 0 : 1;
}

/** Sort an iterable with `comparator`, returning a fresh array. */
function sorted(iterable, comparator) {
  return [...iterable].sort(comparator);
}

class HierarchyDumperFSS {
  /**
   * @param {{print: function(string): void, println: function(string=): void}} out
   *        a `java.io.PrintWriter` stand-in — see `src/cli/Writer.js`
   */
  constructor(out) {
    this.out = out;
  }

  /**
   * Emit `EquivalentClasses` / `SubClassOf` axioms covering the whole class
   * hierarchy, then a blank line.
   *
   * @param {import('./Hierarchy').Hierarchy} atomicConceptHierarchy
   */
  printAtomicConceptHierarchy(atomicConceptHierarchy) {
    for (const node of sorted(atomicConceptHierarchy.getAllNodesSet(),
      (n1, n2) => atomicConceptComparator(n1.getRepresentative(), n2.getRepresentative()))) {
      const equivs = sorted(node.getEquivalentElements(), atomicConceptComparator);
      const representative = equivs[0];
      if (equivs.length > 1) {
        let first = true;
        for (const equiv of equivs) {
          if (first) {
            this.out.print(`EquivalentClasses( <${representative.iri}>`);
            first = false;
          } else {
            this.out.print(` <${equiv.iri}>`);
          }
        }
        this.out.print(' )');
        this.out.println();
      }
      if (representative !== THING) {
        for (const sub of sorted(node.getChildNodes(),
          (n1, n2) => atomicConceptComparator(n1.getRepresentative(), n2.getRepresentative()))) {
          const subRepresentative = sub.getRepresentative();
          if (subRepresentative !== NOTHING) {
            this.out.print(`SubClassOf( <${subRepresentative.iri}> <${representative.iri}> )`);
            this.out.println();
          }
        }
      }
    }
    this.out.println();
  }

  /**
   * Emit `EquivalentObjectProperties` / `SubObjectPropertyOf` axioms, then a
   * blank line.
   *
   * @param {import('./Hierarchy').Hierarchy} objectRoleHierarchy
   */
  printObjectPropertyHierarchy(objectRoleHierarchy) {
    for (const node of sorted(objectRoleHierarchy.getAllNodesSet(),
      (n1, n2) => objectRoleComparator(n1.getRepresentative(), n2.getRepresentative()))) {
      const equivs = sorted(node.getEquivalentElements(), objectRoleComparator);
      const representative = equivs[0];
      if (equivs.length > 1) {
        let first = true;
        for (const equiv of equivs) {
          if (first) {
            this.out.print('EquivalentObjectProperties( ');
            this._printRole(representative);
            first = false;
          } else {
            this.out.print(' ');
            this._printRole(equiv);
          }
        }
        this.out.print(' )');
        this.out.println();
      }
      if (representative !== TOP_OBJECT_ROLE) {
        for (const sub of sorted(node.getChildNodes(),
          (n1, n2) => objectRoleComparator(n1.getRepresentative(), n2.getRepresentative()))) {
          const subRepresentative = sub.getRepresentative();
          if (subRepresentative !== BOTTOM_OBJECT_ROLE) {
            this.out.print('SubObjectPropertyOf( ');
            this._printRole(subRepresentative);
            this.out.print(' ');
            this._printRole(representative);
            this.out.print(' )');
            this.out.println();
          }
        }
      }
    }
    this.out.println();
  }

  /**
   * Emit `EquivalentDataProperties` / `SubDataPropertyOf` axioms, then a blank
   * line.
   *
   * @param {import('./Hierarchy').Hierarchy} dataRoleHierarchy
   */
  printDataPropertyHierarchy(dataRoleHierarchy) {
    for (const node of sorted(dataRoleHierarchy.getAllNodesSet(),
      (n1, n2) => dataRoleComparator(n1.getRepresentative(), n2.getRepresentative()))) {
      const equivs = sorted(node.getEquivalentElements(), dataRoleComparator);
      const representative = equivs[0];
      if (equivs.length > 1) {
        let first = true;
        for (const equiv of equivs) {
          if (first) {
            this.out.print(`EquivalentDataProperties( <${representative.iri}>`);
            first = false;
          } else {
            this.out.print(` <${equiv.iri}>`);
          }
        }
        this.out.print(' )');
        this.out.println();
      }
      if (representative !== TOP_DATA_ROLE) {
        for (const sub of sorted(node.getChildNodes(),
          (n1, n2) => dataRoleComparator(n1.getRepresentative(), n2.getRepresentative()))) {
          const subRepresentative = sub.getRepresentative();
          if (subRepresentative !== BOTTOM_DATA_ROLE) {
            this.out.print(`SubDataPropertyOf( <${subRepresentative.iri}> <${representative.iri}> )`);
            this.out.println();
          }
        }
      }
    }
    this.out.println();
  }

  /** `<iri>` for an atomic role, `ObjectInverseOf( ... )` for an inverse. */
  _printRole(role) {
    if (role instanceof AtomicRole) {
      this.out.print(`<${role.iri}>`);
    } else {
      this.out.print('ObjectInverseOf( ');
      this._printRole(role.getInverse());
      this.out.print(' )');
    }
  }
}

module.exports = {
  HierarchyDumperFSS,
  atomicConceptComparator,
  objectRoleComparator,
  dataRoleComparator
};
