'use strict';

// ---------------------------------------------------------------------------
// model/Atom.js — predicate applied to terms.
//
// Mirrors org.semanticweb.HermiT.model.Atom. An Atom is interned: identical
// predicate + argument tuples are the same object, so extension tables can use
// object identity for deduplication.
// ---------------------------------------------------------------------------

const { Variable } = require('./Term');

class Atom {
  /**
   * @param {DLPredicate} dlPredicate
   * @param {Term[]} arguments
   */
  constructor(dlPredicate, args) {
    this.dlPredicate = dlPredicate;
    this.arguments = args;
    if (args.length !== dlPredicate.getArity()) {
      throw new Error(
        `Atom arity mismatch: predicate ${dlPredicate} has arity ${dlPredicate.getArity()}, got ${args.length} arguments`
      );
    }
  }

  getArity() { return this.arguments.length; }
  getArgument(index) { return this.arguments[index]; }
  /** The argument at index if it is a Variable, else null. */
  getArgumentVariable(index) {
    const t = this.arguments[index];
    return t instanceof Variable ? t : null;
  }
  getDLPredicate() { return this.dlPredicate; }

  toString() {
    return `${this.dlPredicate}(${this.arguments.map(String).join(', ')})`;
  }
}

// ---- interning --------------------------------------------------------------

const _atoms = new Map();

/**
 * Interned Atom factory (mirrors Atom.create).
 * @param {DLPredicate} predicate
 * @param {...Term} args
 */
function createAtom(predicate, ...args) {
  const key = `${predKey(predicate)}(${args.map(termKey).join(',')})`;
  let a = _atoms.get(key);
  if (!a) {
    a = new Atom(predicate, args);
    _atoms.set(key, a);
  }
  return a;
}

function predKey(p) {
  // Predicates are interned themselves; their toString() is a canonical key.
  return `${p.kind}:${p.toString()}`;
}

function termKey(t) {
  return `${t.kind}:${t.toString()}`;
}

module.exports = { Atom, createAtom };
