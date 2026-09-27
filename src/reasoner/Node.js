'use strict';

// ---------------------------------------------------------------------------
// reasoner/Node.js — the OWL API's `Node<T>` / `NodeSet<T>`, reimplemented.
//
// protege-js has no equivalent classes, and HermiT's `Reasoner` returns them
// from every public query (`getSuperClasses`, `getInstances`, …). A `Node` is a
// set of mutually *equivalent* entities (one representative plus its synonyms);
// a `NodeSet` is a set of such nodes.
//
// Entities are compared by a canonical key rather than by identity, because
// protege-js does not intern its OWL entities: two `OWLClass` objects built
// from the same IRI are `!==` but must be the same node member.
// ---------------------------------------------------------------------------

const E = require('../owl/OWLExpressions');

/**
 * A canonical identity key for anything that can appear inside a `Node`:
 * an OWL entity, an object property expression (possibly an inverse), an
 * individual (named or anonymous), or a literal.
 *
 * @param {*} x
 * @returns {string}
 */
function entityKey(x) {
  if (x === null || x === undefined) return 'null';
  if (typeof x === 'string') return `s:${x}`;
  // `atomKey` has no case for ObjectInverseOf (it would fall through to
  // `o:${String(x)}`), so route anonymous property expressions through
  // `structuralKey`, which does.
  if (E.isObjectInverseOf(x)) return E.structuralKey(x);
  return E.atomKey(x);
}

/**
 * A set of equivalent entities.
 *
 * @template T
 */
class Node {
  /**
   * @param {T|Iterable<T>} [entities] a single entity or an iterable of them
   */
  constructor(entities) {
    /** @type {Map<string, T>} key → entity, insertion ordered */
    this._entities = new Map();
    if (entities !== undefined && entities !== null) {
      if (typeof entities[Symbol.iterator] === 'function' && typeof entities !== 'string') {
        for (const e of entities) this.add(e);
      } else {
        this.add(entities);
      }
    }
  }

  /** @param {T} entity */
  add(entity) {
    if (entity === null || entity === undefined) return this;
    this._entities.set(entityKey(entity), entity);
    return this;
  }

  /** @returns {Set<T>} */
  getEntities() { return new Set(this._entities.values()); }

  /** Every entity except `entity` (compared by key). */
  getEntitiesMinus(entity) {
    const result = new Set();
    const skip = entityKey(entity);
    for (const [key, value] of this._entities) if (key !== skip) result.add(value);
    return result;
  }

  /** The first entity added — the node's canonical representative. */
  getRepresentativeElement() {
    for (const value of this._entities.values()) return value;
    return null;
  }

  getSize() { return this._entities.size; }

  isEmpty() { return this._entities.size === 0; }

  isSingleton() { return this._entities.size === 1; }

  /** @param {T} entity */
  contains(entity) { return this._entities.has(entityKey(entity)); }

  /** @returns {Iterator<T>} */
  [Symbol.iterator]() { return this._entities.values(); }

  toString() {
    return `{${[...this._entities.values()].map(String).join(', ')}}`;
  }
}

/**
 * A set of {@link Node}s.
 *
 * @template T
 */
class NodeSet {
  /**
   * @param {Node<T>|Iterable<Node<T>>|T|Iterable<T>} [nodes] nodes, or bare
   *        entities (each of which becomes its own singleton node)
   */
  constructor(nodes) {
    /** @type {Map<string, Node<T>>} node key → node */
    this._nodes = new Map();
    if (nodes !== undefined && nodes !== null) {
      const list = (typeof nodes[Symbol.iterator] === 'function' && typeof nodes !== 'string')
        ? [...nodes] : [nodes];
      for (const item of list) {
        if (item instanceof Node) this.addNode(item);
        else this.addNode(new Node(item));
      }
    }
  }

  /** @param {Node<T>} node */
  addNode(node) {
    if (node === null || node === undefined || node.isEmpty()) return this;
    // Key the node by its member keys so that two nodes holding the same
    // entities collapse into one.
    const key = [...node._entities.keys()].sort().join('|');
    this._nodes.set(key, node);
    return this;
  }

  /** @returns {Set<Node<T>>} */
  getNodes() { return new Set(this._nodes.values()); }

  /** @returns {Set<T>} every entity of every node, flattened */
  getFlattened() {
    const result = new Set();
    for (const node of this._nodes.values()) {
      for (const entity of node.getEntities()) result.add(entity);
    }
    return result;
  }

  isEmpty() { return this._nodes.size === 0; }

  isSingleton() { return this._nodes.size === 1; }

  /** @param {T} entity */
  containsEntity(entity) {
    const key = entityKey(entity);
    for (const node of this._nodes.values()) if (node._entities.has(key)) return true;
    return false;
  }

  /** @returns {Node<T>|null} */
  getNodeForEntity(entity) {
    const key = entityKey(entity);
    for (const node of this._nodes.values()) if (node._entities.has(key)) return node;
    return null;
  }

  /** @returns {Set<T>} */
  getEntitiesMinus(entity) {
    const result = new Set();
    const skip = entityKey(entity);
    for (const node of this._nodes.values()) {
      for (const [key, value] of node._entities) if (key !== skip) result.add(value);
    }
    return result;
  }

  /** @returns {Iterator<Node<T>>} */
  [Symbol.iterator]() { return this._nodes.values(); }

  toString() {
    return [...this._nodes.values()].map((n) => n.toString()).join('\n');
  }
}

// Typed aliases, mirroring the OWL API's OWLClassNode / OWLClassNodeSet etc.
// They carry no extra behaviour; they exist so callers can be explicit.
const OWLClassNode = Node;
const OWLClassNodeSet = NodeSet;
const OWLObjectPropertyNode = Node;
const OWLObjectPropertyNodeSet = NodeSet;
const OWLDataPropertyNode = Node;
const OWLDataPropertyNodeSet = NodeSet;
const OWLNamedIndividualNode = Node;
const OWLNamedIndividualNodeSet = NodeSet;

module.exports = {
  Node,
  NodeSet,
  entityKey,
  OWLClassNode,
  OWLClassNodeSet,
  OWLObjectPropertyNode,
  OWLObjectPropertyNodeSet,
  OWLDataPropertyNode,
  OWLDataPropertyNodeSet,
  OWLNamedIndividualNode,
  OWLNamedIndividualNodeSet
};
