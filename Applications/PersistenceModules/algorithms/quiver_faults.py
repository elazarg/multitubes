#!/usr/bin/env python3
"""Exact section-space sensitivity for integer edge matrices."""
import argparse
from bisect import bisect_left
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction
from operator import index
from random import Random
from time import perf_counter

import numpy as np


@dataclass(frozen=True)
class Edge:
    source: int
    target: int
    transfer: np.ndarray


def zeros(m, n):
    return np.zeros((m, n), dtype=object)


def unit(n):
    return np.eye(n, dtype=object)


def integer_matrix(transfer, shape):
    raw = np.asarray(transfer, dtype=object)
    if raw.shape != shape:
        raise ValueError(f"edge matrix has shape {raw.shape}, expected {shape}")
    try:
        return np.array([index(value) for value in raw.flat], dtype=object).reshape(shape)
    except TypeError as exc:
        raise ValueError("edge matrix entries must be integers") from exc


def normalized(row):
    pivot = min(row)
    return {i: a / row[pivot] for i, a in row.items()}


def axpy(row, other_row, scale, modulus=None):
    for i, value in other_row.items():
        new = row.get(i, 0) + scale * value
        if modulus is not None:
            new %= modulus
        if new:
            row[i] = new
        elif i in row:
            del row[i]


def eliminate(row, echelon, modulus=None):
    if modulus is None:
        row = {i: Fraction(a) for i, a in row.items() if a}
    else:
        row = {i: int(a) % modulus for i, a in row.items() if int(a) % modulus}
    while row:
        pivot = min(row)
        if pivot not in echelon:
            if modulus is None:
                echelon[pivot] = normalized(row)
            else:
                inverse = pow(row[pivot], -1, modulus)
                echelon[pivot] = {i: (a * inverse) % modulus for i, a in row.items()}
            return
        axpy(row, echelon[pivot], -row[pivot], modulus)


def exact_rank(matrix):
    echelon = {}
    for row in matrix:
        eliminate(dict(enumerate(row)), echelon)
    return len(echelon)


class Tree:
    """A validated quiver and its out-tree. If supplied, modulus must be prime."""

    def __init__(self, dims, edges, parent_edge, modulus=None):
        self.modulus = None if modulus is None else index(modulus)
        if self.modulus is not None and self.modulus < 2:
            raise ValueError("the modulus must be a prime")
        dims = [index(d) for d in dims]
        if not dims or min(dims) < 0:
            raise ValueError("supply a nonempty list of nonnegative stalk dimensions")
        self.dims = dims
        self.n = len(dims)
        self.edges = []
        for edge in edges:
            u, v = index(edge.source), index(edge.target)
            if not (0 <= u < self.n and 0 <= v < self.n):
                raise ValueError("edge endpoints must be vertex indices")
            self.edges.append(Edge(u, v, integer_matrix(edge.transfer, (dims[v], dims[u]))))
        parent_edge = [None if e is None else index(e) for e in parent_edge]
        if len(parent_edge) != self.n or parent_edge.count(None) != 1:
            raise ValueError("parent_edge must give exactly one edge per non-root vertex")
        self.root = parent_edge.index(None)
        self.tree_edges = {e: v for v, e in enumerate(parent_edge) if e is not None}
        if len(self.tree_edges) != self.n - 1 or any(
                not 0 <= e < len(self.edges) for e in self.tree_edges):
            raise ValueError("tree edge IDs must be valid and distinct")
        self.checks = [e for e in range(len(self.edges)) if e not in self.tree_edges]
        edges = self.edges
        self.parent = [self.root] * self.n
        children = [[] for _ in dims]
        self.depth = [0] * self.n
        jumps = [unit(d) for d in dims]
        for e, v in self.tree_edges.items():
            if edges[e].target != v:
                raise ValueError("each tree edge must point to its indexed vertex")
            u = edges[e].source
            self.parent[v] = u
            children[u].append(v)
            jumps[v] = edges[e].transfer

        self.order = []
        self.start, self.end = [0] * self.n, [0] * self.n
        todo = [(False, self.root)]
        while todo:
            leaving, v = todo.pop()
            if leaving:
                self.end[v] = len(self.order)
            else:
                self.start[v] = len(self.order)
                self.order.append(v)
                self.depth[v] = self.depth[self.parent[v]] + (v != self.root)
                todo.append((True, v))
                todo.extend((False, w) for w in reversed(children[v]))
        if len(self.order) != self.n:
            raise ValueError("the selected tree must reach every vertex")
        self.up, self.jump = [self.parent], [jumps]
        for _ in range(1, max(self.depth).bit_length()):
            previous_up, previous_jump = self.up[-1], self.jump[-1]
            self.up.append([previous_up[previous_up[v]] for v in range(self.n)])
            self.jump.append([self.multiply(previous_jump[v], previous_jump[previous_up[v]])
                              for v in range(self.n)])
        self.from_root = [None] * self.n
        self.from_root[self.root] = unit(dims[self.root])
        for v in self.order[1:]:
            self.from_root[v] = self.multiply(jumps[v], self.from_root[self.parent[v]])

    def failure_ids(self, failures):
        numbers = sorted({index(e) for e in failures})
        if numbers and (numbers[0] < 0 or numbers[-1] >= len(self.edges)):
            raise ValueError("failure edge ID out of range")
        return numbers

    def multiply(self, left, right):
        product = left @ right
        return product if self.modulus is None else product % self.modulus

    def ancestor(self, a, v):
        return self.start[a] <= self.start[v] < self.end[a]

    def product(self, a, v):
        distance = self.depth[v] - self.depth[a]
        product = unit(self.dims[v])
        while distance:
            bit = distance.bit_length() - 1
            product = self.multiply(product, self.jump[bit][v])
            v = self.up[bit][v]
            distance -= 1 << bit
        assert v == a
        return product

    def lca(self, u, v):
        if self.ancestor(u, v):
            return u
        if self.ancestor(v, u):
            return v
        for up in reversed(self.up):
            if not self.ancestor(up[u], v):
                u = up[u]
        return self.parent[u]

    def incidences(self, number):
        edge = self.edges[number]
        return ((edge.source, -edge.transfer), (edge.target, unit(self.dims[edge.target])))

    def defect_block(self, number, a):
        target = self.edges[number].target
        value = zeros(self.dims[target], self.dims[a])
        for v, coefficient in self.incidences(number):
            if self.ancestor(a, v):
                value += coefficient @ self.product(a, v)
        return value


def gram_single_faults(tree):
    """Section dimensions for all single-edge deletions plus the original."""
    if tree.modulus is not None:
        raise ValueError("the Gram batch requires ordered-field arithmetic")
    dims, root = tree.dims, tree.root
    root_gram = zeros(dims[root], dims[root])
    mixed = [zeros(dims[root], d) for d in dims]
    diagonal = [zeros(d, d) for d in dims]
    check_gram = {}
    for e in tree.checks:
        (u, U), (v, V) = tree.incidences(e)
        residual = U @ tree.from_root[u] + V @ tree.from_root[v]
        check_gram[e] = residual.T @ residual
        root_gram += check_gram[e]
        mixed[u] += residual.T @ U
        mixed[v] += residual.T @ V
        diagonal[u] += U.T @ U
        diagonal[v] += V.T @ V
        a = tree.lca(u, v)
        left = U @ tree.product(a, u)
        right = V @ tree.product(a, v)
        cross = left.T @ right
        diagonal[a] += cross + cross.T

    for v in reversed(tree.order[1:]):
        u = tree.parent[v]
        transfer = tree.jump[0][v]
        mixed[u] += mixed[v] @ transfer
        diagonal[u] += transfer.T @ diagonal[v] @ transfer

    answers = {}
    for e, v in tree.tree_edges.items():
        gram = np.block([[root_gram, mixed[v]], [mixed[v].T, diagonal[v]]])
        answers[e] = dims[root] + dims[v] - exact_rank(gram)
    for e in tree.checks:
        answers[e] = dims[root] - exact_rank(root_gram - check_gram[e])
    return dims[root] - exact_rank(root_gram), answers


class SegmentLayout:
    """Canonical preorder intervals anchored at least common ancestors."""
    def __init__(self, tree):
        self.tree = tree
        self.width = 1 << (tree.n - 1).bit_length()
        self.anchor = [None] * (2 * self.width)
        for i, v in enumerate(tree.order):
            self.anchor[self.width + i] = v
        for node in range(self.width - 1, 0, -1):
            a, b = self.anchor[2 * node:2 * node + 2]
            self.anchor[node] = a if b is None else tree.lca(a, b)

        self.from_parent_anchor = [None] * (2 * self.width)
        for node in range(2, 2 * self.width):
            v = self.anchor[node]
            if v is not None:
                self.from_parent_anchor[node] = tree.product(self.anchor[node // 2], v)

    def lifted_incidence(self, vertex, coefficient):
        node = self.tree.start[vertex] + self.width
        while True:
            yield node, coefficient
            if node == 1:
                return
            coefficient = self.tree.multiply(coefficient, self.from_parent_anchor[node])
            node //= 2

    def canonical(self, start, end):
        left = start + self.width
        right = end + self.width
        while left < right:
            if left % 2 == 1:
                yield left
                left += 1
            if right % 2 == 1:
                right -= 1
                yield right
            left //= 2
            right //= 2


class GramFaultOracle(SegmentLayout):
    """Exact range sums of transported incidence-pair products."""
    def __init__(self, tree):
        if tree.modulus is not None:
            raise ValueError("the Gram index requires ordered-field arithmetic")
        super().__init__(tree)
        self.buckets = {}
        for number in tree.checks:
            incidence_lists = [list(self.lifted_incidence(v, coefficient))
                               for v, coefficient in tree.incidences(number)]
            for first in incidence_lists:
                for second in incidence_lists:
                    for i, left in first:
                        for j, right in second:
                            term = left.T @ right
                            if (i, j) in self.buckets:
                                self.buckets[i, j] += term
                            else:
                                self.buckets[i, j] = term

    def cover(self, a):
        tree = self.tree
        return [(node, tree.product(a, self.anchor[node]))
                for node in self.canonical(tree.start[a], tree.end[a])]

    def query(self, failures):
        tree = self.tree
        failures = tree.failure_ids(failures)
        free = [tree.root] + [tree.tree_edges[e] for e in failures if e in tree.tree_edges]
        covers = [self.cover(a) for a in free]
        blocks = []
        for k, a in enumerate(free):
            row = []
            for l, b in enumerate(free):
                gram = zeros(tree.dims[a], tree.dims[b])
                for i, left in covers[k]:
                    for j, right in covers[l]:
                        value = self.buckets.get((i, j))
                        if value is not None:
                            gram += left.T @ value @ right
                row.append(gram)
            blocks.append(row)
        gram = np.block(blocks)
        for e in failures:
            if e not in tree.tree_edges:
                residual = np.concatenate([tree.defect_block(e, a) for a in free], axis=1)
                gram -= residual.T @ residual
        return free, gram

    def dimension(self, failures):
        _, gram = self.query(failures)
        return len(gram) - exact_rank(gram)


class Bucket:
    """Segment tree of compressed bases, keyed by check-edge ID."""
    def __init__(self, entries, modulus):
        self.edges = [e for e, _ in entries]
        self.width = 1 << (len(entries) - 1).bit_length()
        self.bases = [{} for _ in range(2 * self.width)]
        for i, (_, matrix) in enumerate(entries, self.width):
            for row in matrix:
                eliminate(dict(enumerate(row)), self.bases[i], modulus)
        for i in range(self.width - 1, 0, -1):
            for child in (2 * i, 2 * i + 1):
                for row in self.bases[child].values():
                    eliminate(row, self.bases[i], modulus)

    def basis_rows(self, excluded):
        if not excluded:
            yield from self.bases[1].values()
            return
        beginning = 0
        positions = sorted(bisect_left(self.edges, e) for e in excluded)
        for end in positions + [len(self.edges)]:
            left, right = beginning + self.width, end + self.width
            while left < right:
                if left % 2 == 1:
                    yield from self.bases[left].values()
                    left += 1
                if right % 2 == 1:
                    right -= 1
                    yield from self.bases[right].values()
                left //= 2
                right //= 2
            beginning = end + 1


class SpanFaultOracle(SegmentLayout):
    """Transport compressed row spans, including over small finite fields."""
    def __init__(self, tree):
        super().__init__(tree)
        self.modulus = tree.modulus
        entries = defaultdict(list)
        for e in tree.checks:
            ((u, U), (v, V)) = tree.incidences(e)
            right = list(self.lifted_incidence(v, V))
            for i, left_block in self.lifted_incidence(u, U):
                for j, right_block in right:
                    entries[i, j].append((e, np.concatenate([left_block, right_block], axis=1)))
        self.buckets = {pair: Bucket(rows, self.modulus) for pair, rows in entries.items()}

    def query(self, failures):
        tree = self.tree
        failures = tree.failure_ids(failures)
        free = [tree.root] + [tree.tree_edges[e] for e in failures if e in tree.tree_edges]
        boundaries = {0, tree.n}
        for a in free:
            boundaries.update((tree.start[a], tree.end[a]))
        split = sorted(boundaries)
        selected = []
        for left, right in zip(split, split[1:]):
            selected.extend(self.canonical(left, right))
        selected_set = set(selected)

        def selected_ancestor(v):
            node = tree.start[v] + self.width
            while node not in selected_set:
                node //= 2
            return node

        excluded = defaultdict(list)
        for e in failures:
            if e not in tree.tree_edges:
                edge = tree.edges[e]
                excluded[selected_ancestor(edge.source), selected_ancestor(edge.target)].append(e)
        anchor_map = {}
        for i in selected:
            a = self.anchor[i]
            anchor_map[i] = np.concatenate([tree.product(s, a) if tree.ancestor(s, a)
                                            else zeros(tree.dims[a], tree.dims[s])
                                            for s in free], axis=1)
        echelon = {}
        for i in selected:
            for j in selected:
                bucket = self.buckets.get((i, j))
                if bucket is not None:
                    transfer = np.concatenate([anchor_map[i], anchor_map[j]], axis=0)
                    for row in bucket.basis_rows(excluded.get((i, j), [])):
                        pulled = {}
                        for index, coefficient in row.items():
                            axpy(pulled, dict(enumerate(transfer[index])), coefficient, self.modulus)
                        eliminate(pulled, echelon, self.modulus)
        return free, echelon

    def dimension(self, failures):
        free, echelon = self.query(failures)
        return sum(self.tree.dims[a] for a in free) - len(echelon)


def rooted_resolve(tree, failures):
    """Rebuild the small section matrix for an individual failure set."""
    failures = set(tree.failure_ids(failures))
    free = [tree.root] + [tree.tree_edges[e] for e in failures if e in tree.tree_edges]
    width = sum(tree.dims[v] for v in free)
    echelon = {}
    for e in tree.checks:
        if e not in failures:
            residual = np.concatenate([tree.defect_block(e, a) for a in free], axis=1)
            for row in residual:
                eliminate(dict(enumerate(row)), echelon, tree.modulus)
            if len(echelon) == width:
                break
    return width - len(echelon)


def sparse_rows(dims, edges, vertex_order=None):
    if vertex_order is None:
        vertex_order = range(len(dims))
    offset = [0] * len(dims)
    columns = 0
    for vertex in vertex_order:
        offset[vertex] = columns
        columns += dims[vertex]
    for e, edge in enumerate(edges):
        for i, coefficients in enumerate(edge.transfer):
            row = {int(offset[edge.source] + j): -int(a)
                   for j, a in enumerate(coefficients) if a}
            axpy(row, {int(offset[edge.target] + i): 1}, 1)
            yield e, i, row


def full_resolve(dims, edges, failures, modulus=None):
    """Uncompressed rank, constructed directly from the original graph."""
    echelon = {}
    for e, _, row in sparse_rows(dims, edges):
        if e not in failures:
            eliminate(row, echelon, modulus)
    return sum(dims) - len(echelon)


def dual_batch(dims, edges, vertex_order=None):
    """Sparse one-elimination algorithm with coordinate-restricted dual basis."""
    echelon, expressions = {}, {}
    label_by_row = []
    restricted = [dict() for _ in edges]
    for index, (edge, local_row, data) in enumerate(sparse_rows(dims, edges, vertex_order)):
        label_by_row.append((edge, local_row))
        row = {i: Fraction(a) for i, a in data.items()}
        expression = {index: Fraction(1)}
        while row:
            pivot = min(row)
            if pivot not in echelon:
                scale = row[pivot]
                echelon[pivot] = normalized(row)
                expressions[pivot] = {i: a / scale for i, a in expression.items()}
                break
            scale = -row[pivot]
            axpy(row, echelon[pivot], scale)
            axpy(expression, expressions[pivot], scale)
        else:
            dependency = defaultdict(dict)
            for i, a in expression.items():
                e, local = label_by_row[i]
                dependency[e][local] = a
            for e, restrictions in dependency.items():
                eliminate(restrictions, restricted[e])
    initial = sum(dims) - len(echelon)
    return initial, {e: initial + dims[edge.target] - len(restricted[e])
                     for e, edge in enumerate(edges)}


def random_case(rng, n, extra, max_dim, workload):
    if workload == "heterogeneous":
        dims = [rng.randrange(max_dim + 1) for _ in range(n)]
    else:
        dims = [max_dim] * n

    def edge(u, v, tag):
        if workload == "heterogeneous":
            matrix = np.array([rng.randrange(-1, 2) for _ in range(dims[v] * dims[u])],
                              dtype=object).reshape(dims[v], dims[u])
        else:
            matrix = zeros(max_dim, max_dim)
            for i in range(max_dim):
                if i == 0:
                    matrix[i, i] = 1
                elif workload in ("redundant", "star"):
                    matrix[i, i] = (i + u + v + tag) % 3 != 0
                else:
                    matrix[i, i] = rng.randrange(0, 2)
                    matrix[i, 0] = rng.randrange(-1, 2)
        return Edge(u, v, matrix)

    edges = []
    parent_edge = [None]
    for v in range(1, n):
        u = (v - 1 if workload == "line" else
             0 if workload == "star" else
             rng.randrange(v) if workload == "heterogeneous" else (v - 1) // 2)
        parent_edge.append(len(edges))
        edges.append(edge(u, v, 0))
    for i in range(extra):
        if workload == "star":
            u = v = i % n
        elif workload == "local":
            u = i % n
            v = (u + 1) % n
        else:
            u, v = rng.randrange(n), rng.randrange(n)
        edges.append(edge(u, v, i + 1))
    return dims, edges, parent_edge


def check():
    dims = [1, 2, 1]
    edges = [Edge(0, 1, np.array([[1], [0]], dtype=object)),
             Edge(1, 2, np.array([[0, 1]], dtype=object)),
             Edge(2, 0, unit(1))]
    tree = Tree(dims, edges, [None, 0, 1])
    assert gram_single_faults(tree) == (0, {0: 2, 1: 1, 2: 1})
    assert SpanFaultOracle(tree).dimension({0, 1}) == 3

    for dtype in (np.int64, object):
        large = np.array([[np.int64(2 ** 32)]], dtype=dtype)
        tree = Tree([1, 1], [Edge(0, 1, [[0]]), Edge(1, 0, large)], [None, 0])
        assert gram_single_faults(tree) == (0, {0: 1, 1: 1})
        assert SpanFaultOracle(tree).dimension({0}) == GramFaultOracle(tree).dimension({0}) == 1

    edges = [Edge(0, 0, zeros(1, 1)), Edge(0, 0, zeros(1, 1))]
    tree = Tree([1], edges, [None], 2)
    assert SpanFaultOracle(tree).dimension(set()) == 0

    rng = Random(771711)
    cases, queries = 0, 0
    for workload in ("heterogeneous", "redundant", "line", "local"):
        for n in range(1, 17):
            for _ in range(5):
                dims, edges, parent_edge = random_case(rng, n, rng.randrange(2 * n + 1),
                                                       rng.randrange(1, 5), workload)
                tree = Tree(dims, edges, parent_edge)
                initial, all_single = gram_single_faults(tree)
                assert (initial, all_single) == dual_batch(dims, edges)
                assert initial == full_resolve(dims, edges, set())
                oracle = GramFaultOracle(tree)
                spans = SpanFaultOracle(tree)
                prime = rng.choice([2, 3, 5])
                modular_tree = Tree(dims, edges, parent_edge, prime)
                spans_mod = SpanFaultOracle(modular_tree)
                for e, actual in all_single.items():
                    expected = full_resolve(dims, edges, {e})
                    assert actual == expected == oracle.dimension({e}) == spans.dimension({e})
                    queries += 1
                for _ in range(6):
                    failures = set(rng.sample(range(len(edges)),
                                    rng.randrange(min(5, len(edges)) + 1)))
                    expected = full_resolve(dims, edges, failures)
                    assert rooted_resolve(tree, failures) == expected == oracle.dimension(failures)
                    assert expected == spans.dimension(failures)
                    modular_expected = full_resolve(dims, edges, failures, prime)
                    assert spans_mod.dimension(failures) == modular_expected
                    assert rooted_resolve(modular_tree, failures) == modular_expected
                    queries += 1
                cases += 1
    print(f"{cases} instances and {queries} deletion queries passed")


def benchmark():
    rng = Random(229313)
    print("case,n,m,section_dimension,tree_cuts_with_growth,gram_batch_s,dual_batch_s,"
          "repeated_rooted_s,gram_index_prep_s,gram_100_queries_s,"
          "span_index_prep_s,span_100_queries_s")
    for workload in ("redundant", "line", "local", "star"):
        for n in (80, 160, 320):
            dims, edges, parent_edge = random_case(rng, n, n, 3, workload)
            start = perf_counter()
            tree = Tree(dims, edges, parent_edge)
            expected = gram_single_faults(tree)
            gram_time = perf_counter() - start
            start = perf_counter()
            dual_answers = dual_batch(dims, edges, reversed(tree.order))
            dual_time = perf_counter() - start
            assert expected == dual_answers
            start = perf_counter()
            rooted_answers = {e: rooted_resolve(tree, {e}) for e in range(len(edges))}
            root_time = perf_counter() - start
            assert expected[1] == rooted_answers
            start = perf_counter()
            oracle = GramFaultOracle(tree)
            preprocess = perf_counter() - start
            failures = [set(rng.sample(range(len(edges)), i % 5)) for i in range(100)]
            start = perf_counter()
            dimensions = [oracle.dimension(f) for f in failures]
            oracle_time = perf_counter() - start
            start = perf_counter()
            spans = SpanFaultOracle(tree)
            span_prep = perf_counter() - start
            start = perf_counter()
            span_answers = [spans.dimension(f) for f in failures]
            span_time = perf_counter() - start
            assert dimensions == span_answers
            assert dimensions == [rooted_resolve(tree, f) for f in failures]
            growth = sum(expected[1][e] > expected[0] for e in tree.tree_edges)
            print(f"{workload},{n},{len(edges)},{expected[0]},{growth},{gram_time:.4f},"
                  f"{dual_time:.4f},{root_time:.4f},{preprocess:.4f},{oracle_time:.4f},"
                  f"{span_prep:.4f},{span_time:.4f}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--benchmark", action="store_true")
    arguments = parser.parse_args()
    if arguments.benchmark:
        benchmark()
    else:
        check()
