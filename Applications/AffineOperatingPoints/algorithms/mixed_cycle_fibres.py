"""Diagnose bounded max-affine fibres where both kinds of gain cycle occur."""

import argparse
from dataclasses import dataclass
import json

from affine_spectrum import (
    cyclic_vertices,
    expansive_descendants,
    optimize,
    positive_edges,
    problem,
    rational,
    reachable,
    slack,
)
from operating_point_poset import _cyclic_components


@dataclass(frozen=True)
class Fibre:
    status: str
    rows: tuple
    lower: tuple = ()
    upper: tuple = ()
    continuum_vertex: int | None = None
    critical: tuple = ()
    successors: tuple = ()

    def _propagate(self, values):
        for _ in range(len(values) - 1):
            updated = values.copy()
            for row in self.rows:
                value = row.gain * values[row.tail] + row.offset
                updated[row.head] = max(updated[row.head], value)
            if values == updated:
                break
            values = updated
        return tuple(values)

    def vector(self, upset):
        """Realize an upset for a finite fibre, allowing the empty upset."""
        if self.status != "finite":
            raise ValueError("only a finite feasible fibre is indexed by upsets")
        chosen = set(upset)
        if any(type(index) is not int or not 0 <= index < len(self.critical) for index in chosen):
            raise ValueError("the upset contains an invalid component ID")
        if any(not self.successors[index] <= chosen for index in chosen):
            raise ValueError("the selected components must be closed under tight reachability")

        values = list(self.lower)
        for index in chosen:
            for vertex in self.critical[index]:
                values[vertex] = self.upper[vertex]
        return self._propagate(values)

    def continuum_witness(self, reading):
        """Realize a chosen reading at the reported varying coordinate."""
        if self.status != "continuum":
            raise ValueError("a varying coordinate requires a continuum fibre")
        reading = rational(reading)
        vertex = self.continuum_vertex
        if not self.lower[vertex] <= reading <= self.upper[vertex]:
            raise ValueError("the requested reading is outside the projected interval")
        values = list(self.lower)
        values[vertex] = reading
        return self._propagate(values)

    def summary(self):
        result = {"status": self.status}
        if self.status == "infeasible":
            return result
        result.update(lower=self.lower, upper=self.upper)
        if self.status == "continuum":
            vertex = self.continuum_vertex
            result.update(continuum_vertex=vertex, interval=(self.lower[vertex], self.upper[vertex]))
        else:
            result.update(critical=self.critical, successors=tuple(
                tuple(sorted(group)) for group in self.successors
            ))
        return result


def index_fibre(vertices, level, branches):
    """Return the infeasibility, finiteness, or continuum diagnosis at a fixed level."""
    rows = problem(vertices, rational(level), branches)
    if any(row.gain <= 0 for row in rows):
        raise ValueError("every branch gain must be positive")
    edges = positive_edges(rows)
    if (len(reachable(vertices, edges, [0])) != vertices
            or len(reachable(vertices, [(v, u, a) for u, v, a in edges], [0])) != vertices):
        raise ValueError("the branch graph must be strongly connected")
    if (not expansive_descendants(vertices, edges)
            or not expansive_descendants(vertices, [(u, v, 1 / a) for u, v, a in edges])):
        raise ValueError("the graph must have both an expansive and a contracting cycle")

    import z3

    x = [z3.Real(f"x_{i}") for i in range(vertices)]
    constraints = [x[r.head] >= z3.RealVal(str(r.gain)) * x[r.tail] + z3.RealVal(str(r.offset))
                   for r in rows]
    total = z3.Sum(x)
    upper = optimize(z3, x, constraints, total)
    if upper is None:
        return Fibre("infeasible", rows)
    lower = optimize(z3, x, constraints, -total)
    if lower is None:
        raise RuntimeError("the same relaxation has a greatest point but no least point")

    tight = tuple(row for row in rows if slack(row, upper) == 0)
    joint_edges = [(r.tail, r.head, r.gain) for r in tight
                   if lower[r.tail] < upper[r.tail] and lower[r.head] < upper[r.head]
                   and slack(r, lower) == 0]
    neutral = cyclic_vertices(vertices, joint_edges)
    if neutral:
        return Fibre("continuum", rows, lower, upper, min(neutral))

    adjacency = [[] for _ in range(vertices)]
    for row in tight:
        adjacency[row.tail].append(row.head)
    critical = tuple(group for group in _cyclic_components(adjacency)
                     if lower[group[0]] < upper[group[0]])
    tight_edges = [(r.tail, r.head, r.gain) for r in tight]
    successors = []
    for group in critical:
        descendants = reachable(vertices, tight_edges, group)
        successors.append(frozenset(i for i, part in enumerate(critical) if part[0] in descendants))
    return Fibre("finite", rows, lower, upper, critical=critical, successors=tuple(successors))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, help="JSON graph and operating level")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--upset", nargs="*", type=int, help="decode a finite fibre upset")
    mode.add_argument("--reading", help="realize a reading at the reported varying coordinate")
    args = parser.parse_args()
    with open(args.input, encoding="utf-8") as source:
        graph = json.load(source)
    index = index_fibre(graph["vertices"], graph["level"], graph["branches"])
    result = index.summary()
    if args.upset is not None:
        result["vector"] = index.vector(args.upset)
    if args.reading is not None:
        result["vector"] = index.continuum_witness(args.reading)
    print(json.dumps(result, default=str))


if __name__ == "__main__":
    main()
