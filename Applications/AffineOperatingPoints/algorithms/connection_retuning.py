"""Index exact intercepts that repair a missing max-affine operating level."""

import argparse
from dataclasses import dataclass
from fractions import Fraction
import heapq
import json

from affine_spectrum import (
    adjacency,
    cyclic_vertices,
    optimize,
    positive_edges,
    problem,
    rational,
    reachable,
    slack,
    tight_edges,
)


@dataclass(frozen=True)
class Interval:
    """A closed interval, with None for an unbounded endpoint."""

    lower: Fraction | None = None
    upper: Fraction | None = None


def source_components(size, edges):
    """Return the source SCCs of the original graph."""
    graph = adjacency(size, edges)
    reverse = adjacency(size, [(v, u, a) for u, v, a in edges])
    seen = set()
    order = []
    for start in range(size):
        if start in seen:
            continue
        seen.add(start)
        stack = [(start, iter(graph[start]))]
        while stack:
            vertex, neighbors = stack[-1]
            neighbor = next(neighbors, None)
            if neighbor is None:
                order.append(vertex)
                stack.pop()
            elif neighbor not in seen:
                seen.add(neighbor)
                stack.append((neighbor, iter(graph[neighbor])))

    components = []
    owner = [None] * size
    for start in reversed(order):
        if owner[start] is not None:
            continue
        number = len(components)
        component = [start]
        owner[start] = number
        for vertex in component:
            for neighbor in reverse[vertex]:
                if owner[neighbor] is None:
                    owner[neighbor] = number
                    component.append(neighbor)
        components.append(component)
    targets = {owner[v] for u, v, _ in edges if owner[u] != owner[v]}
    return [tuple(component) for i, component in enumerate(components) if i not in targets]


def greatest_potential(size, rows):
    """Find the greatest potential with one bounded-objective rational LP."""
    import z3

    variables = [z3.Real(f"potential_{v}") for v in range(size)]
    constraints = [
        variables[e.head] >= z3.RealVal(str(e.gain)) * variables[e.tail]
        + z3.RealVal(str(e.offset))
        for e in rows
    ]
    result = optimize(z3, variables, constraints, z3.Sum(variables))
    if result is None:
        raise RuntimeError("the expansive relaxed system must be feasible")
    return result


def forward_thresholds(origin, upper, outgoing):
    """Return landing readings maximized over old walks from one anchor."""
    deficit = [None] * len(upper)
    deficit[origin] = 0
    queue = [(0, origin)]
    while queue:
        value, vertex = heapq.heappop(queue)
        if value != deficit[vertex]:
            continue
        for neighbor, branches in outgoing[vertex].items():
            candidate = min(edge_slack + gain * value for gain, edge_slack in branches)
            if deficit[neighbor] is None or candidate < deficit[neighbor]:
                deficit[neighbor] = candidate
                heapq.heappush(queue, (candidate, neighbor))
    return tuple(None if value is None else reading - value
                 for value, reading in zip(deficit, upper))


def capped_potential(tail, cap, upper, incoming):
    """Return the greatest old potential with its tail coordinate capped."""
    deficit = [0] * len(upper)
    deficit[tail] = max(0, upper[tail] - cap)
    queue = [(-deficit[tail], tail)]
    while queue:
        negative, vertex = heapq.heappop(queue)
        value = -negative
        if value != deficit[vertex]:
            continue
        for neighbor, branches in incoming[vertex].items():
            candidate = max((value - edge_slack) / gain for gain, edge_slack in branches)
            if candidate > deficit[neighbor]:
                deficit[neighbor] = candidate
                heapq.heappush(queue, (-candidate, neighbor))
    return tuple(reading - value for reading, value in zip(upper, deficit))


@dataclass(frozen=True)
class RepairIndex:
    level: Fraction
    upper: tuple
    bad_sources: tuple
    source_cap: tuple = ()
    merged_cap: tuple = ()
    return_cap: dict | None = None
    capped_heads: dict | None = None

    def query(self, tail, head, gain):
        """Return the ordered disjoint intercept intervals for tail -> head."""
        if any(type(v) is not int or not 0 <= v < len(self.upper) for v in (tail, head)):
            raise ValueError("candidate endpoints must be valid integer vertices")
        gain = rational(gain)
        if gain <= 1:
            raise ValueError("candidate gains must exceed one")
        if len(self.bad_sources) != 1 or head not in self.return_cap:
            return ()

        source_cap = self.source_cap[tail]
        if source_cap is not None:
            maximum = self.capped_heads[head][tail] + self.level - gain * source_cap
            return (Interval(None, maximum),)

        return_cap = self.return_cap[head][tail]
        merged_cap = self.merged_cap[tail]
        start = self.upper[head] + self.level
        higher = Interval(start - gain * return_cap, None)
        if merged_cap is None:
            return (higher,)
        if merged_cap <= return_cap:
            return (Interval(),)
        return (Interval(None, start - gain * merged_cap), higher)


def index_repairs(size, level, branches):
    """Preprocess one missing level for constant-time candidate queries."""
    level = rational(level)
    rows = problem(size, level, branches)
    if any(e.gain <= 1 for e in rows):
        raise ValueError("all original gains must exceed one")
    if len({e.tail for e in rows}) != size:
        raise ValueError("every vertex must have an outgoing branch")

    edges = positive_edges(rows)
    upper = greatest_potential(size, rows)
    pins = cyclic_vertices(size, tight_edges(rows, upper))
    sources = source_components(size, edges)
    good_pins = [tuple(v for v in source if v in pins) for source in sources]
    bad = tuple(source for source, group in zip(sources, good_pins) if not group)
    if not bad:
        raise ValueError("the specified level already admits an operating point")
    if len(bad) > 1:
        return RepairIndex(level, upper, bad)

    outgoing = [{} for _ in upper]
    incoming = [{} for _ in upper]
    for e in rows:
        edge_slack = slack(e, upper)
        outgoing[e.tail].setdefault(e.head, []).append((e.gain, edge_slack))
        incoming[e.head].setdefault(e.tail, []).append((e.gain, edge_slack))

    head_vertices = bad[0]
    possible_merged_pins = pins & reachable(size, edges, head_vertices)
    needed_pins = possible_merged_pins | {v for group in good_pins for v in group}
    thresholds = {v: forward_thresholds(v, upper, outgoing) for v in needed_pins}
    return_cap = {v: forward_thresholds(v, upper, outgoing) for v in head_vertices}

    source_cap = [None] * size
    for group in good_pins:
        if not group:
            continue
        for tail in range(size):
            thresholds_to_tail = [thresholds[v][tail] for v in group]
            if any(value is None for value in thresholds_to_tail):
                continue
            needed = min(thresholds_to_tail)
            previous = source_cap[tail]
            if previous is None or needed > previous:
                source_cap[tail] = needed

    merged_cap = [None] * size
    for vertex in possible_merged_pins:
        for tail, needed in enumerate(thresholds[vertex]):
            previous = merged_cap[tail]
            if needed is not None and (previous is None or needed < previous):
                merged_cap[tail] = needed

    capped_heads = {v: [None] * size for v in head_vertices}
    for tail, cap in enumerate(source_cap):
        if cap is not None:
            capped = capped_potential(tail, cap, upper, incoming)
            for head in head_vertices:
                capped_heads[head][tail] = capped[head]

    return RepairIndex(level, upper, bad, tuple(source_cap), tuple(merged_cap),
                       return_cap, capped_heads)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, help="JSON graph, level and candidate branches")
    args = parser.parse_args()
    with open(args.input, encoding="utf-8") as source:
        data = json.load(source)
    index = index_repairs(data["vertices"], data["level"], data["branches"])
    repairs = [index.query(*candidate) for candidate in data["candidates"]]
    print(json.dumps({
        "bad_sources": index.bad_sources,
        "intercepts": [[[interval.lower, interval.upper] for interval in answer]
                       for answer in repairs],
    }, default=str))


if __name__ == "__main__":
    main()
