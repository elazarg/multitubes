"""Exact uniform-tolerance curves for single replacements in unit-scale sensor networks."""

from bisect import bisect_right
from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable

Scalar = int | str | Fraction
Line = tuple[Fraction, Fraction]
OffsetInterval = tuple[Fraction | None, Fraction | None]
Label = tuple[Fraction, int]


@dataclass(frozen=True)
class _Arc:
    tail: int
    head: int
    comparison: int
    sign: int
    weight: Fraction


@dataclass(frozen=True)
class _Envelope:
    lines: tuple[Line, ...]
    breaks: tuple[Fraction, ...]

    def evaluate(self, argument: Fraction) -> Fraction:
        slope, intercept = self.lines[bisect_right(self.breaks, argument)]
        return slope * argument + intercept


def _envelope(lines: Iterable[Line]) -> _Envelope:
    """Build an upper envelope from lines in strictly increasing slope order."""
    active: list[Line] = []
    breaks: list[Fraction] = []
    for line in lines:
        slope, intercept = line
        while active:
            previous_slope, previous_intercept = active[-1]
            crossing = (previous_intercept - intercept) / (slope - previous_slope)
            if not breaks or crossing > breaks[-1]:
                breaks.append(crossing)
                break
            active.pop()
            breaks.pop()
        active.append(line)
    return _Envelope(tuple(active), tuple(breaks))


class ReplacementCurve:
    """Replace one offset in the original network, with every other offset fixed."""

    def __init__(self, minimum: Fraction, negative: list[Line], positive: list[Line]):
        self.minimum = minimum
        self._tolerance = _envelope([*negative, (Fraction(0), minimum), *positive])
        self._lower = _envelope((1 / a, -b / a) for a, b in reversed(negative))
        self._negative_upper = _envelope((-1 / a, b / a) for a, b in positive)

    def tolerance(self, offset: Scalar) -> Fraction:
        return self._tolerance.evaluate(Fraction(offset))

    def pieces(self) -> tuple[tuple[Fraction | None, Fraction, Fraction], ...]:
        """Return (start, slope, intercept) for each piece, from left to right."""
        starts = (None, *self._tolerance.breaks)
        return tuple((start, *line) for start, line in zip(starts, self._tolerance.lines))

    def acceptable_offsets(self, cap: Scalar) -> OffsetInterval | None:
        """Return closed bounds. None means an empty interval or an unbounded endpoint."""
        cap = Fraction(cap)
        if cap < self.minimum:
            return None
        lower = self._lower.evaluate(cap) if self._lower.lines else None
        upper = -self._negative_upper.evaluate(cap) if self._negative_upper.lines else None
        return lower, upper

    def best_offsets(self) -> OffsetInterval:
        interval = self.acceptable_offsets(self.minimum)
        assert interval is not None
        return interval


def _maximum_mean(vertex_count: int, arcs: list[_Arc]) -> Fraction:
    """Karp's maximum cycle mean formula on each bidirected connected component."""
    outgoing: list[list[_Arc]] = [[] for _ in range(vertex_count)]
    for arc in arcs:
        outgoing[arc.tail].append(arc)
    visited = set()
    maximum = Fraction(0)
    for base, edges in enumerate(outgoing):
        if base in visited or not edges:
            continue
        vertices = [base]
        visited.add(base)
        for tail in vertices:
            for arc in outgoing[tail]:
                if arc.head not in visited:
                    visited.add(arc.head)
                    vertices.append(arc.head)
        local_index = {vertex: index for index, vertex in enumerate(vertices)}
        local_arcs = [
            (local_index[tail], local_index[arc.head], arc.weight)
            for tail in vertices
            for arc in outgoing[tail]
        ]
        size = len(vertices)
        first: list[Fraction | None] = [None] * size
        first[0] = Fraction(0)
        layers = [first]
        for _ in vertices:
            previous = layers[-1]
            current: list[Fraction | None] = [None] * size
            for tail, head, weight in local_arcs:
                if previous[tail] is not None:
                    candidate = previous[tail] + weight
                    if current[head] is None or candidate > current[head]:
                        current[head] = candidate
            layers.append(current)
        for target, final in enumerate(layers[-1]):
            if final is not None:
                mean = min(
                    (final - layer[target]) / (size - length)
                    for length, layer in enumerate(layers[:-1])
                    if layer[target] is not None
                )
                maximum = max(maximum, mean)
    return maximum


def _tight_cycle(vertex_count: int, arcs: list[_Arc], mean: Fraction) -> set[int]:
    """Return the comparison IDs of a simple cycle at the maximum mean."""
    shifted = [(arc, arc.weight - mean) for arc in arcs]
    potential = [Fraction(0)] * vertex_count
    for _ in range(vertex_count - 1):
        updated = potential.copy()
        for arc, weight in shifted:
            updated[arc.head] = max(updated[arc.head], potential[arc.tail] + weight)
        if updated == potential:
            break
        potential = updated

    incoming: list[list[_Arc]] = [[] for _ in range(vertex_count)]
    outgoing: list[list[int]] = [[] for _ in range(vertex_count)]
    for arc, weight in shifted:
        if potential[arc.tail] + weight == potential[arc.head]:
            incoming[arc.head].append(arc)
            outgoing[arc.tail].append(arc.head)
    indegree = [len(edges) for edges in incoming]
    ready = deque(vertex for vertex, degree in enumerate(indegree) if degree == 0)
    while ready:
        for head in outgoing[ready.popleft()]:
            indegree[head] -= 1
            if indegree[head] == 0:
                ready.append(head)

    vertex = next(vertex for vertex, degree in enumerate(indegree) if degree > 0)
    position: dict[int, int] = {}
    trail: list[int] = []
    while vertex not in position:
        position[vertex] = len(trail)
        arc = next(arc for arc in incoming[vertex] if indegree[arc.tail] > 0)
        trail.append(arc.comparison)
        vertex = arc.tail
    return set(trail[position[vertex]:])


def _offer(best: list[Label], weight: Fraction, first_comparison: int) -> None:
    """Keep the best two weights from distinct first comparisons."""
    label = weight, first_comparison
    for index, (previous, comparison) in enumerate(best):
        if comparison == first_comparison:
            if previous >= weight:
                return
            best[index] = label
            break
    else:
        best.append(label)
    best.sort(reverse=True)
    del best[2:]


def replacement_curves(
    vertex_count: int, comparisons: Iterable[tuple[int, int, Scalar]]
) -> tuple[ReplacementCurve, ...]:
    """Index comparisons by input order. Accept zero-based vertices and rational offsets."""
    if vertex_count < 0:
        raise ValueError("vertex count must be nonnegative")

    arcs = []
    outgoing: list[list[_Arc]] = [[] for _ in range(vertex_count)]
    negative: list[list[Line]] = []
    positive: list[list[Line]] = []
    for index, (tail, head, offset) in enumerate(comparisons):
        if not (0 <= tail < vertex_count and 0 <= head < vertex_count):
            raise ValueError("comparison endpoint is outside the vertex range")
        weight = Fraction(offset)
        forward = _Arc(tail, head, index, 1, weight)
        reverse = _Arc(head, tail, index, -1, -weight)
        arcs.extend((forward, reverse))
        negative.append([])
        positive.append([])
        if tail == head:
            negative[index].append((Fraction(-1), Fraction(0)))
            positive[index].append((Fraction(1), Fraction(0)))
        else:
            outgoing[tail].append(forward)
            outgoing[head].append(reverse)
    if not arcs:
        return ()

    mean = _maximum_mean(vertex_count, arcs)
    baselines = [mean] * len(negative)
    if mean > 0:
        for comparison in _tight_cycle(vertex_count, arcs, mean):
            remaining = [arc for arc in arcs if arc.comparison != comparison]
            baselines[comparison] = _maximum_mean(vertex_count, remaining)

    for root, departures in enumerate(outgoing):
        if not departures:
            continue
        layer: list[list[Label]] = [[] for _ in range(vertex_count)]
        for arc in departures:
            _offer(layer[arc.head], arc.weight, arc.comparison)
        for length in range(1, vertex_count):
            cycle_length = length + 1
            for departure in departures:
                # The edited edge closes the walk in the reverse orientation.
                for value, first in layer[departure.head]:
                    if first != departure.comparison:
                        sign = -departure.sign
                        lines = positive if sign > 0 else negative
                        lines[departure.comparison].append(
                            (Fraction(sign, cycle_length), value / cycle_length)
                        )
                        break
            if length == vertex_count - 1:
                break
            following: list[list[Label]] = [[] for _ in range(vertex_count)]
            for arc in arcs:
                if arc.head != root:
                    for value, first in layer[arc.tail]:
                        _offer(following[arc.head], value + arc.weight, first)
            layer = following

    return tuple(
        ReplacementCurve(baseline, decreasing, list(reversed(increasing)))
        for baseline, decreasing, increasing in zip(baselines, negative, positive)
    )
