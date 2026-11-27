"""Exact finite-horizon deadline stress under common-cause delay calendars."""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass, field
from fractions import Fraction
from heapq import heappop, heappush
import json
from pathlib import Path

Rational = int | Fraction


@dataclass(frozen=True, slots=True)
class Dependency:
    tail: int
    head: int
    nominal: Rational
    group: str | None = None
    extra: Rational = 0


@dataclass(frozen=True, slots=True)
class Deadline:
    layer: int
    vertex: int
    due: Rational


@dataclass(frozen=True, slots=True)
class TimingProblem:
    initial: tuple[Rational | None, ...]
    layers: tuple[tuple[Dependency, ...], ...]
    deadlines: tuple[Deadline, ...]


@dataclass(frozen=True, slots=True)
class Witness:
    release_vertex: int
    dependencies: tuple[tuple[int, int], ...]
    deadline_index: int
    groups: frozenset[str]


@dataclass(frozen=True, slots=True)
class _Arc:
    tail: int
    head: int
    base: Fraction
    group: str | None
    extra: Fraction
    kind: str
    layer: int
    index: int


@dataclass(frozen=True, slots=True)
class _Scan:
    arc: _Arc
    open_bit: int
    close_bit: int
    group_bit: int
    first_into_head: bool
    last_out_of_tail: bool
    keep_head: bool
    keep_tail: bool


@dataclass(frozen=True, slots=True)
class _Link:
    item: _Arc | str
    rest: _Link | None


@dataclass(frozen=True, slots=True)
class Outcome:
    excess: Fraction
    _prefix: _Link | None = field(repr=False)
    _suffix: _Link | None = field(default=None, repr=False)
    _selected: str | None = field(default=None, repr=False)

    def witness(self) -> Witness:
        prefix = list(_items(self._prefix))
        items = reversed(prefix)
        release = deadline = None
        edges: list[tuple[int, int]] = []
        groups = set() if self._selected is None else {self._selected}
        for sequence in (items, _items(self._suffix)):
            for item in sequence:
                if isinstance(item, str):
                    groups.add(item)
                elif item.kind == "dependency":
                    edges.append((item.layer, item.index))
                elif item.kind == "release":
                    release = item.index
                else:
                    deadline = item.index
        assert release is not None and deadline is not None
        return Witness(release, tuple(edges), deadline, frozenset(groups))


@dataclass(frozen=True, slots=True)
class Report:
    best_by_budget: tuple[Outcome | None, ...]
    avoided: dict[str, Outcome | None]
    required: dict[str, Outcome | None]
    calendar_width: int
    event_width: int


def _items(link: _Link | None):
    while link is not None:
        yield link.item
        link = link.rest


def _fraction(value: Rational | str) -> Fraction:
    if not isinstance(value, (int, Fraction, str)):
        raise ValueError("Times and delays must be integers or exact rational strings.")
    return Fraction(value)


def _arcs(problem: TimingProblem, cluster: bool) -> tuple[list[_Arc], int, int]:
    width = len(problem.initial)
    horizon = len(problem.layers)
    if not width:
        raise ValueError("Supply at least one event.")
    source = width * (horizon + 1)
    sink = source + 1
    zero = Fraction(0)
    arcs = [
        _Arc(source, vertex, _fraction(value), None, zero, "release", 0, vertex)
        for vertex, value in enumerate(problem.initial)
        if value is not None
    ]
    observations: list[list[_Arc]] = [[] for _ in range(horizon + 1)]
    for index, deadline in enumerate(problem.deadlines):
        if not (0 <= deadline.layer <= horizon and 0 <= deadline.vertex < width):
            raise ValueError("Deadline outside the timing layers.")
        vertex = width * deadline.layer + deadline.vertex
        observations[deadline.layer].append(
            _Arc(vertex, sink, -_fraction(deadline.due), None, zero, "deadline",
                 deadline.layer, index)
        )
    arcs.extend(observations[0])
    for layer, dependencies in enumerate(problem.layers, 1):
        buckets: dict[str | int | None, list[_Arc]] = {}
        for index, dep in enumerate(dependencies):
            if not (0 <= dep.tail < width and 0 <= dep.head < width):
                raise ValueError("Dependency endpoint outside the event set.")
            extra = _fraction(dep.extra)
            if dep.group is not None and not isinstance(dep.group, str):
                raise ValueError("Group names must be strings.")
            if extra < 0 or (dep.group is None and extra != 0):
                raise ValueError("A nonnegative extra delay requires a named group.")
            arc = _Arc(
                width * (layer - 1) + dep.tail, width * layer + dep.head,
                _fraction(dep.nominal), dep.group, extra, "dependency", layer, index,
            )
            buckets.setdefault(dep.group if cluster else index, []).append(arc)
        for bucket in buckets.values():
            arcs.extend(bucket)
        arcs.extend(observations[layer])
    return arcs, source, sink


def _compile(arcs: list[_Arc], source: int, sink: int) -> tuple[list[_Scan], int, int]:
    remaining_groups = Counter(arc.group for arc in arcs if arc.group is not None)
    remaining_out = Counter(arc.tail for arc in arcs)
    with_incoming = {arc.head for arc in arcs}
    incoming_seen: set[int] = set()
    live_events = {source, sink}
    bits: dict[str, int] = {}
    free_bits: list[int] = []
    next_bit = 1
    calendar_width, event_width = 0, len(live_events)
    scans = []
    for arc in arcs:
        group_bit = open_bit = close_bit = 0
        group = arc.group
        if group is not None:
            if group not in bits:
                if free_bits:
                    open_bit = heappop(free_bits)
                else:
                    open_bit = next_bit
                    next_bit <<= 1
                bits[group] = open_bit
                calendar_width = max(calendar_width, len(bits))
            group_bit = bits[group]
            remaining_groups[group] -= 1
            if not remaining_groups[group]:
                close_bit = bits.pop(group)
                heappush(free_bits, close_bit)
        remaining_out[arc.tail] -= 1
        first = arc.head not in incoming_seen
        last = remaining_out[arc.tail] == 0
        incoming_seen.add(arc.head)
        live_events.add(arc.head)
        event_width = max(event_width, len(live_events))
        if last:
            live_events.discard(arc.tail)
        keep_head = arc.head == sink or bool(remaining_out[arc.head])
        keep_tail = arc.tail == source or arc.tail in with_incoming
        if not keep_head:
            live_events.discard(arc.head)
        scans.append(_Scan(arc, open_bit, close_bit, group_bit, first, last,
                           keep_head, keep_tail))
    return scans, calendar_width, event_width


@dataclass(frozen=True, slots=True)
class _Label:
    score: Fraction
    trace: _Link | None = None


Table = dict[tuple[int, int], _Label]
Frontier = dict[int, Table]


def _put(table: Table, key: tuple[int, int], label: _Label, item: _Arc | str | None = None,
         added: Rational = 0) -> None:
    value = label.score if item is None else label.score + added
    current = table.get(key)
    if current is None or value > current.score:
        if item is None:
            table[key] = label
        else:
            table[key] = _Label(value, _Link(item, label.trace))


def analyze(problem: TimingProblem, budget: int, *, cluster: bool = True) -> Report:
    """Return best excess for each budget and all one-group restrictions at the given cap.

    None denotes an unreachable observation or an infeasible group restriction. A
    positive excess denotes a missed deadline. Original dependency indices are zero
    based within layers numbered from one. Deadline indices are zero based.
    """
    if not isinstance(budget, int) or budget < 0:
        raise ValueError("Budget must be a nonnegative integer.")
    arcs, source, sink = _arcs(problem, cluster)
    scans, calendar_width, event_width = _compile(arcs, source, sink)
    budget = min(budget, sum(bool(scan.open_bit) for scan in scans))
    zero = _Label(Fraction(0))
    frontier: Frontier = {source: {(0, 0): zero}}
    snapshots: dict[str, Frontier] = {}

    for scan in scans:
        arc = scan.arc
        if scan.open_bit:
            group = arc.group
            assert group is not None
            snapshots[group] = frontier
            frontier = {vertex: labels.copy() for vertex, labels in frontier.items()}
            for vertex, labels in snapshots[group].items():
                for (mask, used), label in labels.items():
                    if used < budget:
                        _put(frontier[vertex], (mask | scan.open_bit, used + 1), label, group)
        if scan.keep_head and arc.tail in frontier:
            labels = frontier.setdefault(arc.head, {})
            for (mask, used), label in frontier[arc.tail].items():
                weight = arc.base + (arc.extra if mask & scan.group_bit else 0)
                _put(labels, (mask, used), label, arc, weight)
        if scan.last_out_of_tail:
            frontier.pop(arc.tail, None)
        if scan.close_bit:
            next_frontier: Frontier = {}
            for vertex, labels in frontier.items():
                target = next_frontier.setdefault(vertex, {})
                for (mask, used), label in labels.items():
                    _put(target, (mask & ~scan.close_bit, used), label)
            frontier = next_frontier

    exact = frontier.get(sink, {})
    bests: list[Outcome | None] = []
    best: Outcome | None = None
    for cap in range(budget + 1):
        label = exact.get((0, cap))
        if label is not None and (best is None or label.score > best.excess):
            best = Outcome(label.score, label.trace)
        bests.append(best)

    suffix: Frontier = {sink: {(0, used): zero for used in range(budget + 1)}}
    avoided: dict[str, Outcome | None] = {}
    required: dict[str, Outcome | None] = {}
    for scan in reversed(scans):
        arc = scan.arc
        if scan.close_bit:
            suffix = {
                vertex: {
                    (mask | bit, used): label
                    for (mask, used), label in labels.items()
                    for bit in (0, scan.close_bit)
                }
                for vertex, labels in suffix.items()
            }
        if scan.keep_tail and arc.head in suffix:
            labels = suffix.setdefault(arc.tail, {})
            for (mask, used), label in suffix[arc.head].items():
                weight = arc.base + (arc.extra if mask & scan.group_bit else 0)
                _put(labels, (mask, used), label, arc, weight)
        if scan.first_into_head:
            suffix.pop(arc.head, None)
        if scan.open_bit:
            group = arc.group
            assert group is not None
            prefix = snapshots.pop(group)
            next_suffix: Frontier = {}
            conditioned: list[Outcome | None] = [None, None]
            for vertex, labels in suffix.items():
                target = next_suffix.setdefault(vertex, {})
                starts = prefix.get(vertex, {})
                for (mask, used), label in labels.items():
                    selected = bool(mask & scan.open_bit)
                    if used < selected:
                        continue
                    key = (mask & ~scan.open_bit, used - selected)
                    item = group if selected else None
                    _put(target, key, label, item)
                    before = starts.get(key)
                    if before is not None:
                        score = before.score + label.score
                        current = conditioned[selected]
                        if current is None or score > current.excess:
                            conditioned[selected] = Outcome(score, before.trace, label.trace, item)
            avoided[group], required[group] = conditioned
            suffix = next_suffix

    return Report(tuple(bests), avoided, required, calendar_width, event_width)


def example() -> TimingProblem:
    """Two production paths reconverge; two repeated causes jointly miss the deadline."""
    return TimingProblem(
        (0, None),
        (
            (Dependency(0, 0, 4), Dependency(0, 1, 2, "supplier", 2)),
            (Dependency(0, 0, 4), Dependency(1, 1, 2, "crew", 2)),
            (Dependency(0, 0, 3), Dependency(1, 1, 2, "supplier", 2)),
            (Dependency(0, 0, 3), Dependency(1, 0, 2, "crew", 2)),
        ),
        (Deadline(4, 0, 14),),
    )


def _load(path: Path) -> TimingProblem:
    data = json.loads(path.read_text())
    return TimingProblem(
        tuple(None if value is None else _fraction(value) for value in data["initial"]),
        tuple(tuple(Dependency(**dep) for dep in layer) for layer in data["layers"]),
        tuple(Deadline(**deadline) for deadline in data["deadlines"]),
    )


def _show(outcome: Outcome | None) -> dict | None:
    if outcome is None:
        return None
    witness = outcome.witness()
    return {
        "excess": str(outcome.excess),
        "release_vertex": witness.release_vertex,
        "dependencies": witness.dependencies,
        "deadline_index": witness.deadline_index,
        "groups": sorted(witness.groups),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, help="JSON timing problem, or use the built-in demo.")
    parser.add_argument("--budget", type=int, default=2)
    args = parser.parse_args()
    try:
        report = analyze(example() if args.input is None else _load(args.input), args.budget)
    except (KeyError, OSError, TypeError, ValueError, ZeroDivisionError) as error:
        parser.error(str(error))
    print(json.dumps({
        "calendar_width": report.calendar_width,
        "event_width": report.event_width,
        "best_by_budget": [_show(outcome) for outcome in report.best_by_budget],
        "avoided": {group: _show(outcome) for group, outcome in report.avoided.items()},
        "required": {group: _show(outcome) for group, outcome in report.required.items()},
    }, indent=2))


if __name__ == "__main__":
    main()
