"""Value profiles for noncrossing unions of shared delay occurrences."""

from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import dataclass
from fractions import Fraction

from delay_calendars import TimingProblem, _arcs

Transfer = dict[tuple[int, int, int], Fraction]


def _identity(vertices: set[int]) -> Transfer:
    return {(vertex, vertex, 0): Fraction(0) for vertex in vertices}


def _maximize(matrix: Transfer, key: tuple[int, int, int], value: Fraction) -> None:
    old = matrix.get(key)
    if old is None or value > old:
        matrix[key] = value


def _compose(left: Transfer, right: Transfer, cap: int) -> Transfer:
    from_vertex = defaultdict(list)
    for (middle, end, budget), weight in right.items():
        from_vertex[middle].append((end, budget, weight))
    result: Transfer = {}
    for (start, middle, first_budget), first_weight in left.items():
        for end, second_budget, second_weight in from_vertex[middle]:
            budget = first_budget + second_budget
            if budget <= cap:
                _maximize(result, (start, end, budget), first_weight + second_weight)
    return result


@dataclass(slots=True)
class _Scope:
    group: str | None
    off: Transfer
    on: Transfer | None = None

    def append(self, off: Transfer, on: Transfer, cap: int) -> None:
        self.off = _compose(self.off, off, cap)
        if self.on is not None:
            self.on = _compose(self.on, on, cap)

    def close(self, cap: int) -> Transfer:
        assert self.on is not None
        for (start, end, budget), weight in self.on.items():
            if budget < cap:
                _maximize(self.off, (start, end, budget + 1), weight)
        return self.off


def nested_excess(problem: TimingProblem, budget: int) -> tuple[Fraction | None, ...]:
    """Return at-most-budget excesses in the original per-layer dependency order.

    Raises ValueError when the raw arc-order group word contains a subsequence
    A, B, A, B for distinct groups. Budget above the number of groups is capped.
    """
    if not isinstance(budget, int) or budget < 0:
        raise ValueError("Budget must be a nonnegative integer.")
    arcs, source, sink = _arcs(problem, False)
    remaining_groups = Counter(arc.group for arc in arcs if arc.group is not None)
    remaining_out = Counter(arc.tail for arc in arcs)
    budget = min(budget, len(remaining_groups))
    seen: set[str] = set()
    live = {source, sink}
    stack = [_Scope(None, _identity(live))]
    for arc in arcs:
        group = arc.group
        if group is not None:
            if group not in seen:
                identity = _identity(live)
                stack.append(_Scope(group, identity, identity))
                seen.add(group)
            elif stack[-1].group != group:
                raise ValueError("The original arc order has crossing group occurrences.")
        before = live.copy()
        remaining_out[arc.tail] -= 1
        if remaining_out[arc.tail] == 0:
            live.discard(arc.tail)
        if remaining_out[arc.head] or arc.head == sink:
            live.add(arc.head)
        leaf = _identity(before & live)
        on_leaf = leaf
        if arc.tail in before and arc.head in live:
            transition = (arc.tail, arc.head, 0)
            leaf[transition] = arc.base
            if group is not None:
                on_leaf = leaf.copy()
                on_leaf[transition] = arc.base + arc.extra
        stack[-1].append(leaf, on_leaf, budget)
        if group is not None:
            remaining_groups[group] -= 1
            if not remaining_groups[group]:
                summary = stack.pop().close(budget)
                stack[-1].append(summary, summary, budget)
    exact = stack[0].off
    values = []
    best: Fraction | None = None
    for used in range(budget + 1):
        value = exact.get((source, sink, used))
        if value is not None and (best is None or value > best):
            best = value
        values.append(best)
    return tuple(values)
