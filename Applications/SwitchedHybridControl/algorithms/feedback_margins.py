"""Exact affine-constraint margins around a gauged feasible baseline."""

from dataclasses import dataclass
from fractions import Fraction
from heapq import heapify, heappop, heappush
from typing import Sequence


ZERO = Fraction(0)
ONE = Fraction(1)


@dataclass(frozen=True)
class Arc:
    tail: int
    head: int
    gain: Fraction
    bias: Fraction


@dataclass
class Propagation:
    value: list[Fraction]
    arc: list[int | None]
    scanned_arcs: int
    slope: list[Fraction] | None = None


@dataclass(frozen=True)
class HeadRejection:
    """Two directed base paths support the violated margin.

    A missing feedback path means a zero lower bound on the candidate tail.
    An empty tuple denotes the length-zero path at the candidate head.
    """

    feedback: tuple[int, ...] | None
    to_budget: tuple[int, ...]


@dataclass
class HeadProfile:
    base: "Baseline"
    head: int
    seed: Propagation
    left_slope: list[Fraction]

    def saturates(self, tail: int, gain: Fraction) -> bool:
        """Whether the head-maximal assignment attains the requested support."""
        return gain >= ZERO and gain * self.left_slope[tail] <= ONE

    def margin(self, tail: int, gain: Fraction) -> Fraction:
        if not self.saturates(tail, gain):
            raise ValueError("candidate is outside the exact endpoint-gain range")
        return self.seed.value[self.head] - gain * self.seed.value[tail]

    def certify_rejection(self, candidate: Arc) -> HeadRejection:
        if candidate.head != self.head:
            raise ValueError("candidate must enter the profile head")
        if candidate.bias <= self.margin(candidate.tail, candidate.gain):
            raise ValueError("candidate meets its margin")
        feedback = None
        if self.seed.value[candidate.tail] > ZERO:
            path = []
            vertex = candidate.tail
            while vertex != self.head:
                index = self.seed.arc[vertex]
                assert index is not None
                path.append(index)
                vertex = self.base.arcs[index].tail
            feedback = tuple(reversed(path))
        return HeadRejection(feedback, tuple(self.base.budget_path(self.head)))


class Baseline:
    """A normalized feasible region: 0 <= x <= budget, x[v] >= a*x[u]+b.

    Existing arcs have 0 <= a <= 1 and b <= 0. Physical data can be shifted
    by an original feasible radius and divided by a positive gauge first.
    """

    def __init__(self, budget: Sequence[Fraction], arcs: Sequence[Arc]):
        self.budget = [Fraction(bound) for bound in budget]
        self.arcs = [
            Arc(arc.tail, arc.head, Fraction(arc.gain), Fraction(arc.bias))
            for arc in arcs
        ]
        size = len(budget)
        self.outgoing: list[list[int]] = [[] for _ in budget]
        self.incoming: list[list[int]] = [[] for _ in budget]
        if any(bound < ZERO for bound in self.budget):
            raise ValueError("baseline must satisfy upper budgets")
        for index, arc in enumerate(self.arcs):
            if not (0 <= arc.tail < size and 0 <= arc.head < size):
                raise ValueError("arc endpoint outside the graph")
            if not (ZERO <= arc.gain <= ONE and arc.bias <= ZERO):
                raise ValueError("base arcs must be scaled and baseline-feasible")
            self.outgoing[arc.tail].append(index)
            if arc.gain > ZERO:
                self.incoming[arc.head].append(index)
        self.upper = self._greatest()

    def _greatest(self) -> Propagation:
        """Propagate upper budgets backward over the positive-gain arcs."""
        values = self.budget.copy()
        witness = [None] * len(values)
        queue = [(bound, vertex) for vertex, bound in enumerate(values)]
        # Each vertex can settle only once. Strict improvements stale old keys.
        heapify(queue)
        scanned = 0
        while queue:
            value, vertex = heappop(queue)
            if value != values[vertex]:
                continue
            for index in self.incoming[vertex]:
                arc = self.arcs[index]
                scanned += 1
                candidate = (value - arc.bias) / arc.gain
                if candidate < values[arc.tail]:
                    values[arc.tail] = candidate
                    witness[arc.tail] = index
                    heappush(queue, (candidate, arc.tail))
        return Propagation(values, witness, scanned)

    def budget_path(self, start: int) -> list[int]:
        path = []
        vertex = start
        while self.upper.arc[vertex] is not None:
            index = self.upper.arc[vertex]
            path.append(index)
            vertex = self.arcs[index].head
        return path

    def _forward(
        self, seeds: Sequence[tuple[int, Fraction, Fraction]], *,
        gains_only: bool = False, reverse: bool = False,
    ) -> Propagation:
        """Maximize (value, -left slope) with zero as the default seed."""
        size = len(self.budget)
        values, slopes = [ZERO] * size, [ZERO] * size
        witness = [None] * size
        queue = []
        for vertex, value, slope in seeds:
            value, slope = Fraction(value), Fraction(slope)
            if (value, -slope) > (values[vertex], -slopes[vertex]):
                values[vertex], slopes[vertex] = value, slope
                heappush(queue, (-value, slope, vertex))
        adjacency = self.incoming if reverse else self.outgoing
        scanned = 0
        while queue:
            negated, slope, vertex = heappop(queue)
            value = -negated
            if (value, slope) != (values[vertex], slopes[vertex]):
                continue
            for index in adjacency[vertex]:
                arc = self.arcs[index]
                scanned += 1
                candidate = arc.gain * value
                candidate_slope = arc.gain * slope
                if not gains_only:
                    candidate += arc.bias
                neighbor = arc.tail if reverse else arc.head
                if (candidate, -candidate_slope) > (values[neighbor], -slopes[neighbor]):
                    values[neighbor], slopes[neighbor] = candidate, candidate_slope
                    witness[neighbor] = index
                    heappush(queue, (-candidate, candidate_slope, neighbor))
        return Propagation(values, witness, scanned, slopes)

    def least_above(self, floors: Sequence[tuple[int, Fraction]]) -> Propagation:
        """Return the least solution above zero and the requested new floors."""
        return self._forward([(v, value, ZERO) for v, value in floors])

    def head_profile(self, head: int) -> HeadProfile:
        seed = self._forward([(head, self.upper.value[head], ONE)])
        assert seed.slope is not None
        return HeadProfile(self, head, seed, seed.slope)

    def tail_batch(self, tail: int, candidates: Sequence[Arc]) -> list[Fraction] | None:
        """Return a feasible assignment for the common-tail batch, or None."""
        ceiling = self.upper.value[tail]
        for arc in candidates:
            if arc.tail != tail or arc.gain < ZERO:
                raise ValueError("batch must share a tail and have nonnegative gains")
        gains = None
        if any(arc.gain > ONE for arc in candidates):
            gains = self._forward([(tail, ONE, ZERO)], gains_only=True, reverse=True).value
        for arc in candidates:
            if gains is not None and arc.gain * gains[arc.head] > ONE:
                raise ValueError("gain violates the feedback bound")
            slack = self.upper.value[arc.head] - arc.bias
            if slack < ZERO:
                return None
            if arc.gain > ZERO:
                ceiling = min(ceiling, slack / arc.gain)
        closure = self._forward(
            [(arc.head, arc.bias + arc.gain * ceiling, ZERO) for arc in candidates]
        )
        if closure.value[tail] > ceiling:
            return None
        return closure.value


def normalized_arc(arc: Arc, radius: Sequence[Fraction], gauge: Sequence[Fraction]) -> Arc:
    """Convert the physical inequality to shifted, gauge-normalized coordinates."""
    tail, head = arc.tail, arc.head
    numerator = Fraction(arc.bias) + Fraction(arc.gain) * radius[tail] - radius[head]
    return Arc(tail, head, Fraction(arc.gain) * gauge[tail] / gauge[head],
               numerator / gauge[head])


def example_cli() -> None:
    """Run a query on the physical switched-control example."""
    import argparse

    parser = argparse.ArgumentParser(description="Feedback margin in the two-mode comparison")
    parser.add_argument("--gain", type=Fraction, default=Fraction(2))
    parser.add_argument("--offset", type=Fraction, default=Fraction(7))
    args = parser.parse_args()
    if args.gain < 0:
        parser.error("gain must be nonnegative")

    radius, gauge = [Fraction(3, 2), Fraction(4)], [Fraction(1), Fraction(4)]
    budgets = [Fraction(5, 2), Fraction(16)]
    physical_arcs = [Arc(0, 1, Fraction(2), Fraction(1)), Arc(1, 0, Fraction(1, 8), Fraction(1))]
    base = Baseline(
        [(u - b) / g for u, b, g in zip(budgets, radius, gauge)],
        [normalized_arc(arc, radius, gauge) for arc in physical_arcs],
    )
    arc = normalized_arc(Arc(0, 1, args.gain, args.offset), radius, gauge)
    profile = base.head_profile(arc.head)
    if not profile.saturates(arc.tail, arc.gain):
        parser.exit(2, "The gain is outside the exact endpoint-profile range.\n")
    limit = gauge[arc.head] * profile.margin(arc.tail, arc.gain)
    limit += radius[arc.head] - args.gain * radius[arc.tail]
    print(f"Maximum physical offset {limit}")
    if args.offset <= limit:
        assignment = [b + g * x for b, g, x in zip(radius, gauge, profile.seed.value)]
        print("Feasible radii (" + ", ".join(str(value) for value in assignment) + ")")
    else:
        proof = profile.certify_rejection(arc)
        print(f"Infeasible. Original feedback path {proof.feedback}, budget path {proof.to_budget}.")


if __name__ == "__main__":
    example_cli()
