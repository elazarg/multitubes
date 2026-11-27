#!/usr/bin/env python3
"""Exact range diagnostics for a fixed scalar Kalman packet log."""

from __future__ import annotations

import json
import sys
from collections.abc import Iterable, Iterator
from dataclasses import asdict, dataclass
from enum import Enum
from fractions import Fraction
from math import lcm
from pathlib import Path


Rational = int | str | Fraction


def nonnegative(value: Rational) -> Fraction:
    if not isinstance(value, (int, str, Fraction)):
        raise TypeError("use an integer, rational string, or Fraction")
    value = Fraction(value)
    if value < 0:
        raise ValueError("expected a nonnegative rational")
    return value


def compare(first: int | Fraction, second: int | Fraction) -> int:
    return (first > second) - (first < second)


@dataclass(frozen=True, slots=True)
class Cut:
    """The real number base + sqrt(radicand), with rational components."""

    base: Fraction
    radicand: Fraction = Fraction(0)

    def compare(self, other: Cut) -> int:
        offset = self.base - other.base
        if offset < 0:
            return -other.compare(self)
        if offset == 0:
            return compare(self.radicand, other.radicand)

        # Compare offset + sqrt(self.radicand) with sqrt(other.radicand).
        residual = offset * offset + self.radicand - other.radicand
        if residual >= 0:
            return 1 if residual or self.radicand else 0
        return compare(4 * offset * offset * self.radicand, residual * residual)


ZERO_CUT = Cut(Fraction(0))


class Boundary(Enum):
    IMPOSSIBLE = "impossible"
    UNBOUNDED = "unbounded"


Bound = Fraction | Boundary


@dataclass(frozen=True, slots=True)
class Map:
    """(a*x + b)/(c*x + d), with nonnegative integer coefficients and d > 0."""

    a: int
    b: int
    c: int
    d: int

    @classmethod
    def from_rationals(cls, a: Fraction, b: Fraction, c: Fraction, d: Fraction) -> Map:
        if a == c == 0:
            constant = b / d
            return cls(0, constant.numerator, 0, constant.denominator)
        coefficients = (a, b, c, d)
        denominator = lcm(*(value.denominator for value in coefficients))
        return cls(*(value.numerator * (denominator // value.denominator)
                     for value in coefficients))

    def __call__(self, prior: Fraction) -> Fraction:
        numerator, denominator = prior.as_integer_ratio()
        return Fraction(self.a * numerator + self.b * denominator,
                        self.c * numerator + self.d * denominator)

    def after(self, prior: Map) -> Map:
        if self.a == self.c == 0:
            return self
        if prior.a == prior.c == 0:
            constant = self(Fraction(prior.b, prior.d))
            return Map(0, constant.numerator, 0, constant.denominator)
        return Map(self.a * prior.a + self.b * prior.c,
                   self.a * prior.b + self.b * prior.d,
                   self.c * prior.a + self.d * prior.c,
                   self.c * prior.b + self.d * prior.d)

    def at_most(self, cap: Bound) -> Bound:
        """Return the endpoint of the nonnegative preimage of [0, cap]."""
        if isinstance(cap, Boundary):
            return cap
        allowance = cap * self.d - self.b
        if allowance < 0:
            return Boundary.IMPOSSIBLE
        slope = self.a - cap * self.c
        if slope <= 0:
            return Boundary.UNBOUNDED
        return allowance / slope

    def exceeds_at(self, cap: Fraction, point: Cut) -> bool:
        coefficient = self.a - cap * self.c
        allowance = cap * self.d - self.b
        if coefficient == 0:
            return allowance < 0
        order = point.compare(Cut(allowance / coefficient))
        return order * coefficient > 0


IDENTITY = Map(1, 0, 0, 1)
ZERO_MAP = Map(0, 0, 0, 1)


def dominance_cut(earlier: Map, later: Map) -> Cut | None:
    """For positive x, later(x) > earlier(x) exactly when x is below this cut."""
    constant = later.b * earlier.d - earlier.b * later.d
    linear = (later.a * earlier.d + later.b * earlier.c
              - earlier.a * later.d - earlier.b * later.c)
    quadratic = later.a * earlier.c - earlier.a * later.c
    near_zero = constant or linear or quadratic
    if near_zero <= 0:
        return ZERO_CUT
    at_infinity = quadratic or linear or constant
    if at_infinity > 0:
        return None  # Every positive x.
    if quadratic == 0:
        return Cut(Fraction(-constant, linear))
    discriminant = linear * linear - 4 * quadratic * constant
    return Cut(Fraction(-linear, 2 * quadratic),
               Fraction(discriminant, 4 * quadratic * quadratic))


@dataclass(frozen=True, slots=True)
class Piece:
    time: int
    mapping: Map
    cut: Cut | None  # The highest-prior piece has no finite cut.


@dataclass(slots=True)
class Envelope:
    pieces: list[Piece]
    zero_peak: Fraction
    zero_time: int

    def peak(self, prior: Fraction) -> tuple[Fraction, int]:
        if prior == 0:
            return self.zero_peak, self.zero_time
        low, high = 1, len(self.pieces)
        point = Cut(prior)
        while low < high:
            middle = (low + high) // 2
            cut = self.pieces[middle].cut
            assert cut is not None
            if point.compare(cut) < 0:
                low = middle + 1
            else:
                high = middle
        piece = self.pieces[low - 1]
        return piece.mapping(prior), piece.time

    def safe_initial(self, cap: Fraction) -> Bound:
        if self.zero_peak > cap:
            return Boundary.IMPOSSIBLE
        if self.pieces[0].mapping.at_most(cap) is Boundary.UNBOUNDED:
            return Boundary.UNBOUNDED
        low, high = 1, len(self.pieces)
        while low < high:
            middle = (low + high) // 2
            piece = self.pieces[middle]
            assert piece.cut is not None
            if piece.mapping.exceeds_at(cap, piece.cut):
                low = middle + 1
            else:
                high = middle
        return self.pieces[low - 1].mapping.at_most(cap)


def summarize(maps: list[Map], left: int, right: int) -> tuple[Map, Envelope]:
    prefix = IDENTITY
    pieces = []
    zero_peak, zero_time = Fraction(-1), left
    for time in range(left + 1, right + 1):
        prefix = maps[time - 1].after(prefix)
        at_zero = Fraction(prefix.b, prefix.d)
        if at_zero > zero_peak:
            zero_peak, zero_time = at_zero, time

        cut = None
        while pieces:
            cut = dominance_cut(pieces[-1].mapping, prefix)
            if cut == ZERO_CUT:
                break
            previous = pieces[-1].cut
            if cut is not None and (previous is None or cut.compare(previous) < 0):
                break
            pieces.pop()
        if cut != ZERO_CUT:
            pieces.append(Piece(time, prefix, cut))
    return prefix, Envelope(pieces, zero_peak, zero_time)


@dataclass(slots=True)
class Node:
    left: int
    right: int
    end_map: Map
    envelope: Envelope
    children: tuple[Node, Node] | tuple[()]

    @classmethod
    def build(cls, maps: list[Map], left: int, right: int) -> Node:
        end_map, envelope = summarize(maps, left, right)
        children = ()
        if left + 1 < right:
            middle = (left + right) // 2
            children = cls.build(maps, left, middle), cls.build(maps, middle, right)
        return cls(left, right, end_map, envelope, children)

    def cover(self, left: int, right: int) -> Iterator[Node]:
        if right <= self.left or self.right <= left:
            return
        if left <= self.left and self.right <= right:
            yield self
            return
        for child in self.children:
            yield from child.cover(left, right)

    def first_excess(self, prior: Fraction, cap: Fraction) -> int:
        """The caller has established a strict violation somewhere in this node."""
        if not self.children:
            return self.right
        first, second = self.children
        if first.envelope.peak(prior)[0] > cap:
            return first.first_excess(prior, cap)
        return second.first_excess(first.end_map(prior), cap)


@dataclass(frozen=True, slots=True)
class Report:
    final_covariance: Fraction
    peak_ratio: Fraction | None
    peak_time: int | None
    first_excess: int | None


Step = tuple[Rational, Rational, Rational | None]


class DeadlineIndex:
    """Index logged steps (squared gain, process noise, observation noise or None)."""

    def __init__(self, steps: Iterable[Step], profile: Iterable[Rational] | None = None):
        steps = list(steps)
        self.n = len(steps)
        self.profile = ([Fraction(1)] * (self.n + 1) if profile is None else
                        [nonnegative(weight) for weight in profile])
        if len(self.profile) != self.n + 1 or not all(self.profile):
            raise ValueError("profile must contain n+1 positive values")
        maps = []
        for time, (gain, noise, observation) in enumerate(steps, start=1):
            a = nonnegative(gain) * self.profile[time - 1]
            q = nonnegative(noise)
            w = self.profile[time]
            if observation is None:
                mapping = Map.from_rationals(a, q, Fraction(0), w)
            else:
                r = nonnegative(observation)
                mapping = ZERO_MAP if r == 0 else Map.from_rationals(r * a, r * q, w * a,
                                                                    w * (q + r))
            maps.append(mapping)
        self.root = Node.build(maps, 0, self.n) if maps else None

    def _cover(self, left: int, right: int) -> list[Node]:
        if not 0 <= left <= right <= self.n:
            raise IndexError("expected 0 <= left <= right <= number of steps")
        return list(self.root.cover(left, right)) if self.root is not None and left < right else []

    def analyze(self, left: int, right: int, initial: Rational,
                cap: Rational | None = None) -> Report:
        """Use initial covariance at left and inspect the times left+1, ..., right."""
        blocks = self._cover(left, right)
        multiplier = nonnegative(cap) if cap is not None else None
        prior = nonnegative(initial) / self.profile[left]
        peak_ratio, peak_time, first_excess = None, None, None
        for block in blocks:
            block_peak, block_time = block.envelope.peak(prior)
            if peak_ratio is None or block_peak > peak_ratio:
                peak_ratio, peak_time = block_peak, block_time
            if multiplier is not None and first_excess is None and block_peak > multiplier:
                first_excess = block.first_excess(prior, multiplier)
            prior = block.end_map(prior)
        return Report(prior * self.profile[right], peak_ratio, peak_time, first_excess)

    def safe_initial(self, left: int, right: int, cap: Rational) -> Bound:
        """Largest initial covariance under all inclusive profile caps, or a Boundary."""
        blocks = self._cover(left, right)
        multiplier = nonnegative(cap)
        bound = Boundary.UNBOUNDED
        for block in reversed(blocks):
            through_end = block.end_map.at_most(bound)
            within = block.envelope.safe_initial(multiplier)
            if Boundary.IMPOSSIBLE in (through_end, within):
                return Boundary.IMPOSSIBLE
            finite = [value for value in (through_end, within) if isinstance(value, Fraction)]
            bound = min(finite) if finite else Boundary.UNBOUNDED
        return bound * self.profile[left] if isinstance(bound, Fraction) else bound


DEMO = {
    "steps": [[1, 0, None], [2, 0, 2], [1, 1, None], [1, 0, 0], [1, 1, None]],
    "profile": [1, 1, 1, 2, 1, 1],
    "queries": [{"left": 0, "right": 5, "initial": "3/4", "cap": "4/5"},
                {"left": 1, "right": 3, "initial": "1/2", "cap": "4/5"},
                {"left": 3, "right": 5, "initial": 7, "cap": 1}],
}


def main() -> None:
    # Exact covariances on long logs can exceed Python's decimal conversion limit.
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    if len(sys.argv) > 2 or sys.argv[1:] == ["--help"]:
        print("usage: python3 riccati_deadlines.py [request.json | -]")
        return
    if len(sys.argv) == 1:
        request = DEMO
    elif sys.argv[1] == "-":
        request = json.load(sys.stdin)
    else:
        request = json.loads(Path(sys.argv[1]).read_text())
    index = DeadlineIndex(request["steps"], request.get("profile"))
    for query in request["queries"]:
        result = asdict(index.analyze(**query))
        if "cap" in query and query["cap"] is not None:
            result["safe_initial"] = index.safe_initial(query["left"], query["right"], query["cap"])
        print(json.dumps(result, default=lambda value: value.value if isinstance(value, Boundary)
                         else str(value)))


if __name__ == "__main__":
    main()
