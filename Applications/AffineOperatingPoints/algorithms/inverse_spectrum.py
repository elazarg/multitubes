"""Compile closed rational interval unions into floorless max-affine networks."""

import argparse
from dataclasses import dataclass
from fractions import Fraction
import json


def _rational(value):
    if type(value) not in (int, str, Fraction):
        raise ValueError("use exact integers, rational strings, or Fractions")
    return Fraction(value)


def merge_intervals(intervals):
    """Use None for an infinite endpoint, with direction given by its position."""
    rows = []
    for lo, hi in intervals:
        lo = None if lo is None else _rational(lo)
        hi = None if hi is None else _rational(hi)
        if lo is not None and hi is not None and lo > hi:
            raise ValueError("interval lower endpoint exceeds its upper endpoint")
        rows.append((lo, hi))
    rows.sort(key=lambda row: (row[0] is not None, row[0]))
    result = []
    for lo, hi in rows:
        if not result:
            result.append((lo, hi))
            continue
        previous_lo, previous_hi = result[-1]
        if previous_hi is None:
            break
        if lo is None or lo <= previous_hi:
            result[-1] = (previous_lo, None if hi is None else max(previous_hi, hi))
        else:
            result.append((lo, hi))
    return tuple(result)


@dataclass(frozen=True)
class Network:
    intervals: tuple
    vertices: int
    branches: tuple
    shift: Fraction

    def contains(self, level):
        level = _rational(level)
        return any((lo is None or lo <= level) and (hi is None or level <= hi)
                   for lo, hi in self.intervals)

    def _ceilings(self, level):
        x = [None] * self.vertices
        for u, v, gain, offset in self.branches:
            if u == v:
                ceiling = (level - offset) / (gain - 1)
                x[u] = ceiling if x[u] is None else min(x[u], ceiling)
        return x

    def eigenvector(self, level):
        """Return a rational eigenvector at level, or None if level is excluded."""
        level = _rational(level)
        if not self.contains(level):
            return None
        return tuple(self._ceilings(level))

    def relaxation_witness(self, level):
        """Return a rational witness of F(x) <= level + x at any rational level."""
        level = _rational(level)
        x = self._ceilings(level)
        for u, v, gain, offset in self.branches:
            if u != v:
                x[u] = min(x[u], (x[v] + level - offset) / gain)
        return tuple(x)

    def problem(self, level=None):
        """Use the adjacent fixed-level solver's (vertices, level, branches) fields."""
        result = {"vertices": self.vertices, "branches": self.branches}
        if level is not None:
            result["level"] = _rational(level)
        return result


def compile_spectrum(intervals):
    """Return a weakly connected network with gains 2 and 3 and offsets >= 0."""
    merged = merge_intervals(intervals)
    gadgets = []
    zero = Fraction(0)

    def lower(endpoint):
        gadgets.append((((3, zero),), endpoint / 2))

    def upper(endpoint):
        gadgets.append((((2, zero),), -endpoint / 2))

    def gap(center, radius):
        gadgets.append((((2, center), (3, center)), (3 * center + radius) / 2))

    if not merged:
        lower(Fraction(1))
        upper(zero)
    else:
        if merged[0][0] is not None:
            lower(merged[0][0])
        for (_, left), (right, _) in zip(merged, merged[1:]):
            gap((left + right) / 2, (right - left) / 2)
        if merged[-1][1] is not None:
            upper(merged[-1][1])
        if not gadgets:
            gap(zero, zero)

    sink = len(gadgets)
    branches = []
    for u, (loops, arc_offset) in enumerate(gadgets):
        branches.extend((u, u, gain, offset) for gain, offset in loops)
        branches.append((u, sink, 2, arc_offset))
    branches.append((sink, sink, 3, zero))
    shift = max(zero, max(-offset / (gain - 1) for _, _, gain, offset in branches))
    shifted = tuple((u, v, gain, offset + (gain - 1) * shift)
                    for u, v, gain, offset in branches)
    return Network(merged, sink + 1, shifted, shift)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("intervals", help="JSON file of [lower, upper] pairs, null for infinity")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--level", help="include the level for the fixed-level solver")
    mode.add_argument("--witness", metavar="LEVEL", help="output an eigenvector or null")
    mode.add_argument("--relaxation-witness", metavar="LEVEL", help="output an inequality witness")
    args = parser.parse_args()
    with open(args.intervals, encoding="utf-8") as source:
        network = compile_spectrum(json.load(source))
    if args.witness is not None:
        result = network.eigenvector(args.witness)
    elif args.relaxation_witness is not None:
        result = network.relaxation_witness(args.relaxation_witness)
    else:
        result = network.problem(args.level)
    print(json.dumps(result, default=str))


if __name__ == "__main__":
    main()
