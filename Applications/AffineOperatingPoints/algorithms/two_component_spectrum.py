"""Compile rational interval unions with exactly two strong components."""

import argparse
from dataclasses import dataclass
from fractions import Fraction
import json

from inverse_spectrum import _rational, merge_intervals


LOW = Fraction(1, 2)
MIDDLE = Fraction(3, 5)
HIGH = Fraction(4, 5)
LOWER_TEST = Fraction(3, 4)


@dataclass(frozen=True)
class Network:
    intervals: tuple
    vertices: int
    branches: tuple
    shift: Fraction
    margin: Fraction
    root_slopes: tuple
    relay_extra: tuple

    def eigenvector(self, level):
        """Return an exact witness or None when the level is excluded."""
        level = _rational(level)
        if self.intervals == ((None, None),):
            return min(level, level / 2), level / 2
        for root, (lower, upper) in enumerate(self.intervals, start=1):
            if (lower is None or lower <= level) and (upper is None or level <= upper):
                break
        else:
            return None

        anchor = self.root_slopes[root] * level
        center = 6 * anchor - 3 * level - self.margin
        other = 6 * center - 3 * level - self.margin
        roots = [center] + [other] * len(self.intervals)
        roots[root] = anchor
        relays = [3 * value - level for value in roots]
        extra = [2 * roots[index] - level for index in self.relay_extra]
        return tuple(value - self.shift for value in roots + relays + extra + [level / 2])

    def relaxation_witness(self, level):
        """Return an exact inequality witness at any real rational level."""
        level = _rational(level)
        value = min((level - offset) / (gain - 1) for _, _, gain, offset in self.branches)
        return (value,) * self.vertices

    def problem(self, level=None):
        """Use the fixed-level solver's vertices, branches and level fields."""
        output = {"vertices": self.vertices, "branches": self.branches}
        if level is not None:
            output["level"] = _rational(level)
        return output


def compile_spectrum(intervals):
    """Use only gains 2 and 3, and nonnegative rational offsets."""
    intervals = merge_intervals(intervals)
    zero = Fraction(0)
    if intervals == ((None, None),):
        branches = ((0, 0, 2, zero), (0, 0, 3, zero), (0, 1, 3, zero), (1, 1, 3, zero))
        return Network(intervals, 2, branches, zero, zero, (), ())

    endpoints = [endpoint for interval in intervals for endpoint in interval
                 if endpoint is not None]
    margin = 10 * max([Fraction(1)] + [abs(endpoint) for endpoint in endpoints])
    root_intervals = ((Fraction(1), zero),) + intervals
    count = len(root_intervals)
    slopes = []
    extra = []
    branches = []
    for index, (lower, upper) in enumerate(root_intervals):
        relay = count + index
        branches.append((index, relay, 3, zero))
        if lower is None:
            slope = HIGH
            extra_relay = 2 * count + len(extra)
            extra.append(index)
            branches.extend(((index, extra_relay, 2, zero), (extra_relay, index, 3, zero)))
        elif upper is None:
            slope = LOW
            branches.append((index, index, 3, zero))
        else:
            slope = MIDDLE
            branches.append((relay, index, 2, zero))
        slopes.append(slope)
        if index != 0:
            branches.extend(((count, index, 2, -margin), (relay, 0, 2, -margin)))

    sink = 2 * count + len(extra)
    branches.append((sink, sink, 3, zero))
    for index, ((lower, upper), slope) in enumerate(zip(root_intervals, slopes)):
        if lower is not None:
            branches.append((index, sink, 2, 2 * (LOWER_TEST - slope) * lower))
        if upper is not None:
            branches.append((index, sink, 3, 3 * (LOW - slope) * upper))

    shift = max(zero, max(-offset / (gain - 1) for _, _, gain, offset in branches))
    shifted = tuple((u, v, gain, offset + (gain - 1) * shift) for u, v, gain, offset in branches)
    return Network(intervals, sink + 1, shifted, shift, margin, tuple(slopes), tuple(extra))


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
