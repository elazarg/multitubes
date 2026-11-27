"""Compare two-LP eigenvalue decisions against exact enumeration of branch policies."""

import argparse
from dataclasses import replace
from fractions import Fraction as Q
from itertools import product
from random import Random
from time import perf_counter

from affine_spectrum import Result, certify, demo, solve


def feasible(inequalities):
    """Independent exact Fourier–Motzkin elimination, for tiny examples."""
    current = list(set(inequalities))
    while current and len(current[0][0]):
        positive = []
        negative = []
        zero = set()
        for lhs, rhs in current:
            coefficient, *rest = lhs
            if coefficient > 0:
                positive.append((tuple(x / coefficient for x in rest), rhs / coefficient))
            elif coefficient < 0:
                negative.append((tuple(x / -coefficient for x in rest), rhs / -coefficient))
            else:
                zero.add((tuple(rest), rhs))
        for p, pr in positive:
            for n, nr in negative:
                row = tuple(x + y for x, y in zip(p, n))
                zero.add((row, pr + nr))
        if any(not any(lhs) and rhs < 0 for lhs, rhs in zero):
            return False
        current = list(zero)
    return all(rhs >= 0 for _, rhs in current)


def reference(size, level, branches):
    rows_by_head = [[] for _ in range(size)]
    for tail, head, gain, offset in branches:
        lhs = [Q(0)] * size
        lhs[head] -= 1
        lhs[tail] += Q(gain)
        rows_by_head[head].append((tuple(lhs), Q(level) - Q(offset)))
    rows = [row for group in rows_by_head for row in group]
    if not feasible(rows):
        return "relaxation_infeasible"
    for policy in product(*rows_by_head):
        equalities = [(tuple(-a for a in lhs), -rhs) for lhs, rhs in policy]
        if feasible(rows + equalities):
            return "eigenvector"
    return "no_eigenvector"


def compare(size, level, branches, expected=None):
    result = solve(size, level, branches)
    expected = reference(size, level, branches) if expected is None else expected
    assert result.status == expected, (size, level, branches, result, expected)
    assert certify(size, level, branches, result)
    if result.status == "no_eigenvector":
        assert not certify(size, level, branches, replace(result, ray=(Q(0),) * size))
        assert not certify(size, level, branches, replace(result, ray=tuple(-value for value in result.ray)))
    elif result.status == "relaxation_infeasible":
        assert not certify(size, level, branches, replace(result, multipliers=()))
    return result.status


def random_cases():
    counts = {}
    rng = Random(135103)
    for trial in range(480):
        size = 1 + trial % 4
        level = rng.choice((-3, -1, Q(-1, 3), 0, Q(1, 2), 1, 3))
        branches = []
        for head in range(size):
            for j in range(rng.choice((1, 2, 2, 3))):
                tail = head if j == 0 and trial % 3 else rng.randrange(size)
                gain = rng.choice((0, Q(1, 3), Q(1, 2), 1, 1, Q(3, 2), 2, 3))
                offset = rng.choice((-1, Q(-2, 3), 0, 1, Q(3, 2)))
                branches.append((tail, head, gain, offset))
        outcome = compare(size, level, branches)
        counts[outcome] = counts.get(outcome, 0) + 1
    return counts


def fixtures():
    for invalid in (float("nan"), float("inf"), True):
        forged = Result("no_eigenvector", (0,), (invalid,))
        assert not certify(1, 0, [(0, 0, 0, 0)], forged)
    # A valid downward ray from a feasible but nonmaximizing U proves nothing.
    capped = [(0, 0, 2, 0), (1, 1, 1, 0), (0, 1, 1, 1)]
    forged = Result("no_eigenvector", (-1, 0), (1, 0))
    assert not certify(2, 0, capped, forged)
    compare(2, 0, capped, "eigenvector")
    for case in demo():
        compare(case["vertices"], case["level"], case["branches"])
    cases = [
        (2, 0, [(0, 1, 1, 2), (1, 0, 1, -2)], "eigenvector"),
        (2, 0, [(0, 1, 1, 2), (1, 0, 1, -1)], "relaxation_infeasible"),
        (2, 0, [(0, 1, 1, 2), (1, 0, 1, -3)], "no_eigenvector"),
        (2, 0, [(0, 1, 6, 2), (1, 0, "1/8", -3)], "eigenvector"),
        (3, 0, [(1, 0, 0, 3), (0, 1, 2, 0), (1, 2, "1/2", 0)], "eigenvector"),
        (4, 0, [(0, 0, 2, 0), (0, 1, 3, 1), (1, 1, 2, 0),
                (0, 2, "1/2", 2), (2, 3, "1/2", 0)], "no_eigenvector"),
        (4, 0, [(0, 0, 2, 0), (0, 1, 3, -1), (1, 1, 2, 0),
                (0, 2, "1/2", 2), (2, 3, "1/2", 0)], "eigenvector"),
        (2, Q(1, 3), [(0, 0, 2, 0),
                       (0, 1, Q(1, 3), 1), (1, 1, Q(1, 2), 0)], "eigenvector"),
        (2, 0, [(0, 0, 2, 0), (1, 1, 1, -1), (1, 0, 0, -2)], "no_eigenvector"),
    ]
    for size, level, branches, expected in cases:
        assert reference(size, level, branches) == expected
        compare(size, level, branches, expected)


def benchmark():
    for sources in (32, 96, 256):
        branches = [(sources, sources, 3, 0)]
        for i in range(sources):
            branches.extend(((i, i, 2, 0), (i, i, 3, 0), (i, sources, 2, i + 1)))
        for level in (0, 2 * sources):
            start = perf_counter()
            outcome = "no_eigenvector" if level == 0 else "eigenvector"
            compare(sources + 1, level, branches, outcome)
            print(f"{sources + 1:4} vertices, {len(branches):4} branches, "
                  f"{outcome:14} {perf_counter() - start:.3f}s")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--benchmark", action="store_true")
    args = parser.parse_args()
    fixtures()
    print(random_cases())
    if args.benchmark:
        benchmark()


if __name__ == "__main__":
    main()
