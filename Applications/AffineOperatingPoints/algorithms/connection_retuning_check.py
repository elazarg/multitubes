"""Verify the entire repair set by eliminating the original eigenvector variables."""

from fractions import Fraction as Q
from itertools import product
from random import Random

import z3

from connection_retuning import Interval, index_repairs


def real(value):
    return z3.RealVal(str(value))


def eigen_formula(size, level, branches):
    readings = [z3.Real(f"x_{vertex}") for vertex in range(size)]
    incoming = [[] for _ in readings]
    for tail, head, gain, offset in branches:
        residual = real(gain) * readings[tail] + offset - level - readings[head]
        incoming[head].append(residual)
    return z3.Exists(readings, z3.And(
        *(residual <= 0 for row in incoming for residual in row),
        *(z3.Or(*(residual == 0 for residual in row)) for row in incoming),
    ))


def assert_equivalent(actual, expected, instance):
    solver = z3.SolverFor("QF_LRA")
    solver.add(actual != expected)
    result = solver.check()
    assert result == z3.unsat, (instance, actual, expected, result, solver.model())


def exact_policy_intervals(size, branches):
    """Eliminate the readings from each choice of one tight branch per head."""
    incoming = [[] for _ in range(size)]
    for branch in branches:
        incoming[branch[1]].append(branch)

    intervals = set()
    for policy in product(*incoming):
        augmented = []
        for tail, head, gain, constant, parameter in policy:
            row = [Q(0)] * size
            row[head] = Q(1)
            row[tail] -= gain
            augmented.append([*row, constant, parameter])
        # A policy's cycles are all expansive, so its equality matrix is invertible.
        for column in range(size):
            pivot = next(i for i in range(column, size) if augmented[i][column])
            augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
            divisor = augmented[column][column]
            row = [entry / divisor for entry in augmented[column]]
            augmented[column] = row
            for i, other in enumerate(augmented):
                if i != column and other[column]:
                    multiple = other[column]
                    augmented[i] = [x - multiple * y for x, y in zip(other, row)]

        lower, upper = None, None
        for tail, head, gain, constant, parameter in branches:
            x_tail, rate_tail = augmented[tail][-2:]
            x_head, rate_head = augmented[head][-2:]
            shift = gain * x_tail + constant - x_head
            rate = gain * rate_tail + parameter - rate_head
            if rate > 0:
                bound = -shift / rate
                upper = bound if upper is None else min(upper, bound)
            elif rate < 0:
                bound = -shift / rate
                lower = bound if lower is None else max(lower, bound)
            elif shift > 0:
                break
            if lower is not None and upper is not None and lower > upper:
                break
        else:
            intervals.add(Interval(lower, upper))
    return intervals


def interval_formula(parameter, intervals):
    return z3.Or(*(z3.And(
        *([parameter >= real(interval.lower)] if interval.lower is not None else []),
        *([parameter <= real(interval.upper)] if interval.upper is not None else []),
    ) for interval in intervals))


def check_candidate(index, size, level, branches, candidate):
    tail, head, gain = candidate
    offset = z3.Real("offset")
    affine_rows = [(u, v, Q(a), Q(b) - level, Q(0)) for u, v, a, b in branches]
    affine_rows.append((tail, head, Q(gain), -Q(level), Q(1)))
    result = interval_formula(offset, exact_policy_intervals(size, affine_rows))
    intervals = index.query(*candidate)
    expected = interval_formula(offset, intervals)
    assert_equivalent(result, expected, (level, branches, candidate, intervals))


def demo_graph():
    return [
        (0, 0, 2, 0), (0, 0, 3, 0),
        (1, 1, 2, 0), (2, 2, 3, 0),
        (0, 1, 2, 0), (0, 2, 2, 2),
    ]


def fixtures():
    count = 0

    def compare(size, branches, candidate, expected, all_pairs=False):
        nonlocal count
        index = index_repairs(size, 0, branches)
        assert index.query(*candidate) == expected, (candidate, index, expected)
        candidates = ([(u, v, candidate[2]) for u in range(size) for v in range(size)]
                      if all_pairs else [candidate])
        for choice in candidates:
            check_candidate(index, size, 0, branches, choice)
            count += 1

    base = demo_graph()
    level = z3.Real("operating_level")
    level_rows = [(u, v, Q(a), Q(b), Q(-1)) for u, v, a, b in base]
    original_spectrum = interval_formula(level, exact_policy_intervals(3, level_rows))
    assert_equivalent(original_spectrum, z3.Or(level <= -4, level >= 4), base)

    compare(3, base, (1, 0, 2), (Interval(None, Q(-1)), Interval(Q(3), None)), True)
    good = [*base, (3, 3, 2, 0)]
    compare(4, [*good, (3, 1, 2, -3)], (1, 0, 2),
            (Interval(None, Q(9, 2)),), True)
    compare(4, [*good, (3, 1, 2, -2)], (1, 0, 2),
            (Interval(None, Q(3)),))
    compare(4, [*good, (3, 1, 2, -1)], (1, 0, 2), (Interval(None, Q(1)),))
    compare(4, good, (3, 0, 2), (Interval(None, Q(-1)),))
    compare(4, good, (1, 3, 2), ())

    chain = [(0, 0, 2, 0), (1, 1, 2, 0), (2, 2, 2, 0),
             (0, 1, 2, 0), (1, 2, 2, 2)]
    compare(3, chain, (1, 0, 2), (Interval(Q(3, 2), None),), True)
    # An outside source also reaches the merged component, which needs no pin of its own.
    compare(4, [*chain, (0, 2, 2, 2), (3, 3, 2, 0), (3, 1, 2, -1)],
            (1, 0, 2), (Interval(None, Q(1)),))
    # New and old pin ranges meet at a common endpoint.
    compare(2, [(0, 0, 2, 0), (1, 1, 2, 0), (0, 1, 2, 2)], (1, 0, 2), (Interval(),))
    # Two old bad sources cannot both change source status by adding one branch.
    compare(4, [*base, (3, 3, 2, 0), (3, 2, 2, 2)], (2, 0, 3), (), True)

    for size, branches, message in [
        (1, [(0, 0, 2, 0)], "already admits"),
        (1, [(0, 0, 1, 0)], "gains must exceed"),
        (2, [(0, 0, 2, 0), (0, 1, 2, 0)], "outgoing branch"),
    ]:
        try:
            index_repairs(size, 0, branches)
        except ValueError as exc:
            assert message in str(exc), exc
        else:
            raise AssertionError((size, branches, message))

    return count


def random_cases():
    rng = Random(4538)
    count = 0
    for trial in range(72):
        size = 2 + trial % 4
        level = Q(rng.randrange(-2, 3), rng.randrange(1, 4))
        gains = (Q(3, 2), 2, 3)
        branches = [(v, v, rng.choice(gains), rng.randrange(-5, 6)) for v in range(size)]
        for _ in range(2 * size):
            tail, head = sorted(rng.sample(range(size), 2))
            if rng.randrange(6) == 0:
                head, tail = tail, head
            branches.append((tail, head, rng.choice(gains),
                             Q(rng.randrange(-8, 9), rng.randrange(1, 4))))

        solver = z3.Solver()
        solver.add(eigen_formula(size, real(level), branches))
        status = solver.check()
        assert status in (z3.sat, z3.unsat)
        if status == z3.sat:
            try:
                index_repairs(size, level, branches)
            except ValueError as exc:
                assert "already admits" in str(exc), exc
            else:
                raise AssertionError((level, branches, "already admits an operating point"))
            continue

        index = index_repairs(size, level, branches)
        candidates = {(rng.randrange(size), rng.randrange(size), rng.choice(gains))
                      for _ in range(5)}
        candidates.update((u, v, rng.choice(gains))
                          for source in index.bad_sources for v in source for u in range(size))
        for candidate in sorted(candidates):
            check_candidate(index, size, level, branches, candidate)
            count += 1

    return count


if __name__ == "__main__":
    print(f"Direct all-real quantifier elimination verified {fixtures() + random_cases()} candidates.")
