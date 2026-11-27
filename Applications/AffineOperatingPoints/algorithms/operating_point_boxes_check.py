"""Compare sparse box queries to generator scans and direct rational constraints."""

from fractions import Fraction as Q
from random import Random

import z3

from operating_point_boxes import OperatingPointBoxes
from operating_point_poset import OperatingPointPoset


def real(value):
    return z3.RealVal(str(value))


def check_box(sparse, dense, branches, level, bounds):
    witness = sparse.match_box(bounds)
    assert witness == dense.match_box(bounds), (branches, level, bounds, witness)

    x = [z3.Real(f"reading_{vertex}") for vertex in range(len(dense.upper))]
    incoming = [[] for _ in x]
    for tail, head, gain, offset in branches:
        incoming[head].append(real(gain) * x[tail] + real(offset) - x[head] - real(level))
    solver = z3.SolverFor("QF_LRA")
    for row in incoming:
        solver.add(*(residual <= 0 for residual in row))
        solver.add(z3.Or(*(residual == 0 for residual in row)))
    for vertex, (lower, upper) in bounds.items():
        if lower is not None:
            solver.add(x[vertex] >= real(lower))
        if upper is not None:
            solver.add(x[vertex] <= real(upper))

    if witness is not None:
        solver.push()
        solver.add(*(point == real(value) for point, value in zip(x, witness)))
        assert solver.check() == z3.sat, (branches, level, bounds, witness)
        solver.pop()
        solver.add(z3.Or(*(point > real(value) for point, value in zip(x, witness))))
    assert solver.check() == z3.unsat, (branches, level, bounds, witness)


def cases(size, level, branches, boxes):
    sparse = OperatingPointBoxes(size, level, branches)
    dense = OperatingPointPoset(size, level, branches)
    for bounds in boxes:
        check_box(sparse, dense, branches, level, bounds)
    return len(boxes)


def fixtures():
    branches = [(0, 0, 2, 0), (1, 1, 2, 0), (0, 1, 2, -1), (1, 0, 2, -1)]
    sparse = OperatingPointBoxes(2, 0, branches)
    expected = [
        ({}, (0, 0)),
        ({0: (None, None)}, (0, 0)),
        ({0: (None, "-1/2")}, (-1, 0)),
        ({0: (None, "-1/2"), 1: (None, "-1/2")}, None),
        ({0: (0, None)}, (0, 0)),
        ({0: (-1, -1), 1: (0, None)}, (-1, 0)),
        ({0: ("-3/4", "-1/2")}, None),
        ({0: (1, 0)}, None),
    ]
    for bounds, witness in expected:
        assert sparse.match_box(bounds) == witness, bounds
    return cases(2, 0, branches, [bounds for bounds, _ in expected])


def random_cases():
    rng = Random(674123)
    count = 0
    for trial in range(42):
        size = 1 + trial % 6
        scales = [Q(rng.randint(1, 8), rng.randint(1, 4)) for _ in range(size)]
        level = Q(rng.randint(-5, 5), rng.randint(1, 3))
        pairs = [(v, (v + 1) % size) for v in range(size)]
        pairs += [(v, v) for v in range(size)]
        pairs += [(rng.randrange(size), rng.randrange(size)) for _ in range(size + 1)]
        branches = [
            (u, v, rng.choice((2, 3, Q(3, 2))) * scales[v] / scales[u],
             Q(rng.randint(-4, 4), rng.randint(1, 3)) * scales[v] + level)
            for u, v in pairs
        ]
        boxes = [{}]
        for _ in range(7):
            bounds = {}
            for vertex in rng.sample(range(size), rng.randint(1, size)):
                endpoints = (Q(rng.randint(-12, 12), rng.randint(1, 4)),
                             Q(rng.randint(-12, 12), rng.randint(1, 4)))
                lower, upper = sorted(endpoints)
                bounds[vertex] = (lower if rng.randrange(2) else None,
                                  upper if rng.randrange(2) else None)
            boxes.append(bounds)
        count += cases(size, level, branches, boxes)
    return count


if __name__ == "__main__":
    print(f"Generator scans and direct QF_LRA verified {fixtures() + random_cases()} boxes.")
