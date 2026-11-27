"""Compare the real operating points with independent exact Z3 model blocking."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from random import Random

import z3

from operating_point_lattice import compile_operating_points
from operating_point_poset import OperatingPointPoset


def exact_models(case, upper, limit):
    size = case["vertices"]
    level = z3.RealVal(str(case["level"]))
    variables = [z3.Real(f"oracle_{index}") for index in range(size)]
    candidates = [[] for _ in variables]
    for tail, head, gain, offset in case["branches"]:
        candidates[head].append(
            z3.RealVal(str(gain)) * variables[tail] + z3.RealVal(str(offset)) - level
        )

    solver = z3.SolverFor("QF_LRA")
    for reading, incoming in zip(variables, candidates):
        solver.add(*(reading >= branch for branch in incoming))
    solver.push()
    solver.add(*(reading == z3.RealVal(str(value)) for reading, value in zip(variables, upper)))
    assert solver.check() == z3.sat
    solver.pop()
    solver.push()
    solver.add(z3.Or(*(reading > z3.RealVal(str(value))
                      for reading, value in zip(variables, upper))))
    assert solver.check() == z3.unsat
    solver.pop()
    for reading, incoming in zip(variables, candidates):
        solver.add(z3.Or(*(reading == branch for branch in incoming)))

    vectors = set()
    while (status := solver.check()) == z3.sat:
        model = solver.model()
        values = tuple(model.eval(reading, model_completion=True) for reading in variables)
        vectors.add(tuple(
            Fraction(value.numerator_as_long(), value.denominator_as_long())
            for value in values
        ))
        assert len(vectors) <= limit
        solver.add(z3.Or(*(reading != value for reading, value in zip(variables, values))))
    assert status == z3.unsat
    return vectors


def verify(case, rng):
    index = OperatingPointPoset(**case)
    upsets = tuple(index.upsets())
    assert len(set(upsets)) == len(upsets)
    points = set()
    point_at = {}
    for upset in upsets:
        vector = index.vector(upset)
        assert index.decode(vector) == upset
        point_at[upset] = vector
        points.add(vector)
    assert points == exact_models(case, index.upper, len(upsets))

    for left, right in zip(upsets, reversed(upsets)):
        vector_order = all(a <= b for a, b in zip(point_at[left], point_at[right]))
        assert (set(left) <= set(right)) == vector_order
        union = tuple(sorted(set(left) | set(right)))
        assert point_at[union] == tuple(map(max, zip(point_at[left], point_at[right])))

    size = case["vertices"]
    boxes = [{}, {0: (1, -1)}]
    for _ in range(10):
        vector = rng.choice(tuple(sorted(points)))
        bounds = {}
        for vertex, current in enumerate(vector):
            if rng.randrange(2):
                lower = current + Fraction(rng.randrange(-2, 3), 3)
                upper = lower + Fraction(rng.randrange(0, 4), 3)
                bounds[vertex] = (
                    lower if rng.randrange(2) else None,
                    upper if rng.randrange(2) else None,
                )
        boxes.append(bounds)
    for bounds in boxes:
        matches = [
            vector for vector in points
            if all((lower is None or lower <= vector[vertex]) and
                   (upper is None or vector[vertex] <= upper)
                   for vertex, (lower, upper) in bounds.items())
        ]
        expected = tuple(map(max, zip(*matches))) if matches else None
        assert index.match_box(bounds) == expected
    return index, points, len(boxes)


def expected_upsets(vertices, arcs):
    return {
        bits
        for bits in product((0, 1), repeat=vertices)
        if all(bits[tail] <= bits[head] for tail, head in arcs)
    }


def relation_cases(rng):
    for size in range(4):
        possible = [(tail, head) for tail in range(size) for head in range(size) if tail != head]
        for subset in product((False, True), repeat=len(possible)):
            yield size, [edge for edge, include in zip(possible, subset) if include]
    for subset in product((False, True), repeat=4):
        possible = [(0, 2), (0, 3), (1, 2), (1, 3)]
        yield 4, [edge for edge, include in zip(possible, subset) if include]
    yield 5, [(0, 4), (1, 4), (2, 4), (3, 4), (1, 4), (3, 3)]
    for _ in range(12):
        yield 5, [edge for edge in combinations(range(5), 2) if rng.randrange(2)]


def mixed_cases(rng):
    yield dict(vertices=2, level=0, branches=[
        (0, 0, 2, 0), (1, 1, 2, 0), (0, 1, "1/2", 0), (1, 0, 3, -1),
    ])
    yield dict(vertices=2, level=0, branches=[
        (0, 0, 2, 0), (0, 1, 2, -1), (1, 0, 2, 0),
    ])  # The greatest relaxation itself fails one fixed-point equation.
    yield dict(vertices=4, level=0, branches=[
        (0, 0, 2, 0), (1, 1, 2, 0), (2, 2, 2, 0), (0, 3, 2, 0),
        (1, 3, 2, 0), (3, 2, 2, 0), (2, 0, 2, -1), (2, 1, 2, -1),
    ])  # Meet of upsets can differ from the coordinatewise minimum of readings.
    for _ in range(30):
        size = rng.randrange(2, 7)
        level = Fraction(3, 7)
        scales = [Fraction(rng.randrange(1, 8), rng.randrange(1, 8)) for _ in range(size)]
        upper = [Fraction(rng.randrange(-8, 9), rng.randrange(1, 5)) for _ in range(size)]
        anchors = {0} | {vertex for vertex in range(size) if rng.randrange(3) == 0}
        branches = []

        def append(tail, head, slack):
            gain = Fraction(rng.randrange(2, 6)) * scales[head] / scales[tail]
            offset = upper[head] + level - gain * upper[tail] - slack
            branches.append((tail, head, gain, offset))

        for tail in range(size):
            append(tail, (tail + 1) % size, int(tail in anchors))
            if tail in anchors:
                append(tail, tail, 0)
        for _ in range(2 * size):
            append(rng.randrange(size), rng.randrange(size), rng.randrange(4))
        yield dict(vertices=size, level=level, branches=branches)


def main():
    rng = Random(722027)
    checked = vectors = boxes = 0
    for vertices, arcs in relation_cases(rng):
        expected = expected_upsets(vertices, arcs)
        for bounded in (False, True):
            shifted = checked % 3 == 0
            case = compile_operating_points(
                vertices, arcs, bounded_indegree=bounded, nonnegative_offsets=shifted
            )
            assert case["level"] == 0
            assert all(gain == 2 and offset in (int(shifted) - 1, int(shifted))
                       for _, _, gain, offset in case["branches"])
            if bounded:
                assert max(Counter(head for _, head, _, _ in case["branches"]).values()) <= 2
            index, solutions, queries = verify(case, rng)
            start = -int(shifted)
            inactive = start - (2 if bounded else 1)
            assert all(vector[vertices] == start for vector in solutions)
            assert all(value in (inactive, start)
                       for vector in solutions for value in vector[:vertices])
            assert {
                tuple(int(value == start) for value in vector[:vertices])
                for vector in solutions
            } == expected
            assert len(solutions) == len(expected)
            checked += 1
            vectors += len(solutions)
            boxes += queries

    for case in mixed_cases(rng):
        index, solutions, queries = verify(case, rng)
        checked += 1
        vectors += len(solutions)
        boxes += queries
    invalid = (
        [(0, 1, "1/2", 0), (1, 0, 2, 0)],  # Unit cycle.
        [(0, 1, "1/2", 0), (1, 0, "3/2", 0)],  # Contractive cycle.
        [(0, 0, 2, 0), (1, 1, 2, 0)],  # Disconnected.
        [(0, 1, 2, 0), (1, 0, 0, 0)],  # Zero gain.
    )
    for branches in invalid:
        try:
            OperatingPointPoset(2, 0, branches)
        except ValueError:
            pass
        else:
            raise AssertionError("accepted an invalid index input")
    print(f"Checked {checked} networks, {vectors} exact operating points, and {boxes} boxes.")


if __name__ == "__main__":
    main()
