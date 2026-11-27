"""Check exact curves against independent simple-cycle enumeration."""

from fractions import Fraction
from itertools import combinations, product
from random import Random

from calibration_replacement import replacement_curves


def simple_cycles(vertex_count, comparisons):
    outgoing = [[] for _ in range(vertex_count)]
    for edge, (tail, head, weight) in enumerate(comparisons):
        weight = Fraction(weight)
        outgoing[tail].append((head, edge, 1, weight))
        outgoing[head].append((tail, edge, -1, -weight))

    def extend(root, tail, visited, path, total):
        for head, edge, sign, weight in outgoing[tail]:
            extended_path = path + ((edge, sign, weight),)
            if head == root:
                yield extended_path, total + weight
            elif head > root and head not in visited:
                yield from extend(
                    root, head, visited | {head}, extended_path, total + weight
                )

    return [
        cycle
        for root in range(vertex_count)
        for cycle in extend(root, root, {root}, (), Fraction(0))
    ]


def brute_lines(cycles, comparisons, edited):
    lines = {Fraction(0): Fraction(0)}
    for path, total in cycles:
        coefficient = sum(sign for edge, sign, _ in path if edge == edited)
        slope = Fraction(coefficient, len(path))
        intercept = (total - coefficient * Fraction(comparisons[edited][2])) / len(path)
        lines[slope] = max(intercept, lines.get(slope, intercept))
    return list(lines.items())


def brute_bounds(lines, cap):
    if any(slope == 0 and intercept > cap for slope, intercept in lines):
        return None
    lower = max(((cap - b) / a for a, b in lines if a < 0), default=None)
    upper = min(((cap - b) / a for a, b in lines if a > 0), default=None)
    if lower is not None and upper is not None and lower > upper:
        return None
    return lower, upper


def check(vertex_count, comparisons):
    cycles = simple_cycles(vertex_count, comparisons)
    curves = replacement_curves(vertex_count, comparisons)
    point_count = cap_count = 0
    for edited, curve in enumerate(curves):
        lines = brute_lines(cycles, comparisons, edited)
        baseline = max(
            (total / len(path) for path, total in cycles
             if all(edge != edited for edge, _, _ in path)),
            default=Fraction(0),
        )
        assert curve.minimum == baseline
        assert curve.best_offsets() == brute_bounds(lines, baseline)

        knots = {(d - b) / (a - c) for (a, b), (c, d) in combinations(lines, 2)}
        knots.update(start for start, _, _ in curve.pieces() if start is not None)
        ordered = sorted(knots)
        points = set(ordered)
        points.update((left + right) / 2 for left, right in zip(ordered, ordered[1:]))
        if ordered:
            points.update((ordered[0] - 1, ordered[-1] + 1))
        points.update((Fraction(comparisons[edited][2]), Fraction(-101), Fraction(101)))

        caps = {baseline - 1, baseline, baseline + 1, Fraction(0)}
        for point in points:
            expected = max(a * point + b for a, b in lines)
            assert curve.tolerance(point) == expected
            caps.add(expected)
        for cap in caps:
            assert curve.acceptable_offsets(cap) == brute_bounds(lines, cap)
        point_count += len(points)
        cap_count += len(caps)
    return len(curves), point_count, cap_count


def main():
    demonstration = [(0, 1, -3), (0, 1, 0), (0, 2, 4), (2, 1, 0)]
    edited = replacement_curves(3, demonstration)[0]
    assert edited.pieces() == (
        (None, Fraction(-1, 2), Fraction(0)),
        (Fraction(-8), Fraction(-1, 3), Fraction(4, 3)),
        (Fraction(0), Fraction(0), Fraction(4, 3)),
        (Fraction(8, 3), Fraction(1, 2), Fraction(0)),
    )
    assert edited.tolerance(-3) == Fraction(7, 3)
    assert edited.best_offsets() == (0, Fraction(8, 3))
    assert edited.acceptable_offsets("3/2") == (Fraction(-1, 2), 3)
    group_e = [(3, 2, -1), (1, 0, 7), (1, 3, -1),
               (2, 0, 0), (0, 3, 1), (2, 1, -2)]
    match = replacement_curves(4, group_e)[1]
    assert match.tolerance(7) == 3
    assert match.minimum == Fraction(4, 3)
    assert match.best_offsets() == (-2, 2)
    for margin, cap, ratings in (
        (7, Fraction(3), (4, 0, 1, 2)),
        (-2, Fraction(4, 3), (Fraction(-2, 3), 0, Fraction(2, 3), Fraction(1, 3))),
        (2, Fraction(4, 3), (Fraction(2, 3), 0, Fraction(2, 3), Fraction(1, 3))),
    ):
        for index, (second, first, score_margin) in enumerate(group_e):
            observed = margin if index == 1 else score_margin
            assert abs(ratings[first] - ratings[second] - observed) <= cap
    rng = Random(1030801)
    fixtures = [
        (0, []),
        (7, []),
        (3, demonstration),
        (4, group_e),
        (5, [(0, 0, 5), (0, 0, -1), (1, 2, 5), (3, 4, "-11/4")]),
        (4, [(0, 1, 2), (1, 2, 5), (2, 3, 6), (3, 0, -4)]),
    ]
    pair_options = [None, -2, 0, 3]
    for choices in product(pair_options, repeat=6):
        pairs = combinations(range(4), 2)
        fixtures.append((4, [
            (tail, head, weight)
            for (tail, head), weight in zip(pairs, choices)
            if weight is not None
        ]))
    for _ in range(250):
        size = rng.randrange(1, 7)
        comparisons = [
            (rng.randrange(size), rng.randrange(size),
             Fraction(rng.randrange(-13, 14), rng.randrange(1, 5)))
            for _ in range(rng.randrange(1, 12))
        ]
        fixtures.append((size, comparisons))
    curve_count = point_count = cap_count = 0
    for vertex_count, comparisons in fixtures:
        curves, points, caps = check(vertex_count, comparisons)
        curve_count += curves
        point_count += points
        cap_count += caps
    print(
        f"Checked {len(fixtures)} networks, {curve_count} curves, "
        f"{point_count} tolerance queries and {cap_count} offset intervals."
    )


if __name__ == "__main__":
    main()
