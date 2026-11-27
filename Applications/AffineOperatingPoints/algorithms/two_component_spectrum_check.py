"""Check expanded affine networks by exact enumeration of active branches."""

from fractions import Fraction
from itertools import combinations, product
from random import Random

from two_component_spectrum import compile_spectrum


def contains(intervals, level):
    return any((lo is None or lo <= level) and (hi is None or level <= hi)
               for lo, hi in intervals)


def components(vertex_count, branches):
    outgoing = [[] for _ in range(vertex_count)]
    for tail, head, _, _ in branches:
        outgoing[tail].append(head)
    reachable = []
    for start in range(vertex_count):
        seen = {start}
        todo = [start]
        while todo:
            for target in outgoing[todo.pop()]:
                if target not in seen:
                    seen.add(target)
                    todo.append(target)
        reachable.append(seen)
    return {frozenset(v for v in reachable[u] if u in reachable[v])
            for u in range(vertex_count)}


def policy_potential(policy, vertex):
    """Find (slope, intercept) of a vertex's solution under a fixed policy."""
    seen = {}
    current = vertex
    gain, slope, intercept = 1, 0, Fraction(0)
    while current not in seen:
        seen[current] = gain, slope, intercept
        tail, _, next_gain, offset = policy[current]
        slope -= gain
        intercept += gain * offset
        gain *= next_gain
        current = tail

    earlier_gain, earlier_slope, earlier_intercept = seen[current]
    # Both compositions equal the original vertex and end at the same vertex.
    factor = earlier_gain - gain
    root_slope = Fraction(slope - earlier_slope, factor)
    root_intercept = (intercept - earlier_intercept) / factor
    return gain * root_slope + slope, gain * root_intercept + intercept


def policy_solution(policy, branches):
    affine = tuple(policy_potential(policy, vertex) for vertex in range(len(policy)))
    lower, upper = None, None
    for tail, head, gain, offset in branches:
        tail_slope, tail_offset = affine[tail]
        head_slope, head_offset = affine[head]
        rate = gain * tail_slope - head_slope - 1
        constant = gain * tail_offset + offset - head_offset
        if rate == 0:
            if constant > 0:
                return None
            continue
        intercept = -constant / rate
        if rate < 0:
            lower = intercept if lower is None else max(lower, intercept)
        else:
            upper = intercept if upper is None else min(upper, intercept)
        if lower is not None and upper is not None and lower > upper:
            return None
    return (lower, upper), affine


def exact_policy_solutions(vertices, branches):
    incoming = [[] for _ in range(vertices)]
    for branch in branches:
        incoming[branch[1]].append(branch)
    solutions = set()
    for policy in product(*incoming):
        solution = policy_solution(policy, branches)
        if solution is not None:
            solutions.add(solution)
    return solutions


def samples_at_boundaries(intervals, extra=()):
    endpoints = {endpoint for row in intervals for endpoint in row if endpoint is not None}
    boundaries = sorted(endpoints.union(extra))
    if not boundaries:
        return [Fraction(0)]
    return [boundaries[0] - 1, boundaries[-1] + 1, *boundaries,
            *((a + b) / 2 for a, b in zip(boundaries, boundaries[1:]))]


def coincide_at(maps):
    """Find all isolated crossings between distinct affine vector-valued maps."""
    levels = set()
    for left, right in combinations(set(maps), 2):
        differences = [(a - c, b - d) for (a, b), (c, d) in zip(left, right)]
        for rate, constant in differences:
            if rate:
                level = -constant / rate
                if all(a * level + b == 0 for a, b in differences):
                    levels.add(level)
                break
    return levels


def check_fibre_counts(solutions, target_ranges, expected):
    # The domain boundaries and the isolated intersections of affine maps
    # partition the line into singletons and open intervals of constant count.
    ranges = [interval for interval, _ in solutions]
    extra = coincide_at(affine for _, affine in solutions)
    for level in samples_at_boundaries([*target_ranges, *ranges], extra):
        potentials = {tuple(a * level + b for a, b in affine)
                      for interval, affine in solutions if contains([interval], level)}
        assert len(potentials) == expected(level), (level, len(potentials))


def check(intervals, exact=True):
    raw = [tuple(None if x is None else Fraction(x) for x in row) for row in intervals]
    network = compile_spectrum(intervals)
    assert {gain for _, _, gain, _ in network.branches} == {2, 3}
    assert all(offset >= 0 for _, _, _, offset in network.branches)
    parts = components(network.vertices, network.branches)
    assert parts == {frozenset(range(network.vertices - 1)), frozenset({network.vertices - 1})}
    assert any(tail != head and head == network.vertices - 1
               for tail, head, _, _ in network.branches)
    assert network.vertices <= 2 * len(network.intervals) + 4
    assert len(network.branches) <= 6 * len(network.intervals) + 5

    if exact:
        def expected(level):
            if network.intervals == ((None, None),):
                return 2 if level < 0 else 1
            if not contains(raw, level):
                return 0
            if any(level in row for row in network.intervals):
                return 1
            return 2

        solutions = exact_policy_solutions(network.vertices, network.branches)
        extra = [(Fraction(0), Fraction(0))] if network.intervals == ((None, None),) else []
        check_fibre_counts(solutions, [*raw, *network.intervals, *extra], expected)

    for level in [*samples_at_boundaries(raw), Fraction(-10**30), Fraction(10**30)]:
        potential = network.relaxation_witness(level)
        assert all(gain * potential[u] + offset <= level + potential[v]
                   for u, v, gain, offset in network.branches)
        eigen = network.eigenvector(level)
        assert (eigen is not None) == contains(raw, level)
        if eigen is not None:
            values = [[] for _ in range(network.vertices)]
            for u, v, gain, offset in network.branches:
                values[v].append(gain * eigen[u] + offset)
            assert all(max(row) == x + level for row, x in zip(values, eigen))


def check_sink_ring(count):
    zero = Fraction(0)
    unshifted = [(1, 0, 2, zero), (0, 1, 3, zero)]
    for i in range(count):
        y = i + 2
        previous = (i - 1) % count + 2
        unshifted.extend(((y, y, 3, zero), (0, y, 2, zero),
                          (0, y, 3, Fraction(-3, 10)), (previous, y, 3, Fraction(-1))))
    branches = tuple((u, v, gain, offset + Fraction(gain - 1, 2))
                     for u, v, gain, offset in unshifted)
    assert min(offset for _, _, _, offset in branches) >= 0
    assert components(count + 2, branches) == {frozenset({0, 1}),
                                                frozenset(range(2, count + 2))}

    def expected(level):
        if 0 < level < 1:
            return 2**count
        return 1 if level in (0, 1) else 0

    solutions = exact_policy_solutions(count + 2, branches)
    check_fibre_counts(solutions, [(Fraction(0), Fraction(1))], expected)


def main():
    fixtures = [
        [],
        [(None, None)],
        [(None, 0), (0, None)],
        [(None, -1), (1, None)],
        [(5, None)],
        [(None, 9)],
        [(1, 1)],
        [(-5, -5), (-3, -2), (1, 4), (10, 11), (14, 16)],
        [(None, -4), (-2, -2), (0, 1), (2, None)],
        [(None, -2), (-1, 0), (0, 1), (4, 4), (5, 6), (8, None), (-4, -3)],
        [(None, "-7/5"), ("-14/11", "-12/11"), (0, 0), ("1/5", None)],
        [(-10**25, -10**25 + 1), ("1/1000000000000001", "1/1000000000000000")],
        [(4, 5), (2, 3), (1, 2), (0, 2)],
    ]
    random = Random(271828)
    for _ in range(34):
        rows = []
        for index in range(random.randrange(1, 5)):
            left = Fraction(3 * index) + Fraction(random.randrange(4), 8)
            right = left + Fraction(random.randrange(5), 7)
            rows.append((None if random.randrange(17) == 0 else left,
                         None if random.randrange(17) == 0 else right))
        random.shuffle(rows)
        fixtures.append(rows)
    for rows in fixtures:
        check(rows)

    large = [(None, -3)] + [(3 * i, 3 * i + 1) for i in range(60)] + [(184, None)]
    check(large, exact=False)
    for count in range(2, 7):
        check_sink_ring(count)
    print(f"Independent exact policy enumeration checked {len(fixtures)} spectra and fibre counts.")
    print("Exact coordinate and graph checks also passed on a 62-interval target.")
    print("Exact fibre counts passed for sink rings of sizes two through six.")


if __name__ == "__main__":
    main()
