"""Independent small-instance oracles for periodic_buffers.py."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from random import Random

from periodic_buffers import (
    Edge, Progression, Run, admissible_phases, envelope, find_lasso,
    index_period, realize,
)


def expand(edges, runs, base, counts):
    expanded = [i for run in runs for _ in range(run.copies) for i in run.word]
    assert Counter(expanded) == Counter({i: c for i, c in enumerate(counts) if c})
    vertex = base
    for i in expanded:
        assert edges[i].tail == vertex
        vertex = edges[i].head
    assert vertex == base
    assert sum(len(run.word) for run in runs) <= 2 * len(edges) * len(
        {v for edge in edges for v in (edge.tail, edge.head)})
    return expanded


def brute_envelopes(edges, word, stock, box):
    """Expand all rotations and evaluate all corners directly."""
    width = 1 + len(box)
    scenarios = []
    for corner in product(*box):
        weights = []
        for i in word:
            coefficient = edges[i].weight
            weights.append(tuple(
                coefficient[offset] + sum(c * t for c, t in zip(
                    coefficient[offset + 1:offset + width], corner))
                for offset in range(0, len(coefficient), width)
            ))
        scenarios.append(weights)
    result = []
    for phase in range(len(word)):
        low, high = list(stock), list(stock)
        for weights in scenarios:
            inventory = list(stock)
            for charge in weights[phase:] + weights[:phase]:
                inventory = [a + c for a, c in zip(inventory, charge)]
                low = list(map(min, zip(low, inventory)))
                high = list(map(max, zip(high, inventory)))
            assert inventory == list(stock)
        result.append(tuple(zip(low, high)))
    return result


def check_phases(rng):
    got_nontrivial = 0
    for _ in range(180):
        vertices = rng.randrange(1, 5)
        resources, parameters = rng.randrange(1, 4), rng.randrange(4)
        size = resources * (1 + parameters)
        edges = [Edge(v, w, tuple(rng.randint(-3, 3) for _ in range(size)))
                 for v in range(vertices) for w in range(vertices)]
        visit = [rng.randrange(vertices) for _ in range(rng.randrange(1, 23))]
        base = visit[0]
        word = [v * vertices + w for v, w in zip(visit, visit[1:] + [base])]
        correction = tuple(-sum(edges[i].weight[j] for i in word) for j in range(size))
        edges.append(Edge(base, base, correction))
        counts = Counter(word + [len(edges) - 1])
        counts = [counts[i] for i in range(len(edges))]
        runs = realize(edges, counts, base)
        expanded = expand(edges, runs, base, counts)
        index = index_period(edges, runs)
        stock = tuple(rng.randint(-4, 8) for _ in range(resources))
        box = tuple(sorted((Fraction(rng.randint(-4, 5), rng.randint(1, 4)),
                            Fraction(rng.randint(-4, 5), rng.randint(1, 4))))
                    for _ in range(parameters))
        expected_envelopes = brute_envelopes(edges, expanded, stock, box)
        for phase, expected in enumerate(expected_envelopes):
            assert envelope(index, phase, stock, box) == expected
        for _ in range(4):
            template = rng.choice(expected_envelopes)
            limits = tuple(sorted((low + rng.randint(-4, 4), high + rng.randint(-4, 4)))
                           for low, high in template)
            allowed = {v for v in range(vertices) if rng.randrange(3)}
            expected = [phase for phase, bounds in enumerate(expected_envelopes)
                        if edges[expanded[phase]].tail in allowed
                        and all(lo <= low <= high <= hi
                                for (lo, hi), (low, high) in zip(limits, bounds))]
            progressions = admissible_phases(index, stock, limits, box, allowed)
            assert progressions == admissible_phases(
                index, stock, limits, box, allowed, method="binary")
            actual = [p.first + p.step * j for p in progressions for j in range(p.count)]
            assert sorted(actual) == expected
            got_nontrivial += 0 < len(expected) < len(expanded)
    assert got_nontrivial >= 30
    return got_nontrivial


def full_column_solution(matrix, columns):
    """Solve a rectangular normalized subsystem by elimination, if unique."""
    rows = [[Fraction(row[j]) for j in columns] + [Fraction(rhs)]
            for row, rhs in matrix]
    for col in range(len(columns)):
        p = next((i for i in range(col, len(rows)) if rows[i][col]), None)
        if p is None:
            return None
        rows[col], rows[p] = rows[p], rows[col]
        pivot = rows[col]
        rows[col] = [x / pivot[col] for x in pivot]
        for i, row in enumerate(rows):
            if i != col and row[col]:
                rows[i] = [a - row[col] * b for a, b in zip(row, rows[col])]
    if any(row[-1] for row in rows[len(columns):]):
        return None
    return [rows[i][-1] for i in range(len(columns))]


def brute_lasso(edges, start):
    # Enumerate basic supports of the normalized circulation polytope,
    # then check every possible connected face by enumerating edge subsets.
    vertices = {start} | {v for edge in edges for v in (edge.tail, edge.head)}
    reachable = {start}
    for _ in vertices:
        reachable |= {e.head for e in edges if e.tail in reachable}
    edges = [e for e in edges if e.tail in reachable]
    if not edges:
        return False
    matrix = [([int(e.tail == v) - int(e.head == v) for e in edges], 0)
              for v in reachable]
    matrix += [([e.weight[i] for e in edges], 0) for i in range(len(edges[0].weight))]
    matrix.append(([1] * len(edges), 1))
    subsets = [frozenset(s) for size in range(1, len(edges) + 1)
               for s in combinations(range(len(edges)), size)]
    basic_supports = []
    for subset in subsets:
        result = full_column_solution(matrix, sorted(subset))
        if result is not None and all(x > 0 for x in result):
            basic_supports.append(subset)
    for subset in subsets:
        allowed = set()
        allowed.update(*(basic for basic in basic_supports if basic <= subset))
        if allowed != subset:
            continue
        incident = {v for i in subset for v in (edges[i].tail, edges[i].head)}
        joined = {next(iter(incident))}
        for _ in incident:
            for i in subset:
                a, b = edges[i].tail, edges[i].head
                if a in joined or b in joined:
                    joined.update((a, b))
        if joined == incident:
            return True
    return False


def check_lasso(rng):
    count = 0
    for _ in range(140):
        size, vertices, dimension = rng.randrange(8), rng.randrange(1, 5), rng.randrange(1, 4)
        edges = [Edge(rng.randrange(vertices), rng.randrange(vertices),
                      tuple(rng.randint(-3, 3) for _ in range(dimension))) for _ in range(size)]
        start = rng.randrange(vertices)
        found = find_lasso(edges, start)
        assert (found is not None) == brute_lasso(edges, start)
        if found is not None:
            path, multiplicities = found
            base = start
            for i in path:
                assert edges[i].tail == base
                base = edges[i].head
            expand(edges, realize(edges, multiplicities, base), base, multiplicities)
            assert all(sum(c * e.weight[j] for e, c in zip(edges, multiplicities)) == 0
                       for j in range(dimension))
            count += 1
    assert 0 < count < 140
    return count


def check_fixtures():
    zero = (Edge(0, 0, (0,)),)
    malformed_runs = (
        (), (Run((), 1),), (Run((0,), 0),), (Run((0,), -1),),
        (Run((0,), True),), (Run((0,), 1.0),), (Run((0,), Fraction(1, 2)),),
        (Run((-1,), 1),), (Run((1,), 1),), (Run((False,), 1),),
        (Run((0,), 1), Run((0.0,), 1)),
    )
    for runs in malformed_runs:
        try:
            index_period(zero, runs)
        except ValueError:
            pass
        else:
            raise AssertionError(f"accepted malformed runs {runs}")

    disconnected = (Edge(0, 0, (1, 0)), Edge(1, 1, (-1, 0)),
                    Edge(0, 1, (0, 1)), Edge(1, 0, (0, 1)))
    assert find_lasso(disconnected, 0) is None
    assert not brute_lasso(disconnected, 0)
    assert find_lasso((Edge(0, 1, (7,)), Edge(1, 1, (0,))), 0) == ((0,), (0, 1))
    assert find_lasso((Edge(1, 1, (0,)),), 0) is None

    n = 2**80
    edges = (Edge(0, 1, (0, 0)), Edge(1, 0, (1, 1)), Edge(0, 0, (-n, -n)))
    transient, counts = find_lasso(edges, 0)
    assert transient == () and counts == (n, n, 1)
    index = index_period(edges, realize(edges, counts, 0))
    assert len(index) == 5
    result = admissible_phases(index, (n,), ((0, 5*n//2),), ((-2, 1),), {1})
    assert result == (Progression(n//2 - 1, 2, n//4 + 1),)
    assert result == admissible_phases(
        index, (n,), ((0, 5*n//2),), ((-2, 1),), {1}, method="binary")
    assert envelope(index, n//2 - 1, (n,), ((-2, 1),)) == ((n//4, 5*n//2),)
    assert envelope(index, n - 1, (n,), ((-2, 1),)) == ((0, 2*n),)

    order_sensitive = (Edge(0, 0, (1,)), Edge(0, 0, (-1,)))
    blocked = index_period(order_sensitive, realize(order_sensitive, (n, n), 0))
    alternating = index_period(order_sensitive, (Run((0, 1), n),))
    assert admissible_phases(blocked, (0,), ((0, 1),)) == ()
    assert admissible_phases(alternating, (0,), ((0, 1),)) == (Progression(0, 2, n),)
    print(f"Huge witness: {2*n+1} events, {len(index)} records, {result[0].count} safe phases")


if __name__ == "__main__":
    rng = Random(972416)
    check_fixtures()
    print(f"Phase oracle: 180 schedules, 720 queries, {check_phases(rng)} partial phase sets")
    print(f"Feasibility oracle: 140 graphs, {check_lasso(rng)} feasible")
