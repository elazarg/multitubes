"""Check both indexes against explicit sets and measure the interval-state lift."""

from bisect import bisect_right
from collections import deque
from random import Random
from statistics import median
from time import perf_counter

from interval_routes import FormulaEdge, FormulaRoutes, GaugeError, TableEdge, TableRoutes


def is_goal(config, target, band):
    vertex, states = config
    return vertex == target and all(band[0] <= state <= band[1] for state in states)


def advance(config, table_edge, rows):
    vertex, states = config
    if vertex != table_edge.source:
        return None
    local = [state - table_edge.first for state in states]
    if any(index < 0 or index >= len(rows) for index in local):
        return None
    return table_edge.target, frozenset().union(*(rows[index] for index in local))


def possible(initial, edges, rows, target, band):
    """Breadth-first search over concrete state subsets, retaining holes."""
    visited = {initial}
    queue = deque([initial])
    while queue:
        config = queue.popleft()
        if is_goal(config, target, band):
            return True
        for edge, edge_rows in zip(edges, rows):
            following = advance(config, edge, edge_rows)
            if following is not None and following not in visited:
                visited.add(following)
                queue.append(following)
    return False


def check_witness(config, edges, rows, target, band, route):
    for edge_id in route:
        config = advance(config, edges[edge_id], rows[edge_id])
        assert config is not None, (edges, rows, route)
    assert is_goal(config, target, band), (edges, rows, route, config)


def as_formula(edge):
    return FormulaEdge(
        edge.name, edge.source, edge.target, edge.first,
        edge.first + len(edge.lower) - 1,
        lambda value: edge.lower[value - edge.first],
        lambda value: edge.upper[value - edge.first],
    )


def compare_every_interval(sizes, edges, rows, target, band, *, dag=False):
    tables = TableRoutes(sizes, edges, target, band)
    if dag:
        formulas = FormulaRoutes(sizes, tuple(map(as_formula, edges)), target, band)
    solvers = [tables, formulas] if dag else [tables]
    count = 0
    for vertex, size in enumerate(sizes):
        for first in range(size):
            for last in range(first, size):
                config = vertex, frozenset(range(first, last + 1))
                expected = possible(config, edges, rows, target, band)
                assert tables.accepts(vertex, first, last) == expected
                for index in solvers:
                    route = index.route(vertex, first, last)
                    assert (route is not None) == expected, (sizes, edges, target, band, config)
                    if route is not None:
                        check_witness(config, edges, rows, target, band, route)
                count += 1
    for edge in edges:
        for index, upper in enumerate(edge.upper, edge.first):
            upper_source = tables.gauge[tables.offsets[edge.source] + index]
            upper_target = tables.gauge[tables.offsets[edge.target] + upper]
            assert upper_source <= upper_target
    return count


def random_case(rng, dag):
    vertices = rng.randint(1, 5)
    sizes = tuple(rng.randint(1, 8) for _ in range(vertices))
    keys = [sorted(rng.sample(range(12), size)) for size in sizes]
    edges, rows = [], []
    for _ in range(rng.randrange(2 * vertices * vertices + 1)):
        source, target = rng.randrange(vertices), rng.randrange(vertices)
        if dag and source >= target:
            continue
        usable = sizes[source] if dag else bisect_right(keys[source], keys[target][-1])
        if not usable:
            continue
        first = rng.randrange(usable)
        last = rng.randrange(first, usable)
        highs = sorted(rng.randrange(sizes[target]) for _ in range(first, last + 1))
        lows = sorted(rng.randrange(sizes[target]) for _ in range(first, last + 1))
        if not dag:
            highs = [
                max(high, bisect_right(keys[target], keys[source][value] - 1))
                for value, high in enumerate(highs, first)
            ]
        lows = [min(low, high) for low, high in zip(lows, highs)]
        edge_rows = [
            frozenset({low, high} | {state for state in range(low + 1, high) if rng.randrange(2)})
            for low, high in zip(lows, highs)
        ]
        edges.append(TableEdge(str(len(edges)), source, target, first, tuple(lows), tuple(highs)))
        rows.append(tuple(edge_rows))
    goal = rng.randrange(vertices)
    first = rng.randrange(sizes[goal])
    last = rng.randrange(first, sizes[goal])
    return compare_every_interval(sizes, edges, rows, goal, (first, last), dag=dag)


def fixtures():
    edges = (
        TableEdge("standardize", 0, 0, 0, (1, 1, 3, 3), (3, 3, 3, 3)),
        TableEdge("promote", 0, 0, 0, (0, 3, 3, 3), (3, 3, 3, 3)),
        TableEdge("archive", 0, 1, 3, (1,), (1,)),
    )
    rows = ((frozenset({1, 3}), frozenset({1, 3}), frozenset({3}), frozenset({3})),
            (frozenset({0, 3}), frozenset({3}), frozenset({3}), frozenset({3})),
            (frozenset({1}),))
    count = compare_every_interval((4, 2), edges, rows, 1, (1, 1))
    index = TableRoutes((4, 2), edges, 1, (1, 1))
    assert index.route(0, 0, 3) == [0, 1, 2]
    for deleted in range(3):
        kept = [edge for edge_id, edge in enumerate(edges) if edge_id != deleted]
        assert TableRoutes((4, 2), kept, 1, (1, 1)).route(0, 0, 3) is None

    # The two singleton witnesses use different first edges.
    edges = (
        TableEdge("left", 0, 1, 0, (1, 2), (1, 2)),
        TableEdge("right", 0, 1, 0, (0, 1), (0, 1)),
    )
    rows = tuple(tuple(frozenset({low}) for low in edge.lower) for edge in edges)
    count += compare_every_interval((2, 3), edges, rows, 1, (1, 1), dag=True)
    index = TableRoutes((2, 3), edges, 1, (1, 1))
    assert index.route(0, 0, 0) == [0]
    assert index.route(0, 1, 1) == [1]
    assert index.route(0, 0, 1) is None

    # One possible execution blocks, although the ordinary relational image has a goal outcome.
    edges = (
        TableEdge("branch", 0, 1, 0, (0,), (2,)),
        TableEdge("narrow guard", 1, 2, 0, (0,), (0,)),
    )
    rows = ((frozenset({0, 2}),), (frozenset({0}),))
    count += compare_every_interval((1, 3, 1), edges, rows, 2, (0, 0), dag=True)
    assert TableRoutes((1, 3, 1), edges, 2, (0, 0)).route(0, 0, 0) is None

    # This instance has a solution, but its upward gauge is impossible.
    reset_down = TableEdge("downward reset", 0, 0, 0, (0, 0), (0, 0))
    try:
        TableRoutes((2,), [reset_down], 0, (0, 0))
    except GaugeError:
        assert possible((0, frozenset({0, 1})), (reset_down,),
                        ((frozenset({0}), frozenset({0})),), 0, (0, 0))
    else:
        raise AssertionError("the downward reset should fail the upward gauge test")

    # The compact frontier stores two disjoint bands across a trillion states.
    size = 10**12
    billion, million = 10**9, 10**6
    edges = (
        FormulaEdge("coarse", 0, 1, 0, size - 1, lambda x: x // billion, lambda x: x // billion),
        FormulaEdge("direct", 0, 2, 10 * billion, size - 1,
                    lambda x: (x - 10 * billion) // million,
                    lambda x: (x - 10 * billion) // million),
        FormulaEdge("accept", 1, 2, 0, 999, lambda x: x, lambda x: x),
    )
    compact = FormulaRoutes((size, 1000, size // million), edges, 2, (2, 2))
    a, b = 2 * billion, 3 * billion - 1
    c, d = 10 * billion + 2 * million, 10 * billion + 3 * million - 1
    assert [(item.first, item.last) for item in compact.frontier[0]] == [(a, b), (c, d)]
    assert compact.route(0, a, b) == [0, 2] and compact.route(0, c, d) == [1]
    assert compact.route(0, a, b + 1) is None and compact.route(0, a, d) is None

    size = 12_000
    advance_one = tuple(min(state + 1, size - 1) for state in range(size))
    edge = TableEdge("promote", 0, 0, 0, advance_one, advance_one)
    index = TableRoutes((size,), [edge], 0, (size - 1, size - 1))
    assert all(high == size - 1 for high in index.ceiling)
    assert index.route(0, 0, size - 1) == [0] * (size - 1)
    return count


def explicit_interval_lift(advance_one):
    size = len(advance_one)
    incoming = {}
    for first in range(size):
        for last in range(first, size):
            finish = advance_one[first], advance_one[last]
            incoming.setdefault(finish, []).append((first, last))
    stop = (size - 1, size - 1)
    settled = {stop}
    queue = deque([stop])
    while queue:
        item = queue.popleft()
        for before in incoming.get(item, ()):
            if before not in settled:
                settled.add(before)
                queue.append(before)
    return len(settled)


def benchmark():
    print("grades,frontier_rows,full_lift_rows,frontier_ms,full_lift_ms")
    for size in (128, 256, 512, 1024):
        promote = tuple(min(state + 1, size - 1) for state in range(size))
        edge = TableEdge("promote", 0, 0, 0, promote, promote)
        table_time, lift_time = [], []
        for _ in range(3):
            start = perf_counter()
            index = TableRoutes((size,), [edge], 0, (size - 1, size - 1))
            middle = perf_counter()
            count = explicit_interval_lift(promote)
            end = perf_counter()
            assert len(index.ceiling) == size and count == size * (size + 1) // 2
            table_time.append(middle - start)
            lift_time.append(end - middle)
        print(f"{size},{len(index.ceiling)},{count},{1e3 * median(table_time):.3f},"
              f"{1e3 * median(lift_time):.3f}")


if __name__ == "__main__":
    import sys

    count = fixtures()
    rng = Random(880176)
    count += sum(random_case(rng, bool(case % 2)) for case in range(1000))
    print(f"Passed 1000 random graphs and fixed fixtures, {count} concrete interval comparisons.")
    if "--benchmark" in sys.argv[1:]:
        benchmark()
