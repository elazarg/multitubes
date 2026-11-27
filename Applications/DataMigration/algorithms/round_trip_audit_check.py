"""Independent explicit reachability checks and synthetic audits."""

import argparse
from collections import deque
from itertools import product
from random import Random
from time import perf_counter

from round_trip_audit import RoundTripAudit, audit_flat_bases


def replay(edges, start, route):
    v, point = start
    for edge in route:
        source, target, image = edges[edge]
        assert v == source
        v, point = target, image[point]
    return v, point


def outgoing(sizes, edges):
    graph = [[] for _ in sizes]
    for edge, (u, v, image) in enumerate(edges):
        graph[u].append((v, image, edge))
    return graph


def reach(start, graph):
    seen = {start}
    queue = deque([start])
    while queue:
        v, point = queue.popleft()
        for u, image, _ in graph[v]:
            other = (u, image[point])
            if other not in seen:
                seen.add(other)
                queue.append(other)
    return seen


def explicit_stable(sizes, edges):
    """Independent BFS per record, stopping at its first failure."""
    graph = outgoing(sizes, edges)

    def is_stable(start):
        seen = {start}
        queue = deque([start])
        while queue:
            v, point = queue.popleft()
            for u, image, _ in graph[v]:
                other = (u, image[point])
                if other in seen:
                    continue
                if u == start[0]:
                    return False
                seen.add(other)
                queue.append(other)
        return True

    return tuple(tuple(is_stable((v, p)) for p in range(size))
                 for v, size in enumerate(sizes))


def schema_reach(sizes, edges, start):
    graph = outgoing(sizes, edges)
    seen = {start}
    queue = deque([start])
    while queue:
        for target, _, _ in graph[queue.popleft()]:
            if target not in seen:
                seen.add(target)
                queue.append(target)
    return seen


def check(sizes, edges):
    audit = RoundTripAudit(sizes, edges)
    statuses = explicit_stable(sizes, edges)
    assert audit.statuses() == statuses
    flats = tuple(all(stable) for stable in statuses)
    assert audit.flat_bases() == flats
    graph = outgoing(sizes, edges)
    component_count = len(sizes)
    lifted_reach = {}
    schemas = tuple(schema_reach(sizes, edges, v) for v in range(component_count))
    if component_count and all(len(row) == component_count for row in schemas):
        flags, failure = audit_flat_bases(
            sizes, [(u, v) for u, v, _ in edges], lambda e, p: edges[e][2][p])
        assert flags == flats
        if failure is None:
            assert any(flats)
        else:
            v, p, route = failure
            assert not any(flats) and sizes[v] == min(sizes)
            u, q = replay(edges, (v, p), route)
            assert u == v and q != p
            assert any(u == v and q != p for u, q in reach((v, p), graph))

    for v, size in enumerate(sizes):
        for p in range(size):
            state = (v, p)
            lifted_reach[state] = reach(state, graph)
            route = audit.counterexample(v, p)
            if statuses[v][p]:
                assert route is None
            else:
                assert route
                u, q = replay(edges, state, route)
                assert u == v and q != p

    for r in range(component_count):
        registry = audit.registry(r)
        assert registry.safe_keys == tuple(p for p in range(sizes[r]) if statuses[r][p])
        for (v, p), reachable in lifted_reach.items():
            if r not in schemas[v] or v not in schemas[r]:
                continue
            expected = {q for u, q in reachable if u == r}
            result = registry.return_keys(v, p)
            assert len(set(result)) == len(result) == min(2, len(expected))
            assert set(result) <= expected
            witnesses = registry.return_witnesses(v, p)
            assert tuple(key for key, _ in witnesses) == result
            for key, route in witnesses:
                assert replay(edges, (v, p), route) == (r, key)
            if len(expected) != 1:
                try:
                    registry.normalize(v, p, v)
                except ValueError:
                    continue
                raise AssertionError("accepted ambiguous return")
            key, = result
            assert registry.normalize(v, p, r) == key
            for u, q in reachable:
                if r in schemas[u]:
                    assert registry.return_keys(u, q) == (key,)
                    rep = registry.normalize(v, p, u)
                    assert (u, rep) in lifted_reach[(r, key)]
                    assert registry.normalize(u, q, u) == rep
                    assert registry.normalize(u, rep, u) == rep
    return audit


def fixture():
    # Registry keys 0, 1, 2. Key 0 is stable with two reachable workspace
    # aliases. Key 2 stays a stable identity through every route.
    sizes = (3, 5)
    edges = (
        (0, 1, (0, 2, 3)),
        (0, 1, (1, 2, 3)),
        (1, 0, (0, 0, 0, 2, 1)),
        (1, 0, (0, 0, 0, 2, 2)),
    )
    audit = check(sizes, edges)
    registry = audit.registry(0)
    assert audit.statuses() == ((True, False, True), (False, False, False, True, False))
    assert registry.return_keys(1, 0) == registry.return_keys(1, 1) == (0,)
    assert set(registry.return_keys(1, 4)) == {1, 2}
    assert registry.normalize(1, 0, 1) == registry.normalize(1, 1, 1) == 0

    # Fully flat registry, two raw transports to one workspace, noninvertible return.
    audit = check((2, 5), (
        (0, 1, (0, 1)),
        (0, 1, (2, 1)),
        (1, 0, (0, 1, 0, 0, 1)),
        (1, 0, (0, 1, 0, 1, 1)),
    ))
    assert audit.flat_bases() == (True, False)
    assert audit.registry(0).return_keys(1, 4) == (1,)  # stable name for an unreachable alias
    assert set(audit.registry(0).return_keys(1, 3)) == {0, 1}


def verify():
    fixture()
    check((), ())
    check((0, 0), ((0, 1, ()), (1, 0, ())))
    check((1, 0), ((1, 0, ()),))
    count = 5
    maps = tuple(product(range(2), repeat=2))
    for a, b, c, d in product(maps, repeat=4):
        check((2, 2), ((0, 1, a), (1, 0, b), (0, 0, c), (0, 1, d)))
        count += 1

    rng = Random(784)
    for _ in range(600):
        n = rng.randrange(1, 8)
        sizes = tuple(rng.randrange(1, 6) for _ in range(n))
        endpoints = [(rng.randrange(n), rng.randrange(n))
                     for _ in range(rng.randrange(4 * n + 1))]
        if rng.randrange(2):
            endpoints.extend((u, (u + 1) % n) for u in range(n))
        edges = tuple((u, v, tuple(rng.randrange(sizes[v]) for _ in range(sizes[u])))
                      for u, v in endpoints)
        check(sizes, edges)
        count += 1
    print(f"Checked {count} networks against explicit per-record directed reachability.")


def benchmark():
    print("All-record audit, two transitions per schema, 16 fully flat record lanes")
    for n in (64, 128, 256):
        sizes = (16,) * n
        identity = tuple(range(16))
        edges = tuple((u, (u + step) % n, identity)
                      for u in range(n) for step in (1, -1))
        t0 = perf_counter()
        fast = RoundTripAudit(sizes, edges).statuses()
        t1 = perf_counter()
        slow = explicit_stable(sizes, edges)
        t2 = perf_counter()
        assert fast == slow
        print(f"  {n:4} schema types: SCC {t1 - t0:.4f} s, per-record BFS {t2 - t1:.4f} s")

    print("Whole-base audit for one 2-key registry and 24 wide workspaces")
    for width in (8, 256, 4096):
        sizes = (2,) + (width,) * 24
        entries = (0, 1) * (width // 2)
        edges = tuple(arc for v in range(1, len(sizes))
                      for arc in ((0, v, (0, 1)), (0, v, (2, 3)), (v, 0, entries)))
        reads = 0

        def evaluate(edge, point):
            nonlocal reads
            reads += 1
            return edges[edge][2][point]

        t0 = perf_counter()
        flags, failure = audit_flat_bases(sizes, [(u, v) for u, v, _ in edges], evaluate)
        t1 = perf_counter()
        full = RoundTripAudit(sizes, edges).flat_bases()
        t2 = perf_counter()
        assert flags == full and failure is None
        print(f"  width {width:4}: lazy {reads:7} probes, {t1 - t0:.4f} s. "
              f"Full audit {sum(len(row) for _, _, row in edges):7} entries, {t2 - t1:.4f} s.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--benchmark", action="store_true")
    args = parser.parse_args()
    verify()
    if args.benchmark:
        benchmark()
