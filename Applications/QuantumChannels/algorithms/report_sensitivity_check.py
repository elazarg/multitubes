#!/usr/bin/env python3
"""Exact density-matrix oracle and reproducible benchmarks for report_sensitivity."""

from fractions import Fraction as Q
from itertools import product
import json
from math import isqrt
from pathlib import Path
import random
from statistics import median
import sys
from time import perf_counter

from report_sensitivity import (
    Entry, Round, cheapest_basis, extend, integer_matrix, integer_vector,
    pivotal_contexts, read_model,
)


def identity(dimension):
    return tuple(tuple(Q(i == j) for j in range(dimension)) for i in range(dimension))


def transpose(matrix):
    return tuple(zip(*matrix))


def multiply(left, right):
    return tuple(tuple(sum(x * y for x, y in zip(row, col)) for col in zip(*right)) for row in left)


def oracle_survival(rounds, factors, suppressed, terminal_factors=None):
    dimension = len(factors[0])
    state = tuple(tuple(sum(v[i] * v[j] for v in factors) for j in range(dimension))
                  for i in range(dimension))
    for index, stage in enumerate(rounds):
        matching = stage.cont + stage.hit if index in suppressed else stage.cont
        images = [multiply(multiply(k, state), transpose(k)) for k in matching]
        state = tuple(tuple(sum(m[i][j] for m in images) for j in range(dimension))
                      for i in range(dimension))
    if terminal_factors is None:
        return sum(state[i][i] for i in range(dimension))
    return sum(v[i] * state[i][j] * v[j] for v in terminal_factors
               for i in range(dimension) for j in range(dimension))


def oracle(rounds, factors, observed, terminal_factors=None):
    n = len(rounds)
    masses = {}
    for mask in range(1 << n):
        selected = {i for i in range(n) if mask & (1 << i)}
        masses[mask] = (oracle_survival(rounds, factors, selected, terminal_factors),
                        sum(rounds[i].cost for i in selected))
    if terminal_factors is None:
        assert masses[(1 << n) - 1][0] == 1
    best = [None] * n
    for index in range(n):
        bit = 1 << index
        for mask in range(1 << n):
            if mask & bit or masses[mask | bit][0] == masses[mask][0]:
                continue
            assert masses[mask | bit][0] > masses[mask][0]
            cost = masses[mask][1]
            if best[index] is None or cost < best[index]:
                best[index] = cost
        context = observed[index]
        assert (context.cost if context else None) == best[index], (index, observed, best)
        if context:
            selected = context.suppressed()
            assert tuple(sorted(set(selected))) == selected and index not in selected
            mask = sum(1 << i for i in selected)
            assert context.cost == masses[mask][1]
            assert masses[mask | bit][0] > masses[mask][0]
    return best


def rotation(dimension, rng, count):
    matrix = [list(row) for row in identity(dimension)]
    for _ in range(count):
        i, j = rng.sample(range(dimension), 2)
        cos, sin = rng.choice([(Q(3, 5), Q(4, 5)), (Q(5, 13), Q(12, 13)), (0, 1)])
        a, b = matrix[i], matrix[j]
        matrix[i] = [cos * x + sin * y for x, y in zip(a, b)]
        matrix[j] = [-sin * x + cos * y for x, y in zip(a, b)]
    return tuple(tuple(row) for row in matrix)


def model_round(cost, before, after, hit_cols, cont_cols):
    def family(groups):
        return tuple(multiply(tuple(tuple(x if j in group else 0 for j, x in enumerate(row))
                                    for row in after), transpose(before))
                     for group in groups if group)

    return {"cost": cost, "hit": family(hit_cols), "continue": family(cont_cols)}


def random_model(rng):
    dimension = rng.randrange(2, 5)
    n = rng.randrange(0, 7)
    frame = identity(dimension)
    factors = [(Q(3, 5), Q(4, 5)) + (Q(0),) * (dimension - 2)]
    if rng.randrange(2):
        factors = [(Q(3, 5),) + (Q(0),) * (dimension - 1),
                   (Q(0), Q(4, 5)) + (Q(0),) * (dimension - 2)]
    data = {"state_factors": factors, "rounds": []}
    for _ in range(n):
        frame_next = rotation(dimension, rng, rng.randrange(dimension + 1))
        after = multiply(frame_next, rotation(dimension, rng, rng.randrange(2)))
        groups = [set() for _ in range(4)]
        for col in range(dimension):
            groups[rng.randrange(4)].add(col)
        data["rounds"].append(model_round(Q(rng.randrange(7), rng.randrange(1, 6)),
                                          frame, after, groups[:2], groups[2:]))
        frame = frame_next
    return read_model(data)


def groups_model(n, width):
    """Any sequence of block flags is possible, in changing Hilbert bases."""
    d = 4
    rng = random.Random(81)
    frame = tuple(tuple(Q(x, 2) for x in row) for row in (
        (1, 1, 1, 1), (1, -1, 1, -1), (1, 1, -1, -1), (1, -1, -1, 1),
    ))
    mix = tuple(tuple(map(Q, row)) for row in (
        (Q(3, 5), 0, Q(4, 5), 0), (0, Q(3, 5), 0, Q(4, 5)),
        (Q(-4, 5), 0, Q(3, 5), 0), (0, Q(-4, 5), 0, Q(3, 5)),
    ))
    start = multiply(frame, ((Q(1, 2),),) * d)
    data = {"state_factors": [tuple(row[0] for row in start)], "rounds": []}
    costs = [Q(rng.randrange(1, 30), rng.randrange(1, 7)) for _ in range(n)]
    for i, cost in enumerate(costs):
        signs = [rng.choice((-1, 1)) for _ in range(d)]
        orders = rng.sample(range(d), d)
        next_frame = tuple(tuple(signs[j] * row[orders[j]] for j in range(d)) for row in frame)
        after = multiply(next_frame, mix) if (i + 1) % width == 0 else next_frame
        data["rounds"].append(model_round(cost, frame, after, [{0, 1}], [{2, 3}]))
        frame = next_frame
    expected = []
    for i, cost in enumerate(costs):
        start = (i // width) * width
        expected.append(sum(costs[start:start + width]) - cost)
    return (*read_model(data), expected)


def clique_model(vertices, edges, designated=False):
    # Pad to square dimension so all edge amplitudes are the same rational number.
    root = isqrt(len(edges) - 1) + 1
    d = root * root
    frame = identity(d)
    data = {"state_factors": [(Q(1, root),) * d], "rounds": []}
    for vertex in range(vertices):
        hit = {j for j, edge in enumerate(edges) if vertex in edge}
        data["rounds"].append(model_round(1, frame, frame, [hit], [set(range(d)) - hit]))
    if designated:
        hit = set(range(len(edges)))
        data["rounds"].append(model_round(1, frame, frame, [hit], [set(range(d)) - hit]))
    return read_model(data)


def check():
    with Path(__file__).with_name("paired-hits.json").open(encoding="utf-8") as stream:
        rounds, factors = read_model(json.load(stream))
    assert oracle(rounds, factors, pivotal_contexts(rounds, factors)) == [5, 3]
    assert [oracle_survival(rounds, factors, selected)
            for selected in (set(), {0}, {1}, {0, 1})] == [Q(16, 25)] * 3 + [1]
    terminal = ((Q(1), Q(0)),)
    observed = pivotal_contexts(rounds, factors, terminal_factors=terminal)
    assert oracle(rounds, factors, observed, terminal) == [None, None]
    grouped, state, expected = groups_model(6, 3)
    assert oracle(grouped, state, pivotal_contexts(grouped, state)) == expected

    rng = random.Random(975316)
    counts = {"rounds": 0, "subset-probabilities": 0, "impossible": 0,
              "positive": 0, "zero-cost": 0}
    for _ in range(100):
        rounds, factors = random_model(rng)
        observed = pivotal_contexts(rounds, factors)
        best = oracle(rounds, factors, observed)
        counts["rounds"] += len(rounds)
        counts["subset-probabilities"] += 1 << len(rounds)
        counts["impossible"] += best.count(None)
        counts["positive"] += sum(cost is not None and cost > 0 for cost in best)
        counts["zero-cost"] += best.count(0)

    for edges, has_triangle in (
        ([(0, 1), (0, 2), (1, 2), (2, 3), (2, 4), (3, 4)], True),
        ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)], False),
    ):
        rounds, factors = clique_model(5, edges)
        extended, _ = clique_model(5, edges, designated=True)
        baseline = oracle_survival(rounds, factors, set())
        dimension = len(factors[0])
        threshold = Q(3, dimension)
        reached = False
        designated_reached = False
        for bits in product((False, True), repeat=len(rounds)):
            suppressed = {i for i, bit in enumerate(bits) if bit}
            loss = oracle_survival(rounds, factors, suppressed) - baseline
            assert loss == Q(sum(u in suppressed and v in suppressed for u, v in edges),
                             dimension)
            reached |= len(suppressed) <= 3 and loss >= threshold
            before = oracle_survival(extended, factors, suppressed)
            after = oracle_survival(extended, factors, suppressed | {5})
            assert after - before == loss
            designated_reached |= len(suppressed) <= 3 and after - before >= threshold
        assert reached == designated_reached == has_triangle
    print(counts)


def forced_reruns(rounds, factors):
    """Optimal weighted support DP applied separately after each forced hit."""
    d = len(factors[0])
    stages = tuple(Round(
        stage.cost,
        tuple(integer_matrix(matrix) for matrix in stage.hit),
        tuple(integer_matrix(matrix) for matrix in stage.cont),
    ) for stage in rounds)
    prefix = cheapest_basis((Entry(Q(0), integer_vector(v)) for v in factors), d)
    output = []
    for i, stage in enumerate(stages):
        current = extend(prefix, Round(0, stage.hit, ()), i, d)
        for j in range(i + 1, len(stages)):
            if not current:
                break
            current = extend(current, stages[j], j, d)
        output.append(current[0].cost if current else None)
        prefix = extend(prefix, stage, i, d)
    return output


def bench():
    print("rounds,window,shared_s,reruns_s")
    for n in (64, 128, 256):
        rounds, factors, expected = groups_model(n, n // 4)
        times = []
        for algorithm in (pivotal_contexts, forced_reruns):
            elapsed = []
            for _ in range(3):
                start = perf_counter()
                actual = algorithm(rounds, factors)
                elapsed.append(perf_counter() - start)
                if algorithm is pivotal_contexts:
                    assert all(len(context.suppressed()) == n // 4 - 1 for context in actual)
                    actual = [context.cost for context in actual]
                assert actual == expected
            times.append(median(elapsed))
        print(f"{n},{n // 4},{times[0]:.6f},{times[1]:.6f}")
    rounds, factors, expected = groups_model(1024, 8)
    start = perf_counter()
    actual = pivotal_contexts(rounds, factors)
    elapsed = perf_counter() - start
    assert [context.cost for context in actual] == expected
    assert all(len(context.suppressed()) == 7 for context in actual)
    print(f"1024,8,{elapsed:.6f},")


if __name__ == "__main__":
    if sys.argv[1:] == ["--bench"]:
        bench()
    else:
        check()
