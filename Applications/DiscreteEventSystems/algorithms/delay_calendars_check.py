"""Differential checks against exact enumeration of global scenarios."""

from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations, product
from math import comb
from random import Random
from time import perf_counter

from delay_calendars import Deadline, Dependency, Outcome, TimingProblem, analyze, example


def groups(problem: TimingProblem) -> tuple[str, ...]:
    return tuple(sorted({
        e.group for layer in problem.layers for e in layer if e.group is not None
    }))


def replay(problem: TimingProblem, selected: set[str] | frozenset[str]) -> Fraction | None:
    """Direct synchronous recurrence in the original layer and dependency order."""
    states = [list(map(lambda x: None if x is None else Fraction(x), problem.initial))]
    for layer in problem.layers:
        row = [None] * len(problem.initial)
        for edge in layer:
            incoming = states[-1][edge.tail]
            if incoming is None:
                continue
            value = incoming + Fraction(edge.nominal)
            if edge.group in selected:
                value += Fraction(edge.extra)
            prior = row[edge.head]
            if prior is None or value > prior:
                row[edge.head] = value
        states.append(row)
    excesses = []
    for d in problem.deadlines:
        arrival = states[d.layer][d.vertex]
        if arrival is not None:
            excesses.append(arrival - Fraction(d.due))
    return max(excesses, default=None)


def brute(problem: TimingProblem, budget: int):
    names = groups(problem)
    budget = min(budget, len(names))
    by_budget = [[] for _ in range(budget + 1)]
    restricted = {g: [[], []] for g in names}
    for used in range(budget + 1):
        for candidate in combinations(names, used):
            selected = set(candidate)
            value = replay(problem, selected)
            if value is not None:
                by_budget[used].append(value)
                for group in names:
                    restricted[group][group in selected].append(value)
    all_values = [max((x for vals in by_budget[:k + 1] for x in vals), default=None)
                  for k in range(budget + 1)]
    splits = {g: tuple(max(vals, default=None) for vals in pair)
              for g, pair in restricted.items()}
    return all_values, splits


def verify_witness(problem: TimingProblem, cap: int, outcome: Outcome,
                   restriction: tuple[str, bool] | None = None) -> None:
    w = outcome.witness()
    assert w.groups <= set(groups(problem))
    assert len(w.groups) <= cap
    if restriction is not None:
        assert (restriction[0] in w.groups) == restriction[1]
    current = w.release_vertex
    value = Fraction(problem.initial[current])
    for step, (layer, index) in enumerate(w.dependencies, 1):
        assert step == layer
        edge = problem.layers[layer - 1][index]
        assert current == edge.tail
        current = edge.head
        value += Fraction(edge.nominal)
        if edge.group in w.groups:
            value += Fraction(edge.extra)
    deadline = problem.deadlines[w.deadline_index]
    assert (len(w.dependencies), current) == (deadline.layer, deadline.vertex)
    assert value - Fraction(deadline.due) == outcome.excess
    assert replay(problem, w.groups) == outcome.excess


def same(problem: TimingProblem, cap: int) -> int:
    values, splits = brute(problem, cap)
    checked = 0
    for ordered in (False, True):
        report = analyze(problem, cap, cluster=ordered)
        assert len(report.best_by_budget) == len(values)
        for budget, (expected, actual) in enumerate(zip(values, report.best_by_budget)):
            assert (None if actual is None else actual.excess) == expected
            if actual is not None:
                verify_witness(problem, budget, actual)
            checked += 1
        assert report.avoided.keys() == report.required.keys() == splits.keys()
        for g, pair in splits.items():
            for chosen, (expected, actual) in enumerate(
                zip(pair, (report.avoided[g], report.required[g]))
            ):
                assert (None if actual is None else actual.excess) == expected
                if actual is not None:
                    verify_witness(problem, cap, actual, (g, bool(chosen)))
                checked += 1
    return checked


def random_problem(rng: Random) -> TimingProblem:
    n = rng.randrange(1, 6)
    horizon = rng.randrange(8)
    pool = [str(i) for i in range(rng.randrange(9))] + [None, None]
    layers = []
    for _ in range(horizon):
        edges = []
        for _ in range(rng.randrange(3 * n + 1)):
            group = rng.choice(pool)
            extra = Fraction(rng.randrange(7), rng.randrange(1, 5)) if group else 0
            edges.append(Dependency(
                rng.randrange(n), rng.randrange(n),
                Fraction(rng.randrange(-9, 13), rng.randrange(1, 5)), group, extra,
            ))
        layers.append(tuple(edges))
    deadlines = tuple(
        Deadline(rng.randrange(horizon + 1), rng.randrange(n),
                 Fraction(rng.randrange(-12, 22), rng.randrange(1, 5)))
        for _ in range(rng.randrange(8))
    )
    initial = tuple(None if rng.randrange(4) == 0 else Fraction(rng.randrange(-4, 7), 3)
                    for _ in range(n))
    return TimingProblem(initial, tuple(layers), deadlines)


def staggered(group_count: int) -> TimingProblem:
    """Three recurrent production events and overlapping three-occurrence calendars."""
    horizon = 2 * group_count + 4
    layers = [
        [Dependency(tail, head, 1 + (3 * t + tail + 2 * head) % 5)
         for tail in range(3) for head in range(3)]
        for t in range(horizon)
    ]
    for g in range(group_count):
        for repeat in range(3):
            t = 2 * g + (0, 2, 5)[repeat]
            station = (g + repeat) % 3
            layers[t].append(Dependency(
                station, (station + g) % 3,
                3 + g % 4, f"crew-{g}", 1 + (g + 2 * repeat) % 7,
            ))
    return TimingProblem(
        (0, 2, 1), tuple(map(tuple, layers)),
        (Deadline(horizon // 2, 0, 5 * (horizon // 2) + 1),
         Deadline(horizon, 2, 5 * horizon + 8)),
    )


def sat_reduction(clauses: list[tuple[int, int, int]], n: int):
    """Balanced parallel literal tracks, with globally reused occurrence labels."""
    labels = {sign: [] for v in range(1, n + 1) for sign in (v, -v)}
    for i, clause in enumerate(clauses):
        for j, lit in enumerate(clause):
            labels[lit].append(f"clause-{i}-{j}")

    layers = []
    budget = 0
    for v in range(1, n + 1):
        length = max(len(labels[v]), len(labels[-v]))
        budget += length
        for i in range(length):
            edges = []
            for track, literal in ((0, v), (1, -v)):
                group = labels[literal][i] if i < len(labels[literal]) else f"pad-{literal}-{i}"
                tail = 0 if i == 0 else track
                head = 0 if i == length - 1 else track
                edges.append(Dependency(tail, head, 0, group, 1))
            layers.append(tuple(edges))
    for i in range(len(clauses)):
        layers.append(tuple(Dependency(0, 0, 0, f"clause-{i}-{j}", 1) for j in range(3)))
    return TimingProblem((0, None), tuple(layers), (Deadline(len(layers), 0, len(layers)),)), budget


def run_checks() -> None:
    rng = Random(79017)
    cases = [
        (example(), 2),
        (example(), 0),
        # The best observation predates every disturbance, which may still be
        # required as a global scenario choice.
        (TimingProblem((3, None), (
            (Dependency(1, 1, 0, "after-observation", 5),),
            (Dependency(1, 1, 0, "after-observation", 5),),
        ), (Deadline(0, 0, 2),)), 1),
        # A dead end, parallel tied arcs, and a missing observation.
        (TimingProblem((0, None, None), (
            (Dependency(0, 1, 1, "a", 0), Dependency(0, 1, 1, "b", 0),
             Dependency(2, 0, 0, "c", 2)),
        ), (Deadline(1, 1, 0), Deadline(1, 2, -999))), 3),
        (staggered(11), 3),
    ]
    for _ in range(380):
        cases.append((random_problem(rng), rng.randrange(9)))
    comparisons = sum(same(problem, cap) for problem, cap in cases)
    for _ in range(80):
        n = 4
        clauses = [
            tuple(v if rng.randrange(2) else -v
                  for v in rng.sample(range(1, n + 1), 3))
            for _ in range(rng.randrange(1, 4))
        ]
        if _ % 9 == 0:
            clauses = [(1, 1, 1), (-1, -1, -1)]
        satisfiable = any(
            all(any(bits[abs(lit) - 1] == (lit > 0) for lit in clause) for clause in clauses)
            for bits in product((False, True), repeat=n)
        )
        problem, cap = sat_reduction(clauses, n)
        optimum = analyze(problem, cap).best_by_budget[-1]
        assert (optimum.excess == 0) == satisfiable
        verify_witness(problem, cap, optimum)

    large = staggered(240)
    report = analyze(large, 4)
    assert report.calendar_width == 3
    assert len(report.required) == 240
    for group in groups(large):
        assert max(report.avoided[group].excess, report.required[group].excess) == (
            report.best_by_budget[-1].excess
        )
    print(f"{len(cases)} differential cases, {comparisons} exact value checks across two "
          "arc orders, and 80 small SAT reductions passed.")
    print("The 240-group run returned all one-group results with calendar width 3.")


def benchmark() -> None:
    print("groups  layers  width  scenarios at most 4    scan (s)  enumerate (s)")
    for size in (6, 10, 14, 240):
        problem = staggered(size)
        started = perf_counter()
        report = analyze(problem, 4)
        scan_time = perf_counter() - started
        scenario_count = sum(comb(size, k) for k in range(5))
        reference_time = "skipped"
        if size <= 14:
            started = perf_counter()
            values, splits = brute(problem, 4)
            reference_time = f"{perf_counter() - started:.3f}"
            assert values[-1] == report.best_by_budget[-1].excess
            assert splits == {
                g: (report.avoided[g].excess, report.required[g].excess) for g in splits
            }
        print(f"{size:6}  {len(problem.layers):6}  {report.calendar_width:5}  "
              f"{scenario_count:19,}    {scan_time:8.3f}  {reference_time:>13}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--benchmark", action="store_true")
    args = parser.parse_args()
    if args.benchmark:
        benchmark()
    else:
        run_checks()
