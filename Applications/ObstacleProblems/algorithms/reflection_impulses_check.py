"""Independent exact replays and a reproducible benchmark for reflection_impulses."""

import argparse
import csv
from fractions import Fraction as F
from itertools import product
from random import Random
from time import perf_counter

from reflection_impulses import ImpulseIndex, Response, Stage


def coefficients(stages):
    return [tuple(map(F, (s.retention, s.shift, s.lo, s.hi, s.lower_weight, s.upper_weight)))
            for s in stages]


def trajectories(stages, initial, intervention=None):
    state, shortage, overflow = F(initial), F(0), F(0)
    for i, (a, b, lo, hi, low_price, high_price) in enumerate(stages):
        raw = state * a + b
        if intervention is not None and i == intervention[0]:
            raw += intervention[1]
        if raw < lo:
            shortage += low_price * (lo - raw)
            state = lo
        elif raw > hi:
            overflow += high_price * (raw - hi)
            state = hi
        else:
            state = raw
        yield Response(shortage, overflow, state)


def check_case(stages, initial, amplitudes):
    index = ImpulseIndex(stages, initial)
    stages = coefficients(stages)
    base = list(trajectories(stages, initial))
    checks = 0
    for amplitude in amplitudes:
        batch = index.all_stages(amplitude)
        for start in range(len(stages)):
            perturbed = trajectories(stages, initial, (start, amplitude))
            for deadline, (baseline, altered) in enumerate(zip(base, perturbed)):
                if deadline >= start:
                    expected = Response(*(new - old for old, new in zip(baseline, altered)))
                    actual = index.query(start, amplitude, deadline)
                    assert actual == expected, (stages, initial, start, amplitude, deadline, actual,
                                                expected)
                    checks += 1
            assert batch[start] == expected, (stages, initial, start, amplitude, batch[start],
                                              expected)
            checks += 1
    return checks


def check_meter(path):
    stages = []
    with open(path, newline='') as data:
        for row in csv.DictReader(data):
            increment = F(row['pv_kwh']) - F(row['load_kwh'])
            stages.append(Stage(1, increment, 0, 2, lower_weight=2, upper_weight=1))
    return check_case(stages, 1, [F(-2), F(-1, 2), F(1, 2), F(2)])


def check():
    variants = [Stage(1, b, 0, 1) for b in (-2, -1, 0, 1, 2)] + [
        Stage(1, 1, 0, 0), Stage(1, -1, 0, 0), Stage(0, 0, -1, 2),
        Stage(0, 2, -1, 0), Stage(F(1, 2), F(2, 3), 0, 1, 2, 0),
        Stage(2, F(-1, 2), 0, 2, 0, F(2, 3)), Stage(1, 0, 0, 2, -1, -2),
    ]
    amplitudes = [F(-2), F(-1), F(-1, 2), F(0), F(1, 2), F(1), F(2)]
    exhaustive = sum(check_case(stages, initial, amplitudes)
                     for stages in product(variants, repeat=3) for initial in (0, F(1, 2)))
    print(f'{exhaustive:,} exhaustive exact comparisons', flush=True)
    rng = Random(3254)
    random = 0
    for _ in range(200):
        stages = []
        for _ in range(rng.randrange(1, 31)):
            lo = F(rng.randrange(-8, 9), 3)
            hi = lo + F(rng.randrange(7), rng.randrange(1, 5))
            a = rng.choice([0, 1, 2, F(1, 3), F(3, 2), F(7, 8)])
            shift = F(rng.randrange(-13, 14), rng.randrange(1, 5))
            weights = [F(rng.randrange(-3, 4), rng.randrange(1, 5)) for _ in range(2)]
            stages.append(Stage(a, shift, lo, hi, *weights))
        random += check_case(stages, F(rng.randrange(-8, 9), 2), amplitudes)
    print(f'{random:,} randomized exact comparisons', flush=True)

    # Constant bounds and retention. Each start has a distinct upper slope on
    # each adjacent interval in its list of future upper-contact levels.
    n = 50
    base = [F(0)] + [1 - F(1, 3 * 6 ** j) for j in range(n)]
    stages = [Stage(F(1, 2), base[j + 1] - base[j] / 2, 0, 1) for j in range(n)]
    index = ImpulseIndex(stages, 0)
    distinct_knots = set()
    pieces = 0
    for i in range(n):
        knots = [F(0)] + [F(1, 2 ** i * 3 ** (j + 1)) for j in reversed(range(i, n))]
        distinct_knots.update(knots[1:])
        knots.append(2 * knots[-1])
        slopes = []
        for left, right in zip(knots, knots[1:]):
            fleft = index.query(i, left).upper
            fright = index.query(i, right).upper
            slopes.append((fright - fleft) / (right - left))
        assert slopes == [0] + [F(1, 2 ** (j - i)) for j in reversed(range(i, n))]
        pieces += len(slopes) - 1
    assert len(distinct_knots) == pieces == n * (n + 1) // 2
    assert ImpulseIndex([], 0).all_stages(1) == []
    print(f'{pieces:,} distinct knots across the {n} quadratic-witness curves')


def early_stop_replay(steps, start, amplitude):
    difference = amplitude
    low_change, high_change = 0, 0
    for i in range(start, len(steps)):
        a, base_raw, lo, hi, low_price, high_price, base_state, l0, u0 = steps[i]
        raw = base_raw + (difference if i == start else a * difference)
        state = min(hi, max(lo, raw))
        low_change += low_price * (max(0, lo - raw) - l0)
        high_change += high_price * (max(0, raw - hi) - u0)
        difference = state - base_state
        if not difference:
            break
    return Response(low_change, high_change, difference)


def replay_data(stages, initial):
    steps, state = [], initial
    for step in stages:
        raw = step.retention * state + step.shift
        state = min(step.hi, max(step.lo, raw))
        lower, upper = max(0, step.lo - raw), max(0, raw - step.hi)
        steps.append((step.retention, raw, step.lo, step.hi, step.lower_weight,
                      step.upper_weight, state, lower, upper))
    return steps


def benchmark(n):
    rng = Random(2901)
    traces = {
        'late contact': [Stage(1, 2 + i % 2, 0, 2 * n + n // 2, 1 + i % 9, 1 + i % 7)
                         for i in range(n)],
        'frequent contacts': [Stage(1, rng.randrange(-5, 6), 0, 8, 1, 1 + i % 7)
                              for i in range(n)],
    }
    for name, stages in traces.items():
        start = perf_counter()
        index = ImpulseIndex(stages, 0)
        build = perf_counter() - start
        start = perf_counter()
        batch = index.all_stages(7)
        sweep = perf_counter() - start
        start = perf_counter()
        online = [index.query(i, 7) for i in range(n)]
        online_time = perf_counter() - start
        start = perf_counter()
        steps = replay_data(stages, 0)
        replay = [early_stop_replay(steps, i, 7) for i in range(n)]
        replay_time = perf_counter() - start
        assert batch == online == replay
        print(f'{name}, n={n:,}, seconds: build {build:.4f}, batch {sweep:.4f}, '
              f'online {online_time:.4f}, replay {replay_time:.4f}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--benchmark', type=int, metavar='N')
    parser.add_argument('--meter', help='optional CSV with pv_kwh,load_kwh columns')
    args = parser.parse_args()
    if args.benchmark is not None:
        benchmark(args.benchmark)
    else:
        check()
        if args.meter:
            print(f'{check_meter(args.meter):,} metered comparisons')
