#!/usr/bin/env python3
"""Compare the range index against direct covariance recurrence and scalar inverses."""

from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path
from random import Random
from subprocess import run
from sys import argv, executable
from time import perf_counter

from riccati_deadlines import Boundary, Cut, DeadlineIndex


NO = Boundary.IMPOSSIBLE
ALL = Boundary.UNBOUNDED


def replay(steps, profile, left, right, initial, cap):
    current = F(initial)
    values = []
    for time in range(left + 1, right + 1):
        gain, noise, observation = steps[time - 1]
        prediction = gain * current + noise
        if observation is None:
            current = prediction
        elif observation == 0:
            current = F(0)
        else:
            current = prediction * observation / (prediction + observation)
        values.append(current / profile[time])
    peak = max(values, default=None)
    peak_time = left + 1 + values.index(peak) if values else None
    first = next((time for time, val in enumerate(values, start=left + 1) if val > cap), None)
    return current, peak, peak_time, first


def backward(steps, profile, left, right, cap):
    """Direct inverse on physical covariances, with no composed maps or envelopes."""
    upper = ALL
    for time in range(right, left, -1):
        threshold = cap * profile[time]
        if upper is not ALL:
            threshold = min(threshold, upper)
        gain, noise, observation = steps[time - 1]
        if observation == 0 or observation is not None and threshold >= observation:
            upper = ALL
            continue
        if observation is not None:
            threshold = threshold * observation / (observation - threshold)
        if threshold < noise:
            return NO
        upper = (threshold - noise) / gain if gain else ALL
    return upper


def check_query(index, steps, profile, left, right, initial, cap):
    reference = replay(steps, profile, left, right, initial, cap)
    report = index.analyze(left, right, initial, cap)
    output = (report.final_covariance, report.peak_ratio, report.peak_time, report.first_excess)
    assert output == reference, (steps, profile, left, right, initial, cap, output, reference)
    bound = index.safe_initial(left, right, cap)
    baseline = backward(steps, profile, left, right, cap)
    assert bound == baseline, (steps, profile, left, right, cap, bound, baseline)
    assert (bound is ALL or (bound is not NO and initial <= bound)) == (report.first_excess is None)


def test_examples():
    # At zero both times tie, with a different winner immediately to the right.
    index = DeadlineIndex([(1, 0, None), (2, 0, 2)])
    assert index.analyze(0, 2, 0).peak_time == 1
    assert index.analyze(0, 2, F(1, 2)).peak_time == 2
    assert index.analyze(0, 2, 1).peak_time == 1
    assert index.safe_initial(0, 2, 0) == 0
    # A genuine irrational input cut (sqrt(13) - 1)/4.
    index = DeadlineIndex([(2, 0, None), (1, 1, 3)])
    cut = index.root.envelope.pieces[1].cut
    assert cut == Cut(F(-1, 4), F(13, 16))
    assert index.analyze(0, 2, F(13, 20)).peak_time == 2
    assert index.analyze(0, 2, F(33, 50)).peak_time == 1
    assert Cut(F(-2), F(16)).compare(Cut(F(1), F(1))) == 0
    assert index.safe_initial(0, 2, F(5, 4)) == F(4, 7)
    assert index.safe_initial(0, 2, F(3, 2)) == F(3, 4)
    # Finite limiting ceiling, unattained from every finite prior.
    index = DeadlineIndex([(1, 0, 2), (0, 1, None), (1, 1, None)])
    assert index.safe_initial(0, 3, 2) is ALL
    assert index.safe_initial(0, 3, F(19, 10)) is NO
    assert index.safe_initial(0, 0, 0) is ALL
    # Exact observation with zero predicted variance is a legal zero, as in Lean.
    index = DeadlineIndex([(0, 0, 0), (3, 0, None)])
    assert index.analyze(0, 2, 7, 0).peak_ratio == 0
    assert index.safe_initial(0, 2, 0) is ALL
    index = DeadlineIndex([(1, F(1, 5), 2), (0, F(2, 3), None), (1, F(1, 7), 3)])
    constant = index.root.end_map
    expected = replay([(1, F(1, 5), 2), (0, F(2, 3), None), (1, F(1, 7), 3)],
                      [F(1)] * 4, 0, 3, F(7), F(0))[0]
    assert (constant.a, constant.b, constant.c, constant.d) == (
        0, expected.numerator, 0, expected.denominator)
    # Every prefix can be the unique peak for some starting covariance.
    count = 64
    steps = [(count, 0, None)]
    intercept = 0
    for time in range(1, count):
        gain = F(count - time, count - time + 1)
        next_intercept = intercept + count - time
        steps.append((gain, next_intercept - gain * intercept, None))
        intercept = next_intercept
    index = DeadlineIndex(steps)
    assert len(index.root.envelope.pieces) == count
    assert [index.analyze(0, count, F(2 * i + 1, 2)).peak_time for i in range(count)] == list(
        range(count, 0, -1))


def test_cli_large_rationals():
    gain = "1" + "0" * 2200
    request = {
        "steps": [[gain, 0, None]] * 2,
        "queries": [{"left": 0, "right": 2, "initial": 1, "cap": 1}],
    }
    script = Path(__file__).with_name("riccati_deadlines.py")
    result = run(
        [executable, "-X", "int_max_str_digits=4300", str(script), "-"],
        input=json.dumps(request),
        capture_output=True,
        text=True,
        check=True,
    )
    output = json.loads(result.stdout)
    covariance = "1" + "0" * 4400
    assert output["final_covariance"] == output["peak_ratio"] == covariance
    assert output["safe_initial"] == "1/" + covariance


def main():
    test_examples()
    test_cli_large_rationals()
    queries = 0
    palette = ((0, 0, 0), (0, 2, 3), (1, 0, None), (2, 0, 2), (1, 1, 3), (2, 3, None))
    for length in range(5):
        for steps in product(palette, repeat=length):
            profile = (F(1), F(2), F(3, 2), F(1, 2), F(4))[:length + 1]
            index = DeadlineIndex(steps, profile)
            for left in range(length + 1):
                for right in range(left, length + 1):
                    for initial, cap in product((F(0), F(2, 3), F(5)), (F(0), F(1), F(2), F(5))):
                        check_query(index, steps, profile, left, right, initial, cap)
                        queries += 1
    random = Random(41501)
    for length in (15, 31, 64, 127):
        for _ in range(8):
            profile = [F(random.randint(1, 5), random.randint(1, 3)) for _ in range(length + 1)]
            steps = [(F(random.randint(0, 7), random.randint(1, 5)),
                      F(random.randint(0, 9), random.randint(1, 4)),
                      random.choice([None, F(0), F(1, 3), F(1), F(5), F(10)]))
                     for _ in range(length)]
            index = DeadlineIndex(steps, profile)
            for _ in range(140):
                left = random.randrange(length + 1)
                right = random.randrange(left, length + 1)
                initial, cap = (F(random.randrange(150), random.randint(1, 31)) for _ in range(2))
                check_query(index, steps, profile, left, right, initial, cap)
                queries += 1
    print(f"Verified {queries:,} exact report/bound pairs and targeted boundary cases.")


def benchmark():
    random = Random(41967)
    count, queries = 2048, 400
    steps = [(F(0) if i % 97 == 0 else F(random.randint(4, 9), 7), F(1 + i % 5, 17),
              None if i % 11 < 4 else F(1 + i % 5, 3)) for i in range(count)]
    profile = [F(2 + i % 7, 3) for i in range(count + 1)]
    start = perf_counter()
    index = DeadlineIndex(steps, profile)
    print(f"Build ({count} steps): {perf_counter() - start:.3f} s")
    for label, shortest, longest in (("short", 1, 4), ("long", 512, 1536)):
        workload = []
        for _ in range(queries):
            length = random.randint(shortest, longest)
            left = random.randint(0, count - length)
            workload.append((left, left + length, F(random.randrange(80), 29),
                             F(random.randrange(30), 7)))
        start = perf_counter()
        direct = [(replay(steps, profile, left, right, prior, cap),
                   backward(steps, profile, left, right, cap))
                  for left, right, prior, cap in workload]
        direct_time = perf_counter() - start
        start = perf_counter()
        indexed = []
        for left, right, prior, cap in workload:
            report = index.analyze(left, right, prior, cap)
            indexed.append(((report.final_covariance, report.peak_ratio, report.peak_time,
                             report.first_excess), index.safe_initial(left, right, cap)))
        indexed_time = perf_counter() - start
        assert indexed == direct
        print(f"{queries} {label} windows: direct {direct_time:.3f} s, index {indexed_time:.3f} s")


if __name__ == "__main__":
    if argv[1:] == ["--benchmark"]:
        benchmark()
    else:
        main()
