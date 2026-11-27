"""Exact path cuts, threshold hinges, and dispatch replay for the OPSD excerpt."""
import argparse
import csv
import hashlib
from datetime import datetime, timedelta, timezone
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
from random import Random

HERE = Path(__file__).resolve().parent
EXCERPT = HERE / "opsd_residential3_may2017.csv"
SOURCE_HASH = "15956440b27465686eae2abf5895cbc3dab80f934a891bcb2f4f944428e97d60"


def extract(source):
    assert hashlib.sha256(source.read_bytes()).hexdigest() == SOURCE_HASH
    columns = ["DE_KN_residential3_" + kind for kind in ("pv", "grid_import", "grid_export")]
    start = datetime(2017, 5, 1, tzinfo=timezone.utc)
    times = [(start + timedelta(hours=i)).strftime("%Y-%m-%dT%H:%M:%SZ") for i in range(97)]
    with source.open(newline="") as file:
        needed = set(times)
        selected = {row["utc_timestamp"]: row for row in csv.DictReader(file)
                    if row["utc_timestamp"] in needed}
    counters = []
    for time in times:
        row = selected[time]
        markers = {field.strip() for field in row["interpolated"].split(";")}
        assert not set(columns).intersection(markers)
        counters.append(tuple(Q(row[field]) for field in columns))
    with EXCERPT.open("w", newline="") as file:
        writer = csv.writer(file, lineterminator="\n")
        writer.writerow(("pv_kwh", "load_kwh"))
        for old, new in zip(counters, counters[1:]):
            pv, imported, exported = (end - begin for begin, end in zip(old, new))
            load = imported + pv - exported
            assert min(pv, imported, exported, load) >= 0
            pv, load = pv * 1000, load * 1000
            assert pv.denominator == load.denominator == 1
            writer.writerow(f"{int(value) // 1000}.{int(value) % 1000:03d}" for value in (pv, load))


def replay(data, capacity, theta):
    state = capacity
    imported = spill = Q(0)
    for pv, load in data:
        unbounded = state + theta * pv - load
        imported += max(0, -unbounded)
        spill += max(0, unbounded - capacity)
        state = min(capacity, max(0, unbounded))
    return imported, spill, state


def cut_line(data, capacity, mask):
    slope = intercept = Q(0)
    previous = 1
    for i, (pv, load) in enumerate(data):
        z = (mask >> i) & 1
        slope += (1 - z) * pv
        intercept += z * load + capacity * previous * (1 - z)
        previous = z
    return slope, intercept, mask


def best_line(lines, theta):
    return min(lines, key=lambda line: (line[0] * theta + line[1], line[2]))


def path_min_cut(data, capacity, theta):
    # Prefix line and mask for each possible final side. The initial predecessor
    # is the source side, so a cut before the first time vertex costs capacity.
    zero = None
    one = (Q(0), Q(0), 0)
    for i, (pv, load) in enumerate(data):
        enter_zero = (one[0] + pv, one[1] + capacity, one[2])
        enter_one = (one[0], one[1] + load, one[2] | (1 << i))
        if zero is None:
            zero, one = enter_zero, enter_one
        else:
            stay_zero = (zero[0] + pv, zero[1], zero[2])
            leave_zero = (zero[0], zero[1] + load, zero[2] | (1 << i))
            zero = best_line((enter_zero, stay_zero), theta)
            one = best_line((enter_one, leave_zero), theta)
    return best_line((zero, one), theta)


def solve_curve(data, capacity):
    """Split between exact supporting-line crossings until each interval is certified."""
    high = 1 + max(((load + capacity) / pv for pv, load in data if pv), default=0)
    start, end = Q(0), Q(high)
    knots = {start, end}

    def split(lo, left, hi, right):
        if left[:2] == right[:2]:
            return
        assert left[0] > right[0]
        cross = (right[1] - left[1]) / (left[0] - right[0])
        assert lo <= cross <= hi
        middle = path_min_cut(data, capacity, cross)
        if middle[0] * cross + middle[1] == left[0] * cross + left[1]:
            knots.add(cross)
        else:
            assert lo < cross < hi
            split(lo, left, cross, middle)
            split(cross, middle, hi, right)

    split(start, path_min_cut(data, capacity, start),
          end, path_min_cut(data, capacity, end))
    knots = sorted(knots)
    intervals = [(left, right, path_min_cut(data, capacity, (left + right) / 2))
                 for left, right in zip(knots, knots[1:])]
    # The smallest numerical mask is the inclusion-minimal optimal source set.
    thresholds = [end] * len(data)
    previous = 0
    for left, right, (slope, _, mask) in intervals:
        assert (previous & mask) == previous
        for i in range(len(data)):
            if ((mask ^ previous) >> i) & 1:
                thresholds[i] = left
        previous = mask
    return intervals, thresholds


def total_import(data, capacity, theta):
    cut = path_min_cut(data, capacity, theta)
    return sum(load for _, load in data) - cut[0] * theta - cut[1]


def verify(data, capacity, brute=False):
    intervals, thresholds = solve_curve(data, capacity)
    high = intervals[-1][1]
    floor = total_import(data, capacity, high)
    params = {high + 1, *(left for left, _, _ in intervals), high}
    params.update((2 * left + right) / 3 for left, right, _ in intervals)
    params.update((left + 2 * right) / 3 for left, right, _ in intervals)
    if brute:
        cut_lines = [cut_line(data, capacity, mask) for mask in range(1 << len(data))]
        if len(data) <= 3:
            params.update((b2 - b1) / (m1 - m2)
                          for m1, b1, _ in cut_lines for m2, b2, _ in cut_lines
                          if m1 != m2 and (b2 - b1) / (m1 - m2) >= 0)
    for theta in params:
        if brute:
            assert path_min_cut(data, capacity, theta) == best_line(cut_lines, theta)
        hinges = floor + sum(pv * max(0, cutoff - theta)
                             for (pv, _), cutoff in zip(data, thresholds))
        assert hinges == total_import(data, capacity, theta) == replay(data, capacity, theta)[0]
    return intervals, thresholds, floor, len(params)


def tiny_checks():
    cases = points = 0
    random = Random(1729)
    configurations = [(n, samples) for n in (1, 2, 3)
                      for samples in product(range(3), repeat=2 * n)]
    configurations += [(n, tuple(random.randrange(5) for _ in range(2 * n)))
                       for n in range(4, 8) for _ in range(10)]
    for n, samples in configurations:
        data = [(Q(samples[i]), Q(samples[n + i])) for i in range(n)]
        for capacity in map(Q, (0, 1, 2)):
            _, _, _, count = verify(data, capacity, brute=True)
            cases += 1
            points += count
    print(f"Tiny checks: {cases} traces, {points} exact parameter comparisons")


def metered_check():
    with EXCERPT.open(newline="") as file:
        data = [(Q(pv), Q(load)) for pv, load in list(csv.reader(file))[1:]]
    capacity, target = Q(4), Q(10)
    intervals, thresholds, floor, count = verify(data, capacity)
    demand = sum(load for _, load in data)
    for left, right, (slope, offset, _) in intervals:
        if slope:
            parameter = (demand - offset - target) / slope
            if left <= parameter <= right:
                break
    else:
        raise AssertionError("Target lies outside all strictly decreasing intervals")
    assert replay(data, capacity, parameter)[0] == target
    assert total_import(data, capacity, parameter) == target
    assert total_import(data, capacity, (left + parameter) / 2) > target
    positive_knots = sorted({t for (pv, _), t in zip(data, thresholds) if pv and t > 0})
    print(f"Excerpt SHA256: {hashlib.sha256(EXCERPT.read_bytes()).hexdigest()}")
    print(f"Hours: {len(data)}. PV: {sum(pv for pv, _ in data)} kWh. Load: {demand} kWh.")
    print(f"Positive import knots: {len(positive_knots)}. Last knot: {positive_knots[-1]}.")
    print(f"Floor: {floor} kWh. Exact parameter checks: {count}.")
    for theta in map(Q, (0, 1, 2)):
        print(f"Multiplier {theta}: import {replay(data, capacity, theta)[0]} kWh")
    print(f"Inverse: multiplier {parameter} ({float(parameter):.8f}) for {target} kWh.")
    print(f"Bracket: ({left}, {right}); within it import = {demand-offset} - {slope} * multiplier.")
    print(f"Import, spill and final charge at inverse: {replay(data, capacity, parameter)}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, help="Regenerate the excerpt from the OPSD source CSV.")
    args = parser.parse_args()
    if args.source:
        extract(args.source)
    tiny_checks()
    metered_check()
