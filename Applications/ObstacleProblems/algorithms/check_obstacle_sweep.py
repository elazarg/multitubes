"""Independent full-scan and fixed-orbit checks for obstacle_sweep.sweep."""
from dataclasses import dataclass
from fractions import Fraction as Q
from math import inf
from random import Random

from obstacle_sweep import Step, sweep


@dataclass(frozen=True)
class Line:
    start: Q | float
    end: Q | float
    slope: Q
    offset: Q


def sample(start, end):
    if start == -inf:
        return 0 if end == inf else end - 1
    if end == inf:
        return start + 1
    return (start + end) / 2


def clip_line(line, lower, upper):
    cuts = [line.start, line.end]
    if line.slope:
        for limit in (lower, upper):
            root = (limit - line.offset) / line.slope
            if line.start < root < line.end:
                cuts.append(root)
    cuts = sorted(set(cuts))
    for start, end in zip(cuts, cuts[1:]):
        midpoint = sample(start, end)
        value = line.slope * midpoint + line.offset
        if value <= lower:
            yield True, value >= upper, Line(start, end, Q(0), lower)
        elif value >= upper:
            yield False, True, Line(start, end, Q(0), upper)
        else:
            yield False, False, Line(start, end, line.slope, line.offset)


def reference_trace(steps, initial):
    curve = [Line(-inf, inf, *map(Q, initial))]
    contact_pairs = []
    knots = set()
    visits = 0
    for step in steps:
        visits += len(curve)
        next_curve = []
        lower_through, upper_from = -inf, inf
        for segment in curve:
            raw = Line(segment.start, segment.end,
                       step.gain * segment.slope + step.forcing,
                       step.gain * segment.offset + step.shift)
            for low, high, piece in clip_line(raw, step.lower, step.upper):
                if low:
                    lower_through = max(lower_through, piece.end)
                if high:
                    upper_from = min(upper_from, piece.start)
                if piece.start != -inf:
                    knots.add(piece.start)
                if next_curve and (piece.slope, piece.offset) == (
                    next_curve[-1].slope, next_curve[-1].offset
                ):
                    old = next_curve.pop()
                    piece = Line(old.start, piece.end, piece.slope, piece.offset)
                next_curve.append(piece)
        curve = next_curve
        if step.lower == step.upper:
            lower_through, upper_from = inf, -inf
        contact_pairs.append((lower_through, upper_from))
    return contact_pairs, knots, visits


def replay(steps, parameter, seed):
    values = []
    observed = shortfall = spill = Q(0)
    for step in steps:
        raw = step.gain * seed + step.shift + step.forcing * parameter
        shortfall += step.weight * max(0, step.lower - raw)
        spill += step.weight * max(0, raw - step.upper)
        seed = min(step.upper, max(step.lower, raw))
        values.append(seed)
        observed += step.weight * seed
    return seed, observed, shortfall, spill, values


def free_seed_coefficients(steps):
    gain, slope, offset = Q(1), Q(0), Q(0)
    for step in steps:
        gain *= step.gain
        slope = step.gain * slope + step.forcing
        offset = step.gain * offset + step.shift
    return slope / (1 - gain), offset / (1 - gain)


def contact_enumeration_seed(steps, parameter):
    # Any fixed orbit either follows the full affine branch or has a saturated
    # value. In the second case propagate that known obstacle to the end.
    slope, offset = free_seed_coefficients(steps)
    candidates = {slope * parameter + offset}
    for i, step in enumerate(steps, 1):
        for obstacle in (step.lower, step.upper):
            candidates.add(replay(steps[i:], parameter, obstacle)[0])
    fixed = [seed for seed in candidates if replay(steps, parameter, seed)[0] == seed]
    assert len(fixed) == 1
    return fixed[0]


def check(steps, initial, periodic=False):
    trace = sweep(steps, initial, periodic=periodic)
    if periodic:
        reference_contacts, knots, _ = reference_trace(steps * 2, free_seed_coefficients(steps))
        reference_contacts = reference_contacts[len(steps):]
    else:
        reference_contacts, knots, _ = reference_trace(steps, initial)
    assert [(c.lower_through, c.upper_from) for c in trace.contacts] == reference_contacts

    curves = trace.final, trace.observed, trace.shortfall, trace.spill
    knots.update(k for curve in curves for k in curve.knots)
    ordered = sorted(knots)
    regions = list(zip([-inf, *ordered], [*ordered, inf]))
    parameters = set(ordered)
    for start, end in regions:
        midpoint = sample(start, end)
        parameters.add(midpoint)
        delta = 1 if start == -inf else (midpoint - start) / 3
        if end != inf:
            delta = min(delta, (end - midpoint) / 3)
        parameters.add(midpoint + delta)

    for parameter in parameters:
        if periodic:
            seed = contact_enumeration_seed(steps, parameter)
        else:
            seed = initial[0] * parameter + initial[1]
        final, observed, shortfall, spill, values = replay(steps, parameter, seed)
        assert [curve(parameter) for curve in curves] == [final, observed, shortfall, spill]
        for step, contact, value in zip(steps, trace.contacts, values, strict=True):
            assert (parameter <= contact.lower_through) == (step.lower == value)
            assert (parameter >= contact.upper_from) == (step.upper == value)
        if all(step.weight >= 0 for step in steps):
            for curve, direction in ((trace.observed, 1), (trace.shortfall, -1), (trace.spill, 1)):
                for target in (curve(parameter), curve(parameter) - 1, curve(parameter) + 1):
                    invert = curve.first_at_least if direction == 1 else curve.first_at_most
                    crossing = invert(target)
                    if crossing not in (-inf, inf):
                        assert curve(crossing) == target
                        assert direction * (curve(crossing - 1) - target) < 0
                    if direction * (curve(parameter) - target) >= 0:
                        assert crossing <= parameter
    return len(parameters)


def random_checks():
    rng = Random(52725)
    checked_parameters = 0
    n = 0
    fixtures = (
        ((Step(1, 0, 1, 0, 1), Step(1, 0, 0, 0, 1)), (0, 0), False),
        ((Step(0, 0, 0, 0, 0),), (0, 0), True),
        ((Step(0, 0, 1, 0, 0),), (0, 0), True),
        ((Step(1, 0, 1, 0, 1), Step(1, 0, 0, 1, 2)), (0, 0), False),
        ((Step(1, -1, 0, 0, 1),), (0, 0), False),
        ((Step(1, 2, 0, 0, 1),), (0, 0), False),
        ((Step(2, 0, 1, 0, 5), Step(Q(1, 3), 1, 1, 0, 6)), (0, 0), True),
    )
    for steps, initial, periodic in fixtures:
        checked_parameters += check(steps, initial, periodic=periodic)
        n += 1
    for _ in range(350):
        steps = []
        gain = Q(1)
        for _ in range(rng.randrange(1, 9)):
            a = rng.choice([0, Q(1, 4), Q(1, 2), 1, Q(3, 2), 2])
            gain *= a
            lower = rng.randrange(-3, 4)
            upper = lower + rng.randrange(5)
            steps.append(Step(a, rng.randrange(-4, 5), rng.randrange(4), lower, upper,
                              rng.choice([-1, 0, 1, 2, Q(3, 2)])))
        steps = tuple(steps)
        initial = (rng.randrange(4), rng.randrange(-4, 5))
        checked_parameters += check(steps, initial)
        n += 1
        if gain < 1:
            checked_parameters += check(steps, initial, periodic=True)
            n += 1
    print(f"{n} checked finite and periodic traces, {checked_parameters} exact parameter probes")


def worst_case_counts():
    print("n, scanning visits, deque endpoint checks, deque piece creations")
    for n in (128, 512, 2048):
        steps = tuple(Step(1, i, 1, 0, n * n + 1) for i in range(1, n + 1))
        result = sweep(steps, aggregate=False)
        visits = (n * n + 3 * n - 2) // 2
        if n <= 512:
            assert reference_trace(steps, (0, 0))[2] == visits
        assert len(result.final.knots) == n + 1
        print(n, visits, result.endpoint_checks, result.piece_creations, sep=", ")


if __name__ == "__main__":
    random_checks()
    worst_case_counts()
