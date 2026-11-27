"""Independent small rational LP checks and fixed feedback examples."""

from fractions import Fraction as F
from itertools import combinations
from random import Random

from feedback_margins import Arc, Baseline, normalized_arc


def rows_for(budget, arcs):
    size = len(budget)
    constraints = []
    for i, cap in enumerate(budget):
        row = [F(0)] * size
        row[i] = F(1)
        constraints.append((*row, F(cap)))
        row[i] = F(-1)
        constraints.append((*row, F(0)))
    for arc in arcs:
        row = [F(0)] * size
        row[arc.tail] += arc.gain
        row[arc.head] -= 1
        constraints.append((*row, -arc.bias))
    return constraints


def basic_solution(active):
    rows = [list(row) for row in active]
    size = len(rows)
    for col in range(size):
        pivot = next((i for i in range(col, size) if rows[i][col]), None)
        if pivot is None:
            return None
        rows[col], rows[pivot] = rows[pivot], rows[col]
        div = rows[col][col]
        for j in range(col, size + 1):
            rows[col][j] /= div
        for i in range(size):
            if i == col or not rows[i][col]:
                continue
            mul = rows[i][col]
            for j in range(col, size + 1):
                rows[i][j] -= mul * rows[col][j]
    return tuple(row[-1] for row in rows)


def satisfies_rows(solution, rows):
    return all(sum(a * x for a, x in zip(row, solution)) <= row[-1] for row in rows)


def vertices(budget, arcs):
    rows = rows_for(budget, arcs)
    seen = set()
    for active in combinations(rows, len(budget)):
        vertex = basic_solution(active)
        if vertex is not None and vertex not in seen and satisfies_rows(vertex, rows):
            seen.add(vertex)
            yield vertex


def path_summary(arcs, first, path):
    end, gain, bias = first, F(1), F(0)
    for index in path:
        arc = arcs[index]
        assert arc.tail == end
        end = arc.head
        gain *= arc.gain
        bias = arc.gain * bias + arc.bias
    return end, gain, bias


def check_head_rejection(base, candidate, cert):
    if cert.feedback is None:
        gain, bias = F(0), F(0)
    else:
        end, gain, bias = path_summary(base.arcs, candidate.head, cert.feedback)
        assert end == candidate.tail
    end, budget_gain, budget_bias = path_summary(base.arcs, candidate.head, cert.to_budget)
    assert budget_gain > 0
    ceiling = (base.budget[end] - budget_bias) / budget_gain
    cycle_gap = 1 - gain * candidate.gain
    assert cycle_gap >= 0
    assert candidate.bias + candidate.gain * bias > cycle_gap * ceiling


def fixed_examples():
    # Imported from the SwitchedHybridControl two-mode example.
    radius, gauge = [F(3, 2), F(4)], [F(1), F(4)]
    arcs = [Arc(0, 1, F(2), F(1)), Arc(1, 0, F(1, 8), F(1))]
    budget = [F(5, 2), F(16)]
    base = Baseline(
        [(cap - b) / g for cap, b, g in zip(budget, radius, gauge)],
        [normalized_arc(arc, radius, gauge) for arc in arcs],
    )
    profile = base.head_profile(1)
    replacement = normalized_arc(Arc(0, 1, F(2), F(7)), radius, gauge)
    assert profile.margin(replacement.tail, replacement.gain) == replacement.bias
    assert profile.seed.value == [1, 2]
    rejected = normalized_arc(Arc(0, 1, F(2), F(8)), radius, gauge)
    check_head_rejection(base, rejected, profile.certify_rejection(rejected))
    assert base.tail_batch(0, [replacement]) == [1, 2]

    # A normalized new gain of 2 has return gain 1/2 and is admissible.
    boundary = normalized_arc(Arc(0, 1, F(8), F(-8)), radius, gauge)
    assert profile.margin(boundary.tail, boundary.gain) == boundary.bias

    # Outside the return condition the best feasible head may be interior.
    base_arcs = [Arc(0, 1, F(1, 2), F(-1))]
    base = Baseline([10, 10], base_arcs)
    profile = base.head_profile(0)
    assert max(h - 3 * u for h, u in vertices([10, 10], base_arcs)) == 2
    assert profile.seed.value[0] - 3 * profile.seed.value[1] == -2
    assert not profile.saturates(1, F(3))

    # A steep edge crosses a shallow edge at the maximum head. The tied
    # shallow path is the left derivative, so gain 3 remains admissible.
    base = Baseline([5, 10], [Arc(0, 1, F(1, 2), F(-1)), Arc(0, 1, F(3, 10), F(0))])
    tied = base.head_profile(0)
    assert tied.left_slope[1] == F(3, 10)
    assert tied.margin(1, F(3)) == F(1, 2)
    rejection = Arc(1, 0, F(3), F(3, 4))
    check_head_rejection(base, rejection, tied.certify_rejection(rejection))

    # Distinct heads can interact through two newly added transitions.
    candidate_a = Arc(0, 1, F(1, 2), F(3, 4))
    candidate_b = Arc(1, 0, F(1, 2), F(3, 4))
    assert next(vertices([1, 1], [candidate_a]), None) is not None
    assert next(vertices([1, 1], [candidate_b]), None) is not None
    assert next(vertices([1, 1], [candidate_a, candidate_b]), None) is None


def randomized():
    random = Random(57_201)
    margins = rejected = batches = 0
    gains = [F(0), F(1, 3), F(1, 2), F(4, 5), F(1), F(6, 5), F(2)]
    for _ in range(300):
        size = random.randint(1, 3)
        budget = [F(random.randrange(9), 2) for _ in range(size)]
        arcs = [
            Arc(random.randrange(size), random.randrange(size), random.choice(gains[:5]),
                F(-random.randrange(5), 3))
            for _ in range(random.randrange(1, 8))
        ]
        base = Baseline(budget, arcs)
        feasible = list(vertices(budget, arcs))
        assert base.upper.value == [max(v[i] for v in feasible) for i in range(size)]
        assert satisfies_rows(base.upper.value, rows_for(budget, arcs))
        head, tail = random.randrange(size), random.randrange(size)
        profile = base.head_profile(head)
        head_candidates, tail_candidates = [], []
        for v in range(size):
            for a in gains:
                optimum = max(point[head] - a * point[v] for point in feasible)
                endpoint = profile.seed.value[head] - a * profile.seed.value[v]
                assert profile.saturates(v, a) == (endpoint == optimum)
                if not profile.saturates(v, a):
                    continue
                threshold = profile.margin(v, a)
                assert threshold == optimum
                candidate = Arc(v, head, a, threshold + F(1, 100))
                check_head_rejection(base, candidate, profile.certify_rejection(candidate))
                head_candidates.append(Arc(v, head, a, threshold))
                margins += 1
                rejected += 1

            return_gain = base._forward([(v, F(1), F(0))], gains_only=True).value[tail]
            a = random.choice([a for a in gains if a * return_gain <= 1])
            tail_candidates.append(Arc(tail, v, a, F(random.randrange(-1, 18), 6)))
        assert satisfies_rows(profile.seed.value, rows_for(budget, [*arcs, *head_candidates]))
        tail_solution = base.tail_batch(tail, tail_candidates)
        rows = rows_for(budget, [*arcs, *tail_candidates])
        exists = next(vertices(budget, [*arcs, *tail_candidates]), None) is not None
        assert (tail_solution is not None) == exists
        if tail_solution is not None:
            assert satisfies_rows(tail_solution, rows)
        batches += 1
    print(f"Passed {margins} exact margins and {rejected} rejection certificates, "
          f"{batches} common-tail batches, and the fixed examples.")


if __name__ == "__main__":
    fixed_examples()
    randomized()
