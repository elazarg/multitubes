"""Compare the strong-connectivity classification to direct all-level QE."""

from fractions import Fraction as Q
from random import Random

import z3

from strongly_connected_spectrum import Spectrum, classify


def real(value):
    return z3.RealVal(str(value))


def assert_valid(formula):
    solver = z3.SolverFor("QF_LRA")
    solver.add(z3.Not(formula))
    assert solver.check() == z3.unsat, solver


def compare(size, branches, expected=None):
    result = classify(size, branches)
    if expected is not None:
        assert result == expected, (size, branches, result)
    lam = z3.Real("lam")
    xs = [z3.Real(f"x_{i}") for i in range(size)]
    incoming = [[] for _ in xs]
    for u, v, a, b in branches:
        incoming[v].append(real(a) * xs[u] + real(b) - xs[v] - lam)
    inequalities = [term <= 0 for row in incoming for term in row]
    equalities = [z3.Or(*(term == 0 for term in row)) for row in incoming]
    eliminate = z3.Tactic("qe")

    if result.kind == "all_real":
        target = z3.BoolVal(True)
    elif result.kind == "upper_ray":
        target = lam >= real(result.cutoff)
    else:
        assert result.kind == "singleton"
        target = lam == real(result.cutoff)
        assert len(result.scale) == size and result.scale[0] == 1
        assert all(value > 0 for value in result.scale)
        assert all(Q(a) * result.scale[u] == result.scale[v] for u, v, a, _ in branches)
    eigen = eliminate(z3.Exists(xs, z3.And(*inequalities, *equalities))).as_expr()
    relax = eliminate(z3.Exists(xs, z3.And(*inequalities))).as_expr()
    assert_valid(eigen == target)
    assert_valid(relax == (z3.BoolVal(True) if result.cutoff is None else lam >= real(result.cutoff)))


def check_eigenvector(branches, level, vector):
    demands = [[] for _ in vector]
    for u, v, a, b in branches:
        demands[v].append(Q(a) * vector[u] + Q(b))
    assert all(max(row) == level + value for row, value in zip(demands, vector))


def fixtures():
    all_real = [(1, 0, 2, 0), (0, 1, 3, 0)]
    compare(2, all_real, Spectrum("all_real"))
    for lam in (Q(-3), Q(0), Q(5, 2)):
        check_eigenvector(all_real, lam, (3 * lam / 5, 4 * lam / 5))

    # Strong connectivity uses the zero-gain arrow, which is a constant floor.
    ray = [(0, 0, 2, 0), (1, 0, 0, 0), (0, 1, "1/2", 0)]
    compare(2, ray, Spectrum("upper_ray", Q(0)))
    for lam in (Q(0), Q(1, 3), Q(5)):
        check_eigenvector(ray, lam, (lam, -lam / 2))

    singleton = [(1, 0, 2, 3), (0, 1, "1/2", 1)]
    compare(2, singleton, Spectrum("singleton", Q(5, 3), (Q(1), Q(1, 2))))
    check_eigenvector(singleton, Q(5, 3), (Q(0), Q(-2, 3)))

    closed_gap = [(0, 0, 2, 0), (0, 0, 3, 0), (0, 1, 2, "1/2"),
                  (1, 1, 3, 0), (1, 0, 2, 0)]
    compare(2, closed_gap, Spectrum("all_real"))
    check_eigenvector(closed_gap, Q(0), (Q(-1, 3), Q(-1, 6)))

    cases = [
        (1, [(0, 0, 0, 4)], Spectrum("all_real")),
        (1, [(0, 0, "1/2", 4)], Spectrum("all_real")),
        (1, [(0, 0, 1, 4), (0, 0, 1, -5)], Spectrum("singleton", Q(4), (Q(1),))),
        (1, [(0, 0, 0, 1), (0, 0, 1, 5)], Spectrum("upper_ray", Q(5))),
        (1, [(0, 0, 2, 1), (0, 0, "1/2", 1)], Spectrum("upper_ray", Q(1))),
        (2, [(1, 0, 2, 0), (0, 1, 3, 0), (0, 0, 1, 2)], Spectrum("upper_ray", Q(2))),
        (2, [(1, 0, 1, 0), (0, 1, "1/2", 0), (0, 0, 1, 2)], Spectrum("upper_ray", Q(2))),
    ]
    for size, branches, expected in cases:
        compare(size, branches, expected)
    for size, branches in [(0, []), (1, []), (1, [(0, 0, -1, 0)]),
                           (2, [(0, 0, 1, 0), (1, 1, 1, 0)])]:
        try:
            classify(size, branches)
        except ValueError:
            continue
        raise AssertionError((size, branches))
    return 4 + len(cases)


def random_cases():
    rng = Random(12381)
    for trial in range(30):
        size = 1 + trial % 4
        scales = [Q(rng.choice((1, 2, 3, 5)), rng.choice((1, 2, 3))) for _ in range(size)]
        pairs = [(v, (v + 1) % size) for v in range(size)]
        pairs.extend((rng.randrange(size), rng.randrange(size)) for _ in range(1 + trial % 4))
        branches = []
        for u, v in pairs:
            if trial % 3 == 0:
                gain = scales[v] / scales[u]
            else:
                gain = rng.choice((0, Q(1, 2), 1, Q(3, 2), 2, 3))
            offset = Q(rng.randrange(-4, 5), rng.choice((1, 2, 3)))
            branches.append((u, v, gain, offset))
        compare(size, branches)
    return trial + 1


if __name__ == "__main__":
    print(f"Direct all-real quantifier elimination verified {fixtures() + random_cases()} graphs.")
