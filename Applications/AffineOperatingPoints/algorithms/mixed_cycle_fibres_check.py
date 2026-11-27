"""Verify the mixed-cycle diagnosis with direct exact real formulas."""

from fractions import Fraction
from itertools import combinations
from random import Random

import z3

from mixed_cycle_fibres import index_fibre


def real(value):
    return z3.RealVal(Fraction(value))


def formulas(vertices, level, branches):
    x = tuple(z3.Real(f"x_{i}") for i in range(vertices))
    incoming = [[] for _ in x]
    for u, v, gain, offset in branches:
        incoming[v].append(real(gain) * x[u] + real(offset) - real(level) - x[v])
    weak = z3.And(*(term <= 0 for terms in incoming for term in terms))
    tight = z3.And(*(z3.Or(*(term == 0 for term in terms)) for terms in incoming))
    return x, weak, z3.And(weak, tight)


def prove(formula):
    solver = z3.SolverFor("QF_LRA")
    solver.add(z3.Not(formula))
    assert solver.check() == z3.unsat, formula


def at_point(formula, variables, values):
    return z3.substitute(formula, *((x, real(value)) for x, value in zip(variables, values)))


def check(vertices, level, branches, expected=None, expected_status=None):
    index = index_fibre(vertices, level, branches)
    x, relaxation, eigen = formulas(vertices, level, branches)
    if expected_status is not None:
        assert index.status == expected_status
    if index.status == "infeasible":
        prove(z3.Not(relaxation))
        return

    prove(at_point(relaxation, x, index.lower))
    prove(at_point(relaxation, x, index.upper))
    prove(z3.Implies(relaxation, z3.And(*(
        z3.And(real(lo) <= val, val <= real(hi))
        for val, lo, hi in zip(x, index.lower, index.upper)
    ))))
    if index.status == "continuum":
        v = index.continuum_vertex
        other = [variable for i, variable in enumerate(x) if i != v]
        projected = z3.Tactic("qe")(z3.Exists(other, eigen)).as_expr() if other else eigen
        interval = z3.And(real(index.lower[v]) <= x[v], x[v] <= real(index.upper[v]))
        prove(projected == interval)
        assert index.lower[v] < index.upper[v]
        lo, hi = index.lower[v], index.upper[v]
        for k in range(5):
            reading = lo + Fraction(k, 4) * (hi - lo)
            vector = index.continuum_witness(reading)
            assert vector[v] == reading
            prove(at_point(eigen, x, vector))
        return

    vectors = {}
    ids = range(len(index.critical))
    for count in range(len(index.critical) + 1):
        for choice in combinations(ids, count):
            if all(index.successors[i] <= set(choice) for i in choice):
                vectors[frozenset(choice)] = index.vector(choice)
    assert len(vectors) == len(set(vectors.values()))
    if expected is not None:
        assert set(vectors.values()) == expected
    expected_formula = z3.Or(*(
        z3.And(*(variable == real(value) for variable, value in zip(x, vector)))
        for vector in vectors.values()
    ))
    prove(eigen == expected_formula)
    for left, a in vectors.items():
        for right, b in vectors.items():
            assert (left <= right) == all(p <= q for p, q in zip(a, b))


def main():
    compact = [(0, 0, Fraction(1, 2), 0), (0, 0, 2, -1)]
    check(1, 0, compact, {(0,), (1,)}, "finite")
    check(1, 0, [*compact, (0, 0, 1, -1)], {(0,), (1,)}, "finite")
    check(1, 0, [*compact, (0, 0, 1, 0)], expected_status="continuum")
    check(1, 0, [(0, 0, Fraction(1, 2), 1), (0, 0, 2, -1)],
          expected_status="infeasible")

    frozen = [(0, 0, Fraction(1, 2), 0), (0, 0, 2, 0), (0, 0, 1, 0),
              (1, 1, Fraction(1, 2), 0), (1, 1, 2, -1),
              (0, 1, 2, 0), (1, 0, 2, -2)]
    check(2, 0, frozen, {(0, 0), (0, 1)}, "finite")
    chained = compact + [(1, 1, gain, offset) for _, _, gain, offset in compact]
    chained.extend(((0, 1, 2, -1), (1, 0, 2, Fraction(-3, 2))))
    check(2, 0, chained, {(0, 0), (Fraction(1, 2), 1), (1, 1)}, "finite")
    check(2, 0, [*compact, (0, 1, 2, 0), (1, 0, Fraction(1, 2), 0)],
          expected_status="continuum")
    # Both cycle regimes can occur without a contracting or expansive self-loop.
    check(2, 0, [(0, 1, Fraction(1, 3), 0), (1, 0, Fraction(1, 3), 0),
                 (0, 1, 2, -1), (1, 0, 2, -1)], {(0, 0), (1, 1)}, "finite")

    rng = Random(891013)
    gains = (Fraction(1, 3), 2, 4)
    for i in range(80):
        vertices = 2 + i % 4
        level = Fraction(rng.randrange(-7, 8), 3)
        branches = [(v, v, gain, Fraction(rng.randrange(-6, 7), 4))
                    for v in range(vertices) for gain in gains[:2]]
        branches += [(v, (v + 1) % vertices, rng.choice(gains),
                      Fraction(rng.randrange(-5, 4), 4)) for v in range(vertices)]
        branches += [(rng.randrange(vertices), rng.randrange(vertices), rng.choice(gains),
                      Fraction(rng.randrange(-5, 4), 4)) for _ in range(vertices)]
        check(vertices, level, branches)

    print("Checked exact finite, infeasible, and continuum fibres on 88 graphs.")


if __name__ == "__main__":
    main()
