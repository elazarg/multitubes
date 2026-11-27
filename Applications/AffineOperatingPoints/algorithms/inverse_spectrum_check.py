"""Check the compiler with direct real quantifier elimination in Z3."""

from fractions import Fraction
from random import Random

import z3

from inverse_spectrum import compile_spectrum


def rv(value):
    return z3.RealVal(str(value))


def real_projection(rows, variables):
    eliminator = z3.Tactic("qe")
    return eliminator(z3.Exists(variables, z3.And(*rows))).as_expr()


def prove(formula):
    check = z3.SolverFor("QF_LRA")
    check.add(z3.Not(formula))
    assert check.check() == z3.unsat


def check(intervals):
    network = compile_spectrum(intervals)
    assert {gain for _, _, gain, _ in network.branches} == {2, 3}
    assert min(offset for _, _, _, offset in network.branches) >= 0
    assert {u for u, v, _, _ in network.branches if u != v
            and v == network.vertices - 1} == set(range(network.vertices - 1))

    level = z3.Real("level")
    x = [z3.Real(f"x_{vertex}") for vertex in range(network.vertices)]
    rows = [[] for _ in x]
    for u, v, gain, offset in network.branches:
        rows[v].append(gain * x[u] + rv(offset) - x[v] - level)
    weak = [term <= 0 for row in rows for term in row]
    tight = [z3.Or(*(term == 0 for term in row)) for row in rows]
    raw_membership = z3.Or(*(z3.And(
        True if lo is None else level >= rv(lo),
        True if hi is None else level <= rv(hi),
    ) for lo, hi in intervals))
    prove(real_projection(weak + tight, x) == raw_membership)
    prove(real_projection(weak, x))

    admissible = [Fraction(n, 3) for n in range(-12, 13)]
    admissible.extend(Fraction(endpoint) for pair in intervals for endpoint in pair
                      if endpoint is not None)
    for number in admissible:
        target = any((lo is None or Fraction(lo) <= number)
                     and (hi is None or number <= Fraction(hi))
                     for lo, hi in intervals)
        relaxation = network.relaxation_witness(number)
        assert all(gain * relaxation[u] + offset <= relaxation[v] + number
                   for u, v, gain, offset in network.branches)
        witness = network.eigenvector(number)
        assert (witness is not None) == target
        if witness is not None:
            maxima = [None] * network.vertices
            for u, v, gain, offset in network.branches:
                candidate = gain * witness[u] + offset
                maxima[v] = candidate if maxima[v] is None else max(maxima[v], candidate)
            assert all(value == number + coord for value, coord in zip(maxima, witness))


def main():
    fixtures = [
        [],
        [(None, None)],
        [(None, -1), (1, None)],
        [(1, None)],
        [(None, -1)],
        [(-1, -1)],
        [("-11/3", "-10/3"), ("-5/2", "-1/3")],
        [(5, 6), (None, -2), (-1, 0), (0, 1), (4, 4), (8, None), (-4, -3)],
        [(0, None), (None, 2)],
        [(5, 7), (1, 3), (1, 2), (1, 4), (4, 6), (2, 2)],
        [(None, -3), (3, None), (0, 0)],
        [(-3, -1), (1, 3), (4, 4)],
    ]
    rng = Random(271828)
    for _ in range(12):
        rows = []
        for _ in range(rng.randrange(1, 5)):
            a, b = sorted(Fraction(rng.randrange(-18, 19), 3) for _ in range(2))
            rows.append((None if rng.randrange(15) == 0 else a,
                         None if rng.randrange(15) == 0 else b))
        fixtures.append(rows)
    for rows in fixtures:
        check(rows)
    print(f"Direct real quantifier elimination verified {len(fixtures)} spectra and all relaxations.")


if __name__ == "__main__":
    main()
