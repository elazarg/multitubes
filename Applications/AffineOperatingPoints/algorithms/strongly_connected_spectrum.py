"""Classify the full spectrum of a strongly connected max-affine graph."""

import argparse
from dataclasses import asdict, dataclass
from fractions import Fraction
import json

from affine_spectrum import optimize, problem, reachable


@dataclass(frozen=True)
class Spectrum:
    kind: str
    cutoff: Fraction | None = None
    scale: tuple[Fraction, ...] = ()


def unit_cycle_scale(size, rows):
    """Return h with h[0] = 1 and a_e h[u] = h[v], or an empty tuple."""
    outgoing = [[] for _ in range(size)]
    for e in rows:
        if e.gain == 0:
            return ()
        outgoing[e.tail].append(e)
    scale = [None] * size
    scale[0] = Fraction(1)
    stack = [0]
    while stack:
        tail = stack.pop()
        for e in outgoing[tail]:
            value = e.gain * scale[tail]
            if scale[e.head] is None:
                scale[e.head] = value
                stack.append(e.head)
            elif scale[e.head] != value:
                return ()
    return tuple(scale)


def relaxation_cutoff(size, rows):
    """One LP over the compact polytope of normalized gain-flow certificates."""
    import z3

    weights = [z3.Real(f"p_{i}") for i in range(len(rows))]
    balance = [[] for _ in range(size)]
    for e, p in zip(rows, weights):
        balance[e.tail].append(z3.RealVal(str(e.gain)) * p)
        balance[e.head].append(-p)
    constraints = [p >= 0 for p in weights]
    constraints.append(z3.Sum(weights) == 1)
    constraints.extend(z3.Sum(terms) == 0 for terms in balance)
    objective = z3.Sum([z3.RealVal(str(e.offset)) * p for e, p in zip(rows, weights)])
    optimum = optimize(z3, weights, constraints, objective)
    if optimum is None:
        return None
    return sum((e.offset * p for e, p in zip(rows, optimum)), Fraction(0))


def classify(size, branches):
    """Return all_real, upper_ray, or singleton for a strongly connected graph."""
    rows = problem(size, Fraction(0), branches)
    edges = [(e.tail, e.head, e.gain) for e in rows]
    reverse = [(v, u, gain) for u, v, gain in edges]
    if len(reachable(size, edges, (0,))) != size or len(reachable(size, reverse, (0,))) != size:
        raise ValueError("the full branch graph must be strongly connected")
    scale = unit_cycle_scale(size, rows)
    cutoff = relaxation_cutoff(size, rows)
    if scale:
        if cutoff is None:
            raise RuntimeError("a unit-gain cycle supplies a normalized certificate")
        return Spectrum("singleton", cutoff, scale)
    if cutoff is None:
        return Spectrum("all_real")
    return Spectrum("upper_ray", cutoff)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, help="JSON with vertices and branches")
    args = parser.parse_args()
    with open(args.input, encoding="utf-8") as source:
        data = json.load(source)
    print(json.dumps(asdict(classify(data["vertices"], data["branches"])), default=str))


if __name__ == "__main__":
    main()
