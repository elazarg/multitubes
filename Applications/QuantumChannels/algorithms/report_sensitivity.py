#!/usr/bin/env python3
"""Minimum context cost making each hit report pivotal in a finite instrument."""

import argparse
from dataclasses import dataclass
from fractions import Fraction
from heapq import merge
from itertools import chain
import json
from math import gcd, lcm


@dataclass(frozen=True, slots=True)
class Round:
    cost: Fraction
    hit: tuple
    cont: tuple


@dataclass(frozen=True, slots=True)
class Trace:
    time: int
    rest: "Trace | None"


@dataclass(frozen=True, slots=True)
class Entry:
    cost: Fraction
    vector: tuple
    hits: Trace | None = None


@dataclass(frozen=True, slots=True)
class Context:
    cost: Fraction
    before: Trace | None
    after: Trace | None

    def suppressed(self):
        """Chronological report indices in the context, excluding the pivotal index."""
        def positions(trace):
            while trace is not None:
                yield trace.time
                trace = trace.rest

        return tuple(chain(reversed(tuple(positions(self.before))), positions(self.after)))


def dot(left, right):
    return sum(x * y for x, y in zip(left, right))


def matvec(matrix, vector):
    return tuple(dot(row, vector) for row in matrix)


def primitive(vector):
    divisor = gcd(*vector)
    if divisor == 0:
        return vector
    if next(x for x in vector if x) < 0:
        divisor = -divisor
    return tuple(x // divisor for x in vector)


def integer_vector(vector):
    denominator = lcm(*(x.denominator for x in vector))
    return primitive(tuple(x.numerator * (denominator // x.denominator) for x in vector))


def integer_matrix(matrix):
    shape = len(matrix[0])
    flat = integer_vector(tuple(chain.from_iterable(matrix)))
    return tuple(flat[i : i + shape] for i in range(0, len(flat), shape))


def cheapest_basis(candidates, dimension):
    """Retain a basis at every cutoff from candidates in ascending cost order."""
    basis = []
    pivots = {}
    for entry in candidates:
        remainder = entry.vector
        for index, pivot in sorted(pivots.items()):
            if remainder[index]:
                remainder = primitive(tuple(
                    pivot[index] * x - remainder[index] * y for x, y in zip(remainder, pivot)
                ))
        first_nonzero = next((index for index, x in enumerate(remainder) if x), None)
        if first_nonzero is not None:
            pivots[first_nonzero] = remainder
            basis.append(entry)
            if len(basis) == dimension:
                break
    return basis


def extend(basis, stage, index, dimension, backward=False):
    def candidates(family, cost, is_hit):
        matrices = tuple(tuple(zip(*matrix)) for matrix in family) if backward else family
        for entry in basis:
            trace = Trace(index, entry.hits) if is_hit else entry.hits
            for matrix in matrices:
                vector = primitive(matvec(matrix, entry.vector))
                if any(vector):
                    yield Entry(entry.cost + cost, vector, trace)

    ordered = merge(
        candidates(stage.cont, 0, False),
        candidates(stage.hit, stage.cost, True),
        key=lambda entry: entry.cost,
    )
    return cheapest_basis(ordered, dimension)


def join(prefix, stage, suffix):
    best = None
    for matrix in stage.hit:
        for left in prefix:
            image = matvec(matrix, left.vector)
            for right in suffix:
                cost = left.cost + right.cost
                if best is not None and cost >= best.cost:
                    break
                if dot(image, right.vector):
                    best = Context(cost, left.hits, right.hits)
                    break
    return best


def pivotal_contexts(rounds, factors, *, terminal_factors=None):
    """Returns one minimum-cost context per round and None for an impossible round.

    Use read_model for normalized rational instruments from an ordinary JSON input.
    Supply terminal_factors for a positive terminal effect with that Gram decomposition.
    """
    dimension = len(factors[0])
    stages = tuple(Round(
        stage.cost,
        tuple(integer_matrix(matrix) for matrix in stage.hit),
        tuple(integer_matrix(matrix) for matrix in stage.cont),
    ) for stage in rounds)
    prefix = [cheapest_basis(
        (Entry(Fraction(0), integer_vector(vector)) for vector in factors), dimension
    )]
    for index, stage in enumerate(stages[:-1]):
        prefix.append(extend(prefix[-1], stage, index, dimension))
    if terminal_factors is None:
        suffix = [
            Entry(Fraction(0), tuple(int(j == i) for j in range(dimension)))
            for i in range(dimension)
        ]
    else:
        suffix = cheapest_basis(
            (Entry(Fraction(0), integer_vector(vector)) for vector in terminal_factors),
            dimension,
        )
    results = [None] * len(stages)
    for index in reversed(range(len(stages))):
        stage = stages[index]
        results[index] = join(prefix[index], stage, suffix)
        if index:
            suffix = extend(suffix, stage, index, dimension, backward=True)
    return results


def rational(value):
    if isinstance(value, bool) or not isinstance(value, (str, int, Fraction)):
        raise ValueError("use exact numbers or rational strings")
    return Fraction(value)


def read_model(data):
    """Input rho = sum(v v^T for v in state_factors), with unit trace."""
    factors = tuple(tuple(map(rational, vector)) for vector in data["state_factors"])
    dimension = len(factors[0]) if factors else 0
    if not dimension or any(len(vector) != dimension for vector in factors):
        raise ValueError("state_factors must be nonempty and have a common positive dimension")
    if sum(dot(vector, vector) for vector in factors) != 1:
        raise ValueError("the input state must have unit trace")

    stages = []
    for index, stage in enumerate(data["rounds"]):
        cost = rational(stage["cost"])
        if cost < 0:
            raise ValueError(f"round {index} has negative suppression cost")
        hit, cont = (
            tuple(tuple(tuple(map(rational, row)) for row in matrix) for matrix in stage[key])
            for key in ("hit", "continue")
        )
        matrices = hit + cont
        if any(len(m) != dimension or any(len(row) != dimension for row in m) for m in matrices):
            raise ValueError(f"round {index} has a Kraus matrix with the wrong dimension")
        columns = [tuple(zip(*matrix)) for matrix in matrices]
        if any(sum(dot(m[i], m[j]) for m in columns) != (i == j)
               for i in range(dimension) for j in range(i + 1)):
            raise ValueError(f"round {index} has Kraus matrices that do not sum to a channel")
        stages.append(Round(cost, hit, cont))
    return stages, factors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("instrument", help="JSON input with state_factors and rounds")
    parser.add_argument("--witnesses", action="store_true", help="include all context report IDs")
    args = parser.parse_args()
    try:
        with open(args.instrument, encoding="utf-8") as stream:
            data = json.load(stream, parse_float=Fraction)
        stages, factors = read_model(data)
    except (ValueError, KeyError, TypeError, ZeroDivisionError) as error:
        parser.error(str(error))
    result = []
    for index, context in enumerate(pivotal_contexts(stages, factors)):
        row = {"report": index, "additional_cost": str(context.cost) if context is not None else None}
        if args.witnesses:
            row["suppress_other_reports"] = list(context.suppressed()) if context is not None else None
        result.append(row)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
