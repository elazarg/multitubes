"""Exact scenario checks for the noncrossing-calendar profile."""
from fractions import Fraction
from random import Random

from delay_calendars import Deadline, Dependency, TimingProblem, example
from delay_calendars_check import brute
from nested_delay_calendars import nested_excess


def word(rng, names):
    if not names:
        return [None] * rng.randrange(3)
    root, *rest = names
    split = rng.randrange(len(rest) + 1)
    return [root, *word(rng, rest[:split]), root, *word(rng, rest[split:])]


def reconvergent(rng, names):
    layers = []
    for name in word(rng, names):
        edges = [
            Dependency(u, v, Fraction(rng.randrange(-4, 9), 3), name,
                       Fraction(rng.randrange(8), 2) if name is not None else 0)
            for u in range(3) for v in range(3) if rng.randrange(4) != 0
        ]
        layers.append(tuple(edges))
    self_deadlines = (
        Deadline(len(layers), 0, 5),
        Deadline(len(layers) // 2, 2, -3),
    )
    return TimingProblem((0, None, 1), tuple(layers), self_deadlines)


def main():
    rng = Random(7326)
    cases = 0
    for size in range(8):
        for _ in range(20):
            problem = reconvergent(rng, tuple(map(str, range(size))))
            cap = rng.randrange(9)
            values, _ = brute(problem, cap)
            assert nested_excess(problem, cap) == tuple(values)
            cases += 1

    try:
        nested_excess(example(), 2)
    except ValueError:
        pass
    else:
        raise AssertionError("Crossing supplier/crew calendars were accepted.")

    depth = 120
    labels = tuple(range(1, depth + 1))
    deep = TimingProblem(
        (0,),
        tuple((Dependency(0, 0, 1, str(value), value),)
              for value in (*labels, *reversed(labels))),
        (Deadline(2 * depth, 0, 2 * depth),),
    )
    assert nested_excess(deep, 4) == (0, 240, 478, 714, 948)
    print(f"{cases} independent scenario comparisons passed, plus crossing rejection "
          f"and a closed-form depth-{depth} profile.")


if __name__ == "__main__":
    main()
