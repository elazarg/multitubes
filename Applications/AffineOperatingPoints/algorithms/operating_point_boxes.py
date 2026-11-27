"""Find the greatest max-affine operating point in each box of channel bounds."""

import argparse
from fractions import Fraction
from heapq import heapify, heappop, heappush
import json

from affine_spectrum import rational
from operating_point_poset import _cyclic_components, _from_seeds, _prepare


class OperatingPointBoxes:
    """Index a strongly connected network with gain product above one on every cycle."""

    def __init__(self, vertices, level, branches):
        _, self._scale, self.upper, self._outgoing, tight = _prepare(
            vertices, level, branches
        )
        self._incoming = [{} for _ in range(vertices)]
        for tail, neighbors in enumerate(self._outgoing):
            for head, transfers in neighbors.items():
                self._incoming[head][tail] = transfers
        self._seeds = tuple(part[0] for part in _cyclic_components(tight))
        if not self._seeds:
            raise RuntimeError("the greatest relaxation must have a tight directed cycle")

    def match_box(self, bounds):
        """Return the greatest operating point in bounds, or None.

        Each key is a vertex and its value is (lower, upper). A missing
        vertex or a None endpoint means there is no bound there.
        """
        zero = Fraction(0)
        required = [zero] * len(self.upper)
        lowers = {}
        for vertex, (lower, upper) in bounds.items():
            if type(vertex) is not int or not 0 <= vertex < len(self.upper):
                raise ValueError("box endpoints must have valid channel IDs")
            lower = rational(lower) if lower is not None else None
            upper = rational(upper) if upper is not None else None
            if lower is not None:
                lowers[vertex] = lower
                if upper is not None and lower > upper:
                    return None
            if upper is not None:
                required[vertex] = max(zero, (self.upper[vertex] - upper) / self._scale[vertex])

        # Propagate the required deficits backwards to get the greatest capped relaxation.
        queue = [(-value, vertex) for vertex, value in enumerate(required) if value > 0]
        heapify(queue)
        while queue:
            negative, head = heappop(queue)
            value = -negative
            if value != required[head]:
                continue
            for tail, transfers in self._incoming[head].items():
                candidate = max((value - slack) / gain for gain, slack in transfers)
                if candidate > required[tail]:
                    required[tail] = candidate
                    heappush(queue, (-candidate, tail))

        # Join the principals whose seeds retain their original relaxation readings.
        eligible = [seed for seed in self._seeds if required[seed] == 0]
        if not eligible:
            return None
        result = _from_seeds(self._outgoing, self._scale, self.upper, eligible)
        if any(result[vertex] < lower for vertex, lower in lowers.items()):
            return None
        return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, help="JSON graph, level and boxes")
    args = parser.parse_args()
    with open(args.input, encoding="utf-8") as source:
        data = json.load(source)
    index = OperatingPointBoxes(data["vertices"], data["level"], data["branches"])
    answers = [index.match_box({int(vertex): pair for vertex, pair in box.items()})
               for box in data["boxes"]]
    print(json.dumps(answers, default=str))


if __name__ == "__main__":
    main()
