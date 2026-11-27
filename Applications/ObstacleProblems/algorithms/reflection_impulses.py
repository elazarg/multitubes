"""Exact single-impulse queries on a two-sided reflected trace."""

from bisect import bisect_right
from dataclasses import dataclass
from fractions import Fraction
from typing import NamedTuple

Scalar = int | Fraction | str


@dataclass(frozen=True)
class Stage:
    retention: Scalar
    shift: Scalar
    lo: Scalar
    hi: Scalar
    lower_weight: Scalar = 1
    upper_weight: Scalar = 1


class Response(NamedTuple):
    lower: Fraction  # Change in weighted unmet demand.
    upper: Fraction  # Change in weighted spill.
    state: Fraction  # Unweighted change in state at the deadline.


ZERO = Response(Fraction(0), Fraction(0), Fraction(0))


class _MinSearch:
    """Range minima and first strict crossing of upper thresholds."""

    def __init__(self, heights):
        size = 1 << max(0, (len(heights) - 1).bit_length())
        self.size = size
        self.tree = [(float('inf'), len(heights))] * (2 * size)
        for i, height in enumerate(heights):
            self.tree[size + i] = height, i
        for i in range(size - 1, 0, -1):
            self.tree[i] = min(self.tree[2 * i], self.tree[2 * i + 1])

    def argmin(self, start, stop):
        best = self.tree[self.size + start]
        left, right = start + self.size, stop + self.size
        while left < right:
            if left % 2:
                best = min(best, self.tree[left])
                left += 1
            if right % 2:
                right -= 1
                best = min(best, self.tree[right])
            left //= 2
            right //= 2
        return best[1]

    def first_below(self, start, stop, threshold):
        def search(node, left, right):
            if stop <= left or right <= start or self.tree[node][0] >= threshold:
                return None
            if right == left + 1:
                return left
            middle = (left + right) // 2
            found = search(2 * node, left, middle)
            if found is not None:
                return found
            return search(2 * node + 1, middle, right)

        return search(1, 0, self.size)


class _PositiveIndex:
    def __init__(self, scale, block_stop, deficit, room, lower_weight, upper_weight):
        self.scale, self.block_stop = scale, block_stop
        self.lower_rate = [p * w for p, w in zip(scale, lower_weight)]
        self.upper_rate = [p * w for p, w in zip(scale, upper_weight)]
        self.cumulative = [Fraction(0)]
        self.lower_prefix = [Fraction(0)]
        self.height = []
        for p, d, cap, w in zip(scale, deficit, room, lower_weight):
            self.cumulative.append(self.cumulative[-1] + d / p)
            self.lower_prefix.append(self.lower_prefix[-1] + d * w)
            self.height.append(self.cumulative[-1] + cap / p)
        self.min_search = _MinSearch(self.height)

        # Integrals along chains of the nearest strictly lower future threshold.
        n = len(scale)
        self.chain_area = [Fraction(0)] * n
        self.last_min = list(range(n))
        stack = []
        for i in reversed(range(n)):
            if i + 1 == block_stop[i]:
                stack.clear()
            while stack and self.height[stack[-1]] >= self.height[i]:
                stack.pop()
            if stack:
                parent = stack[-1]
                h = self.height[i] - self.height[parent]
                self.chain_area[i] = self.chain_area[parent] + h * self.upper_rate[parent]
                self.last_min[i] = self.last_min[parent]
            stack.append(i)

    def _evaluate(self, start, stop, level, minimum, first_upper, last_lower):
        ceiling = min(level, self.height[minimum])
        lower_end = min(ceiling, self.cumulative[stop])
        lower = self.lower_prefix[last_lower] - self.lower_prefix[start]
        if last_lower < stop:
            lower += (lower_end - self.cumulative[last_lower]) * self.lower_rate[last_lower]
        upper = Fraction(0)
        if first_upper is not None:
            upper = (level - self.height[first_upper]) * self.upper_rate[first_upper]
            upper += self.chain_area[first_upper] - self.chain_area[minimum]
        state = max(Fraction(0), ceiling - self.cumulative[stop]) * self.scale[stop - 1]
        return Response(-lower, upper, state)

    def query(self, start, amplitude, stop):
        if not amplitude:
            return ZERO
        effective = min(stop, self.block_stop[start])
        level = self.cumulative[start] + amplitude / self.scale[start]
        minimum = self.min_search.argmin(start, effective)
        first_upper = None
        if self.height[minimum] < level:
            first_upper = self.min_search.first_below(start, effective, level)
        lower_end = min(level, self.height[minimum], self.cumulative[effective])
        last_lower = bisect_right(self.cumulative, lower_end, start, effective + 1) - 1
        response = self._evaluate(start, effective, level, minimum, first_upper, last_lower)
        if effective < stop:
            return Response(response.lower, response.upper, Fraction(0))
        return response

    def all_stages(self, amplitude):
        n = len(self.scale)
        if not amplitude:
            return [ZERO] * n
        levels = [c + amplitude / p for c, p in zip(self.cumulative, self.scale)]
        if any(levels[i] < levels[i - 1] and self.block_stop[i] == self.block_stop[i - 1]
               for i in range(1, n)):
            return [self.query(i, amplitude, n) for i in range(n)]

        pending = []
        first_upper = [None] * n
        for i, level in enumerate(levels):
            if i and self.block_stop[i] != self.block_stop[i - 1]:
                pending.clear()
            pending.append(i)
            while pending and levels[pending[-1]] > self.height[i]:
                first_upper[pending.pop()] = i

        responses = []
        last_lower = 0
        for i, level in enumerate(levels):
            stop = self.block_stop[i]
            minimum = self.last_min[i]
            lower_end = min(level, self.height[minimum], self.cumulative[stop])
            last_lower = max(last_lower, i)
            while last_lower < stop and self.cumulative[last_lower + 1] <= lower_end:
                last_lower += 1
            response = self._evaluate(i, stop, level, minimum, first_upper[i], last_lower)
            if stop < n:
                response = Response(response.lower, response.upper, Fraction(0))
            responses.append(response)
        return responses


class ImpulseIndex:
    """Index weighted regulator changes from one signed addition to a stage's raw input.

    Stages and deadlines use zero-based inclusive indexes. Lower and upper weights are
    fixed at construction and may differ at each stage. All returned numbers are exact
    Python fractions. Zero retention at a later stage ends the effect on the trajectory.
    """

    def __init__(self, stages, initial: Scalar):
        x = Fraction(initial)
        scale, reset, lower_weight, upper_weight = [], [], [], []
        lower, upper, top_room, bottom_room = [], [], [], []
        for i, stage in enumerate(stages):
            a, b = Fraction(stage.retention), Fraction(stage.shift)
            lo, hi = Fraction(stage.lo), Fraction(stage.hi)
            if a < 0 or lo > hi:
                raise ValueError('expected nonnegative retention and ordered bounds')
            raw = a * x + b
            x = min(hi, max(lo, raw))
            reset.append(a == 0)
            scale.append(Fraction(1) if not i or a == 0 else a * scale[-1])
            lower.append(max(Fraction(0), lo - raw))
            upper.append(max(Fraction(0), raw - hi))
            top_room.append(hi - x)
            bottom_room.append(x - lo)
            lower_weight.append(Fraction(stage.lower_weight))
            upper_weight.append(Fraction(stage.upper_weight))
        n = len(scale)
        block_stop = [n] * n
        stop = n
        for i in reversed(range(n)):
            block_stop[i] = stop
            if reset[i]:
                stop = i
        self.n = n
        self.positive = _PositiveIndex(scale, block_stop, lower, top_room, lower_weight, upper_weight)
        self.negative = _PositiveIndex(scale, block_stop, upper, bottom_room, upper_weight, lower_weight)

    def query(self, stage: int, amplitude: Scalar, deadline: int | None = None) -> Response:
        """Return the cumulative changes through an inclusive deadline (default last stage)."""
        if deadline is None:
            deadline = self.n - 1
        if not 0 <= stage <= deadline < self.n:
            raise ValueError('expected 0 <= stage <= deadline < number of stages')
        amplitude = Fraction(amplitude)
        if amplitude >= 0:
            return self.positive.query(stage, amplitude, deadline + 1)
        lower, upper, state = self.negative.query(stage, -amplitude, deadline + 1)
        return Response(upper, lower, -state)

    def all_stages(self, amplitude: Scalar) -> list[Response]:
        """Evaluate the same impulse separately at every stage through the last deadline."""
        amplitude = Fraction(amplitude)
        if amplitude >= 0:
            return self.positive.all_stages(amplitude)
        return [Response(upper, lower, -state)
                for lower, upper, state in self.negative.all_stages(-amplitude)]
