"""Exact parameter sweeps for finite or contractive periodic scalar storage traces."""
from bisect import bisect_left, bisect_right
from collections import deque
from dataclasses import dataclass, replace
from fractions import Fraction as Q
from itertools import groupby
from math import inf


@dataclass(frozen=True, slots=True)
class Step:
    gain: Q
    shift: Q
    forcing: Q
    lower: Q
    upper: Q
    weight: Q = Q(1)

    def __post_init__(self):
        for field in ("gain", "shift", "forcing", "lower", "upper", "weight"):
            object.__setattr__(self, field, Q(getattr(self, field)))
        if self.gain < 0 or self.forcing < 0 or self.lower > self.upper:
            raise ValueError("Require gain, forcing >= 0 and lower <= upper.")


@dataclass(frozen=True, slots=True)
class Contact:
    lower_through: Q | float
    upper_from: Q | float


@dataclass(frozen=True, slots=True)
class Response:
    knots: tuple[Q, ...]
    lines: tuple[tuple[Q, Q], ...]

    def __call__(self, parameter):
        slope, offset = self.lines[bisect_right(self.knots, parameter)]
        return slope * parameter + offset

    def slopes_at(self, parameter):
        return (
            self.lines[bisect_left(self.knots, parameter)][0],
            self.lines[bisect_right(self.knots, parameter)][0],
        )

    def first_at_least(self, target):
        """Infimum parameter attaining target, with infinities for the two tails.

        Requires a nondecreasing response, as when all observation weights are nonnegative.
        """
        return self._first_crossing(target, 1)

    def first_at_most(self, target):
        """Infimum parameter attaining at most target on a nonincreasing response."""
        return self._first_crossing(-target, -1)

    def _first_crossing(self, target, direction):
        if self.knots:
            first_value = direction * self(self.knots[0])
            last_value = direction * self(self.knots[-1])
        else:
            first_value = last_value = direction * self.lines[0][1]
        first_slope, first_offset = self.lines[0]
        first_slope *= direction
        first_offset *= direction
        if target <= first_value:
            return -inf if not first_slope else (target - first_offset) / first_slope
        last_slope, last_offset = self.lines[-1]
        last_slope *= direction
        last_offset *= direction
        if target > last_value:
            return inf if not last_slope else (target - last_offset) / last_slope

        lower, upper = 0, len(self.knots) - 1
        while lower < upper:
            middle = (lower + upper) // 2
            parameter = self.knots[middle]
            slope, offset = self.lines[middle]
            if direction * (slope * parameter + offset) >= target:
                upper = middle
            else:
                lower = middle + 1
        slope, offset = self.lines[lower]
        return (direction * target - offset) / slope


@dataclass(frozen=True, slots=True)
class Piece:
    start: Q | None
    end: Q | None
    slope: Q
    offset: Q
    born: int


@dataclass(frozen=True, slots=True)
class Sweep:
    contacts: tuple[Contact, ...]
    final: Response
    observed: Response | None
    shortfall: Response | None
    spill: Response | None
    piece_creations: int
    endpoint_checks: int


def line_at(slope, offset, endpoint, infinity):
    if endpoint is not None:
        return slope * endpoint + offset
    assert slope >= 0
    return infinity if slope else offset


class _ResponseSum:
    """Accumulate affine contributions supported on intervals."""
    def __init__(self):
        self.slope = self.offset = Q(0)
        self.deltas = []

    def add(self, start, end, slope, offset):
        if not (slope or offset):
            return
        if start is None:
            self.slope += slope
            self.offset += offset
        else:
            self.deltas.append((start, slope, offset))
        if end is not None:
            self.deltas.append((end, -slope, -offset))

    def finish(self):
        slope, offset = self.slope, self.offset
        lines = [(slope, offset)]
        knots = []
        self.deltas.sort(key=lambda change: change[0])
        for parameter, changes in groupby(self.deltas, key=lambda change: change[0]):
            slope_change = offset_change = Q(0)
            for _, ds, do in changes:
                slope_change += ds
                offset_change += do
            if slope_change or offset_change:
                knots.append(parameter)
                slope += slope_change
                offset += offset_change
                lines.append((slope, offset))
        return Response(tuple(knots), tuple(lines))


class _Trace:
    def __init__(self, slope, offset, aggregate):
        self.pieces = deque([Piece(None, None, slope, offset, 0)])
        self.gain = Q(1)
        self.slope = self.offset = Q(0)
        self.phase = 0
        self.creations = 1
        self.checks = 0
        self.aggregate = aggregate
        # Prefix sums of weighted gains over observable phases, with phase zero weighted zero.
        self.gain_weights = [Q(0), Q(0)]
        self.weight = Q(0)
        self.observed = _ResponseSum()
        self.shortfall = _ResponseSum()
        self.spill = _ResponseSum()

    def coefficient_difference(self, piece, bound):
        return (
            self.gain * piece.slope + self.slope,
            self.gain * piece.offset + self.offset - bound,
        )

    def endpoint(self, slope, offset, endpoint, infinity):
        self.checks += 1
        return line_at(slope, offset, endpoint, infinity)

    def obstacle_piece(self, start, end, bound):
        self.creations += 1
        return Piece(start, end, -self.slope / self.gain,
                     (bound - self.offset) / self.gain, self.phase)

    def discard(self, piece):
        if self.aggregate:
            mass = self.gain_weights[self.phase] - self.gain_weights[piece.born]
            self.observed.add(piece.start, piece.end, mass * piece.slope, mass * piece.offset)

    def record_loss(self, accumulator, start, end, slope, offset):
        if self.weight:
            accumulator.add(start, end, self.weight * slope, self.weight * offset)

    def trim_lower(self, bound):
        while self.pieces:
            piece = self.pieces[0]
            slope, offset = self.coefficient_difference(piece, bound)
            if self.endpoint(slope, offset, piece.end, inf) > 0:
                break
            self.record_loss(self.shortfall, piece.start, piece.end, -slope, -offset)
            self.discard(self.pieces.popleft())
        else:
            self.pieces.append(self.obstacle_piece(None, None, bound))
            return inf

        if self.endpoint(slope, offset, piece.start, -inf) > 0:
            assert piece.start is None
            return -inf

        threshold = -offset / slope
        if piece.start != threshold:
            self.record_loss(self.shortfall, piece.start, threshold, -slope, -offset)
            self.discard(self.pieces.popleft())
            self.pieces.appendleft(replace(piece, start=threshold, born=self.phase))
            self.creations += 1
        self.pieces.appendleft(self.obstacle_piece(None, threshold, bound))
        return threshold

    def trim_upper(self, bound):
        while self.pieces:
            piece = self.pieces[-1]
            slope, offset = self.coefficient_difference(piece, bound)
            if self.endpoint(slope, offset, piece.start, -inf) < 0:
                break
            self.record_loss(self.spill, piece.start, piece.end, slope, offset)
            self.discard(self.pieces.pop())
        else:
            self.pieces.append(self.obstacle_piece(None, None, bound))
            return -inf

        if self.endpoint(slope, offset, piece.end, inf) < 0:
            assert piece.end is None
            return inf

        threshold = -offset / slope
        if piece.end != threshold:
            self.record_loss(self.spill, threshold, piece.end, slope, offset)
            self.discard(self.pieces.pop())
            self.pieces.append(replace(piece, end=threshold, born=self.phase))
            self.creations += 1
        self.pieces.append(self.obstacle_piece(threshold, None, bound))
        return threshold

    def advance(self, step, observable):
        self.phase += 1
        self.weight = step.weight if self.aggregate and observable else Q(0)
        if step.gain:
            self.gain *= step.gain
            self.slope = step.gain * self.slope + step.forcing
            self.offset = step.gain * self.offset + step.shift
        else:
            while self.pieces:
                self.discard(self.pieces.pop())
            self.gain, self.slope, self.offset = Q(1), step.forcing, step.shift
            self.pieces.append(Piece(None, None, Q(0), Q(0), self.phase))
            self.creations += 1

        low = self.trim_lower(step.lower)
        high = self.trim_upper(step.upper)
        contact = Contact(inf, -inf) if step.lower == step.upper else Contact(low, high)

        if self.aggregate:
            self.observed.add(None, None, self.slope * self.weight, self.offset * self.weight)
            self.gain_weights.append(self.gain_weights[-1] + self.gain * self.weight)
        return contact

    def responses(self):
        final = Response(
            tuple(piece.start for piece in list(self.pieces)[1:]),
            tuple((self.gain * piece.slope + self.slope,
                   self.gain * piece.offset + self.offset) for piece in self.pieces),
        )
        if not self.aggregate:
            return final, None, None, None

        self.phase += 1
        for piece in self.pieces:
            self.discard(piece)
        return final, self.observed.finish(), self.shortfall.finish(), self.spill.finish()


def sweep(steps, initial=(0, 0), *, periodic=False, aggregate=True):
    """Return exact phase contacts plus final and optional weighted phase responses.

    The initial seed takes (slope, offset). For periodic replay with product(gain) < 1
    the seed is determined by periodicity. A contact with an infinite threshold is
    either all parameters or empty, according to the inequality direction.
    """
    steps = tuple(steps)
    if periodic:
        gain, slope, offset = Q(1), Q(0), Q(0)
        for step in steps:
            gain *= step.gain
            slope = step.gain * slope + step.forcing
            offset = step.gain * offset + step.shift
        if gain >= 1:
            raise ValueError("Periodic replay requires the product of gains to be below one.")
        initial = (slope / (1 - gain), offset / (1 - gain))

    slope, offset = map(Q, initial)
    if slope < 0:
        raise ValueError("Require a nonnegative seed slope.")

    trace = _Trace(slope, offset, aggregate)
    if periodic:
        for step in steps:
            trace.advance(step, observable=False)
    contacts = tuple(trace.advance(step, observable=True) for step in steps)
    final, observed, shortfall, spill = trace.responses()
    return Sweep(contacts, final, observed, shortfall, spill, trace.creations, trace.checks)
