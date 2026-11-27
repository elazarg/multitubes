"""Minimum-cost inverse binary dilation after a contiguous source-site outage."""

from collections import deque
from dataclasses import dataclass

Interval = tuple[int, int]


@dataclass(frozen=True)
class Layer:
    """One registered layer, with inclusive one-based intervals in its parent."""

    parent: int  # 0 is the seed layer. Other layers are numbered from 1.
    rows: tuple[Interval | None, ...]
    required: tuple[int, ...] = ()
    forbidden: tuple[int, ...] = ()


@dataclass(frozen=True)
class Solution:
    cost: int
    sites: tuple[int, ...]


class _DepthMinimum:
    """Constant-time RMQ on an Euler depth array with adjacent differences of ±1."""

    def __init__(self, depths):
        self.depths = depths
        self.width = max(1, (len(depths).bit_length() - 1) // 2)
        self.blocks = []
        tables = [None] * (1 << self.width)
        block_minima = []
        for start in range(0, len(depths), self.width):
            relative = [0]
            mask = 0
            stop = min(start + self.width, len(depths))
            for index in range(start + 1, stop):
                step = depths[index] - depths[index - 1]
                mask = (mask << 1) | (step > 0)
                relative.append(relative[-1] + step)
            shape = (1 << (len(relative) - 1)) | mask
            if tables[shape] is None:
                table = []
                for left in range(len(relative)):
                    best = left
                    suffix = []
                    for right in range(left, len(relative)):
                        if relative[right] < relative[best]:
                            best = right
                        suffix.append(best)
                    table.append(suffix)
                tables[shape] = table
            table = tables[shape]
            self.blocks.append(table)
            block_minima.append(start + table[0][-1])

        self.levels = [block_minima]
        span = 2
        while span <= len(block_minima):
            previous = self.levels[-1]
            half = span // 2
            level = [
                self._better(previous[index], previous[index + half])
                for index in range(len(block_minima) - span + 1)
            ]
            self.levels.append(level)
            span *= 2

    def _better(self, left, right):
        return left if self.depths[left] <= self.depths[right] else right

    def _in_block(self, block, left, right):
        return block * self.width + self.blocks[block][left][right - left]

    def query(self, left, right):
        low, low_offset = divmod(left, self.width)
        high, high_offset = divmod(right, self.width)
        if low == high:
            return self._in_block(low, low_offset, high_offset)

        a = self._in_block(low, low_offset, self.width - 1)
        b = self._in_block(high, 0, high_offset)
        best = self._better(a, b)
        if high - low > 1:
            size = high - low - 1
            level = size.bit_length() - 1
            middle = self.levels[level]
            best = self._better(best, middle[low + 1])
            best = self._better(best, middle[high - (1 << level)])
        return best


class _RangeMinimum:
    """Rightmost minimum by Cartesian tree and Euler-tour LCA."""

    def __init__(self, values):
        length = len(values)
        left = [-1] * length
        right = [-1] * length
        spine = []
        for index, value in enumerate(values):
            child = -1
            while spine and values[spine[-1]] >= value:
                child = spine.pop()
            left[index] = child
            if spine:
                right[spine[-1]] = index
            spine.append(index)

        first = [-1] * length
        tour = []
        depths = []
        visits = [(spine[0], 0, True)]
        while visits:
            vertex, depth, enter = visits.pop()
            if enter:
                first[vertex] = len(tour)
                for child in (right[vertex], left[vertex]):
                    if child >= 0:
                        visits.append((vertex, depth, False))
                        visits.append((child, depth + 1, True))
            tour.append(vertex)
            depths.append(depth)
        self.first = first
        self.tour = tour
        self.rmq = _DepthMinimum(depths)

    def query(self, left, right):
        a, b = self.first[left], self.first[right]
        return self.tour[self.rmq.query(min(a, b), max(a, b))]


class _MaximumRise:
    """Chen–Chao range maximum-sum segment queries on successive differences."""

    def __init__(self, values):
        self.values = values
        self.low = _RangeMinimum(values)
        spine = []
        self.partner = []
        self.rise = []
        for end, value in enumerate(values):
            start = end
            while spine and values[spine[-1]] < value:
                earlier = self.partner[spine.pop()]
                if values[earlier] < values[start]:
                    start = earlier
            self.partner.append(start)
            self.rise.append(value - values[start])
            spine.append(end)
        self.high = _RangeMinimum([-rise for rise in self.rise])

    def query(self, left, right):
        if left >= right:
            return None
        end = self.high.query(left + 1, right)
        if self.rise[end] == 0:
            return None
        start = self.partner[end]
        if start >= left:
            return start, end
        start = self.low.query(left, end - 1)
        if end < right:
            later = self.high.query(end + 1, right)
            if self.rise[later] > self.values[end] - self.values[start]:
                return self.partner[later], later
        return start, end


def _support_index(supports):
    """For an ordered parent layer, index its nonempty supports and their gaps."""
    count = [0]
    intervals = []
    gaps = [0]
    for support in supports:
        if support is not None:
            if intervals:
                left, right = intervals[-1]
                if support[0] < left or support[1] < right:
                    raise ValueError("parent supports must have nondecreasing endpoints")
                gaps.append(gaps[-1] + (support[0] > right + 1))
            intervals.append(support)
        count.append(len(intervals))
    return count, intervals, gaps


def _image_constraints(source_size, layers):
    """Read the compact relations without expanding their incidences."""
    supports = [[(site, site) for site in range(1, source_size + 1)]]
    indices = [None]
    positive = []
    banned_deltas = [0] * (source_size + 2)
    for number, layer in enumerate(layers, 1):
        if not 0 <= layer.parent < len(supports):
            raise ValueError("a parent layer must precede its child")
        if indices[layer.parent] is None:
            indices[layer.parent] = _support_index(supports[layer.parent])
        count, intervals, gaps = indices[layer.parent]
        output = []
        for row in layer.rows:
            if row is None:
                output.append(None)
                continue
            left, right = row
            if not 1 <= left <= right < len(count):
                raise ValueError("predecessor interval is outside its parent layer")
            first, stop = count[left - 1], count[right]
            if first == stop:
                output.append(None)
                continue
            last = stop - 1
            if gaps[last] != gaps[first]:
                raise ValueError("an output's reverse support has a hole")
            output.append((intervals[first][0], intervals[last][1]))
        for site in layer.required:
            if not 1 <= site <= len(output):
                raise ValueError("required site is outside its layer")
            positive.append((output[site - 1], (number, site)))
        for site in layer.forbidden:
            if not 1 <= site <= len(output):
                raise ValueError("forbidden site is outside its layer")
            support = output[site - 1]
            if support is not None:
                left, right = support
                banned_deltas[left] += 1
                banned_deltas[right + 1] -= 1
        supports.append(output)
        indices.append(None)
    return positive, banned_deltas


def _hitting_paths(weights, intervals):
    """Two linear sliding-minimum DPs on the implicit path of consecutive choices."""
    terminal = len(weights) - 1
    end = [terminal] * (terminal + 1)
    blocker = [None] * terminal
    for left, right, observation in intervals:
        if right < end[left - 1]:
            end[left - 1] = right
            blocker[left - 1] = observation
    for site in range(terminal - 2, -1, -1):
        if end[site + 1] < end[site]:
            end[site] = end[site + 1]
            blocker[site] = blocker[site + 1]

    forward = [0] * (terminal + 1)
    prev = [0] * (terminal + 1)
    window = deque([0])
    for site in range(1, terminal + 1):
        while end[window[0]] < site:
            window.popleft()
        prev[site] = window[0]
        forward[site] = weights[site] + forward[prev[site]]
        while window and forward[window[-1]] >= forward[site]:
            window.pop()
        window.append(site)

    backward = [0] * (terminal + 1)
    next_site = [terminal] * (terminal + 1)
    window = deque([terminal])
    for site in range(terminal - 1, -1, -1):
        while window[0] > end[site]:
            window.popleft()
        next_site[site] = window[0]
        backward[site] = weights[site] + backward[next_site[site]]
        while window and backward[window[-1]] >= backward[site]:
            window.pop()
        window.append(site)
    return end, blocker, forward, prev, backward, next_site


class SeedBlockIndex:
    """Index an inverse design through binary dilation layers with fixed observations."""

    def __init__(self, costs, layers):
        costs = tuple(costs)
        if any(type(cost) is not int or cost < 0 for cost in costs):
            raise ValueError("source costs must be nonnegative integers")
        self.source_size = len(costs)
        positive, banned_deltas = _image_constraints(len(costs), layers)

        rank = [0]
        sites = [0]
        weights = [0]
        banned = 0
        for site, cost in enumerate(costs, 1):
            banned += banned_deltas[site]
            if banned == 0:
                sites.append(site)
                weights.append(cost)
            rank.append(len(sites) - 1)
        self.eligible_sites = tuple(sites[1:])
        self.rank = rank
        self.weights = weights + [0]
        self.terminal = len(sites)
        self.infeasible_observation = None

        intervals = []
        for support, observation in positive:
            if support is None:
                self.infeasible_observation = observation
                return
            left, right = support
            if rank[left - 1] == rank[right]:
                self.infeasible_observation = observation
                return
            intervals.append((rank[left - 1] + 1, rank[right], observation))
        (
            self.end, self.blocker, self.forward, self.prev, self.backward, self.next
        ) = _hitting_paths(self.weights, intervals)

        ceiling = 3 * (1 + sum(weights))
        labels = []
        values = []
        self.prefix_event = [0] * self.terminal
        self.suffix_event = [0] * (self.terminal + 1)
        prefix = 0
        for suffix in range(1, self.terminal + 1):
            self.suffix_event[suffix] = len(values)
            labels.append(suffix)
            values.append(self.backward[suffix] - ceiling)
            while prefix < self.terminal and self.end[prefix] == suffix:
                self.prefix_event[prefix] = len(values)
                labels.append(prefix)
                values.append(ceiling - self.forward[prefix])
                prefix += 1
        self.labels = labels
        self.rise = _MaximumRise(values)

    def _cut(self, block):
        left, right = block
        if not 1 <= left <= right <= self.source_size:
            raise ValueError("outage must be an inclusive interval of physical source sites")
        return self.rank[left - 1], self.rank[right] + 1

    def _bridge(self, block):
        if block is None:
            if self.infeasible_observation is None:
                return self.prev[self.terminal], self.terminal
            return None

        prefix, suffix = self._cut(block)
        if self.infeasible_observation is not None or suffix > self.end[prefix]:
            return None
        start, end = self.rise.query(self.suffix_event[suffix], self.prefix_event[prefix])
        return self.labels[end], self.labels[start]

    def blocking_observation(self, block=None):
        """Return a (layer, site) that cannot be hit, or None if feasible."""
        if block is None:
            return self.infeasible_observation
        prefix, suffix = self._cut(block)
        if self.infeasible_observation is not None:
            return self.infeasible_observation
        if suffix > self.end[prefix]:
            return self.blocker[prefix]
        return None

    def min_cost(self, block=None):
        """Minimum cost after excluding a block, or None when infeasible."""
        bridge = self._bridge(block)
        if bridge is None:
            return None
        prefix, suffix = bridge
        return self.forward[prefix] + self.backward[suffix]

    def min_cost_including(self, site):
        """Minimum no-outage cost when a specific physical site must be used."""
        if not 1 <= site <= self.source_size:
            raise ValueError("site is outside the source layer")
        rank = self.rank[site]
        if self.infeasible_observation is not None or rank == self.rank[site - 1]:
            return None
        return self.forward[rank] + self.backward[rank] - self.weights[rank]

    def solve(self, block=None):
        """Return one minimum-cost seed mask in reconstruction time O(mask size + 1)."""
        bridge = self._bridge(block)
        if bridge is None:
            return None
        prefix, suffix = bridge
        cost = self.forward[prefix] + self.backward[suffix]
        sites = []
        while prefix != 0:
            sites.append(self.eligible_sites[prefix - 1])
            prefix = self.prev[prefix]
        sites.reverse()
        while suffix != self.terminal:
            sites.append(self.eligible_sites[suffix - 1])
            suffix = self.next[suffix]
        return Solution(cost, tuple(sites))

    def shortest_budget_break(self, budget):
        """Find a shortest nonempty outage that makes the cost exceed budget."""
        right = 1
        best = None
        for left in range(1, self.source_size + 1):
            right = max(right, left)
            while right <= self.source_size:
                cost = self.min_cost((left, right))
                if cost is None or cost > budget:
                    break
                right += 1
            if right > self.source_size:
                break
            if best is None or right - left < best[1] - best[0]:
                best = (left, right)
        return best


def demonstration():
    """Two camera samplings of a 15-site scan line."""
    size = 15
    costs = (2, 2, 1, 4, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 2)
    rows = tuple((max(1, site - 1), min(size, site + 1)) for site in range(1, size + 1))
    layers = (
        Layer(0, rows),
        Layer(1, ((1, 1), (4, 4), (7, 7), (10, 10), (15, 15)), (2, 3, 4), (1, 5)),
        Layer(0, ((3, 7), (4, 4), (5, 9), (7, 11), (12, 14)), (1, 3, 4), (2, 5)),
    )
    return costs, layers


def main():
    costs, layers = demonstration()
    index = SeedBlockIndex(costs, layers)
    print("Camera A .###.   Camera B #.##.")
    for sites in ((3, 6, 11), (5, 7, 9)):
        image = "".join("#" if site in sites else "." for site in range(1, len(costs) + 1))
        print(f"Matching seed image {image}   sites {sites}   cost 3")
    for block in (None, (6, 6), (7, 7), (6, 7), (6, 8)):
        answer = index.solve(block)
        print(f"Outage {str(block):>6}   {answer if answer is not None else 'infeasible'}")
        if answer is None:
            print(f"  Unreachable required detector {index.blocking_observation(block)}")
    print(f"Shortest outage breaking budget 3   {index.shortest_budget_break(3)}")


if __name__ == "__main__":
    main()
