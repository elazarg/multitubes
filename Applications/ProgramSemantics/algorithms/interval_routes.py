"""Index fixed routes that work for every possible state in an input interval."""

from bisect import bisect_right
from collections import deque
from dataclasses import dataclass
from itertools import accumulate
from typing import Callable


@dataclass(frozen=True)
class TableEdge:
    name: str
    source: int
    target: int
    first: int
    lower: tuple[int, ...]
    upper: tuple[int, ...]


class GaugeError(ValueError):
    """Some strict within-fiber order is forced to be non-strict around a cycle."""


def _components(graph, reverse):
    """Number strongly connected components in topological order."""
    seen = bytearray(len(graph))
    order = []
    for root in range(len(graph)):
        if seen[root]:
            continue
        seen[root] = 1
        stack = [(root, iter(graph[root]))]
        while stack:
            vertex, neighbors = stack[-1]
            neighbor = next(neighbors, None)
            if neighbor is None:
                order.append(vertex)
                stack.pop()
            elif not seen[neighbor]:
                seen[neighbor] = 1
                stack.append((neighbor, iter(graph[neighbor])))

    component = [-1] * len(graph)
    count = 0
    for root in reversed(order):
        if component[root] >= 0:
            continue
        component[root] = count
        stack = [root]
        while stack:
            vertex = stack.pop()
            for neighbor in reverse[vertex]:
                if component[neighbor] < 0:
                    component[neighbor] = count
                    stack.append(neighbor)
        count += 1
    return component, count


def _check_goal(sizes, target, band):
    if not sizes or min(sizes) <= 0:
        raise ValueError("fibers must be nonempty")
    first, last = band
    if not 0 <= target < len(sizes) or not 0 <= first <= last < sizes[target]:
        raise ValueError("invalid goal band")


def _check_query(sizes, vertex, first, last):
    if not 0 <= vertex < len(sizes) or not 0 <= first <= last < sizes[vertex]:
        raise ValueError("invalid input interval")


class TableRoutes:
    """Linear-time frontier index for monotone tables with an upper-endpoint gauge."""

    def __init__(self, sizes, edges, target, band):
        sizes, edges = tuple(sizes), tuple(edges)
        _check_goal(sizes, target, band)
        offsets = list(accumulate(sizes, initial=0))
        size = offsets[-1]
        graph = [[] for _ in range(size)]
        reverse = [[] for _ in range(size)]
        incoming = [[] for _ in range(size)]
        vertex_offset = [0] * size

        def arc(start, finish):
            graph[start].append(finish)
            reverse[finish].append(start)

        for start, finish in zip(offsets, offsets[1:]):
            vertex_offset[start:finish] = [start] * (finish - start)
            for row in range(start, finish - 1):
                arc(row, row + 1)

        for edge_id, edge in enumerate(edges):
            if not 0 <= edge.source < len(sizes) or not 0 <= edge.target < len(sizes):
                raise ValueError(f"invalid endpoint on {edge.name}")
            domain_size = len(edge.lower)
            if len(edge.upper) != domain_size or not (
                0 <= edge.first <= edge.first + domain_size <= sizes[edge.source]
            ):
                raise ValueError(f"invalid domain on {edge.name}")
            start = offsets[edge.source] + edge.first
            finish = offsets[edge.target]
            previous_low = previous_high = -1
            for index, (low, high) in enumerate(zip(edge.lower, edge.upper)):
                if not (
                    0 <= low <= high < sizes[edge.target]
                    and previous_low <= low
                    and previous_high <= high
                ):
                    raise ValueError(f"invalid monotone endpoints on {edge.name}")
                arc(start + index, finish + high)
                incoming[finish + low].append((edge_id, index))
                previous_low, previous_high = low, high

        gauge, count = _components(graph, reverse)
        for vertex, (start, finish) in enumerate(zip(offsets, offsets[1:])):
            for row in range(start, finish - 1):
                if gauge[row] == gauge[row + 1]:
                    raise GaugeError(f"gauge fails at vertex {vertex}, states {row - start} and {row + 1 - start}")
        del graph, reverse

        buckets = [[] for _ in range(count)]
        ceiling = [-1] * size
        settled = bytearray(size)
        route = [None] * size
        cursor = [len(edge.upper) - 1 for edge in edges]
        goal_start = offsets[target]

        for initial in range(band[0], band[1] + 1):
            row = goal_start + initial
            ceiling[row] = band[1]
            buckets[gauge[goal_start + band[1]]].append(row)

        for priority in range(count - 1, -1, -1):
            bucket = buckets[priority]
            while bucket:
                row = bucket.pop()
                if settled[row]:
                    continue
                settled[row] = 1
                right = ceiling[row]
                assert gauge[vertex_offset[row] + right] == priority
                for edge_id, index in incoming[row]:
                    edge = edges[edge_id]
                    last = cursor[edge_id]
                    while last >= 0 and edge.upper[last] > right:
                        last -= 1
                    cursor[edge_id] = last
                    if last < index:
                        continue
                    start = offsets[edge.source]
                    before = start + edge.first + index
                    candidate = edge.first + last
                    if candidate <= ceiling[before]:
                        continue
                    key = gauge[start + candidate]
                    assert key <= priority and not settled[before]
                    ceiling[before] = candidate
                    route[before] = (edge_id, row)
                    buckets[key].append(before)

        self.sizes = sizes
        self.edges = edges
        self.offsets = offsets
        self.ceiling = ceiling
        self.gauge = gauge
        self._route = route

    def accepts(self, vertex, first, last):
        _check_query(self.sizes, vertex, first, last)
        return last <= self.ceiling[self.offsets[vertex] + first]

    def route(self, vertex, first, last):
        """Return a list of edge IDs, or None if no common route works."""
        if not self.accepts(vertex, first, last):
            return None
        row = self.offsets[vertex] + first
        result = []
        while self._route[row] is not None:
            edge_id, row = self._route[row]
            result.append(edge_id)
        return result


@dataclass(frozen=True)
class FormulaEdge:
    name: str
    source: int
    target: int
    first: int
    last: int
    lower: Callable[[int], int]
    upper: Callable[[int], int]

    def preimage(self, first, last):
        """Both endpoint functions are assumed nondecreasing on the domain."""
        left = _first_true(self.first, self.last + 1, lambda x: self.lower(x) >= first)
        right = _first_true(self.first, self.last + 1, lambda x: self.upper(x) > last) - 1
        if left <= right:
            return left, right
        return None


def _first_true(low, high, predicate):
    while low < high:
        mid = (low + high) // 2
        if predicate(mid):
            high = mid
        else:
            low = mid + 1
    return low


@dataclass(frozen=True)
class _Interval:
    first: int
    last: int
    edge_id: int | None = None
    suffix: '_Interval | None' = None


class FormulaRoutes:
    """Compact frontier index for an acyclic graph of monotone endpoint formulas."""

    def __init__(self, sizes, edges, target, band):
        sizes, edges = tuple(sizes), tuple(edges)
        _check_goal(sizes, target, band)
        outgoing = [[] for _ in sizes]
        indegree = [0] * len(sizes)
        for edge_id, edge in enumerate(edges):
            if not 0 <= edge.source < len(sizes) or not 0 <= edge.target < len(sizes):
                raise ValueError(f"invalid endpoint on {edge.name}")
            if not 0 <= edge.first <= edge.last < sizes[edge.source]:
                raise ValueError(f"invalid domain on {edge.name}")
            outgoing[edge.source].append(edge_id)
            indegree[edge.target] += 1
        queue = deque(vertex for vertex, degree in enumerate(indegree) if degree == 0)
        order = []
        while queue:
            vertex = queue.popleft()
            order.append(vertex)
            for edge_id in outgoing[vertex]:
                destination = edges[edge_id].target
                indegree[destination] -= 1
                if indegree[destination] == 0:
                    queue.append(destination)
        if len(order) != len(sizes):
            raise ValueError("compact solver requires an acyclic graph")

        frontier = [[] for _ in sizes]
        for vertex in reversed(order):
            candidates = [_Interval(*band)] if vertex == target else []
            for edge_id in outgoing[vertex]:
                edge = edges[edge_id]
                for suffix in frontier[edge.target]:
                    preimage = edge.preimage(suffix.first, suffix.last)
                    if preimage is not None:
                        candidates.append(_Interval(*preimage, edge_id, suffix))
            candidates.sort(key=lambda item: (item.first, -item.last))
            for candidate in candidates:
                if not frontier[vertex] or frontier[vertex][-1].last < candidate.last:
                    frontier[vertex].append(candidate)

        self.sizes = sizes
        self.edges = edges
        self.frontier = frontier
        self._starts = [[item.first for item in intervals] for intervals in frontier]

    def route(self, vertex, first, last):
        """Return a list of edge IDs, or None if no common route works."""
        _check_query(self.sizes, vertex, first, last)
        index = bisect_right(self._starts[vertex], first) - 1
        if index < 0 or last > self.frontier[vertex][index].last:
            return None
        current = self.frontier[vertex][index]
        result = []
        while current.edge_id is not None:
            result.append(current.edge_id)
            current = current.suffix
        return result


def examples():
    table_edges = (
        TableEdge("standardize", 0, 0, 0, (1, 1, 3, 3), (3, 3, 3, 3)),
        TableEdge("promote", 0, 0, 0, (0, 3, 3, 3), (3, 3, 3, 3)),
        TableEdge("archive", 0, 1, 3, (1,), (1,)),
    )
    table = TableRoutes((4, 2), table_edges, 1, (1, 1))
    print("Initial grades [0, 3]:",
          [table_edges[edge_id].name for edge_id in table.route(0, 0, 3)])

    billion = 10**9
    million = 10**6
    size = 10**12
    formula_edges = (
        FormulaEdge("classify", 0, 1, 0, size - 1,
                    lambda x: x // billion, lambda x: x // billion),
        FormulaEdge("direct grading", 0, 2, 10 * billion, size - 1,
                    lambda x: (x - 10 * billion) // million,
                    lambda x: (x - 10 * billion) // million),
        FormulaEdge("certify grade", 1, 2, 0, 999, lambda x: x, lambda x: x),
    )
    compact = FormulaRoutes((size, 1000, size // million), formula_edges, 2, (2, 2))
    print("Two maximal accepted starting ranges over a trillion-state fiber:",
          [(item.first, item.last) for item in compact.frontier[0]])


if __name__ == "__main__":
    examples()
