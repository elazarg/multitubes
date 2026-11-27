"""Compressed zero-drift schedules and exact robust restart phases."""

from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from math import gcd, lcm


@dataclass(frozen=True)
class Edge:
    tail: int
    head: int
    weight: tuple[int, ...]


@dataclass(frozen=True)
class Run:
    word: tuple[int, ...]
    copies: int


@dataclass(frozen=True)
class Residue:
    """Positions first + step*j, for 0 <= j < copies."""

    first: int
    step: int
    copies: int
    vertex: int
    prefix: tuple[int, ...]
    increment: tuple[int, ...]


@dataclass(frozen=True)
class Progression:
    first: int
    step: int
    count: int


def realize(edges, counts, base):
    """Realize balanced, connected, nonzero counts as closed runs at base."""
    if len(counts) != len(edges) or any(type(c) is not int or c < 0 for c in counts):
        raise ValueError("multiplicities must be nonnegative integers")
    residual = {index: count for index, count in enumerate(counts) if count}
    if not residual:
        raise ValueError("the period must be nonempty")
    outgoing = {}
    balance = {}
    for index in residual:
        edge = edges[index]
        outgoing.setdefault(edge.tail, {})[index] = None
        balance[edge.tail] = balance.get(edge.tail, 0) + residual[index]
        balance[edge.head] = balance.get(edge.head, 0) - residual[index]
    if any(balance.values()):
        raise ValueError("multiplicities must balance at each vertex")

    # Subtract as many copies of the next simple cycle as possible.
    cycles = []
    incident = {}
    while residual:
        vertex = edges[next(iter(residual))].tail
        walk = []
        seen = {}
        while vertex not in seen:
            seen[vertex] = len(walk)
            index = next(iter(outgoing[vertex]))
            walk.append(index)
            vertex = edges[index].head
        cycle = tuple(walk[seen[vertex]:])
        copies = min(residual[index] for index in cycle)
        for index in cycle:
            tail = edges[index].tail
            incident.setdefault(tail, []).append(len(cycles))
            residual[index] -= copies
            if residual[index] == 0:
                del residual[index]
                del outgoing[tail][index]
        cycles.append((cycle, copies))

    if base not in incident:
        raise ValueError("base must belong to the positive support")
    root = incident[base][0]
    children = [{} for _ in cycles]
    entry = {root: base}
    assigned_vertices = set()
    queue = deque([root])
    while queue:
        parent = queue.popleft()
        for index in cycles[parent][0]:
            port = edges[index].tail
            if port in assigned_vertices:
                continue
            assigned_vertices.add(port)
            for child in incident[port]:
                if child not in entry:
                    entry[child] = port
                    children[parent].setdefault(port, []).append(child)
                    queue.append(child)
    if len(entry) != len(cycles):
        raise ValueError("the positive support must be connected")

    # At each tree node traverse the ordinary copies and one copy with splices.
    output = []
    stack = [root]
    while stack:
        task = stack.pop()
        if isinstance(task, Run):
            output.append(task)
            continue
        word, copies = cycles[task]
        pivot = next(i for i, index in enumerate(word) if edges[index].tail == entry[task])
        word = word[pivot:] + word[:pivot]
        splices = children[task]
        if not splices:
            output.append(Run(word, copies))
            continue
        if copies > 1:
            output.append(Run(word, copies - 1))
        for index in reversed(word):
            stack.append(Run((index,), 1))
            stack.extend(reversed(splices.get(edges[index].tail, ())))
    return tuple(output)


def index_period(edges, runs):
    """Check contiguity, closure and coefficient-wise zero drift, then index starts."""
    if not runs or any(not run.word or type(run.copies) is not int or run.copies < 1
                       for run in runs):
        raise ValueError("expected nonempty runs with positive integer copy counts")
    if any(type(edge_id) is not int or not 0 <= edge_id < len(edges)
           for run in runs for edge_id in run.word):
        raise ValueError("edge IDs must be valid integer indices")
    base = edges[runs[0].word[0]].tail
    size = len(edges[runs[0].word[0]].weight)
    position = 0
    current = base
    prefix = (0,) * size
    index = []
    for run in runs:
        word_start = current
        increments = [0] * size
        starts = []
        for edge_id in run.word:
            edge = edges[edge_id]
            if edge.tail != current or len(edge.weight) != size:
                raise ValueError("period edges must join and have equal weight dimension")
            starts.append((current, tuple(p + r for p, r in zip(prefix, increments))))
            for coord, charge in enumerate(edge.weight):
                increments[coord] += charge
            current = edge.head
        if run.copies > 1 and current != word_start:
            raise ValueError("a repeated word must close")
        step = len(run.word)
        increments = tuple(increments)
        for offset, (vertex, charge) in enumerate(starts):
            index.append(Residue(position + offset, step, run.copies, vertex, charge, increments))
        prefix = tuple(p + run.copies * r for p, r in zip(prefix, increments))
        position += step * run.copies
    if current != base or any(prefix):
        raise ValueError("the period must close with zero coefficient-wise charge")
    return tuple(index)


def _charge(residue, copy):
    return tuple(p + copy * d for p, d in zip(residue.prefix, residue.increment))


def _parameters(index, inventory, box):
    stock = tuple(Fraction(value) for value in inventory)
    uncertainty = tuple((Fraction(lo), Fraction(hi)) for lo, hi in box)
    width = 1 + len(uncertainty)
    if (not index or not stock or len(index[0].prefix) != len(stock) * width
            or any(lo > hi for lo, hi in uncertainty)):
        raise ValueError("expected complete inventory coordinates and ordered parameter bounds")
    # Every edge boundary belongs to one run residue. For a fixed parameter
    # vector, intermediate copies interpolate between the two ends.
    endpoints = tuple(
        _charge(residue, copy)
        for residue in index
        for copy in (0, residue.copies - 1)
    )
    return stock, uncertainty, width, endpoints


def _coordinate_bounds(start, stock, uncertainty, width, endpoints):
    for coord, amount in enumerate(stock):
        offset = coord * width
        low = high = amount
        for end in endpoints:
            lower = upper = amount + end[offset] - start[offset]
            for i, (lo, hi) in enumerate(uncertainty, offset + 1):
                coefficient = end[i] - start[i]
                a, b = coefficient * lo, coefficient * hi
                lower += min(a, b)
                upper += max(a, b)
            low = min(low, lower)
            high = max(high, upper)
        yield low, high


def envelope(index, phase, inventory, box=()):
    """Return the exact stock range in each coordinate over all time and calibrations."""
    parameters = _parameters(index, inventory, box)
    for record in index:
        copy, remainder = divmod(phase - record.first, record.step)
        if remainder == 0 and 0 <= copy < record.copies:
            return tuple(_coordinate_bounds(_charge(record, copy), *parameters))
    raise ValueError("phase outside the period")


def _first_true(left, right, predicate):
    """First true in a false-then-true interval, with right as a true sentinel."""
    while left < right:
        mid = (left + right) // 2
        if predicate(mid):
            right = mid
        else:
            left = mid + 1
    return left


def _box_sublevel(constant, slope, coefficients, uncertainty, first, last):
    """Integer sublevel interval of one worst-case signed capacity violation."""
    value = constant + slope * first
    events = []
    for (offset, rate), (lo, hi) in zip(coefficients, uncertainty):
        coefficient = offset + rate * first
        # At a breakpoint at the left endpoint choose the active right branch.
        nonnegative = coefficient > 0 or (coefficient == 0 and rate >= 0)
        scale = hi if nonnegative else lo
        value += coefficient * scale
        slope += rate * scale
        if rate and lo != hi:
            crossing = Fraction(-offset, rate)
            if first < crossing < last:
                events.append((crossing, abs(rate) * (hi - lo)))
    events.sort()
    events.append((last, 0))
    left = first
    safe = None
    for right, slope_change in events:
        if slope:
            zero = left - value / slope
            lower = max(left, zero) if slope < 0 else left
            upper = min(right, zero) if slope > 0 else right
        elif value <= 0:
            lower, upper = left, right
        else:
            lower, upper = right + 1, right
        if lower <= upper:
            safe = (lower if safe is None else safe[0], upper)
        value += slope * (right - left)
        slope += slope_change
        left = right
    if safe is None:
        return 0, -1
    return safe[0].__ceil__(), safe[1].__floor__()


def _breakpoint_interval(record, parameters, limits):
    stock, uncertainty, width, endpoints = parameters
    first, last = 0, record.copies - 1
    for end in endpoints:
        for coord, (amount, (lo, hi)) in enumerate(zip(stock, limits)):
            i = coord * width
            constant = amount + end[i] - record.prefix[i]
            rate = -record.increment[i]
            coeff = [(end[j] - record.prefix[j], -record.increment[j])
                     for j in range(i + 1, i + width)]
            first, last = _box_sublevel(constant - hi, rate, coeff, uncertainty, first, last)
            if first > last:
                return first, last
            first, last = _box_sublevel(lo - constant, -rate,
                                       [(-a, -b) for a, b in coeff], uncertainty, first, last)
            if first > last:
                return first, last
    return first, last


def _binary_interval(record, parameters, limits):
    def violation(copy):
        bounds = _coordinate_bounds(_charge(record, copy), *parameters)
        return max(max(lo - low, high - hi)
                   for (lo, hi), (low, high) in zip(limits, bounds))

    end = record.copies - 1
    # A convex sequence decreases to its minimum, possibly with a plateau,
    # and then increases. The first nonnegative forward difference finds it.
    best = _first_true(0, end, lambda j: violation(j) <= violation(j + 1))
    if violation(best) > 0:
        return 0, -1
    first = _first_true(0, best, lambda j: violation(j) <= 0)
    last = end - _first_true(0, end - best, lambda j: violation(end - j) <= 0)
    return first, last


def admissible_phases(index, inventory, limits, box=(), allowed=None, *, method="breakpoints"):
    """Disjoint safe start progressions. Method 'binary' uses convex search."""
    parameters = _parameters(index, inventory, box)
    stock, uncertainty, _, endpoints = parameters
    limits = tuple((Fraction(lo), Fraction(hi)) for lo, hi in limits)
    if len(limits) != len(stock) or any(lo > hi for lo, hi in limits):
        raise ValueError("expected one ordered capacity interval per stock coordinate")
    if allowed is not None:
        allowed = frozenset(allowed)
    result = []
    if not uncertainty:
        minimum = tuple(map(min, zip(*endpoints)))
        maximum = tuple(map(max, zip(*endpoints)))
        for record in index:
            if allowed is not None and record.vertex not in allowed:
                continue
            first, last = 0, record.copies - 1
            for x, (lo, hi), low, high, prefix, delta in zip(
                    stock, limits, minimum, maximum, record.prefix, record.increment):
                lower, upper = x + high - hi - prefix, x + low - lo - prefix
                if lower > upper:
                    last = -1
                    break
                if delta == 0:
                    if not lower <= 0 <= upper:
                        last = -1
                        break
                else:
                    a, b = sorted((lower / delta, upper / delta))
                    first = max(first, a.__ceil__())
                    last = min(last, b.__floor__())
            if first <= last:
                result.append(Progression(record.first + record.step * first,
                                          record.step, last - first + 1))
        return tuple(result)

    interval = {"breakpoints": _breakpoint_interval, "binary": _binary_interval}[method]
    for record in index:
        if allowed is not None and record.vertex not in allowed:
            continue
        first, last = interval(record, parameters, limits)
        if first <= last:
            result.append(Progression(record.first + record.step * first,
                                      record.step, last - first + 1))
    return tuple(result)


def _feasible_with_edge(matrix, forced, size):
    """Exact phase I for A x = 0, x >= 0, x[forced] >= 1."""
    rows = []
    for row_index, row in enumerate(matrix):
        rhs = -row[forced]
        sign = -1 if rhs < 0 else 1
        artificial_column = [int(i == row_index) for i in range(len(matrix))]
        rows.append(list(map(Fraction, [*(sign * a for a in row),
                                        *artificial_column, abs(rhs)])))
    basis = list(range(size, size + len(rows)))
    cost = [0] * size + [1] * len(rows)
    while True:
        artificial_rows = [row for row, basic in zip(rows, basis) if basic >= size]
        entering = next((j for j, value in enumerate(cost)
                         if value < sum(row[j] for row in artificial_rows)), None)
        if entering is None:
            if any(row[-1] for row in artificial_rows):
                return None
            solution = [Fraction(0)] * size
            for row, basic in zip(rows, basis):
                if basic < size:
                    solution[basic] = row[-1]
            solution[forced] += 1
            return solution
        # Bland's index rule breaks ties, including on degenerate pivots.
        leaving = min((i for i, row in enumerate(rows) if row[entering] > 0),
                      key=lambda i: (rows[i][-1] / rows[i][entering], basis[i]))
        pivot = [a / rows[leaving][entering] for a in rows[leaving]]
        for i, row in enumerate(rows):
            if i != leaving and row[entering]:
                rows[i] = [a - row[entering] * b for a, b in zip(row, pivot)]
        rows[leaving] = pivot
        basis[leaving] = entering


def _strong_components(edges, candidate):
    """Partition candidate edge indices by their support's vertex SCCs."""
    adj, rev = {}, {}
    for i in candidate:
        edge = edges[i]
        adj.setdefault(edge.tail, []).append(edge.head)
        adj.setdefault(edge.head, [])
        rev.setdefault(edge.head, []).append(edge.tail)
    seen, order = set(), []
    for root in adj:
        if root in seen:
            continue
        seen.add(root)
        stack = [(root, iter(adj[root]))]
        while stack:
            vertex, neighbours = stack[-1]
            other = next(neighbours, None)
            if other is None:
                order.append(vertex)
                stack.pop()
            elif other not in seen:
                seen.add(other)
                stack.append((other, iter(adj[other])))
    component = {}
    for root in reversed(order):
        if root in component:
            continue
        component[root] = root
        stack = [root]
        while stack:
            vertex = stack.pop()
            for other in rev.get(vertex, ()):
                if other not in component:
                    component[other] = root
                    stack.append(other)
    partition = {}
    for i in candidate:
        edge = edges[i]
        group = component[edge.tail]
        if component[edge.head] == group:
            partition.setdefault(group, []).append(i)
    return tuple(partition.values())


def find_lasso(edges, start):
    """Return a transient and all edge counts, or None. Small-instance exact LP."""
    if not edges:
        return None
    dimension = len(edges[0].weight)
    if any(len(edge.weight) != dimension for edge in edges):
        raise ValueError("all edges must have the same weight dimension")
    outgoing = {}
    for i, edge in enumerate(edges):
        outgoing.setdefault(edge.tail, []).append(i)
    parent = {start: None}
    queue = deque([start])
    while queue:
        for i in outgoing.get(queue.popleft(), ()):
            vertex = edges[i].head
            if vertex not in parent:
                parent[vertex] = i
                queue.append(vertex)
    reachable = [i for i, edge in enumerate(edges) if edge.tail in parent]
    candidates = list(_strong_components(edges, reachable))
    while candidates:
        candidate = candidates.pop()
        size = len(candidate)
        columns = [edges[i] for i in candidate]
        vertices = sorted({edge.tail for edge in columns} | {edge.head for edge in columns})
        matrix = [[int(edge.tail == v) - int(edge.head == v) for edge in columns]
                  for v in vertices]
        matrix.extend([edge.weight[j] for edge in columns] for j in range(dimension))
        witness = [Fraction(0)] * size
        for j in range(size):
            if witness[j] == 0:
                found = _feasible_with_edge(matrix, j, size)
                if found is not None:
                    witness = [a + b for a, b in zip(witness, found)]
        support = [i for i, weight in zip(candidate, witness) if weight]
        components = _strong_components(edges, support)
        if len(components) != 1:
            candidates.extend(components)
            continue
        base = edges[support[0]].tail
        scale = lcm(*(weight.denominator for weight in witness))
        integers = [int(weight * scale) for weight in witness]
        common = gcd(*integers)
        counts = [0] * len(edges)
        for i, weight in zip(candidate, integers):
            counts[i] = weight // common
        path = []
        while base != start:
            i = parent[base]
            path.append(i)
            base = edges[i].tail
        return tuple(reversed(path)), tuple(counts)
    return None
