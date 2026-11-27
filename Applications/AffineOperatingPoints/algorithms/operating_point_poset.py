"""Index all operating points of a strongly connected expansive max-affine network."""

from collections import deque
from fractions import Fraction
from heapq import heapify, heappop, heappush

from affine_spectrum import optimize, problem, rational


def _components(adjacency):
    """List strongly connected components in condensation topological order."""
    reverse = [[] for _ in adjacency]
    for tail, heads in enumerate(adjacency):
        for head in heads:
            reverse[head].append(tail)

    seen = set()
    finished = []
    for root in range(len(adjacency)):
        if root in seen:
            continue
        seen.add(root)
        trail = [(root, iter(adjacency[root]))]
        while trail:
            tail, successors = trail[-1]
            head = next(successors, None)
            if head is None:
                finished.append(tail)
                trail.pop()
            elif head not in seen:
                seen.add(head)
                trail.append((head, iter(adjacency[head])))

    seen.clear()
    components = []
    for root in reversed(finished):
        if root in seen:
            continue
        part = [root]
        seen.add(root)
        for head in part:
            for tail in reverse[head]:
                if tail not in seen:
                    seen.add(tail)
                    part.append(tail)
        components.append(tuple(part))
    return components


def _cyclic_components(adjacency):
    return tuple(
        part for part in _components(adjacency)
        if len(part) > 1 or part[0] in adjacency[part[0]]
    )


def _scale(size, rows):
    """Positive rational h with a_e*h[u]/h[v] >= 1, checking strict cycle expansion."""
    if any(row.gain <= 0 for row in rows):
        raise ValueError("every branch gain must be positive")
    scale = [Fraction(1)] * size
    if all(row.gain > 1 for row in rows):
        return scale

    for _ in range(size - 1):
        updated = scale.copy()
        for row in rows:
            pitch = scale[row.tail] * row.gain
            updated[row.head] = min(updated[row.head], pitch)
        if updated == scale:
            break
        scale = updated

    tight = [[] for _ in range(size)]
    for row in rows:
        pitch = scale[row.tail] * row.gain
        if pitch < scale[row.head]:
            raise ValueError("the graph must have product greater than one on every cycle")
        if pitch == scale[row.head]:
            tight[row.tail].append(row.head)
    if _cyclic_components(tight):
        raise ValueError("the graph must have product greater than one on every cycle")
    return scale


def _greatest_relaxation(size, rows):
    import z3

    x = [z3.Real(f"u_{vertex}") for vertex in range(size)]
    constraints = [
        x[row.head] >= z3.RealVal(str(row.gain)) * x[row.tail] + z3.RealVal(str(row.offset))
        for row in rows
    ]
    upper = optimize(z3, x, constraints, z3.Sum(x))
    if upper is None:
        raise RuntimeError("a cycle-expansive relaxation must be feasible")
    return upper


def _prepare(vertices, level, branches):
    """Validate the graph and build its normalized deficit and tight graphs."""
    rows = problem(vertices, rational(level), branches)
    outgoing = [[] for _ in range(vertices)]
    for row in rows:
        outgoing[row.tail].append(row.head)
    if len(_components(outgoing)) != 1:
        raise ValueError("the branch graph must be strongly connected")

    scale = _scale(vertices, rows)
    upper = _greatest_relaxation(vertices, rows)
    arcs = [{} for _ in range(vertices)]
    tight = [[] for _ in range(vertices)]
    for row in rows:
        tail, head = row.tail, row.head
        slack = upper[head] - row.gain * upper[tail] - row.offset
        if slack < 0:
            raise RuntimeError("the relaxation optimum failed its exact inequalities")
        if slack == 0:
            tight[tail].append(head)
        gain = row.gain * scale[tail] / scale[head]
        arcs[tail].setdefault(head, []).append((gain, slack / scale[head]))
    return rows, scale, upper, arcs, tight


def _from_seeds(arcs, scale, upper, starts):
    """Reconstruct readings using minimum affine path costs from zero seeds."""
    distance = [None] * len(upper)
    zero = Fraction(0)
    queue = [(zero, vertex) for vertex in starts]
    for _, vertex in queue:
        distance[vertex] = zero
    heapify(queue)
    while queue:
        value, tail = heappop(queue)
        if value != distance[tail]:
            continue
        for head, parallels in arcs[tail].items():
            candidate = min(gain * value + offset for gain, offset in parallels)
            if distance[head] is None or candidate < distance[head]:
                distance[head] = candidate
                heappush(queue, (candidate, head))
    return tuple(
        point - factor * deficit
        for point, factor, deficit in zip(upper, scale, distance)
    )


class OperatingPointPoset:
    """Critical SCCs and the nonempty upsets that encode all operating points."""

    def __init__(self, vertices, level, branches):
        self._rows, self._scale, self.upper, self._arcs, tight = _prepare(
            vertices, level, branches
        )
        self.critical = _cyclic_components(tight)
        component_at = {
            vertex: index
            for index, component in enumerate(self.critical)
            for vertex in component
        }
        self._successors = []
        for part in self.critical:
            seen = {part[0]}
            pending = deque(seen)
            mask = 0
            while pending:
                vertex = pending.popleft()
                if vertex in component_at:
                    mask |= 1 << component_at[vertex]
                for head in tight[vertex]:
                    if head not in seen:
                        pending.append(head)
                        seen.add(head)
            self._successors.append(mask)
        if not self.critical:
            raise RuntimeError("the greatest relaxation must have a tight directed cycle")
        self._generators = None

    def successors(self, component):
        """Return the principal upset of one critical component, including itself."""
        if type(component) is not int or not 0 <= component < len(self.critical):
            raise ValueError("invalid critical-component ID")
        mask = self._successors[component]
        return tuple(index for index in range(len(self.critical)) if mask & (1 << index))

    def _realize(self, components):
        starts = (vertex for index in components for vertex in self.critical[index])
        return _from_seeds(self._arcs, self._scale, self.upper, starts)

    def vector(self, upset):
        """Decode a nonempty upset of critical-component IDs into its operating point."""
        chosen = set(upset)
        count = len(self.critical)
        if not chosen or any(type(index) is not int or not 0 <= index < count for index in chosen):
            raise ValueError("an upset needs valid critical-component IDs and must be nonempty")
        mask = sum(1 << index for index in chosen)
        if any(self._successors[index] & ~mask for index in chosen):
            raise ValueError("the selected components must be closed under tight reachability")
        return self._realize(chosen)

    def decode(self, vector):
        """Recover the upset of an exact operating point."""
        if len(vector) != len(self.upper):
            raise ValueError("the reading must give every channel")
        vector = tuple(rational(value) for value in vector)
        tight_heads = set()
        for row in self._rows:
            value = row.gain * vector[row.tail] + row.offset
            if value > vector[row.head]:
                raise ValueError("the reading must be an operating point")
            if value == vector[row.head]:
                tight_heads.add(row.head)
        if len(tight_heads) != len(self.upper):
            raise ValueError("the reading must be an operating point")
        return tuple(
            index for index, part in enumerate(self.critical)
            if vector[part[0]] == self.upper[part[0]]
        )

    def upsets(self):
        """Enumerate nonempty upsets with polynomial delay."""
        pending = [(len(self.critical) - 1, 0)]
        while pending:
            index, chosen = pending.pop()
            if index < 0:
                if chosen:
                    yield tuple(k for k in range(len(self.critical)) if chosen & (1 << k))
                continue
            bit = 1 << index
            pending.append((index - 1, chosen))
            if (self._successors[index] & ~(chosen | bit)) == 0:
                pending.append((index - 1, chosen | bit))

    def match_box(self, bounds):
        """Return the greatest operating point in the given bounds, or None.

        The mapping at each measured vertex gives (lower, upper), with None
        for an unconstrained endpoint. Missing vertices are unconstrained.
        """
        measurements = []
        for vertex, (lower, upper) in bounds.items():
            if type(vertex) is not int or not 0 <= vertex < len(self.upper):
                raise ValueError("box endpoints must have valid channel IDs")
            lower = rational(lower) if lower is not None else None
            upper = rational(upper) if upper is not None else None
            if lower is not None and upper is not None and lower > upper:
                return None
            measurements.append((vertex, lower, upper))

        if self._generators is None:
            self._generators = tuple(self._realize((index,)) for index in range(len(self.critical)))
        allowed = [
            generator for generator in self._generators
            if all(upper is None or generator[vertex] <= upper
                   for vertex, _, upper in measurements)
        ]
        if not allowed:
            return None
        for vertex, lower, _ in measurements:
            if lower is not None and max(generator[vertex] for generator in allowed) < lower:
                return None
        return tuple(map(max, zip(*allowed)))
