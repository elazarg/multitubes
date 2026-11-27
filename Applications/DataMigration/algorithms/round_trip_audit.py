"""Round-trip audits for a finite quiver of total maps on numbered records."""

from collections import deque
from itertools import accumulate


def _graph(size, endpoints):
    forward = [[] for _ in range(size)]
    reverse = [[] for _ in range(size)]
    for edge, (u, v) in enumerate(endpoints):
        if not (0 <= u < size and 0 <= v < size):
            raise ValueError("edge endpoint out of range")
        forward[u].append((v, edge))
        reverse[v].append((u, edge))
    return forward, reverse


def _components(forward, reverse):
    seen = [False] * len(forward)
    order = []
    for start in range(len(forward)):
        if seen[start]:
            continue
        seen[start] = True
        stack = [(start, iter(forward[start]))]
        while stack:
            vertex, arcs = stack[-1]
            arc = next(arcs, None)
            if arc is None:
                order.append(vertex)
                stack.pop()
            else:
                other, _ = arc
                if not seen[other]:
                    seen[other] = True
                    stack.append((other, iter(forward[other])))
    belongs = [-1] * len(forward)
    roots = []
    for start in reversed(order):
        if belongs[start] != -1:
            continue
        component = len(roots)
        roots.append(start)
        belongs[start] = component
        stack = [start]
        while stack:
            vertex = stack.pop()
            for other, _ in reverse[vertex]:
                if belongs[other] == -1:
                    belongs[other] = component
                    stack.append(other)
    return belongs, roots


def _forest(adjacency, belongs, roots):
    parent = [None] * len(adjacency)
    for root in roots:
        parent[root] = (root, -1)
        stack = [root]
        while stack:
            vertex = stack.pop()
            for other, edge in adjacency[vertex]:
                if belongs[other] == belongs[root] and parent[other] is None:
                    parent[other] = (vertex, edge)
                    stack.append(other)
    return parent


def _parent_edges(parent, vertex):
    previous, edge = parent[vertex]
    while edge != -1:
        yield edge
        previous, edge = parent[previous]


class RoundTripAudit:
    """Audit all records of a quiver given total (source, target, image) tables."""

    def __init__(self, sizes, edges):
        self.sizes = tuple(sizes)
        if any(size < 0 for size in self.sizes):
            raise ValueError("negative fiber size")
        self.edges = tuple(edges)
        self.offset = tuple(accumulate(self.sizes, initial=0))
        endpoints = [(u, v) for u, v, _ in self.edges]
        base_forward, base_reverse = _graph(len(self.sizes), endpoints)
        self.base_component, base_roots = _components(base_forward, base_reverse)
        self.base_in = _forest(base_reverse, self.base_component, base_roots)
        self.base_out = _forest(base_forward, self.base_component, base_roots)
        self.base_forward = base_forward
        self.schema = [v for v, size in enumerate(self.sizes) for _ in range(size)]
        forward = [[] for _ in self.schema]
        self.reverse = [[] for _ in self.schema]
        for edge, (u, v, image) in enumerate(self.edges):
            if len(image) != self.sizes[u]:
                raise ValueError("wrong number of entries")
            if self.base_component[u] != self.base_component[v]:
                continue
            for point, value in enumerate(image):
                if not 0 <= value < self.sizes[v]:
                    raise ValueError("edge image out of range")
                a = self.offset[u] + point
                b = self.offset[v] + value
                forward[a].append((b, edge))
                self.reverse[b].append((a, edge))
        self.component, roots = _components(forward, self.reverse)
        self.exits = [None] * len(roots)
        for a, arcs in enumerate(forward):
            for b, edge in arcs:
                if self.component[a] != self.component[b]:
                    self.exits[self.component[a]] = (b, edge)
                    roots[self.component[a]] = a
        self.up = _forest(self.reverse, self.component, roots)
        self.down = _forest(forward, self.component, roots)
        self.peer = [-1] * len(forward)
        last = [-1] * len(roots)
        for v in range(len(self.sizes)):
            for a in range(self.offset[v], self.offset[v + 1]):
                component = self.component[a]
                b = last[component]
                if b >= self.offset[v]:
                    self.peer[a] = b
                    self.peer[b] = a
                last[component] = a

    def _record(self, v, point):
        if not 0 <= v < len(self.sizes) or not 0 <= point < self.sizes[v]:
            raise IndexError("record out of range")
        return self.offset[v] + point

    def _stable(self, a):
        return self.exits[self.component[a]] is None and self.peer[a] == -1

    def stable(self, v, point):
        return self._stable(self._record(v, point))

    def statuses(self):
        return tuple(tuple(self._stable(a) for a in range(start, end))
                     for start, end in zip(self.offset, self.offset[1:]))

    def flat_bases(self):
        return tuple(all(self._stable(a) for a in range(start, end))
                     for start, end in zip(self.offset, self.offset[1:]))

    def counterexample(self, v, point):
        """Return a changing closed walk as edge IDs, or None if stable."""
        a = self._record(v, point)
        if self._stable(a):
            return None
        route = list(_parent_edges(self.up, a))
        exit_arc = self.exits[self.component[a]]
        if exit_arc is None:
            route.extend(reversed(list(_parent_edges(self.down, self.peer[a]))))
        else:
            b, edge = exit_arc
            route.append(edge)
            route.extend(_parent_edges(self.base_in, self.schema[b]))
            route.extend(reversed(list(_parent_edges(self.base_out, v))))
        return tuple(route)

    def registry(self, root):
        return RegistryAudit(self, root)


class RegistryAudit:
    """Index route-independent names and normalized routes into one registry."""

    def __init__(self, parent, root):
        if not 0 <= root < len(parent.sizes):
            raise IndexError("registry out of range")
        self.parent = parent
        self.root = root
        self.marks = [[] for _ in parent.schema]
        queue = deque()
        for key in range(parent.sizes[root]):
            a = parent.offset[root] + key
            self.marks[a].append((key, -1, -1, -1))
            queue.append((a, 0))
        while queue:
            a, slot = queue.popleft()
            key = self.marks[a][slot][0]
            for b, edge in parent.reverse[a]:
                marks = self.marks[b]
                if len(marks) == 2 or (marks and marks[0][0] == key):
                    continue
                marks.append((key, a, slot, edge))
                queue.append((b, len(marks) - 1))
        self.safe_keys = tuple(key for key in range(parent.sizes[root])
                               if len(self.marks[parent.offset[root] + key]) == 1)
        self.key_row = [-1] * parent.sizes[root]
        for row, key in enumerate(self.safe_keys):
            self.key_row[key] = row
        self.ingress = [None] * len(parent.sizes)
        self.ingress[root] = self.safe_keys
        queue = deque([root])
        while queue:
            u = queue.popleft()
            for v, edge in parent.base_forward[u]:
                if (self.ingress[v] is None
                        and parent.base_component[v] == parent.base_component[root]):
                    image = parent.edges[edge][2]
                    self.ingress[v] = tuple(image[i] for i in self.ingress[u])
                    queue.append(v)

    def _marks(self, v, point):
        a = self.parent._record(v, point)
        if self.ingress[v] is None:
            raise ValueError("record is outside the registry's schema component")
        return a, self.marks[a]

    def return_keys(self, v, point):
        """Return the unique key or two distinct reachable keys."""
        _, marks = self._marks(v, point)
        return tuple(mark[0] for mark in marks)

    def return_witnesses(self, v, point):
        """Return a (key, edge IDs) pair for each retained key."""
        a, marks = self._marks(v, point)
        witnesses = []
        for slot, (key, _, _, _) in enumerate(marks):
            state = a
            route = []
            while True:
                _, other, other_slot, edge = self.marks[state][slot]
                if edge == -1:
                    break
                route.append(edge)
                state, slot = other, other_slot
            witnesses.append((key, tuple(route)))
        return tuple(witnesses)

    def normalize(self, v, point, target):
        """Return the target's chosen representative of the unique registry key."""
        _, marks = self._marks(v, point)
        if not 0 <= target < len(self.ingress) or self.ingress[target] is None:
            raise ValueError("target is outside the registry's schema component")
        if len(marks) != 1:
            raise ValueError("record has ambiguous returns")
        return self.ingress[target][self.key_row[marks[0][0]]]


def audit_flat_bases(sizes, endpoints, evaluate):
    """Audit a strongly connected schema using lazy evaluate(edge, point).

    Return (base_flags, failure), where failure is None or a tuple
    (minimum_schema, changed_start_record, closed_walk_edge_IDs).
    The caller supplies total typed maps.
    """
    sizes = tuple(sizes)
    if not sizes:
        return (), None
    if any(size < 0 for size in sizes):
        raise ValueError("negative fiber size")
    forward, reverse = _graph(len(sizes), endpoints)
    component, roots = _components(forward, reverse)
    if len(roots) != 1:
        raise ValueError("expected one schema component")
    root = min(range(len(sizes)), key=sizes.__getitem__)
    back = _forest(reverse, component, [root])
    queue = deque((root, point) for point in range(sizes[root]))
    parent = {state: None for state in queue}
    color = {state: state[1] for state in queue}

    def ingress(state):
        route = []
        while parent[state] is not None:
            state, edge = parent[state]
            route.append(edge)
        return list(reversed(route))

    while queue:
        state = queue.popleft()
        u, point = state
        key = color[state]
        for v, edge in forward[u]:
            val = evaluate(edge, point)
            if not 0 <= val < sizes[v]:
                raise ValueError("edge image out of range")
            other = (v, val)
            if other not in color:
                color[other] = key
                parent[other] = (state, edge)
                queue.append(other)
            elif color[other] != key:
                suffix = tuple(_parent_edges(back, v))
                terminal = val
                for return_edge in suffix:
                    terminal = evaluate(return_edge, terminal)
                if terminal == key:
                    start = color[other]
                    route = ingress(other)
                else:
                    start = key
                    route = ingress(state)
                    route.append(edge)
                return (False,) * len(sizes), (root, start, tuple(route) + suffix)
    return tuple(size == sizes[root] for size in sizes), None
