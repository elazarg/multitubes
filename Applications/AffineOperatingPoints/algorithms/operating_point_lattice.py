"""Compile implications to a max-affine operating-point instance at level zero."""

import argparse
import json
from pathlib import Path


def compile_operating_points(
    vertices, arcs, *, bounded_indegree=False, nonnegative_offsets=False
):
    """Use vertex IDs 0 through vertices-1 for implications j -> i.

    The hub has ID vertices. Auxiliary channels, when present, follow the hub.
    The output uses the adjacent fixed-level solver's JSON fields.
    """
    if type(vertices) is not int or vertices < 0:
        raise ValueError("vertices must be a nonnegative integer")

    predecessors = [[] for _ in range(vertices)]
    seen = set()
    for tail, head in arcs:
        if any(type(v) is not int or not 0 <= v < vertices for v in (tail, head)):
            raise ValueError("implication endpoints must be valid vertex IDs")
        if tail != head and (tail, head) not in seen:
            predecessors[head].append(tail)
            seen.add((tail, head))

    hub = vertices
    size = vertices + 1
    branches = [(v, v, 2, 0) for v in range(size)]

    def merge(sources):
        """Return the root of a balanced binary tree of gain-two max rows."""
        nonlocal size
        current = list(sources)
        while len(current) > 1:
            following = []
            for index in range(0, len(current) - 1, 2):
                branches.append((current[index], size, 2, 0))
                branches.append((current[index + 1], size, 2, 0))
                following.append(size)
                size += 1
            if len(current) % 2:
                following.append(current[-1])
            current = following
        return current[0]

    if bounded_indegree:
        if vertices:
            branches.append((merge(range(vertices)), hub, 2, 0))
        for head, sources in enumerate(predecessors):
            gate = size
            size += 1
            branches.append((hub, gate, 2, -1))
            if sources:
                branches.append((merge(sources), gate, 2, 0))
            branches.append((gate, head, 2, 0))
    else:
        for head, sources in enumerate(predecessors):
            branches.extend(((head, hub, 2, 0), (hub, head, 2, -1)))
            branches.extend((tail, head, 2, 0) for tail in sources)

    if nonnegative_offsets:
        branches = [(tail, head, gain, offset + 1) for tail, head, gain, offset in branches]
    return dict(vertices=size, level=0, branches=branches)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="JSON file with vertices and directed arcs")
    parser.add_argument(
        "--bounded-indegree", action="store_true", help="use at most two branches per channel"
    )
    parser.add_argument(
        "--nonnegative-offsets", action="store_true", help="emit offsets in {0, 1}"
    )
    args = parser.parse_args()
    try:
        data = json.loads(args.input.read_text(encoding="utf-8"))
        result = compile_operating_points(
            data["vertices"],
            data["arcs"],
            bounded_indegree=args.bounded_indegree,
            nonnegative_offsets=args.nonnegative_offsets,
        )
    except (OSError, ValueError, TypeError, KeyError) as error:
        parser.error(str(error))
    print(json.dumps(result))


if __name__ == "__main__":
    main()
