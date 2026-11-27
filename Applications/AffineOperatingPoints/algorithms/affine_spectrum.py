"""Exact fixed-level max-affine eigenvector testing. Solving requires z3-solver."""

import argparse
from dataclasses import asdict, dataclass
from fractions import Fraction
import json


@dataclass(frozen=True)
class Branch:
    tail: int
    head: int
    gain: Fraction
    offset: Fraction


@dataclass(frozen=True)
class Result:
    status: str
    vector: tuple[Fraction, ...] = ()
    ray: tuple[Fraction, ...] = ()
    multipliers: tuple[Fraction, ...] = ()


def rational(value):
    if type(value) not in (int, str, Fraction):
        raise ValueError("exact rational inputs must be integers, strings, or Fractions")
    return Fraction(value)


def problem(size, level, branches):
    if type(size) is not int or size < 1:
        raise ValueError("vertices must be a positive integer")
    result = []
    incoming = set()
    for tail, head, gain, offset in branches:
        if any(type(v) is not int or not 0 <= v < size for v in (tail, head)):
            raise ValueError("branch endpoints must be valid integer vertices")
        gain = rational(gain)
        if gain < 0:
            raise ValueError("gains must be nonnegative")
        result.append(Branch(tail, head, gain, rational(offset) - level))
        incoming.add(head)
    if len(incoming) != size:
        raise ValueError("every vertex must have an incoming branch")
    return tuple(result)


def positive_edges(branches):
    return [(e.tail, e.head, e.gain) for e in branches if e.gain > 0]


def adjacency(size, edges):
    graph = [[] for _ in range(size)]
    for tail, head, _ in edges:
        graph[tail].append(head)
    return graph


def reachable(size, edges, seeds):
    graph = adjacency(size, edges)
    seen = set(seeds)
    todo = list(seen)
    while todo:
        for head in graph[todo.pop()]:
            if head not in seen:
                seen.add(head)
                todo.append(head)
    return seen


def product_step(labels, edges):
    result = labels.copy()
    for tail, head, gain in edges:
        result[head] = max(result[head], gain * labels[tail])
    return result


def expansive_descendants(size, edges):
    """Mark vertices reachable from a cycle with product strictly above one."""
    labels = [Fraction(1)] * size
    for _ in range(size):
        next_labels = product_step(labels, edges)
        if labels == next_labels:
            return set()
        improved = {v for v in range(size) if next_labels[v] > labels[v]}
        labels = next_labels
    return reachable(size, edges, improved)


def finite_upper_vertices(size, edges):
    return expansive_descendants(size, [(v, u, a) for u, v, a in edges])


def cyclic_vertices(size, edges):
    """Iterative Kosaraju, including singleton SCCs with a self-loop."""
    graph = adjacency(size, edges)
    reverse = adjacency(size, [(v, u, a) for u, v, a in edges])
    seen = set()
    order = []
    for vertex in range(size):
        if vertex in seen:
            continue
        seen.add(vertex)
        stack = [(vertex, iter(graph[vertex]))]
        while stack:
            vertex, neighbors = stack[-1]
            neighbor = next(neighbors, None)
            if neighbor is None:
                stack.pop()
                order.append(vertex)
            elif neighbor not in seen:
                seen.add(neighbor)
                stack.append((neighbor, iter(graph[neighbor])))
    seen.clear()
    cyclic = {u for u, v, _ in edges if u == v}
    for vertex in reversed(order):
        if vertex in seen:
            continue
        component = [vertex]
        seen.add(vertex)
        for member in component:
            for neighbor in reverse[member]:
                if neighbor not in seen:
                    seen.add(neighbor)
                    component.append(neighbor)
        if len(component) > 1:
            cyclic.update(component)
    return cyclic


def slack(e, vector):
    return vector[e.head] - e.gain * vector[e.tail] - e.offset


def tight_edges(branches, vector):
    return [
        (e.tail, e.head, e.gain)
        for e in branches
        if e.gain > 0 and slack(e, vector) == 0
    ]


def missing_lower_vertices(size, branches, edges, pins):
    contractors = expansive_descendants(size, [(u, v, 1 / a) for u, v, a in edges])
    seeds = pins | contractors | {e.head for e in branches if e.gain == 0}
    return set(range(size)) - reachable(size, edges, seeds)


def downward_ray(size, edges, missing):
    reverse = [(v, u, 1 / a) for u, v, a in edges if u in missing and v in missing]
    labels = [Fraction(int(v in missing)) for v in range(size)]
    for _ in range(len(missing) - 1):
        updated = product_step(labels, reverse)
        if labels == updated:
            break
        labels = updated
    return tuple(labels)


def certify(size, level, branches, result):
    """Check an eigenvector, normalized infeasibility proof, or obstruction, without Z3."""
    rows = problem(size, rational(level), branches)
    vector = result.vector
    if any(type(value) not in (int, Fraction)
           for part in (vector, result.ray, result.multipliers) for value in part):
        return False
    if result.status == "relaxation_infeasible":
        weights = result.multipliers
        if (vector or result.ray or len(weights) != len(rows)
                or any(w < 0 for w in weights) or sum(weights) != 1):
            return False
        balance = [Fraction(0)] * size
        for e, weight in zip(rows, weights):
            balance[e.tail] += weight * e.gain
            balance[e.head] -= weight
        return not any(balance) and sum(w * e.offset for w, e in zip(weights, rows)) > 0

    if len(vector) != size or result.multipliers or any(slack(e, vector) < 0 for e in rows):
        return False
    if result.status == "eigenvector":
        return not result.ray and len({e.head for e in rows if slack(e, vector) == 0}) == size
    if result.status != "no_eigenvector":
        return False

    ray = result.ray
    tight = tight_edges(rows, vector)
    if (len(ray) != size or not any(ray) or any(d < 0 for d in ray)
            or any(ray[e.head] > e.gain * ray[e.tail] for e in rows)
            or any(ray[v] for v in cyclic_vertices(size, tight))):
        return False
    return finite_upper_vertices(size, tight) == finite_upper_vertices(size, positive_edges(rows))


def optimize(z3, variables, constraints, objective):
    model = z3.Optimize()
    model.add(*constraints)
    bound = model.maximize(objective)
    status = model.check()
    if status == z3.unsat:
        return None
    if status != z3.sat:
        raise RuntimeError(f"Z3 could not optimize the rational LP: {model.reason_unknown()}")
    if not (z3.is_rational_value(bound.upper()) or z3.is_int_value(bound.upper())):
        raise RuntimeError(f"expected a finite rational optimum, got {bound.upper()}")
    solution = model.model()
    return tuple(read_rational(solution.eval(v, model_completion=True)) for v in variables)


def read_rational(value):
    return Fraction(value.numerator_as_long(), value.denominator_as_long())


def infeasibility_certificate(z3, size, rows):
    weights = [z3.Real(f"p_{i}") for i in range(len(rows))]
    balance = [[] for _ in range(size)]
    for e, p in zip(rows, weights):
        balance[e.tail].append(z3.RealVal(str(e.gain)) * p)
        balance[e.head].append(-p)
    model = z3.SolverFor("QF_LRA")
    model.add(*(p >= 0 for p in weights), z3.Sum(weights) == 1)
    model.add(*(z3.Sum(terms) == 0 for terms in balance))
    model.add(z3.Sum([z3.RealVal(str(e.offset)) * p for e, p in zip(rows, weights)]) > 0)
    if model.check() != z3.sat:
        raise RuntimeError("could not extract a normalized infeasibility certificate")
    return tuple(read_rational(model.model().eval(p)) for p in weights)


def solve(size, level, branches):
    """Decide the eigen-equation and return a checkable exact rational result."""
    import z3

    level = rational(level)
    branches = tuple(branches)
    rows = problem(size, level, branches)
    edges = positive_edges(rows)
    bounded = finite_upper_vertices(size, edges)
    x = [z3.Real(f"x_{v}") for v in range(size)]
    constraints = [
        x[e.head] >= z3.RealVal(str(e.gain)) * x[e.tail] + z3.RealVal(str(e.offset))
        for e in rows
    ]
    objective = z3.Sum([x[v] for v in sorted(bounded)]) if bounded else z3.RealVal(0)
    upper = optimize(z3, x, constraints, objective)
    if upper is None:
        result = Result(
            "relaxation_infeasible", multipliers=infeasibility_certificate(z3, size, rows)
        )
    else:
        tight = tight_edges(rows, upper)
        pins = cyclic_vertices(size, tight)
        missing = missing_lower_vertices(size, rows, edges, pins)
        if missing:
            result = Result("no_eigenvector", upper, downward_ray(size, edges, missing))
        else:
            z = [z3.Real(f"z_{v}") for v in range(size)]
            constraints = [v >= 0 for v in z]
            constraints.extend(z[v] == 0 for v in sorted(pins))
            constraints.extend(
                z[e.head] - z3.RealVal(str(e.gain)) * z[e.tail] <= z3.RealVal(str(slack(e, upper)))
                for e in rows
            )
            delta = optimize(z3, z, constraints, z3.Sum(z))
            if delta is None:
                raise RuntimeError("the zero descent is feasible")
            result = Result("eigenvector", tuple(u - d for u, d in zip(upper, delta)))
    if not certify(size, level, branches, result):
        raise RuntimeError("exact result failed independent arithmetic verification")
    return result


def demo():
    branches = [(0, 0, 2, 0), (0, 0, 3, 0), (0, 1, 2, "1/2"), (1, 1, 3, 0)]
    return [
        dict(vertices=2, level=level, branches=branches)
        for level in ("-1", "0", "1")
    ]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", help="JSON problem file with vertices, level, branches")
    parser.add_argument("--check", help="JSON certificate produced with --input")
    args = parser.parse_args()
    if args.check and not args.input:
        parser.error("--check requires --input")
    if args.input:
        with open(args.input, encoding="utf-8") as source:
            cases = [json.load(source)]
    else:
        cases = demo()
    for case in cases:
        size, level, branches = (case[name] for name in ("vertices", "level", "branches"))
        if args.check:
            with open(args.check, encoding="utf-8") as source:
                cert = json.load(source)
            result = Result(
                cert["status"],
                **{
                    name: tuple(rational(value) for value in cert.get(name, []))
                    for name in ("vector", "ray", "multipliers")
                },
            )
            if not certify(size, level, branches, result):
                parser.exit(1, "invalid certificate\n")
            print("valid certificate")
        else:
            result = asdict(solve(size, level, branches))
            if not args.input:
                result = {"level": level, **result}
            print(json.dumps(result, default=str))


if __name__ == "__main__":
    main()
