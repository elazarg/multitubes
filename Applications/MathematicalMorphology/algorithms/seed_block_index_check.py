"""Independent exact checks using forward dilation, subset enumeration and pair scans."""

from itertools import product
from random import Random

from seed_block_index import Layer, SeedBlockIndex, _MaximumRise, _RangeMinimum, demonstration


def explicit_dilation(source, layers):
    images = [source]
    for layer in layers:
        parent = images[layer.parent]
        image = []
        for row in layer.rows:
            image.append(row is not None and any(parent[row[0] - 1 : row[1]]))
        images.append(image)
    return images[1:]


def explicit_certificate(size, layers):
    """Compare the compact certificate to materialized sets of spatial predecessors."""
    supports = [[{site} for site in range(1, size + 1)]]
    for layer in layers:
        parent = supports[layer.parent]
        nonempty = [support for support in parent if support]
        for a, b in zip(nonempty, nonempty[1:]):
            if min(a) > min(b) or max(a) > max(b):
                return False
        image = []
        for row in layer.rows:
            support = set() if row is None else set.union(set(), *parent[row[0] - 1 : row[1]])
            if support and len(support) != max(support) - min(support) + 1:
                return False
            image.append(support)
        supports.append(image)
    return True


def forward_matches(sites, size, layers):
    source = [site in sites for site in range(1, size + 1)]
    images = explicit_dilation(source, layers)
    return all(
        all(image[site - 1] for site in layer.required)
        and not any(image[site - 1] for site in layer.forbidden)
        for layer, image in zip(layers, images)
    )


def compare_inverse(costs, layers):
    size = len(costs)
    try:
        index = SeedBlockIndex(costs, layers)
    except ValueError:
        assert not explicit_certificate(size, layers)
        return 0
    assert explicit_certificate(size, layers)
    candidates = []
    for mask in product((False, True), repeat=size):
        sites = tuple(site for site, selected in enumerate(mask, 1) if selected)
        if not forward_matches(sites, size, layers):
            continue
        candidates.append((sum(costs[site - 1] for site in sites), sites))

    blocks = [None] + [
        (left, right) for left in range(1, size + 1) for right in range(left, size + 1)
    ]
    eligible = []
    for source_site in range(1, size + 1):
        singleton = [site == source_site for site in range(1, size + 1)]
        images = explicit_dilation(singleton, layers)
        safe = all(
            not any(image[site - 1] for site in layer.forbidden)
            for layer, image in zip(layers, images)
        )
        if safe:
            eligible.append(source_site)
    assert index.eligible_sites == tuple(eligible)

    by_block = {}
    for block in blocks:
        available = [
            (cost, sites)
            for cost, sites in candidates
            if block is None or all(not block[0] <= site <= block[1] for site in sites)
        ]
        expected = min((cost for cost, _ in available), default=None)
        by_block[block] = expected
        result = index.solve(block)
        blocker = index.blocking_observation(block)
        assert index.min_cost(block) == expected, (costs, layers, block, expected)
        if expected is None:
            assert result is None and blocker is not None
            layer, site = blocker
            assert site in layers[layer - 1].required
            survivors = [
                physical in eligible and (block is None or not block[0] <= physical <= block[1])
                for physical in range(1, size + 1)
            ]
            assert not explicit_dilation(survivors, layers)[layer - 1][site - 1]
        else:
            assert blocker is None
            assert result.cost == expected and (result.cost, result.sites) in available
    for site in range(1, size + 1):
        expected = min((cost for cost, sites in candidates if site in sites), default=None)
        assert index.min_cost_including(site) == expected
    for budget in range(-1, sum(costs) + 2):
        broken = [
            block for block in blocks[1:] if by_block[block] is None or by_block[block] > budget
        ]
        expected = min(broken, key=lambda block: (block[1] - block[0], block[0]), default=None)
        assert index.shortest_budget_break(budget) == expected
    return len(blocks)


def test_ranges():
    count = 0
    arrays = (
        array for size in range(1, 8) for array in product((-1, 0, 1), repeat=size)
    )
    rng = Random(4358)
    extended = [tuple(rng.randrange(-100, 101) for _ in range(size)) for size in (47, 63, 126)]
    for values in (*arrays, *extended):
        rmq = _RangeMinimum(values)
        maximum = _MaximumRise(values)
        for a in range(len(values)):
            peak = 0
            minimum = a
            for b in range(a, len(values)):
                peak = max(peak, values[b] - values[minimum])
                if values[b] <= values[minimum]:
                    minimum = b
                assert rmq.query(a, b) == minimum
                best = maximum.query(a, b)
                if best is None:
                    assert peak == 0
                else:
                    start, end = best
                    assert a <= start < end <= b and values[end] - values[start] == peak > 0
                count += 1
    return count


def random_layers(rng, size, trial):
    layers = []
    widths = [size]
    for _ in range(rng.randrange(1, 5)):
        parent = rng.randrange(len(widths))
        parent_size = widths[parent]
        width = rng.randrange(0, 8)
        radius = rng.randrange(0, 3)
        anchors = sorted(rng.choices(range(1, parent_size + 1), k=width)) if parent_size else ()
        if trial % 7 == 0:
            anchors = tuple(reversed(anchors))
        rows = tuple(
            (max(1, anchor - radius), min(parent_size, anchor + radius))
            if parent_size and rng.randrange(6) != 0 else None
            for anchor in (anchors if parent_size else (0,) * width)
        )
        layers.append(Layer(parent, rows))
        widths.append(width)

    hidden = [rng.random() < 0.35 for _ in range(size)]
    explicit = explicit_dilation(hidden, layers)
    result = []
    for layer, image in zip(layers, explicit):
        required, forbidden = [], []
        for site, flag in enumerate(image, 1):
            if trial % 3 == 0 and rng.random() < 0.25:
                flag = not flag
            if rng.random() < 0.6:
                (required if flag else forbidden).append(site)
        result.append(Layer(layer.parent, layer.rows, tuple(required), tuple(forbidden)))
    return tuple(result)


def test_inverse():
    rng = Random(20010)
    examples = (
        ((), ()),
        ((0, 0, 0), ()),
        ((1,), (Layer(0, (None,), (1,)),)),
        ((1,), (Layer(0, ((1, 1),), (1,), (1,)),)),
        # A forbidden hole in source coordinates disappears in eligible-source ranks.
        ((0, 0, 1), (Layer(0, ((1, 3), (2, 2)), (1,), (2,)),)),
        # A genuine hole in a reverse support cannot be replaced by its hull.
        (
            (0, 0, 1),
            (Layer(0, ((1, 1), (3, 3))), Layer(1, ((1, 2),), (1,))),
        ),
        # A non-monotone leaf is sound, but cannot serve as a parent under this encoding.
        (
            (0, 0, 1),
            (Layer(0, ((3, 3), (1, 1))), Layer(1, ((2, 2),), (1,))),
        ),
        demonstration(),
    )
    count = 0
    rejected = 0
    for costs, layers in examples:
        checked = compare_inverse(costs, layers)
        count += checked
        rejected += checked == 0
    for trial in range(432):
        size = trial % 10
        costs = tuple(rng.randrange(6) for _ in range(size))
        layers = random_layers(rng, size, trial)
        checked = compare_inverse(costs, layers)
        count += checked
        rejected += checked == 0
    return count, rejected


def main():
    range_checks = test_ranges()
    inverse_checks, rejected = test_inverse()
    print(f"{range_checks} RMQ/rise intervals and {inverse_checks} exact outage cases passed.")
    print(f"{rejected} cases outside the compact certificate matched the explicit rejection oracle.")


if __name__ == "__main__":
    main()
