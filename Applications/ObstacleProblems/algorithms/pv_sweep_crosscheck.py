"""Cross-check the metered excerpt against the production storage sweep."""
import csv
from fractions import Fraction as Q

from obstacle_sweep import Step, sweep
from pv_cut_check import EXCERPT, replay, verify


def check_production():
    with EXCERPT.open(newline="") as file:
        data = [(Q(row["pv_kwh"]), Q(row["load_kwh"])) for row in csv.DictReader(file)]
    capacity = Q(4)
    _, thresholds, floor, _ = verify(data, capacity)

    # Each measured pv_kwh is kWh at multiplier 1. Keep the excerpt's units;
    # the Step forcing is per unit of a dimensionless multiplier.
    steps = [Step(gain=1, shift=-load, forcing=pv, lower=0, upper=capacity)
             for pv, load in data]
    result = sweep(steps, initial=(0, capacity))
    knots = sorted({t for (pv, _), t in zip(data, thresholds) if pv and t > 0})
    assert [t for t in result.shortfall.knots if t > 0] == knots
    bounds = [Q(0), *knots, knots[-1] + 1]
    for left, right in zip(bounds, bounds[1:]):
        # Two distinct interior comparisons certify these affine restrictions.
        for theta in (left, (2 * left + right) / 3, (left + 2 * right) / 3, right):
            expected = floor + sum(pv * max(0, threshold - theta)
                                   for (pv, _), threshold in zip(data, thresholds))
            assert result.shortfall(theta) == expected
    target = Q(10)
    parameter = result.shortfall.first_at_most(target)
    assert parameter == Q(3926, 2377)
    assert (result.shortfall(parameter), result.spill(parameter), result.final(parameter)) == (
        replay(data, capacity, parameter)
    )
    print(f"Production sweep agrees on all {len(knots)} positive knots, the entire import curve,"
          f" and minimum dimensionless PV multiplier {parameter} for {target} kWh import.")


if __name__ == "__main__":
    check_production()
