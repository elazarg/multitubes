"""Compute exact PV-to-storage response curves from one interval CSV."""
import sys
from argparse import ArgumentParser, ArgumentTypeError
from csv import DictReader
from fractions import Fraction as Q
from json import dump
from math import inf
from pathlib import Path

from obstacle_sweep import Step, sweep


def rational_argument(value):
    try:
        return Q(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ArgumentTypeError(f"invalid rational value: {value!r}") from error


def read_steps(path, capacity, retention):
    with path.open(newline="", encoding="utf-8-sig") as source:
        rows = DictReader(source)
        fields = {"load_kwh", "yield_kwh_per_kw"}
        if rows.fieldnames is None or not fields.issubset(rows.fieldnames):
            raise ValueError("CSV must contain load_kwh and yield_kwh_per_kw columns.")
        steps = []
        for row in rows:
            try:
                load = Q(row["load_kwh"])
                solar = Q(row["yield_kwh_per_kw"])
            except (TypeError, ValueError, ZeroDivisionError) as error:
                raise ValueError(f"Invalid rational value on CSV line {rows.line_num}.") from error
            if load < 0 or solar < 0:
                raise ValueError(f"Negative load or yield on CSV line {rows.line_num}.")
            steps.append(Step(retention, -load, solar, 0, capacity))
    if not steps:
        raise ValueError("CSV must contain at least one time interval.")
    return steps


def curve_json(curve):
    return {
        "knots": [str(knot) for knot in curve.knots],
        "lines": [[str(slope), str(offset)] for slope, offset in curve.lines],
    }


def amounts(result, rating):
    return {
        "rating_kw": str(rating),
        "import_kwh": str(result.shortfall(rating)),
        "spill_kwh": str(result.spill(rating)),
    }


def numeric(value):
    if value == inf:
        return "+inf"
    if value == -inf:
        return "-inf"
    return str(value)


def main():
    # Exact output on long lossy traces can contain more than 4,300 digits.
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    parser = ArgumentParser(
        description="Exact PV sizing and storage curves for a given load and generation profile."
    )
    parser.add_argument("csv", type=Path, help="Columns load_kwh and yield_kwh_per_kw")
    parser.add_argument("--capacity", type=rational_argument, required=True, help="Usable capacity in kWh")
    parser.add_argument("--retention", type=rational_argument, default=Q(1),
                        help="Retained fraction per interval (default 1)")
    seed = parser.add_mutually_exclusive_group()
    seed.add_argument("--initial", type=rational_argument, help="Initial kWh for finite replay (default full)")
    seed.add_argument("--periodic", action="store_true",
                      help="Use the steady-state cycle. Retention must be below 1.")
    output = parser.add_mutually_exclusive_group()
    output.add_argument("--budget", type=rational_argument,
                        help="Find the smallest nonnegative rating meeting this import cap in kWh")
    output.add_argument("--rating", type=rational_argument, help="Evaluate the model at this rating in kW")
    args = parser.parse_args()

    if args.capacity < 0 or not 0 <= args.retention <= 1:
        parser.error("capacity must be nonnegative and retention in [0, 1]")
    initial = args.capacity if args.initial is None else args.initial
    if not 0 <= initial <= args.capacity:
        parser.error("initial charge must be within the battery capacity")
    if args.periodic and args.retention == 1:
        parser.error("periodic mode requires retention below one")
    if any(value is not None and value < 0 for value in (args.budget, args.rating)):
        parser.error("rating and import budget must be nonnegative")

    try:
        steps = read_steps(args.csv, args.capacity, args.retention)
    except (OSError, ValueError) as error:
        parser.error(str(error))

    result = sweep(steps, (0, initial), periodic=args.periodic)
    if args.rating is not None:
        answer = amounts(result, args.rating)
    elif args.budget is not None:
        crossing = result.shortfall.first_at_most(args.budget)
        answer = {"rating_kw": None} if crossing == inf else amounts(result, max(Q(0), crossing))
    else:
        answer = {
            "import_curve_kwh": curve_json(result.shortfall),
            "spill_curve_kwh": curve_json(result.spill),
            "contacts_kw": [
                {"empty_through": numeric(c.lower_through), "full_from": numeric(c.upper_from)}
                for c in result.contacts
            ],
        }
    dump(answer, sys.stdout, indent=2)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
