#!/usr/bin/env python3
"""Check the two layering claims the library makes in prose.

1. The linear-programming group imports nothing from the project outside itself.
2. `FixedPointTheorems` is imported by `MaxAffine/Eigenproblem` alone. `MaxAffine/Spectrum` is
   its only consumer and reaches Brouwer transitively, so the entry point is a single file.

Both are stated as facts in `README.md` and `CLAUDE.md`; this turns them into checks. The
script keys on directory and file names rather than on the root namespace, so it gives the same
answer before and after a move of the tree under a different umbrella.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# The linear-programming group, by the directory holding it. It has been called both
# `LinearAlgebra` and `LinearProgramming`; accept either so the check survives the rename.
LP_DIRS = {"LinearAlgebra", "LinearProgramming"}

# The only file permitted to reach for a fixed-point theorem.
BROUWER_ALLOWED = {("MaxAffine", "Eigenproblem")}

IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_.]+)", re.MULTILINE)


def project_root_name(files):
    """The single top-level directory the library lives in, e.g. `DirectedTransport` or `Maths`."""
    roots = {f.relative_to(ROOT).parts[0] for f in files}
    if len(roots) != 1:
        sys.exit(f"expected one library root, found {sorted(roots)}")
    return roots.pop()


def main():
    files = sorted(
        p
        for p in ROOT.rglob("*.lean")
        if ".lake" not in p.parts and "scripts" not in p.parts and p.is_file()
    )
    if not files:
        sys.exit("no .lean files found")
    root = project_root_name([p for p in files if len(p.relative_to(ROOT).parts) > 1])

    failures = []
    lp_seen = brouwer_seen = 0

    for path in files:
        parts = path.relative_to(ROOT).with_suffix("").parts
        imports = IMPORT_RE.findall(path.read_text(encoding="utf-8"))
        internal = [i for i in imports if i.split(".")[0] == root]

        # (1) the linear-programming group is closed under project imports
        if len(parts) > 1 and parts[-2] in LP_DIRS:
            lp_seen += 1
            for imp in internal:
                if imp.split(".")[1] not in LP_DIRS:
                    failures.append(f"{path.relative_to(ROOT)}: LP group imports {imp}")

        # (2) Brouwer is confined
        if any(i.split(".")[0] == "FixedPointTheorems" for i in imports):
            brouwer_seen += 1
            if tuple(parts[-2:]) not in BROUWER_ALLOWED:
                failures.append(
                    f"{path.relative_to(ROOT)}: imports FixedPointTheorems, which only "
                    "MaxAffine/Eigenproblem may do"
                )

    print(f"library root      : {root}")
    print(f"files scanned     : {len(files)}")
    print(f"linear-programming: {lp_seen} files, closed under project imports")
    print(f"FixedPointTheorems: {brouwer_seen} importers")

    if failures:
        print("\nFAIL")
        for f in failures:
            print("  " + f)
        return 1
    print("\nOK — both layering claims hold")
    return 0


if __name__ == "__main__":
    sys.exit(main())
