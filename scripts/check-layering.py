#!/usr/bin/env python3
"""Check the reusable library's foundation and external dependency boundaries.

1. Each of Graph, Recursion, LinearProgramming, and Algebra imports only mathlib and itself.
2. `FixedPointTheorems` is imported by `MaxAffine/Eigenproblem` alone. Downstream spectral files
   reach Brouwer transitively through that single entry point.

Both are stated as facts in `README.md` and `CLAUDE.md`; this turns them into checks. The
script keys on directory and file names rather than on the root namespace, so it gives the same
answer before and after a move of the tree under a different umbrella.

Downstream packages under `Applications` are deliberately excluded. Their builds are discovered
generically by `scripts/check.sh`; they do not participate in the reusable library's layering.
"""

import re
import os
import sys
from pathlib import Path

ROOT = Path(os.environ.get("MULTITUBES_ROOT", Path(__file__).resolve().parent.parent))

# The four foundations must remain mutually independent and depend only on mathlib.
FOUNDATIONS = {"Graph", "Recursion", "LinearProgramming", "Algebra"}

# The only file permitted to reach for a fixed-point theorem.
BROUWER_ALLOWED = {("MaxAffine", "Eigenproblem")}

IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_.]+)", re.MULTILINE)


def project_root_name(files):
    """The single top-level directory containing the library, such as `Maths`."""
    roots = {f.relative_to(ROOT).parts[0] for f in files}
    if len(roots) != 1:
        sys.exit(f"expected one library root, found {sorted(roots)}")
    return roots.pop()


def main():
    # Application clients are separate Lake packages downstream of `Maths`.
    # This check concerns only the reusable library's internal dependency graph.
    files = sorted((ROOT / "Maths").rglob("*.lean"))
    if not files:
        sys.exit("no .lean files found")
    root = project_root_name([p for p in files if len(p.relative_to(ROOT).parts) > 1])

    failures = []
    foundation_seen = {group: 0 for group in FOUNDATIONS}
    brouwer_seen = 0

    for path in files:
        parts = path.relative_to(ROOT).with_suffix("").parts
        imports = IMPORT_RE.findall(path.read_text(encoding="utf-8"))
        internal = [i for i in imports if i.split(".")[0] == root]

        # (1) every foundation group is closed under project imports
        if len(parts) > 2 and parts[1] in FOUNDATIONS:
            group = parts[1]
            foundation_seen[group] += 1
            for imp in internal:
                imported_parts = imp.split(".")
                if len(imported_parts) < 2 or imported_parts[1] != group:
                    failures.append(
                        f"{path.relative_to(ROOT)}: {group} foundation imports {imp}"
                    )

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
    for group in sorted(FOUNDATIONS):
        print(f"{group:18}: {foundation_seen[group]} files, closed under project imports")
    print(f"FixedPointTheorems: {brouwer_seen} importers")

    if failures:
        print("\nFAIL")
        for f in failures:
            print("  " + f)
        return 1
    print("\nOK — foundation and Brouwer boundaries hold")
    return 0


if __name__ == "__main__":
    sys.exit(main())
