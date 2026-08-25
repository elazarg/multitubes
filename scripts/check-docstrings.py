#!/usr/bin/env python3
"""Check that docstrings name things that exist.

Two checks over the module docstrings, against the environment dumped by `scripts/audit.lean`:

1. **Drift.** Every backticked name in a `## Main definitions` or `## Main results` section must
   resolve, as a declaration, a namespace containing one, or a module. These sections are the
   library's own index; a name that no longer resolves is a promise the tree stops keeping, and
   nothing in the build reads them.
2. **Module references.** Every other backticked `Maths.…` in a docstring must resolve as a
   declaration, a namespace, *or* a module in the tree. This catches a prose reference to a file
   that has moved, which check 1 cannot see because it only reads the index sections.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DECLS = ROOT / "scripts" / ".decls"

SECTION = re.compile(r"^##\s+Main\s+(definitions|results|statements)\s*$", re.MULTILINE)
NEXT_HEADING = re.compile(r"^##\s+", re.MULTILINE)
TICKED = re.compile(r"`([^`\n]+)`")
NAME = re.compile(r"^Maths(\.[A-Za-z_][A-Za-z0-9_'!?]*)+$")


def main():
    if not DECLS.exists():
        sys.exit("run `lake env lean scripts/audit.lean` first")
    decls = set(DECLS.read_text().split("\n"))
    namespaces = set()
    for d in decls:
        parts = d.split(".")
        for i in range(1, len(parts)):
            namespaces.add(".".join(parts[:i]))
    modules = set()
    for p in ROOT.rglob("*.lean"):
        if ".lake" in p.parts or p.parts[len(ROOT.parts)] not in ("Maths", "Maths.lean"):
            continue
        mod = str(p.relative_to(ROOT).with_suffix("")).replace("/", ".")
        modules.add(mod)
        # a directory such as `Maths.Graph` is a legitimate thing for prose to name
        parts = mod.split(".")
        for i in range(1, len(parts)):
            modules.add(".".join(parts[:i]))

    def resolves(n):
        return n in decls or n in namespaces

    files = sorted(
        p
        for p in ROOT.rglob("*.lean")
        if ".lake" not in p.parts and "scripts" not in p.parts
    )
    drift, badmod, checked, mod_checked = [], [], 0, 0

    for path in files:
        text = path.read_text(encoding="utf-8")
        rel = path.relative_to(ROOT)
        index_names = set()
        for mo in SECTION.finditer(text):
            rest = text[mo.end():]
            nxt = NEXT_HEADING.search(rest)
            body = rest[: nxt.start()] if nxt else rest
            for name in TICKED.findall(body):
                name = name.strip()
                if not NAME.match(name):
                    continue
                index_names.add(name)
                checked += 1
                if not (resolves(name) or name in modules):
                    drift.append(f"{rel}: {name}")
        for name in TICKED.findall(text):
            name = name.strip()
            if not NAME.match(name) or name in index_names:
                continue
            mod_checked += 1
            if not (resolves(name) or name in modules):
                badmod.append(f"{rel}: {name}")

    print(f"declarations in environment : {len(decls)}")
    print(f"index names checked         : {checked}, unresolved {len(drift)}")
    print(f"other `Maths.…` references  : {mod_checked}, unresolved {len(badmod)}")
    if drift:
        print("\nDRIFT — named in a `## Main ...` section but does not resolve:")
        for d in sorted(set(drift)):
            print("  " + d)
    if badmod:
        print("\nDANGLING — neither a declaration, a namespace, nor a module:")
        for d in sorted(set(badmod)):
            print("  " + d)
    return 1 if drift or badmod else 0


if __name__ == "__main__":
    sys.exit(main())
