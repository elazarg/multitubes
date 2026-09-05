#!/usr/bin/env python3
"""Check project doc references against declarations from every compiled environment."""

import re
import os
import sys
import tomllib
from pathlib import Path

ROOT = Path(os.environ.get("MULTITUBES_ROOT", Path(__file__).resolve().parent.parent))
SECTION = re.compile(r"^##\s+Main\s+(definitions|results|statements)\s*$", re.MULTILINE)
NEXT_HEADING = re.compile(r"^##\s+", re.MULTILINE)
TICKED = re.compile(r"`([^`\n]+)`")
NAME = re.compile(r"^[A-Z][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)+$")


def target(lakefile: Path) -> str:
    values = tomllib.loads(lakefile.read_text(encoding="utf-8")).get("defaultTargets", [])
    if len(values) != 1:
        raise ValueError(f"{lakefile}: expected one default target")
    return values[0]


def closure(decls):
    namespaces = set()
    for declaration in decls:
        parts = declaration.split(".")
        namespaces.update(".".join(parts[:i]) for i in range(1, len(parts)))
    return decls | namespaces


def modules_for(paths, base: Path):
    modules = set()
    for path in paths:
        module = str(path.relative_to(base).with_suffix("")).replace("/", ".")
        parts = module.split(".")
        modules.update(".".join(parts[:i]) for i in range(1, len(parts) + 1))
    return modules


def main():
    maths_dump = ROOT / ".lake" / "audit" / "Maths.decls"
    if not maths_dump.exists():
        sys.exit("run the environment audits first")
    maths = set(maths_dump.read_text(encoding="utf-8").splitlines())
    core_files = [ROOT / "Maths.lean", *sorted((ROOT / "Maths").rglob("*.lean"))]
    core_modules = modules_for(core_files, ROOT)
    environments = [(core_files, "Maths", closure(maths) | core_modules)]
    for lakefile in sorted((ROOT / "Applications").glob("*/lakefile.toml")):
        module = target(lakefile)
        dump = ROOT / ".lake" / "audit" / f"{module}.decls"
        if not dump.exists():
            sys.exit(f"missing application audit: {dump.name}")
        own = set(dump.read_text(encoding="utf-8").splitlines())
        app_files = sorted(
            path for path in lakefile.parent.rglob("*.lean") if ".lake" not in path.parts
        )
        resolvable = closure(maths | own) | core_modules | modules_for(app_files, lakefile.parent)
        environments.append((app_files, module, resolvable))

    drift, dangling, checked, prose_checked = [], [], 0, 0
    for files, module, resolvable in environments:
        for path in files:
            text = path.read_text(encoding="utf-8")
            indexed = set()
            for match in SECTION.finditer(text):
                rest = text[match.end():]
                next_heading = NEXT_HEADING.search(rest)
                body = rest[:next_heading.start()] if next_heading else rest
                for name in map(str.strip, TICKED.findall(body)):
                    if NAME.match(name) and name.split(".")[0] in {"Maths", module}:
                        indexed.add(name)
                        checked += 1
                        if name not in resolvable:
                            drift.append(f"{path.relative_to(ROOT)}: {name}")
            for name in map(str.strip, TICKED.findall(text)):
                if not NAME.match(name) or name in indexed:
                    continue
                if name.split(".")[0] not in {"Maths", module}:
                    continue
                prose_checked += 1
                if name not in resolvable:
                    dangling.append(f"{path.relative_to(ROOT)}: {name}")

    print(f"index names checked        : {checked}, unresolved {len(drift)}")
    print(f"project prose references   : {prose_checked}, unresolved {len(dangling)}")
    if drift:
        print("\nDRIFT — indexed name does not resolve:")
        print("\n".join("  " + item for item in sorted(set(drift))))
    if dangling:
        print("\nDANGLING — prose name does not resolve:")
        print("\n".join("  " + item for item in sorted(set(dangling))))
    return int(bool(drift or dangling))


if __name__ == "__main__":
    sys.exit(main())
