#!/usr/bin/env python3
"""Run the kernel audit in every independently compiled application environment."""

import os
import re
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TEMPLATE = ROOT / "scripts" / "audit.lean"


def library_root(lakefile: Path) -> str:
    data = tomllib.loads(lakefile.read_text(encoding="utf-8"))
    targets = data.get("defaultTargets", [])
    if len(targets) != 1:
        raise ValueError(f"{lakefile}: expected one default target")
    return targets[0]


def main() -> int:
    source = TEMPLATE.read_text(encoding="utf-8")
    failures = 0
    lakefiles = sorted((ROOT / "Applications").glob("*/lakefile.toml"))
    selected = set(sys.argv[1:])
    if selected:
        lakefiles = [path for path in lakefiles
                     if path.parent.name in selected or library_root(path) in selected]
        if not lakefiles:
            raise ValueError(f"no application matched {sorted(selected)}")
    for lakefile in lakefiles:
        module = library_root(lakefile)
        generated = re.sub(r"^import Maths$", f"import {module}", source, count=1,
                           flags=re.MULTILINE)
        with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=lakefile.parent,
                                         encoding="utf-8") as audit:
            audit.write(generated)
            audit.flush()
            output = ROOT / ".lake" / "audit" / module
            env = os.environ | {"AUDIT_NAMESPACE": module, "AUDIT_OUTPUT": str(output)}
            result = subprocess.run(["lake", "env", "lean", audit.name], cwd=lakefile.parent,
                                    env=env, check=False, capture_output=True, text=True)
            sys.stdout.write(result.stdout)
            sys.stderr.write(result.stderr)
            failures += result.returncode != 0 or "warning:" in result.stdout + result.stderr
    return int(bool(failures))


if __name__ == "__main__":
    sys.exit(main())
