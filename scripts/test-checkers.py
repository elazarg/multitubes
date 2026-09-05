#!/usr/bin/env python3
"""Small regressions for assurance failures that successful project checks cannot exercise."""

import os
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def run(command, **kwargs):
    return subprocess.run(command, cwd=ROOT, check=False, capture_output=True, text=True, **kwargs)


def main() -> int:
    with tempfile.TemporaryDirectory() as temporary:
        temp = Path(temporary)
        log = temp / "command.log"
        successful = run(["scripts/check-command.sh", str(log), "bash", "-c", "exit 0"])
        assert successful.returncode == 0, "successful command was rejected"
        silent = run(["scripts/check-command.sh", str(log), "bash", "-c", "exit 7"])
        assert silent.returncode != 0, "silent nonzero command exit was accepted"
        warning = run(
            ["scripts/check-command.sh", str(log), "bash", "-c", "echo warning: fixture"]
        )
        assert warning.returncode != 0, "zero-exit warning was accepted"
        error = run(
            ["scripts/check-command.sh", str(log), "bash", "-c", "echo error: fixture"]
        )
        assert error.returncode != 0, "zero-exit error was accepted"

        fixture = temp / "layering"
        source = fixture / "Maths" / "Graph"
        source.mkdir(parents=True)
        (source / "Bad.lean").write_text("import Maths.Recursion.Bad\n", encoding="utf-8")
        layered = run(["python3", "scripts/check-layering.py"],
                      env=os.environ | {"MULTITUBES_ROOT": str(fixture)})
        assert layered.returncode != 0, "cross-foundation import was accepted"

        docs = temp / "docs"
        (docs / ".lake" / "audit").mkdir(parents=True)
        (docs / "Maths").mkdir()
        (docs / "Maths.lean").write_text(
            "/-!\n# Fixture\n## Main definitions\n* `Maths.present`\n-/\n", encoding="utf-8")
        (docs / ".lake" / "audit" / "Maths.decls").write_text(
            "Maths.present\n", encoding="utf-8")
        valid_core = run(["python3", "scripts/check-docstrings.py"],
                         env=os.environ | {"MULTITUBES_ROOT": str(docs)})
        assert valid_core.returncode == 0, valid_core.stdout + valid_core.stderr
        (docs / "Maths.lean").write_text(
            "/-!\n# Fixture\n## Main definitions\n* `Maths.missing`\n-/\n", encoding="utf-8")
        drift = run(["python3", "scripts/check-docstrings.py"],
                    env=os.environ | {"MULTITUBES_ROOT": str(docs)})
        assert drift.returncode != 0, "umbrella doc drift was accepted"
        (docs / "Maths.lean").write_text(
            "/-!\n# Fixture\n## Main definitions\n* `Maths.present`\n-/\n", encoding="utf-8")

        application = docs / "Applications" / "FixtureApp"
        application.mkdir(parents=True)
        (application / "lakefile.toml").write_text(
            'defaultTargets = ["FixtureApp"]\n', encoding="utf-8")
        (application / "FixtureApp.lean").write_text(
            "/-!\n# Fixture\n## Main results\n* `FixtureApp.present`\n-/\n",
            encoding="utf-8",
        )
        (docs / ".lake" / "audit" / "FixtureApp.decls").write_text(
            "FixtureApp.present\n", encoding="utf-8")
        valid_app = run(["python3", "scripts/check-docstrings.py"],
                        env=os.environ | {"MULTITUBES_ROOT": str(docs)})
        assert valid_app.returncode == 0, valid_app.stdout + valid_app.stderr
        (application / "FixtureApp.lean").write_text(
            "/-!\n# Fixture\n## Main results\n* `FixtureApp.missing`\n-/\n",
            encoding="utf-8",
        )
        app_drift = run(["python3", "scripts/check-docstrings.py"],
                        env=os.environ | {"MULTITUBES_ROOT": str(docs)})
        assert app_drift.returncode != 0, "application doc drift was accepted"

        audit_source = (ROOT / "scripts" / "audit.lean").read_text(encoding="utf-8")
        audit_source = audit_source.replace(
            "open Lean Elab Command", "axiom AuditFixture.bad : False\n\nopen Lean Elab Command")
        audit_file = temp / "forbidden.lean"
        audit_file.write_text(audit_source, encoding="utf-8")
        audit_output = temp / "forbidden-audit"
        audited = run(
            ["lake", "env", "lean", str(audit_file)],
            env=os.environ | {
                "AUDIT_NAMESPACE": "AuditFixture",
                "AUDIT_OUTPUT": str(audit_output),
            },
        )
        assert audited.returncode == 0, audited.stdout + audited.stderr
        assert (temp / "forbidden-audit.forbidden").read_text(encoding="utf-8").strip(), (
            "forbidden axiom dependency was not recorded"
        )

    print("checker regressions passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
