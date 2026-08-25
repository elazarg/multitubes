#!/usr/bin/env bash
# The four invariants the library's claims rest on. Run from the repository root.
set -uo pipefail
cd "$(dirname "$0")/.."
status=0

echo "== clean rebuild =="
rm -rf .lake/build
log=$(mktemp)
lake build 2>&1 | tee "$log"
errors=$(grep -c 'error:' "$log")
warnings=$(grep -c 'warning:' "$log")
echo "errors $errors, warnings $warnings"
[ "$errors" -eq 0 ] && [ "$warnings" -eq 0 ] || status=1

echo "== environment audit =="
lake env lean scripts/audit.lean || status=1
grep -q . scripts/.sorries && { echo "FAIL: declarations depend on sorryAx"; status=1; }
echo "axioms: $(tr '\n' ' ' < scripts/.axioms)"

echo "== docstrings =="
python3 scripts/check-docstrings.py || status=1

echo "== layering =="
python3 scripts/check-layering.py || status=1

echo "== line length and set_option =="
long=$(awk 'length > 100 {print FILENAME":"FNR}' $(find Maths.lean Maths -name '*.lean'))
[ -n "$long" ] && { echo "FAIL: over 100 chars"; echo "$long"; status=1; }
opts=$(grep -rn 'set_option' --include=*.lean Maths.lean Maths)
[ -n "$opts" ] && { echo "FAIL: set_option in a committed file"; echo "$opts"; status=1; }

echo
[ "$status" -eq 0 ] && echo "all checks passed" || echo "CHECKS FAILED"
exit "$status"
