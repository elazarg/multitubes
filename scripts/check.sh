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

echo "== application package rebuilds =="
application_count=0
while IFS= read -r app_lakefile; do
  application_count=$((application_count + 1))
  app_dir=$(dirname "$app_lakefile")
  echo "-- $app_dir"
  rm -rf "$app_dir/.lake/build"
  app_log=$(mktemp)
  (cd "$app_dir" && lake build) 2>&1 | tee "$app_log"
  app_errors=$(grep -c 'error:' "$app_log")
  app_warnings=$(grep -c 'warning:' "$app_log")
  echo "errors $app_errors, warnings $app_warnings"
  [ "$app_errors" -eq 0 ] && [ "$app_warnings" -eq 0 ] || status=1
done < <(find Applications -mindepth 2 -maxdepth 2 -name lakefile.toml -print | sort)
echo "application packages $application_count"

echo "== environment audit =="
lake env lean scripts/audit.lean || status=1
grep -q . scripts/.sorries && { echo "FAIL: declarations depend on sorryAx"; status=1; }
echo "axioms: $(tr '\n' ' ' < scripts/.axioms)"

echo "== docstrings =="
python3 scripts/check-docstrings.py || status=1

echo "== layering =="
python3 scripts/check-layering.py || status=1

echo "== line length and set_option =="
lean_files=$(find Maths.lean Maths Applications -path '*/.lake' -prune -o -name '*.lean' -print)
long=$(awk 'length > 100 {print FILENAME":"FNR}' $lean_files)
[ -n "$long" ] && { echo "FAIL: over 100 chars"; echo "$long"; status=1; }
opts=$(grep -rn 'set_option' --include=*.lean Maths.lean Maths Applications)
[ -n "$opts" ] && { echo "FAIL: set_option in a committed file"; echo "$opts"; status=1; }

echo
[ "$status" -eq 0 ] && echo "all checks passed" || echo "CHECKS FAILED"
exit "$status"
