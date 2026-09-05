#!/usr/bin/env bash
# The repository invariants its mathematical claims rest on. Run from the repository root.
set -uo pipefail
cd "$(dirname "$0")/.."
status=0

echo "== clean rebuild =="
rm -rf .lake/build
log=$(mktemp)
scripts/check-command.sh "$log" lake build || status=1

echo "== application package rebuilds =="
application_count=0
while IFS= read -r app_lakefile; do
  application_count=$((application_count + 1))
  app_dir=$(dirname "$app_lakefile")
  echo "-- $app_dir"
  rm -rf "$app_dir/.lake/build"
  app_log=$(mktemp)
  (cd "$app_dir" && ../../scripts/check-command.sh "$app_log" lake build) || status=1
done < <(find Applications -mindepth 2 -maxdepth 2 -name lakefile.toml -print | sort)
echo "application packages $application_count"

echo "== environment audit =="
audit_dir=.lake/audit
rm -rf "$audit_dir"
mkdir -p "$audit_dir"
audit_log=$(mktemp)
AUDIT_NAMESPACE=Maths AUDIT_OUTPUT="$audit_dir/Maths" \
  lake env lean scripts/audit.lean 2>&1 | tee "$audit_log" || status=1
grep -q 'warning:' "$audit_log" && { echo "FAIL: warning in Maths audit"; status=1; }
python3 scripts/audit-applications.py || status=1
for audit_failure in "$audit_dir"/*.sorries "$audit_dir"/*.forbidden; do
  [ -s "$audit_failure" ] && {
    echo "FAIL: $(basename "$audit_failure")"
    cat "$audit_failure"
    status=1
  }
done

echo "== docstrings =="
python3 scripts/check-docstrings.py || status=1

echo "== layering =="
python3 scripts/check-layering.py || status=1

echo "== checker regressions =="
python3 scripts/test-checkers.py || status=1

echo "== line length and set_option =="
lean_files=$(find Maths.lean Maths Applications -path '*/.lake' -prune -o -name '*.lean' -print)
long=$(awk 'length > 100 {print FILENAME":"FNR}' $lean_files)
[ -n "$long" ] && { echo "FAIL: over 100 chars"; echo "$long"; status=1; }
opts=$(grep -rn 'set_option' --include=*.lean Maths.lean Maths Applications)
[ -n "$opts" ] && { echo "FAIL: set_option in a committed file"; echo "$opts"; status=1; }

echo
[ "$status" -eq 0 ] && echo "all checks passed" || echo "CHECKS FAILED"
exit "$status"
