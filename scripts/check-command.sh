#!/usr/bin/env bash
# Run a command, preserving its exit status and rejecting Lean errors or warnings in its output.
set -uo pipefail
log=$1
shift
if "$@" 2>&1 | tee "$log"; then command_status=0; else command_status=1; fi
errors=$(grep -c 'error:' "$log")
warnings=$(grep -c 'warning:' "$log")
echo "errors $errors, warnings $warnings"
[ "$command_status" -eq 0 ] && [ "$errors" -eq 0 ] && [ "$warnings" -eq 0 ]
