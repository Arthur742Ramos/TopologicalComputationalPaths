#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repository_root"

search_lean() {
  local pattern=$1
  shift
  if command -v rg >/dev/null 2>&1; then
    rg -n "$pattern" "$@" --glob '*.lean'
  else
    grep -REn --include='*.lean' "$pattern" "$@"
  fi
}

case "${1:-}" in
  "") lake build ;;
  --skip-build) ;;
  *) echo "usage: $0 [--skip-build]" >&2; exit 2 ;;
esac

challenge_lines=$(wc -l < Challenge.lean)
challenge_bytes=$(wc -c < Challenge.lean)
if [ "$challenge_lines" -gt 1000 ] || [ "$challenge_bytes" -gt 102400 ]; then
  echo "Challenge.lean exceeds Palomar's 1,000-line/100 KiB limit" >&2
  echo "observed: ${challenge_lines} lines, ${challenge_bytes} bytes" >&2
  exit 1
fi

if [ "$(search_lean '\bsorry\b' Challenge.lean | wc -l | tr -d ' ')" -ne 1 ]; then
  echo "Challenge.lean must contain exactly one deliberate statement-side sorry" >&2
  exit 1
fi

if search_lean '\bsorry\b|\badmit\b|^axiom |native_decide|Lean\.ofReduceBool' \
  Solution.lean ComputationalPaths; then
  echo "forbidden proof marker found in the proof development" >&2
  exit 1
fi

if search_lean '^axiom |native_decide|Lean\.ofReduceBool' \
  Challenge.lean Solution.lean ComputationalPaths; then
  echo "forbidden axiom or evaluator escape found" >&2
  exit 1
fi

ruby scripts/validate-formalization.rb
ruby -ryaml -rjson -e '
  metadata = YAML.safe_load(File.binread("formalization.yaml"), aliases: false)
  main = metadata.dig("status", "main_results", 0)
  comparator_name = main.fetch("comparator_config")
  expected = main.fetch("declaration")
  config = JSON.parse(File.binread(comparator_name))
  abort "NanoDa replay is disabled" unless config["enable_nanoda"] == true
  abort "Comparator theorem target is wrong" unless config["theorem_names"] == [expected]
  puts "Comparator configuration validation passed for #{comparator_name}"
'
git diff --check

echo "Palomar quality gate passed: Challenge.lean is ${challenge_lines} lines/${challenge_bytes} bytes"
