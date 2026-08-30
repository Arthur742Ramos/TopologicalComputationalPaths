#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repository_root"

case "${1:-}" in
  "") lake build FollowupChallenge FollowupSolution ;;
  --skip-build) ;;
  *) echo "usage: $0 [--skip-build]" >&2; exit 2 ;;
esac

challenge_lines=$(wc -l < FollowupChallenge.lean)
challenge_bytes=$(wc -c < FollowupChallenge.lean)
if [ "$challenge_lines" -gt 1000 ] || [ "$challenge_bytes" -gt 102400 ]; then
  echo "FollowupChallenge.lean exceeds Palomar's 1,000-line/100 KiB limit" >&2
  exit 1
fi

if [ "$(rg -n '\bsorry\b' FollowupChallenge.lean | wc -l | tr -d ' ')" -ne 1 ]; then
  echo "FollowupChallenge.lean must contain exactly one statement-side sorry" >&2
  exit 1
fi

if rg -n '\bsorry\b|\badmit\b|^axiom |native_decide|Lean\.ofReduceBool' \
  FollowupSolution.lean ComputationalPaths --glob '*.lean'; then
  echo "forbidden proof marker found in the follow-up proof development" >&2
  exit 1
fi

if rg -n '^axiom |native_decide|Lean\.ofReduceBool' \
  FollowupChallenge.lean FollowupSolution.lean ComputationalPaths --glob '*.lean'; then
  echo "forbidden axiom or evaluator escape found" >&2
  exit 1
fi

ruby -rjson -e 'config = JSON.parse(File.binread("comparator-followup.json")); abort "NanoDa replay is disabled" unless config["enable_nanoda"] == true; abort "Comparator theorem target is wrong" unless config["theorem_names"] == ["TopologicalComputationalPathsFollowup.main_result"]; puts "Follow-up Comparator configuration validation passed"'
git diff --check

echo "Follow-up quality gate passed: FollowupChallenge.lean is ${challenge_lines} lines/${challenge_bytes} bytes"
