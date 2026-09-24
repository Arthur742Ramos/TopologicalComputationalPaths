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
  "") lake build RoadmapChallenge RoadmapSolution RoadmapRegistryChallenge RoadmapRegistrySolution ;;
  --skip-build) ;;
  *) echo "usage: $0 [--skip-build]" >&2; exit 2 ;;
esac

challenge_lines=$(wc -l < RoadmapChallenge.lean)
challenge_bytes=$(wc -c < RoadmapChallenge.lean)
if [ "$challenge_lines" -gt 1000 ] || [ "$challenge_bytes" -gt 102400 ]; then
  echo "RoadmapChallenge.lean exceeds Palomar's statement limit" >&2
  exit 1
fi

if [ "$(search_lean '\bsorry\b' RoadmapChallenge.lean | wc -l | tr -d ' ')" -ne 1 ]; then
  echo "RoadmapChallenge.lean must have one statement-side placeholder" >&2
  exit 1
fi

registry_lines=$(wc -l < RoadmapRegistryChallenge.lean)
registry_bytes=$(wc -c < RoadmapRegistryChallenge.lean)
if [ "$registry_lines" -gt 1000 ] || [ "$registry_bytes" -gt 102400 ]; then
  echo "RoadmapRegistryChallenge.lean exceeds Palomar's statement limit" >&2
  exit 1
fi
if [ "$(search_lean '\bsorry\b' RoadmapRegistryChallenge.lean | wc -l | tr -d ' ')" -ne 2 ]; then
  echo "RoadmapRegistryChallenge.lean must have two statement placeholders" >&2
  exit 1
fi
if grep '^import ' RoadmapRegistryChallenge.lean | grep -Ev '^import (Mathlib|Lean)(\.|$)'; then
  echo "Registry challenge imports a local development" >&2
  exit 1
fi

if search_lean '\bsorry\b|\badmit\b|^axiom |native_decide|Lean\.ofReduceBool' \
    RoadmapSolution.lean RoadmapRegistrySolution.lean ComputationalPaths; then
  echo "forbidden proof marker in roadmap solution or development" >&2
  exit 1
fi

"${PYTHON:-python3}" - <<'PY'
import json
from pathlib import Path
config = json.loads(Path('comparator-roadmap.json').read_text(encoding='utf-8'))
assert config['challenge_module'] == 'RoadmapChallenge'
assert config['solution_module'] == 'RoadmapSolution'
assert config['theorem_names'] == ['TopologicalComputationalPathsRoadmap.roadmap_result']
assert config['enable_nanoda'] is True
registry = json.loads(Path('comparator-registry-roadmap.json').read_text(encoding='utf-8'))
assert registry['challenge_module'] == 'RoadmapRegistryChallenge'
assert registry['solution_module'] == 'RoadmapRegistrySolution'
assert registry['theorem_names'] == [
    'TopologicalComputationalPathsRoadmapRegistry.open_arrow_pair_quotient',
    'TopologicalComputationalPathsRoadmapRegistry.ordinary_composition_continuous',
]
assert registry['enable_nanoda'] is True
print('Roadmap Comparator configuration validation passed')
PY

ruby scripts/validate-formalization.rb formalization-registry-roadmap.yaml

git diff --check
echo "Roadmap selection gate passed: ${challenge_lines} lines/${challenge_bytes} bytes"
