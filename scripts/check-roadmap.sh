#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repository_root"

case "${1:-}" in
  "") lake build RoadmapChallenge RoadmapSolution ;;
  --skip-build) ;;
  *) echo "usage: $0 [--skip-build]" >&2; exit 2 ;;
esac

challenge_lines=$(wc -l < RoadmapChallenge.lean)
challenge_bytes=$(wc -c < RoadmapChallenge.lean)
if [ "$challenge_lines" -gt 1000 ] || [ "$challenge_bytes" -gt 102400 ]; then
  echo "RoadmapChallenge.lean exceeds Palomar's statement limit" >&2
  exit 1
fi

if [ "$(rg -n '\bsorry\b' RoadmapChallenge.lean | wc -l | tr -d ' ')" -ne 1 ]; then
  echo "RoadmapChallenge.lean must have one statement-side placeholder" >&2
  exit 1
fi

if rg -n '\bsorry\b|\badmit\b|^axiom |native_decide|Lean\.ofReduceBool' \
    RoadmapSolution.lean ComputationalPaths; then
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
print('Roadmap Comparator configuration validation passed')
PY

git diff --check
echo "Roadmap selection gate passed: ${challenge_lines} lines/${challenge_bytes} bytes"
