#!/usr/bin/env bash
set -euo pipefail
repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repository_root"
lake build PreimageChallenge PreimageSolution PreimageTests PreimageAdversarial PreimageBenchmarks \
  ComputationalPaths.Path.Topology.TorusConstraintApplication
diff -u PreimageTests.lean <(python3 scripts/test-torus-preimage.py --lean)
diff -u PreimageBenchmarks.lean <(python3 scripts/test-torus-preimage.py --lean --benchmark)
if [ "$(wc -l < PreimageChallenge.lean)" -gt 1000 ] || \
   [ "$(wc -c < PreimageChallenge.lean)" -gt 102400 ]; then
  echo "Preimage challenge exceeds statement size limit" >&2
  exit 1
fi
echo "Generated fixture parity and challenge size passed"
if command -v rg >/dev/null 2>&1; then
  search=(rg -n)
  count=(rg -c)
else
  search=(grep -En)
  count=(grep -Ec)
fi
if "${search[@]}" '\bsorry\b|\badmit\b|^axiom |native_decide|Lean\.ofReduceBool' \
  ComputationalPaths/Path/Topology/CertifiedTorusPreimage*.lean \
  ComputationalPaths/Path/Topology/TorusConstraintApplication.lean \
  PreimageSolution.lean PreimageTests.lean PreimageAdversarial.lean PreimageBenchmarks.lean; then
  echo "Forbidden proof marker in preimage implementation" >&2
  exit 1
fi
if [ "$("${count[@]}" '\bsorry\b' PreimageChallenge.lean)" != 1 ]; then
  echo "Expected one statement-side hole" >&2
  exit 1
fi
python3 scripts/test-torus-preimage.py
git diff --check
echo "Preimage quality gate passed"
