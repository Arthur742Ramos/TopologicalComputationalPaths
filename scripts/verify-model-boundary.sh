#!/usr/bin/env bash
set -euo pipefail

# Direct replay of actual declarations, without a synthetic Challenge module.
# CLI/dependency format source: pinned lean4export Main.lean and Export.lean.
# Axiom/extension configuration source: pinned nanoda_lib src/util.rs.
repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
manifest_path=${1:-"$repository_root/model-boundary-replay.json"}
nanoda_config="$repository_root/nanoda-model-boundary.json"
cache_root=${MODEL_BOUNDARY_REPLAY_CACHE:-"$repository_root/.cache/model-boundary-replay"}
python_command=${PYTHON:-python3}
lean4export_commit=4e7915201d3f9f04470d9eae002fa695f7cdc589
nanoda_commit=68d5ca9db226849b41a6fff59d796ff19d0a8840

if [ "$#" -gt 1 ]; then
  echo "usage: $0 [selection-manifest.json]" >&2
  exit 2
fi
for required_command in cargo git lake "$python_command"; do
  command -v "$required_command" >/dev/null 2>&1 || {
    echo "error: $required_command is required for model-boundary replay" >&2
    exit 1
  }
done

mkdir -p "$cache_root"
cache_root=$(cd "$cache_root" && pwd)
lean4export_dir="$cache_root/lean4export"
nanoda_dir="$cache_root/nanoda"
evidence_dir="$cache_root/evidence"
mkdir -p "$evidence_dir"
cd "$repository_root"
# Write files first so a failed validator cannot be hidden by process substitution.
"$python_command" scripts/audit_model_boundary.py "$manifest_path" \
  --nanoda-config "$nanoda_config" --list modules > "$evidence_dir/modules.txt"
"$python_command" scripts/audit_model_boundary.py "$manifest_path" \
  --list declarations > "$evidence_dir/declarations.txt"
mapfile -t modules < "$evidence_dir/modules.txt"
mapfile -t declarations < "$evidence_dir/declarations.txt"
"$python_command" - "$manifest_path" "$lean4export_commit" "$nanoda_commit" <<'PY'
import json, sys
from pathlib import Path
manifest = json.loads(Path(sys.argv[1]).read_text(encoding='utf-8'))
if (manifest['lean4export_commit'], manifest['nanoda_commit']) != tuple(sys.argv[2:]):
    raise SystemExit('error: manifest does not match pinned replay tools')
toolchain = Path('lean-toolchain').read_text(encoding='utf-8').strip()
if toolchain != f"leanprover/lean4:v{manifest['lean_version']}":
    raise SystemExit('error: manifest does not match project Lean toolchain')
PY

checkout_exact() {
  local repository=$1 destination=$2 commit=$3
  if [ ! -d "$destination/.git" ]; then
    git clone --filter=blob:none "$repository" "$destination"
  fi
  if [ "$(git -C "$destination" remote get-url origin)" != "$repository" ]; then
    echo "error: cached replay-tool origin differs from the pinned repository" >&2
    exit 1
  fi
  if [ -n "$(git -C "$destination" status --porcelain --untracked-files=normal)" ]; then
    echo "error: cached replay-tool checkout has local changes" >&2
    exit 1
  fi
  git -C "$destination" fetch --depth 1 origin "$commit"
  git -C "$destination" checkout --detach "$commit"
  [ "$(git -C "$destination" rev-parse HEAD)" = "$commit" ] || {
    echo "error: replay-tool checkout is not at its pinned commit" >&2
    exit 1
  }
}

checkout_exact https://github.com/leanprover/lean4export.git "$lean4export_dir" "$lean4export_commit"
checkout_exact https://github.com/robsimmons/nanoda_lib.git "$nanoda_dir" "$nanoda_commit"
project_toolchain=$(tr -d '[:space:]' < "$repository_root/lean-toolchain")
export_toolchain=$(tr -d '[:space:]' < "$lean4export_dir/lean-toolchain")
if [ "$project_toolchain" != "$export_toolchain" ]; then
  echo "error: project and pinned exporter Lean toolchains differ" >&2
  exit 1
fi

export LEAN_NUM_THREADS=1
(cd "$lean4export_dir" && lake build lean4export)
(cd "$nanoda_dir" && cargo build --release --locked -j 1)
lake exe cache get
for module in "${modules[@]}"; do
  lake build "$module"
done
lake env "$lean4export_dir/.lake/build/bin/lean4export" \
  "${modules[@]}" -- "${declarations[@]}" > "$evidence_dir/model-boundary.ndjson"
"$python_command" scripts/audit_model_boundary.py "$manifest_path" \
  "$evidence_dir/model-boundary.ndjson" --nanoda-config "$nanoda_config" \
  > "$evidence_dir/export-audit.json"
cat "$evidence_dir/export-audit.json"
"$nanoda_dir/target/release/nanoda_bin" "$nanoda_config" \
  < "$evidence_dir/model-boundary.ndjson" 2>&1 | tee "$evidence_dir/nanoda.log"
git rev-parse HEAD > "$evidence_dir/source-commit.txt"
cp "$manifest_path" "$evidence_dir/selection.json"
cp "$nanoda_config" "$evidence_dir/nanoda-config.json"
echo "Selected-declaration export audit and independent NanoDa replay passed"
