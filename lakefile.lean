import Lake
open Lake DSL

package «topological_computational_paths» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"

@[default_target]
lean_lib ComputationalPaths where
  roots := #[`ComputationalPaths]
