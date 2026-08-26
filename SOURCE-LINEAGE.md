# Source lineage

This extraction starts from the following parent snapshot:

- repository: `https://github.com/Arthur742Ramos/ComputationalPathsLean`
- tag: `topological-paper-v12`
- commit: `2a2baa1f31c68f0e696021db91f8381dd2854652`
- parent Lean toolchain: `leanprover/lean4:v4.24.0`

The initial port boundary is the scoped geometric rewrite layer and its
topological groupoid results:

```text
ComputationalPaths/Path/Topology/WeightedConcatenation.lean
ComputationalPaths/Path/Topology/ScopedGeometricRewrite.lean
ComputationalPaths/Path/Topology/ScopedGeometricRewriteQuotient.lean
ComputationalPaths/Path/Topology/ScopedGeometricRewriteGroupoid.lean
ComputationalPaths/Path/Topology/ScopedGeometricRewriteComparison.lean
```

The functoriality, fundamental-groupoid, circle, torus, and obstruction modules
remain supporting candidates.  They are not silently treated as part of the
minimal publication claim until their dependency closure and theorem scope
have been checked in this repository.

The parent worktree is not a submodule of this repository.  The exact focused
source commit is recorded in the submission receipt, together with any
theorem-statement changes made during the port.
