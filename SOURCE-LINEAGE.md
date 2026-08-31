# Source lineage

This extraction starts from the following parent snapshot:

- repository: `https://github.com/Arthur742Ramos/ComputationalPathsLean`
- tag: `topological-paper-v12`
- commit: `2a2baa1f31c68f0e696021db91f8381dd2854652`
- source file: `paper/topological/main.tex`
- immutable source URL: `https://github.com/Arthur742Ramos/ComputationalPathsLean/blob/2a2baa1f31c68f0e696021db91f8381dd2854652/paper/topological/main.tex`
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

The functoriality and fundamental-groupoid modules remain supporting
candidates.  The selected claim now includes standalone genuine circle and
torus winding classifications, built from explicit universal-cover lifting and
standard representatives, plus a focused observable-based-fiber construction
built from the parent's universal
continuous-path presentation.  It names the standard based loop quotient,
proves the quotient homeomorphism and final/ordinary pair comparison, and
then performs the Hawaiian-earring obstruction transfer.  Fabel's
non-quotient-square and discontinuity facts are recorded as explicit
hypotheses rather than silently reproved.

The circle module is the standalone covering/lifting portion of the parent's
`CircleTopologicalRealization.lean`; the torus module is the genuine product
loop portion of `TopologicalTorusScoped.lean`.  The focused versions are
ported to Lean 4.32.0 without importing the parent project.  The selected
statement now exposes these as additive-classification certificates, including
identity, composition additivity, explicit standard representatives, and both
directions of the classification.

The parent worktree is not a submodule of this repository.  The exact focused
source commit is recorded above and in `formalization.yaml`, together with the
theorem-statement and toolchain changes made during the port.  The selected
obstruction-transfer source is
`ComputationalPaths/Path/Topology/ScopedGeometricRewriteHawaiianEarring.lean`
at that same parent snapshot; its Fabel inputs are bibliographic background,
not hidden proof dependencies.  The observable based-fiber layer is a new
focused formalization in this repository, with its universal carrier and
topology made explicit rather than attributed to that source file.

## Follow-up lineage

`ComputationalPaths/Path/Topology/QuotientFundamentalGroup.lean` is new to the
focused follow-up.  It is proved directly against Mathlib's compact-open path
space, endpoint-fixed homotopy quotient, and fundamental-group algebra.  Its
quasitopological-group and homogeneity results are established mathematics;
the research lineage and exact non-novelty boundary are recorded in
`formalization-followup.yaml`, with Calcut--McCarthy and Brazas--Fabel as the
primary literature context.

`ComputationalPaths/Path/Topology/QuotientFundamentalGroupFunctorial.lean`
adds direct compact-open/quotient proofs of continuous induced maps,
homeomorphism invariance, path-based basepoint change, its homotopy-class
independence, its identity and composition laws, naturality under continuous
maps, and binary-product preservation under the explicit product-quotient
hypothesis.  It also exposes pointed homotopy naturality for induced quotient
maps and basepoint invariance of the joint-continuity boundary, together with
the pointed fixed-basepoint homotopy corollary, and the path-connected
all-basepoints joint-continuity and discreteness criteria, the global
homotopy-invariant continuity criterion, and the one-basepoint semilocal
criterion in the locally path-connected setting.  It also formalizes the T1
separation boundary under homotopy and path transport, including its
path-connected all-basepoint and global homotopy-invariance forms.  These are
formalized as structural properties of the established quasitopological
fundamental group, not claimed as new paper theorems.

`ComputationalPaths/Path/Topology/FiniteTorusWinding.lean` extends the earlier
circle and two-torus validation to every finite dimension and connects its
explicit winding proof to the general null-class-openness criterion.  Its
basepoint-transport corollary proves discreteness of every based quotient and
semilocal simple connectivity at every point of every finite torus, together
with a common integer-lattice homeomorphism for all based quotients.  This is
an independently checked formalization of classical topology, not a claim of
a new fundamental-group computation.

`ComputationalPaths/Path/Topology/SemilocallySimplyConnected.lean` now adds a
finite compact-open subdivision theorem and an explicit ladder assembly.  In
locally path-connected spaces, this proves openness of every based-loop
homotopy class and the converse implication from semilocal simple connectivity
to discreteness of every based quotient fundamental group; together with the
general reverse implication, it yields the stated equivalence.  The proof is a
direct Mathlib path/quotient construction rather than an unverified import of
a paper theorem.  The same module now transports quotient discreteness across
homotopy equivalences and basepoint paths, and derives homotopy invariance of
semilocal simple connectivity when both spaces are locally path-connected.
Its multiplicative transport lemma also makes joint quotient multiplication
(equivalently the topological-group boundary) homotopy-invariant at
corresponding basepoints.
