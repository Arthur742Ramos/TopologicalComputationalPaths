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
fundamental group, not claimed as new paper theorems.  In addition, when the
target quotient group is abelian, it proves path-choice independence of
basepoint transport even without an endpoint-fixed homotopy between paths;
the underlying theorem only requires the relative loop to be central.  It also
proves that reversing a path gives the inverse continuous multiplicative
transport, completing the groupoid-action coherence.

`ComputationalPaths/Path/Topology/FiniteTorusWinding.lean` extends the earlier
circle and two-torus validation to every finite dimension and connects its
explicit winding proof to the general null-class-openness criterion.  Its
basepoint-transport corollary proves discreteness of every based quotient and
semilocal simple connectivity at every point of every finite torus, together
with a common integer-lattice homeomorphism for all based quotients.  The
classifier is also a continuous multiplicative equivalence to the integer
lattice, and the quotient multiplication is proved commutative at every
basepoint.  It also defines the lattice classifier along an arbitrary explicit
path from the canonical basepoint and proves all such classifiers equal.  This
module additionally proves naturality under arbitrary coordinate-selection
maps between finite tori: the quotient classifier reindexes the winding
vector; the standard representatives and quotient decoder obey the same
reindexing law; the continuous multiplicative lattice classifier obeys that
law even across different dimensions; the coordinate maps satisfy identity and
composition laws; and the path-based classifier satisfies the corresponding
naturality square at arbitrary basepoints after mapping the chosen transport
path.  Abelian-target path independence then yields the same naturality square
for the canonical arbitrary-basepoint classifier without a path parameter.
The lattice reindexings are additionally continuous additive morphisms with
explicit identity/composition laws, and classifier naturality is restated
through that morphism.
For index equivalences, the same construction is upgraded to a torus
homeomorphism and a continuous additive lattice equivalence, again with
identity/composition coherence.
The module also proves the exact injective/surjective correspondence for
surjective/injective index maps at the torus, lattice, and typed quotient
levels, using zero extension for the surjective direction.
For arbitrary index maps it further identifies the image exactly with the
fiber-constant winding vectors, equivalently for typed quotient classes.
It also proves the converse injectivity/surjectivity criteria at the raw
torus, lattice, and typed quotient levels, packages typed quotient coordinate
selection as a contravariant additive functor (continuously for the discrete
quotient topologies), and identifies its kernel by vanishing on the index-map
image.
The arbitrary-basepoint classifier naturality squares are also restated using
the continuous additive reindexing morphism itself.
At arbitrary torus basepoints, the underlying coordinate-selection maps are
also named as continuous multiplicative homomorphisms of quotient fundamental
groups, with identity/composition coherence and a direct classifier
naturality corollary.  The canonical classifiers transport the exact
fiber-constant image, injectivity/surjectivity converse, and
vanishing-on-the-image kernel descriptions to arbitrary basepoints as well.
It also commutes with explicit basepoint transport, providing a naturality
square before any classifier is selected.
The same finite-torus layer now extends coordinate selections to arbitrary
integer matrices: continuous matrix maps act on winding vectors by ordinary
row-by-column multiplication, preserve standard representatives, and induce
typed quotient maps with exact image, kernel, injectivity, and surjectivity
transfer.  Their additive quotient homomorphisms satisfy identity and
composition laws; the lattice and quotient homomorphisms are continuous for
the discrete quotient topologies.  At arbitrary torus basepoints, matrix maps
are also exposed as continuous multiplicative quotient homomorphisms commuting
with explicit basepoint transport.  The path-based classifier naturality
theorem records the endpoint cast from the mapped zero basepoint explicitly,
and abelian-target path independence gives the same square for the canonical
arbitrary-basepoint classifier.  The same classifier transports the exact
matrix image, kernel, injectivity, and surjectivity iff criteria to every
chosen basepoint, each as an explicit iff theorem for the arbitrary-basepoint
quotient homomorphism.  The arbitrary-basepoint homomorphisms also satisfy
typed contravariant composition and identity laws, with endpoint casts induced
by the matrix-map coherence equations.
When an explicit two-sided integer inverse is available, the same construction
also packages a continuous additive equivalence of winding lattices, a torus
homeomorphism, and quotient homeomorphism and continuous additive equivalence
for the transported loop groups.  At every arbitrary torus basepoint, it also
packages a continuous multiplicative quotient equivalence, with explicit
injectivity and surjectivity consequences.
For square matrices, the adjugate-based nonsingular inverse is available
canonically when the determinant is a unit.  The formalization records the
sharp determinant criteria for lattice and quotient injectivity and
surjectivity, and instantiates the canonical inverse through all of the
equivalence layers, including arbitrary basepoints.
It also imports the finite-index theorem for integer linear maps: whenever the
determinant is nonzero, the winding-lattice cokernel is finite with cardinality
`Int.natAbs (Matrix.det A)`, and finiteness is exposed as a separate theorem.
Through the canonical winding classifier, the induced quotient image has the
same exact index and finite cokernel cardinality, with both index and cardinal
forms proved in the quotient-group interface.
The lattice theorem also exposes a Smith-normal-form equivalence with a
product of finite cyclic `ZMod` factors after proving the image has full rank.
It is an independently checked formalization of classical topology,
not a claim
of a new fundamental-group computation.

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
