# Topological Computational Paths

This repository is the focused development home for the topological-semantics
part of the Calculus of Computational Paths.  It is being extracted from the
broader [ComputationalPathsLean](https://github.com/Arthur742Ramos/ComputationalPathsLean)
development so that the mathematical claim, dependencies, and publication
artifact have a small and auditable boundary.

## Intended result

The first result package concerns a scoped geometric rewrite presentation:

1. rewrite traces have a sound quotient relation;
2. the quotient carries a canonical final composable-domain topology on which
   composition is continuous and the groupoid laws hold; and
3. the ordinary pullback topology agrees with that final topology exactly when
   the relevant pair map is a quotient map, with compact-Hausdorff and discrete
   sufficient conditions.
4. the selected certificate classifies based continuous loops in the genuine
   additive circle `AddCircle (1 : ℝ)` by their integer winding number.  The
   proof constructs the covering charts, lifts loops to `ℝ`, proves winding
   invariance and additivity, and straightens every loop to an explicit
   standard representative.
5. the same genuine topological argument, coordinatewise on the product
   torus, classifies based torus loops by `ℤ × ℤ` and proves the corresponding
   standard representatives are complete.
6. the Hawaiian-earring application uses an explicit based fiber of the
   universal continuous-path presentation: its observable geometric fiber,
   endpoint-fixed homotopy quotient, quotient square, and final/ordinary pair
   comparison are all named in the formalization.
7. the selected certificate transfers the source-backed obstruction: if the
   standard based loop quotient has a non-quotient square and discontinuous
   multiplication, then the corresponding based-fiber and scoped ordinary
   failures follow under the stated comparison maps.

At the statement boundary, items 4--5 are full additive-classification
certificates rather than bare equivalence witnesses: each exposes the
invariant, its value on the identity, additivity under quotient composition,
an explicit standard-representative map, and both inverse/completeness laws.

The mathematical point is the exact separation between the canonical topology
forced by explicitly composable representatives and the ordinary pullback
topology on quotient arrows.  This is relevant to work on quotient
fundamental groupoids, topological groupoids, and formalized rewriting: it
isolates the product-quotient condition needed to transport composition and
locates the strict Hawaiian-earring failure at that comparison map.  The
observable based fiber deliberately retains the universal computational-path
trace and coherence witness while using the induced topology of its geometric
loop observation; this makes the comparison with the standard based loop
quotient explicit without conflating trace-sensitive and observable topologies.
The selected result's substantive non-transport core is the universal-cover
classification of actual topological loop spaces: the lift endpoint is a
well-defined complete invariant, and the torus result is obtained from genuine
coordinate paths.  These are classical winding theorems, so this repository
does not claim a new fundamental-group calculation; the plausible specialist
note contribution is the kernel-checked realization of those theorems inside
the computational-path quotient/final-topology semantics.  Synthetic integer
and finite-trace examples are not used as the relevance evidence.

The Palomar-selected declaration is the comparison in item 3, the genuine
circle and torus classifications in items 4--5, and the concrete based-fiber
construction in items 6--7.  Items 1 and 2 supply the spaces and continuous
final-domain operation needed to formulate and prove that comparison; their
largely structural laws are not presented as the research contribution.  The
external Hawaiian-earring non-quotient and discontinuity theorems are explicit
inputs, not claims reproved by this repository.

The package will keep the final-domain statement distinct from the stronger
ordinary-topological-groupoid statement.  That distinction is part of the
mathematical result, not merely an implementation detail.

The concrete circle and torus winding modules are included in this focused
boundary as the unconditional mathematical validation cases.  Geometric
comparison and functoriality remain supporting modules.  The Hawaiian-earring
based fiber and its transfer are a conditional, independently checked
application of the comparison theorem.

## Follow-up theorem package

The repository now also contains a separate, non-destructive follow-up
surface.  Its central theorem applies to the compact-open based-loop quotient
of every pointed topological space.  It first proves continuous functoriality
under continuous maps, the identity and composition laws, invariance under
homotopy equivalences, and basepoint-change equivalences along arbitrary
paths.  It also proves that quotient fundamental groups preserve arbitrary
indexed products under the exact hypothesis that the indexed product of the
loop-quotient projections is a quotient map.

The same theorem proves continuous reversal, separate continuity of
concatenation, explicit translation homeomorphisms and homogeneity, and the
exact equivalence

```text
quotient fundamental group discrete ↔ null-homotopy class open.
```

Under that criterion the loop projection is open, its square is a quotient
map, every homotopy class is open, and concatenation is jointly continuous.
This separates the always-valid quasitopological-group laws from the stronger
joint continuity that fails in the accepted Hawaiian-earring application.
The follow-up also proves that quotient discreteness is invariant under
homotopy equivalence and path-based basepoint change.  The basepoint-change map
depends only on the path's endpoint-fixed homotopy class.  It also proves that
semilocal simple connectivity is homotopy invariant for locally
path-connected spaces, and that basepoint transport composes along
concatenated paths, with transport along a constant path identified with the
identity equivalence.  Reversing a path is proved to give the inverse
continuous multiplicative transport, completing the groupoid-action coherence.
It also shows that joint continuity of quotient
concatenation—and hence the genuine
topological-group boundary—is invariant under homotopy equivalence.
If the target quotient group is abelian, the transport equivalence is in fact
independent of the chosen path even without an endpoint-fixed homotopy between
the paths.  In fact, centrality of the relative loop between two paths exactly
characterizes equality of their transport equivalences.
Continuous maps preserve quotient path concatenation, and the basepoint-change
maps form a natural square with those induced quotient maps.
For homotopic continuous maps, the induced quotient maps are related by the
corresponding basepoint-path conjugacy.
Joint continuity of quotient concatenation—and therefore the topological-group
boundary—is invariant under changing the basepoint along a path as well.
Moreover, a homotopy fixed at the chosen basepoint induces equal based
homomorphisms, expressed with the canonical endpoint cast.
On path-connected spaces, joint continuity at one basepoint is equivalent to
joint continuity at every basepoint.  Discreteness and the genuine
topological-group boundary have the same one-basepoint criterion.  The global
joint-continuity property is invariant under homotopy equivalence between
path-connected spaces.  In the locally path-connected, path-connected
setting, semilocal simple connectivity is likewise equivalent to discreteness
at one chosen basepoint.  The path-connected basepoint transport is exposed
as a continuous multiplicative equivalence, not only as a homeomorphism.
The T1 separation boundary is also invariant under homotopy equivalence and
path transport; on path-connected spaces it can be checked at one basepoint,
and the global T1 property is homotopy-invariant.

The strengthened package also proves the exact T1 criterion by closedness of
the null class (equivalently, of every based-loop homotopy class), both
directions of the discreteness/semilocal-simple-connectivity relationship in
locally path-connected spaces, and the exact agreement boundary with a
genuine topological-group structure.  The forward direction is witnessed by
a finite compact-open subdivision and an explicit homotopy ladder, not merely
by a transported abstract equivalence.
Covering maps induce injective continuous homomorphisms whose images are the
monodromy stabilizers of the chosen lifts.  Discontinuous multiplication is
proved to force failure of the product-quotient hypothesis, and the accepted
Hawaiian-earring facts instantiate this sharp boundary.

The concrete application proves the full certificate uniformly for every
finite-dimensional torus:

```text
π₁((AddCircle 1)^n, 0) ≃ₜ (Fin n → ℤ).
```

The proof is constructive at the representative level: coordinate winding,
explicit standard loops, additivity, endpoint-fixed homotopy completeness,
and openness of the null class are all checked.  Basepoint transport then
proves discreteness of every based quotient and semilocal simple connectivity
at every torus point, not only at the all-zero basepoint.  It also transports
the integer-lattice homeomorphism to every chosen basepoint.  The additive
classifier is further packaged as a continuous multiplicative equivalence to
`Multiplicative (Fin n → ℤ)`, identifying the actual quotient multiplication
with lattice addition and proving commutativity at every basepoint.
The classifier can also be constructed along any explicit path from the
canonical basepoint, and the abelian target theorem proves that all such
path-based classifiers are equal as continuous multiplicative equivalences.
The core winding theorem is natural under every coordinate-selection map
`Fin m → Fin n`: mapping a loop and then taking winding reindexes its lattice
vector, and the corresponding quotient classifier commutes with that map.
The explicit standard-loop representatives and quotient decoder satisfy the
same reindexing equation.
These coordinate maps satisfy explicit identity and composition laws, making
the reindexing statement functorial rather than a collection of unrelated
equalities.  The continuous multiplicative lattice classifier satisfies the
same equation, including coordinate selections between different dimensions.
The path-based classifier satisfies the corresponding naturality square at
arbitrary torus basepoints: transporting along a chosen path and then
selecting coordinates agrees with reindexing the transported lattice vector,
using the mapped path at the target.
Since the target quotient is abelian, the path choice can be eliminated: the
canonical arbitrary-basepoint classifier satisfies this naturality square
without exposing any auxiliary path.
The lattice reindexing maps are also continuous additive morphisms, with
identity and composition coherence; the classifier equation is restated
through that continuous morphism.
For a finite index equivalence, the coordinate map is a torus homeomorphism
and the lattice map is a continuous additive equivalence, with matching
identity and composition laws.
The arbitrary-basepoint classifier naturality squares are likewise restated
directly through the continuous additive reindexing morphism.
The exact image behavior is also formalized: surjective index maps induce
injective torus, lattice, and quotient maps, while injective index maps induce
surjective maps by zero extension.
For an arbitrary index map, the image is characterized exactly as the
fiber-constant part of the target winding lattice, equivalently at the typed
quotient level.
The converse criteria are exact: these reindexing maps are injective exactly
for surjective index maps and surjective exactly for injective index maps.
This holds simultaneously for the raw finite-torus maps, their integer
lattice classifiers, and the typed quotient loop maps.
Typed quotient coordinate selection is also exposed as a contravariant
additive functor, continuous for the discrete quotient topologies, with
explicit identity/composition laws and a kernel description by vanishing on
the coordinates hit by the index map.  At arbitrary torus basepoints, the
same operation is additionally packaged as a continuous multiplicative
homomorphism between the corresponding quotient fundamental groups, with its
own identity/composition coherence and a classifier-naturality corollary.  The
same classifier transports the exact fiber-constant image criterion,
injectivity/surjectivity converses, and vanishing-on-the-image kernel result
to every torus basepoint.  It also commutes with explicit basepoint transport,
giving a naturality square before any classifier is chosen.
The finite-torus API is now extended from coordinate selections to arbitrary
integer matrices: matrix maps are continuous, their winding actions and
standard representatives are natural, and the typed quotient maps satisfy
matrix identity/composition coherence.  Exact image, kernel, injectivity, and
surjectivity criteria transfer through the winding equivalence, and the
resulting lattice and quotient additive maps are continuous for the discrete
topologies.  At arbitrary basepoints, each matrix map is also exposed as a
continuous multiplicative quotient homomorphism commuting with explicit
basepoint transport; the path-based winding classifier satisfies the matching
matrix naturality square with its endpoint cast made explicit.  Abelian-target
path independence then gives the same square for the canonical classifier,
without exposing a path choice.  The canonical classifier also transfers the
matrix image, kernel, injectivity, and surjectivity iff criteria to every
chosen basepoint, with explicit iff statements for image membership, the
identity fiber, injectivity, and surjectivity.  The arbitrary-basepoint
homomorphisms also satisfy typed contravariant composition and identity laws,
with their endpoint casts induced explicitly by matrix-map coherence.
With an explicit two-sided integer-matrix inverse, these maps upgrade to a
continuous additive lattice equivalence, a torus homeomorphism, and a quotient
homeomorphism and continuous additive equivalence for the transported loop
groups.  At every arbitrary torus basepoint, the same inverse gives a
continuous multiplicative equivalence of quotient fundamental groups, with
explicit injectivity and surjectivity corollaries for the induced homomorphism.
For square matrices, the lattice and canonical quotient actions satisfy sharp
determinant criteria: injectivity is equivalent to a nonzero determinant,
surjectivity to a unit determinant, and the canonical nonsingular inverse of a
unimodular matrix instantiates every equivalence layer without an extra inverse
witness, including at arbitrary basepoints.
For every nonzero determinant, the lattice cokernel is also proved finite with
cardinality exactly `Int.natAbs (Matrix.det A)`, so the determinant controls the
quantitative finite index as well as the injectivity and surjectivity boundary.
At the canonical finite-torus basepoint, the induced quotient image has the
same exact index and cokernel cardinality, with finiteness exposed directly.
For composable non-singular square matrices, the determinant index is proved
multiplicative under matrix composition both on the winding lattice and on the
canonical topological quotient obstruction.
This multiplicativity is witnessed structurally: composition by `B` induces a
canonical additive map from the cokernel of `A` into the cokernel of `B ∘ A`,
and that map is proved injective whenever `det B ≠ 0`, on both the winding
lattice and the actual topological loop-class quotient.
The complementary projection from the cokernel of `B ∘ A` onto the cokernel
of `B` is surjective with exactly that image as its kernel, so the result is an
explicit short exact sequence of finite abelian groups rather than only a
numerical identity.
The associated first-isomorphism quotient is also made explicit: quotienting
the composition cokernel by the projection kernel yields an additive
equivalence with the cokernel of `B`, and a proved representative formula
identifies this equivalence with the canonical projection.
The construction is factored through a reusable first-isomorphism theorem for
arbitrary composable additive homomorphisms.  Therefore rectangular integer
matrices in any composable dimensions inherit the same short-exact sequence
under the exact hypothesis that the second matrix action is injective; the
finite-torus quotient maps satisfy the corresponding transported theorem.
At the abstract level, injectivity is characterized exactly by the equality
between the preimage of the composite image and the first map's image, so the
matrix-action hypothesis is a transparent sufficient specialization rather
than a hidden strengthening.
The composite-image subgroups are also identified explicitly with the ranges
of the canonical row-by-column `matrixCompose` maps, and both the lattice and
finite-torus exact-sequence APIs expose this notation directly.
For every rectangular matrix, the winding equivalence is lifted to an explicit
additive equivalence between the finite-torus cokernel and the lattice
cokernel, with a representative formula.  The composite cokernel embedding is
proved natural under these equivalences, and the complementary projection
commutes as well, giving a checked commutative diagram between the topological
and lattice exact sequences.  The named square-matrix `matrixCompose` maps
reuse that result directly, with canonical embedding and projection naturality
theorems so the diagram can be consumed without range-rewrite boilerplate.  A
single rectangular short-exactness certificate packages both sequences and
both commuting squares under the same injectivity hypothesis.
The abstract induced map and projection also expose simp-normalized formulas
on quotient representatives, making the certificate directly usable in
downstream calculations.
The rectangular winding equivalence additionally transports `Nat.card` and
`Finite` exactly, for individual matrices and explicit composites, without
assuming square dimensions or finiteness in advance.
The lattice cokernel is also exposed through its Smith-normal-form
decomposition into finite cyclic `ZMod` factors.  The canonical quotient
cokernel of the induced torus homomorphism is transported through the winding
equivalence to that same explicit product as an additive equivalence of finite
abelian groups, identifying the obstruction structurally at the topological
level rather than only by cardinality.  The Smith-normal-form construction is
now generalized to arbitrary-rank rectangular maps: zero `ZMod 0` factors
record the free part while nonzero factors record torsion.  Under full target
rank, the same cyclic product is finite and its exact cardinality is the
product of the Smith moduli; both the lattice and finite-torus cokernels carry
this decomposition, and lattice finiteness is exactly the full-rank condition.
See the detailed certificate and source lineage in
[`FOLLOWUP.md`](FOLLOWUP.md), `FollowupChallenge.lean`,
`FollowupSolution.lean`, `formalization-followup.yaml`, and
`comparator-followup.json`.  This follow-up does not alter the already
accepted `Challenge.lean` / `Solution.lean` comparison surface.

## Source lineage

The starting implementation is the topological layer at the immutable source
snapshot `topological-paper-v12` of the parent repository, commit
`2a2baa1f31c68f0e696021db91f8381dd2854652`.  The direct source manuscript is
[`paper/topological/main.tex`](https://github.com/Arthur742Ramos/ComputationalPathsLean/blob/2a2baa1f31c68f0e696021db91f8381dd2854652/paper/topological/main.tex).
This focused repo is the publication-oriented extraction of that layer.  The
parent repository remains the canonical broad development tree for the other
topological and geometric constructions.

## Publication boundary

This repository now contains one pinned Lean project with a focused
`Challenge.lean`, a matching `Solution.lean`, and an explicit `comparator.json`.
The compared `main_result` states the exact final-versus-ordinary topology
comparison.  The canonical map from the final composable quotient to the
ordinary pullback is always a continuous bijection.  The theorem identifies
when it is quotient, when it upgrades to a homeomorphism, when the final
topology is induced from the ordinary domain, and when multiplication is
continuous on the ordinary pullback.  It also formalizes discontinuity of
ordinary multiplication as an obstruction and proves compact--Hausdorff and
discrete sufficient cases.  Its Hawaiian-earring portion now includes the
observable based universal fiber, its homeomorphism to the standard
endpoint-fixed loop quotient, the final-versus-ordinary pair comparison, and
the source-backed obstruction transfer.  The concrete circle and torus modules
additionally prove the actual loop-quotient classifications described above by
an explicit covering/lifting argument.  These are the publication-facing
claims; the automatic final-domain groupoid laws remain supporting
infrastructure.
The selected circle and torus fields are full additive-classification
certificates, instantiated by
`ConcreteCircleWinding.topologicalWinding`/`decodeTopologicalWinding` and
`TopologicalTorus.encode`/`decode`.  Their checked laws include identity,
composition additivity, standard-representative completeness, and both
directions of the classification, so the result names actual quotient loop
spaces rather than an abstract placeholder for a classification.

`Challenge.lean` duplicates the statement-facing definitions needed for that
theorem using Lean core and Mathlib; it does not import the extracted project
implementation.  `Solution.lean` imports the extracted, checked comparison
theory and supplies the complete certificate, including the additive
classification and based-fiber proofs.

Before submission, the solution and substantive development must pass the
current Palomar toolchain and dependency checks, contain no `sorry`, `admit`,
custom axioms, or `native_decide`, and have a research-interest statement that
accurately separates the formalized theorem from the surrounding mathematical
program.  Palomar permits the single deliberate statement-side `sorry` in the
Challenge file.

## Status

The focused core, the accepted Palomar statement boundary, and the Lean 4.32.0
port are complete.  `lake build` succeeds for the core, Challenge, and
Solution targets.  Within that accepted package, the only `sorry` is the
deliberate statement-side hole in `Challenge.lean`; `Solution.lean` and the
extracted development contain no
`sorry`, `admit`, custom axioms, or `native_decide`.  The selected solution
packages the exact quotient-map/homeomorphism/topology-agreement comparison,
its ordinary-composition consequence and obstruction, both positive
sufficient-condition theorems, and the concrete observable based-fiber
formalization with its transferred Hawaiian-earring obstruction, including
transferred discontinuity of ordinary multiplication.  It does not claim to
reprove the external Hawaiian-earring theorems.  The circle and torus portions
are selected through full additive-classification certificates: identity,
composition additivity, explicit standard representatives, and inverse laws.

The repository has been checked against Palomar's current metadata, layout,
toolchain, and pinned-manifest rules.  Registration still requires a hosted
Comparator/NanoDa run and an automated editorial review identifying no blocking
problem.  That review is a gate, not approval or endorsement of the
mathematics; registration remains a separate request.

## Reproduce the baseline

From the repository root:

```text
lake build
./scripts/check-palomar.sh
./scripts/check-followup.sh
```

For the independent proof replay, run `./scripts/verify-comparator.sh`.  Use
`./scripts/verify-comparator.sh comparator-followup.json` for the follow-up. It
fetches the exact pinned Comparator, Lean exporter, Landrun, and NanoDa
revisions into the ignored `.cache/` directory, checks the toolchain match, and
replays the selected theorem.  This local replay and CI do not replace
Palomar's hosted verification or automated editorial review; neither is
mathematical approval or endorsement.

Useful local contract checks are:

```text
test "$(wc -l < Challenge.lean)" -le 1000
test "$(wc -c < Challenge.lean)" -le 102400
rg "\\bsorry\\b|\\badmit\\b|^axiom |native_decide" \
  Solution.lean FollowupSolution.lean ComputationalPaths -g "*.lean"
git diff --check
```

The checked-in `lake-manifest.json` records the complete dependency closure;
the `lakefile.toml` and `lean-toolchain` are the only project controls needed
to reproduce the build.  The proved `Solution.lean` declaration uses only
`propext`, `Classical.choice`, and `Quot.sound`; the accepted statement-side
`sorry` appears in `Challenge.lean`, while the separate follow-up statement
hole appears in `FollowupChallenge.lean`.  Neither solution nor the substantive
development contains a proof hole.  The same contract gate runs in
GitHub Actions with the Lean toolchain pinned to an immutable action revision.
