# Topological Computational Paths

This repository is the focused development home for the topological-semantics
part of the Calculus of Computational Paths.  It is being extracted from the
broader [ComputationalPathsLean](https://github.com/Arthur742Ramos/ComputationalPathsLean)
development so that the mathematical claim, dependencies, and publication
artifact have a small and auditable boundary.

## Current follow-up submission scope

The current Comparator artifact is `comparator-followup.json`, selecting
`TopologicalComputationalPathsFollowup.topological_smith_exactness` in
`FollowupSolution.lean`.  The selected declaration is a nonempty
`TopologicalSmithExactnessCertificate` whose core is a compatibility
theorem, not an unstructured existence witness.

Its topology-to-arithmetic part identifies covering-map images with
monodromy stabilizers, records the sharp product-quotient boundary, and
classifies the quotient fundamental group of every finite torus by its
integer winding lattice.  For every rectangular integer matrix, the actual
continuous torus map and its induced quotient map are natural for that
classifier.  The certificate gives the exact image criterion, injectivity and
surjectivity transfer, quotient-level composition, rectangular cokernel
short exactness, arbitrary-rank Smith factors (including free `ZMod 0`
directions), finite-cokernel cardinality/support laws, determinant index, and
the full-rank prime-power refinement.  Infinite/free cases are not silently
called finite: the cardinality and prime-support conclusions carry explicit
finite-cokernel hypotheses.

The trace component is now concrete.  `WindingWord n` is definitionally
`List (Fin n -> Int)`; `traceLength` is definitionally `List.length`,
`trans` is list append, and `standard` is the empty word for zero and a
one-letter word otherwise.  `realize` recursively concatenates the actual
standard torus loops.  The selected bridge proves the representation theorem,
homotopy iff winding equality, exact zero/one minimality, matrix naturality,
normal-form composition/unit laws, and the Smith realizability iff for the
actual induced quotient map.  Thus the shortest-trace statement is derived
from an independent syntax and its topological realization; no certificate
field supplies an arbitrary raw carrier or cost observable.  The repository's
endpoint-varying `ComputationalPaths.Path` APIs remain supporting material and
are not attributed to this selected declaration.

The selected bundle is documented as an `original-proof` provenance record
for this exact synthesis, with novelty and priority explicitly unknown.
Hatcher, Norman, Brazas--Fabel, Calcut--McCarthy, and the parent manuscript
supply literature context and classical ingredients only.  The accepted
baseline and the repository-wide extensions below remain context, not
additional Comparator claims.

## Baseline package (repository context)

The following section describes the accepted first-submission package:

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

The baseline mathematical point is the exact separation between the canonical
topology forced by explicitly composable representatives and the ordinary
pullback topology on quotient arrows.  The follow-up instead selects the
topological Smith certificate described below: it identifies the quotient loop
group with the winding lattice and records the lattice-cokernel composition,
Smith, determinant-index, and prime-power profiles.  The centrality and
product results, the observable based fiber, and the strict Hawaiian-earring
comparison remain useful repository context but are not selected by the
follow-up Comparator.  Winding and Smith calculations are classical
ingredients; the follow-up account distinguishes that mathematics from its
formal packaging and makes no priority claim for the individual results.

The baseline Palomar declaration (the accepted first submission) is the
comparison in item 3, the genuine
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

The follow-up has its own non-destructive Comparator and metadata surface.
`comparator-followup.json` selects
`TopologicalComputationalPathsFollowup.topological_smith_exactness` in
`FollowupSolution.lean`; it does not select the baseline `main_result`.
The declaration is a kernel-checked, all-dimensional compatibility
certificate with three connected layers:

1. quotient-topological facts: covering images are exactly monodromy
   stabilizers, and failure of joint quotient multiplication rules out the
   product quotient map;
2. lattice exactness: composable rectangular integer actions yield an exact
   cokernel sequence, with finite/free Smith semantics and the determinant
   specialization stated under their proper hypotheses; and
3. a concrete finite-torus bridge: actual loop quotient classes, winding
   vectors, the induced continuous matrix maps, and `WindingWord` syntax
   commute in one diagram.

For the third layer, a word is a finite list of winding generators.  Its
length, concatenation, reversal, winding sum, standard form, and matrix action
are definitions or recursive list operations.  Its realization is an actual
concatenation of the standard loops in the finite torus.  The proof then
derives representation by the winding standard loop, homotopy completeness,
the exact zero/one shortest normal form, matrix naturality and composition,
and a Smith-coordinate iff for realizability by an induced quotient map.
The same classifier proves that target classes of the actual topological map
are exactly the integer-lattice image, so the Smith equations are not
detached arithmetic.

The nonroutine selected contribution is the reusable compatibility diagram
from quotient topology through concrete winding-word normalization to
rectangular Smith image decision.  It is an all-dimensional, rank-aware
certificate for induced maps, with explicit free directions and finite
invariant gates.  It is presented as a formalization/methods contribution,
not as a discovery claim for winding or Smith normal form; the bounded
provenance audit records priority as unknown.  Supporting centrality,
indexed-product, endpoint-varying path, CRT, and broader matrix results are
outside this Comparator selection unless a field is named in the declaration.

### Repository-wide finite-torus extensions (not selected by Comparator)

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
`Finite` exactly, for individual matrices and explicit composites.  The
selected cardinality conclusions use the finite-cokernel hypotheses below;
outside that regime `Nat.card` is the totalized value zero rather than an
ordinary finite cardinality.
The lattice cokernel is also exposed through its Smith-normal-form
decomposition into cyclic `ZMod` factors: nonzero moduli are finite cyclic
factors and a zero modulus is the free `ZMod 0` factor.  The canonical quotient
cokernel of the induced torus homomorphism is transported through the winding
equivalence to that same explicit product as an additive equivalence of finite
abelian groups, identifying the obstruction structurally at the topological
level rather than only by cardinality.  The Smith-normal-form construction is
now generalized to arbitrary-rank rectangular maps: zero `ZMod 0` factors
record the free part while nonzero factors record torsion.  Under full target
rank, the same cyclic product is finite and its ordinary cardinality is the
product of the Smith moduli; both the lattice and finite-torus cokernels carry
this decomposition, and lattice finiteness is exactly the full-rank condition.
More precisely, finiteness on either side is equivalent to every Smith modulus
being nonzero, so the criterion detects exactly when no `ZMod 0` free factor
survives (and is equivalent to full target rank).
For square nonsingular matrices, a checked arithmetic bridge identifies the
Smith-modulus product on both sides with `Int.natAbs (Matrix.det A)`.
The supporting arbitrary-rank `Nat.card` formula is a totalized identity: an
infinite cokernel with a surviving `ZMod 0` factor contributes `Nat.card = 0`.
The selected statement does not call that zero an ordinary cardinality.
The same arbitrary-rank presentation identifies the additive exponent with the
lcm of the Smith-factor moduli, so a zero factor forces exponent zero and
records the free summand both elementwise and globally.
Equivalently, exponent zero is characterized by a zero Smith factor; for both
rectangular lattice and finite-torus cokernels this is exactly failure of full
target rank.
More generally, a proposed global annihilator `k` is divisible by the Smith
exponent exactly when every Smith-factor modulus divides `k`; a zero factor
forces `k = 0`.
The sharp trivial-cokernel boundary is the exponent-one case: the exponent is
one exactly when every Smith factor has unit absolute value.
Consequently, a rectangular lattice or finite-torus matrix action is
surjective exactly when all of its Smith factors have unit absolute value.
For square matrices, the adjugate annihilator also gives the global bound
`AddMonoid.exponent (cokernel) ∣ Int.natAbs (Matrix.det A)`, including the
singular case.
The finite/infinite dichotomy is equivalently global: each Smith cokernel is
finite exactly when its exponent is nonzero, so the zero-exponent criterion is
also a complete finiteness test.
For any composable additive cokernel sequence, the composite cokernel
exponent divides the product of the exponents of the two successive
cokernels, without an injectivity hypothesis.  Rectangular lattice and
finite-torus matrix sequences inherit this bound, both for explicit homomorphism
composition and for canonical `matrixCompose` ranges.
Under the injectivity hypothesis needed for exactness, the selected `Nat.card`
identity is asserted after both successive cokernels are known to be finite:
the ordinary composite cardinality is the product of the two successive
cardinalities, on both rectangular interfaces.  The supporting development
also proves the totalized equation outside that regime; there it is only zero
arithmetic.  On the finite-torus side the finite identity is exposed from
injectivity of the underlying lattice action, via the proved quotient-
injectivity transport.
Under the same hypothesis, finiteness is equivalent across the exact
sequence: the composite cokernel is finite exactly when both successive
cokernels are finite, including the canonical `matrixCompose` forms.
Under injectivity of the second map, the least common multiple of the two
successive cokernel exponents divides the composite exponent.  Combined with
the product upper bound, this gives a sharp lcm-to-product interval for every
such exact sequence.
If the two successive cokernel exponents are coprime, injectivity of the
second map sharpens the exponent divisibility bound to an exact product
identity.  The theorem is proved abstractly and transported to rectangular
lattice and finite-torus matrix cokernels, with explicit and canonical
`matrixCompose` forms; finite-torus clients can also use lattice-action
injectivity via the quotient-injectivity equivalence.
For square matrices, the adjugate exponent bounds let coprime determinant
absolute values certify coprime successive exponents.  Thus, when the second
determinant is nonzero, the exact product theorem applies directly to both
lattice and finite-torus cokernels, including canonical `matrixCompose` forms.
For every prime `p`, the selected exact-sequence prime-support law is stated
when both successive cokernels are finite: `p` divides the composite exponent
iff it divides one of the two successive exponents.  Rectangular lattice and
finite-torus wrappers expose this finite torsion-support law in explicit and
canonical `matrixCompose` forms, connecting the sequence bounds to the
prime-power Smith decomposition.  In a free `ZMod 0` case the totalized
exponent is zero, so divisibility by every prime is not interpreted as
torsion-prime support.
For square matrices, a nonzero determinant of the second factor discharges
injectivity automatically, so the same law is directly available from
determinant hypotheses on both lattice and finite-torus cokernels.
The Smith presentation gives the corresponding factor-level finite test: after
the cokernel is finite, a prime divides its exponent exactly when it divides
at least one Smith modulus, on both lattice and finite-torus sides.  A zero
modulus is instead the explicitly recorded free case.
The Smith coordinates also expose exact coordinatewise divisibility tests for
membership in the lattice and finite-torus matrix images.
The topological Smith equivalence includes a quotient-representative formula,
so the decoded coordinates can be evaluated directly on loop classes.
Whenever the Smith factors are nonzero, the cyclic factors are further
decomposed by the Chinese remainder theorem into an explicit product of
prime-power cyclic groups, on both lattice and finite-torus cokernels, with
a representative formula for the refined decoder.
The refined finite product also carries an exact ordinary-cardinality
 certificate: the prime-power orders multiply back to each Smith modulus, so
 both finite cokernel cardinalities are identified with the resulting full
 double product.
The additive exponent of the finite cokernel is likewise proved to be the
least common multiple of the Smith moduli, giving its precise annihilator.
Under the explicit all-factors-nonzero hypothesis, the full `Nat.factorization`
valuation of the exponent at each prime is the `Finset.sup` of the valuations
of the Smith moduli; the same p-adic profile is transported to rectangular
lattice and finite-torus matrix cokernels.  The hypothesis is deliberate:
zero factors represent `ZMod 0` free components.
The same supremum law is now available elementwise for every finite-order
cokernel class: the factorization of its additive order is the supremum of the
factorizations of its decoded Smith-coordinate orders, on both presentations.
The same Smith coordinates give an elementwise annihilation criterion: a
multiple of a lattice or finite-torus cokernel class vanishes exactly when
each transformed coordinate is divisible by the corresponding multiple of
its Smith factor, including the zero-factor equations.
More precisely, the additive order of each class is the lcm of the additive
orders of its decoded Smith coordinates; a nonzero free `ZMod 0` coordinate
therefore records infinite class order.
When all factors are nonzero, each coordinate order is computed explicitly as
its Smith modulus divided by the gcd with the transformed integer coordinate.
For arbitrary rank, infinite order is characterized elementwise: it occurs
exactly when a zero Smith factor carries a nonzero transformed coordinate, and
the same free-coordinate criterion is exposed on lattice and finite-torus
matrix representatives.
Equivalently, a natural number is a multiple of a class's additive order
exactly when it satisfies the corresponding coordinatewise Smith divisibility
equations, including the free-coordinate vanishing constraints.
Conversely, a class has finite additive order exactly when every zero Smith
factor carries a zero transformed coordinate; this torsion test is exposed on
the lattice and finite-torus matrix representatives as well.
For every square matrix, the adjugate gives an explicit preimage of a
determinant multiple.  Hence the determinant annihilates every class in both
the winding-lattice and finite-torus cokernels, including singular matrices;
the theorem is independent of the nonzero-determinant cardinality result.
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

For the follow-up, the parent setting is recorded as a `background` source and
as an `adapts` related formalization.  The selected three-layer theorem (two
general quotient-topology criteria plus the nine-field Topological Smith
synthesis, including the quotient-map Smith-coordinate image obstruction) is
recorded as an `original-proof` source with relationship `other`; the bounded
provenance record for this exact certificate is documented in
[`FIRST-PRESENTATION-AUDIT.md`](FIRST-PRESENTATION-AUDIT.md).
Hatcher and Norman are ingredient-only background, while Brazas--Fabel and
Calcut--McCarthy provide quotient-topological context.  The claim does not
extend to the classical ingredients or to the repository's separate concrete
endpoint-varying path APIs.  The local Lean files implement this checked
certificate and are not cited as an external mathematical source.

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

## Reproduce the checked artifacts

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
