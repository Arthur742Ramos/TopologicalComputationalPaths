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
