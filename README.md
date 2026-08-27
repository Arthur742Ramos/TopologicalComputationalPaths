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
4. the Hawaiian-earring application uses an explicit based fiber of the
   universal continuous-path presentation: its observable geometric fiber,
   endpoint-fixed homotopy quotient, quotient square, and final/ordinary pair
   comparison are all named in the formalization.
5. the selected certificate transfers the source-backed obstruction: if the
   standard based loop quotient has a non-quotient square and discontinuous
   multiplication, then the corresponding based-fiber and scoped ordinary
   failures follow under the stated comparison maps.

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
Synthetic integer and finite-trace examples are deliberately not used as the
relevance evidence for the selected result.

The Palomar-selected declaration is the comparison in item 3, the concrete
based-fiber construction in item 4, and the source-backed transfer in item 5.
Items 1 and 2 supply the spaces and continuous final-domain operation needed
to formulate and prove that comparison; their largely structural laws are not
presented as the research contribution.  The external Hawaiian-earring
non-quotient and discontinuity theorems are explicit inputs, not claims
reproved by this repository.

The package will keep the final-domain statement distinct from the stronger
ordinary-topological-groupoid statement.  That distinction is part of the
mathematical result, not merely an implementation detail.

The circle and torus constructions, geometric comparison, and functoriality
remain planned supporting modules in this focused boundary.  The
Hawaiian-earring based fiber and its transfer are included as a conditional,
independently checked application of the comparison theorem.

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
the source-backed obstruction transfer.  These are the publication-facing
claims; the automatic final-domain groupoid laws remain supporting
infrastructure.

`Challenge.lean` duplicates the statement-facing definitions needed for that
theorem using Lean core and Mathlib; it does not import the extracted project
implementation.  `Solution.lean` imports the extracted, checked comparison
implementation.  `Solution.lean` imports the extracted, checked comparison
theory and supplies the certificate, including the based-fiber proofs.

Before submission, the solution and substantive development must pass the
current Palomar toolchain and dependency checks, contain no `sorry`, `admit`,
custom axioms, or `native_decide`, and have a research-interest statement that
accurately separates the formalized theorem from the surrounding mathematical
program.  Palomar permits the single deliberate statement-side `sorry` in the
Challenge file.

## Status

The focused 30-file core, the Palomar statement boundary, and the Lean 4.32.0
port are complete.  `lake build` succeeds for the core, Challenge, and
Solution targets.  The only `sorry` is the deliberate statement-side hole in
`Challenge.lean`; `Solution.lean` and the extracted development contain no
`sorry`, `admit`, custom axioms, or `native_decide`.  The selected solution
packages the exact quotient-map/homeomorphism/topology-agreement comparison,
its ordinary-composition consequence and obstruction, both positive
sufficient-condition theorems, and the concrete observable based-fiber
formalization with its transferred Hawaiian-earring obstruction, including
transferred discontinuity of ordinary multiplication.  It does not claim to
reprove the external Hawaiian-earring theorems.

The repository has been checked against Palomar's current metadata, layout,
toolchain, and pinned-manifest rules.  Registration still requires a hosted
Comparator/NanoDa run and editorial approval of this revised, concrete
comparison result.

## Reproduce the baseline

From the repository root:

```text
lake build
./scripts/check-palomar.sh
```

For the independent proof replay, run `./scripts/verify-comparator.sh`.  It
fetches the exact pinned Comparator, Lean exporter, Landrun, and NanoDa
revisions into the ignored `.cache/` directory, checks the toolchain match, and
replays the selected theorem.  This local replay and CI do not replace
Palomar's hosted verification or editorial review.

Useful local contract checks are:

```text
test "$(wc -l < Challenge.lean)" -le 1000
test "$(wc -c < Challenge.lean)" -le 102400
rg "\\bsorry\\b|\\badmit\\b|^axiom |native_decide" -g "*.lean" -g "!.lake/**"
git diff --check
```

The checked-in `lake-manifest.json` records the complete dependency closure;
the `lakefile.toml` and `lean-toolchain` are the only project controls needed
to reproduce the build.  The proved `Solution.lean` declaration uses only
`propext`, `Classical.choice`, and `Quot.sound`; the deliberate statement-side
`sorry` appears only in `Challenge.lean`.  The same contract gate runs in
GitHub Actions with the Lean toolchain pinned to an immutable action revision.
