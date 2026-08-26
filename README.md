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
4. the selected certificate includes a concrete one-object trace presentation:
   integer-labelled primitive loops normalize inductively to singleton traces,
   the quotient is bijectively coded by `Int`, and composition adds codes; and
5. it includes a finite trace-sensitive obstruction in which two labels remain
   distinct in the trace carrier but are identified by an observable code, so
   the forward identity is continuous while the reverse identity is not.

The Palomar-selected declaration is the comparison in item 3 together with
the concrete formalized instances in items 4 and 5.  Items 1 and 2 supply the
spaces and continuous final-domain operation needed to formulate and prove
that comparison; their largely structural laws are not presented as the
research contribution.

The package will keep the final-domain statement distinct from the stronger
ordinary-topological-groupoid statement.  That distinction is part of the
mathematical result, not merely an implementation detail.

The circle and torus constructions, geometric comparison, and functoriality
remain planned supporting modules.  The finite obstruction selected above is
already included and independently checked in this focused boundary.

## Source lineage

The starting implementation is the topological layer at the immutable source
snapshot `topological-paper-v12` of the parent repository.  This focused repo
is the publication-oriented extraction of that layer.  The parent repository
remains the canonical broad development tree for the other topological and
geometric constructions.

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
discrete sufficient cases.  These are the publication-facing claims; the
automatic final-domain groupoid laws remain supporting infrastructure.

`Challenge.lean` duplicates the statement-facing definitions needed for that
theorem using Lean core, Mathlib, and the shared computational-path rewrite
kernel; it does not import the extracted topological implementation.
`Solution.lean` imports the extracted, checked comparison theory and supplies
the certificate.

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
its ordinary-composition consequence and obstruction, and both positive
sufficient-condition theorems.

The repository has been checked against Palomar's current metadata, layout,
toolchain, and pinned-manifest rules.  Registration still requires a hosted
Comparator/NanoDa run and editorial approval of this revised, concrete
comparison result.

## Reproduce the baseline

From the repository root:

```text
lake build
```

Useful local contract checks are:

```text
rg "\\bsorry\\b|\\badmit\\b|^axiom |native_decide" -g "*.lean" -g "!.lake/**"
git diff --check
```

The checked-in `lake-manifest.json` records the complete dependency closure;
the `lakefile.toml` and `lean-toolchain` are the only project controls needed
to reproduce the build.
