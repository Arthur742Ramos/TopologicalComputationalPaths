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

The package will keep the final-domain statement distinct from the stronger
ordinary-topological-groupoid statement.  That distinction is part of the
mathematical result, not merely an implementation detail.

The circle and torus constructions, geometric comparison, functoriality, and
the finite separation/obstruction examples are planned as supporting modules.
They will be included only after they have been ported into the focused
dependency boundary and independently checked.

## Source lineage

The starting implementation is the topological layer at the immutable source
snapshot `topological-paper-v12` of the parent repository.  This focused repo
is the publication-oriented extraction of that layer.  The parent repository
remains the canonical broad development tree for the other topological and
geometric constructions.

## Publication boundary

This repository now contains one pinned Lean project with a focused
`Challenge.lean`, a matching `Solution.lean`, and an explicit `comparator.json`.
The compared `main_result` directly states the scoped geometric rewrite
quotient's final-domain topological groupoid certificate: continuity of all
structural operations, the unit, inverse, and associativity laws, rewrite
soundness for geometric realization, and explicit trace-level `Path` and
`ScopedRwEq` witnesses.  `Challenge.lean` duplicates only the statement-facing
definitions needed for that type using Lean core and Mathlib; it does not import
the project library.  `Solution.lean` imports the extracted, checked groupoid
construction and supplies the fields.  The generic final-domain/comparison
interface and its quotient-descent adapter remain supporting material.

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
`sorry`, `admit`, custom axioms, or `native_decide`.  The concrete solution
also proves that its canonically descended operation agrees with the scoped
quotient composition from the extracted development.

The repository has been checked against Palomar's current metadata, layout,
toolchain, and pinned-manifest rules.  A registry submission still requires a
public GitHub repository and immutable commit, followed by Palomar's hosted
Comparator/NanoDa run and editorial review.

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
