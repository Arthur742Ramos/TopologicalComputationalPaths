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
is a new publication-oriented extraction; it is not yet a Palomar submission.
The parent repository remains the canonical broad development tree until the
extraction is complete.

## Publication boundary

The eventual Palomar package will contain one pinned Lean project with a small
`Challenge.lean`, a matching `Solution.lean`, and an explicit Comparator
configuration.  The challenge will state the result using only the permitted
statement-side imports; the solution may use the pinned focused development.

Before submission, the package must pass the current Palomar toolchain and
dependency checks, contain no `sorry`, `admit`, custom axioms, or
`native_decide`, and have a research-interest statement that accurately
separates the formalized theorem from the surrounding mathematical program.

## Status

The initial 30-file core extraction is present and builds successfully with
the parent v4.24.0 toolchain.  The Palomar harness and the supported-toolchain
port are still pending.

## Reproduce the baseline

From the repository root:

```text
lake build
```

The extraction is intentionally committed before the toolchain port, so any
later Lean-version changes can be reviewed separately from source selection.
