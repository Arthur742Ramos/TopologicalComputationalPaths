# Topological semantics manuscript

This directory began with revised LaTeX source from
[`ComputationalPathsLean`](https://github.com/Arthur742Ramos/ComputationalPathsLean),
branch `feat/full-omega-groupoid`, commit `b6f47117`, and has since been edited
in this repository. The bibliography is
[`../refs.bib`](../refs.bib). The manuscript cites the broader parent Lean
artifact and the immutable Palomar version 1; those are distinct from the
working-tree changes in this focused repository.

The revision proves an open-arrow compatibility criterion and gives a
proof of the published universal path-class open-map theorem of Holkar,
Hossain, and Kulkarni. It derives product-trace interchange from primitive
rectangle swaps and proves based completeness for the finite circle and
torus presentations. A continuous trace section identifies the two scoped
quotient topologies when the presentation is complete. A complete
discrete-label presentation over the harmonic archipelago shows that
completeness alone does not suffice. Lean checks the global open-map theorem,
primitive product closure, and the finite based completeness results. The
mathematical harmonic-archipelago counterexample is outside the Lean
selection. The external Palomar preflight and registration boundary is
tracked in [`../../ROADMAP.md`](../../ROADMAP.md).

The manuscript uses equal-slot flat signed words. Existing Lean topology
results use recursive binary `Path.trans`, and the trace-sensitive refinement
retains that binary realization coordinate. Homotopy invariance of weighted
concatenation does not identify these observable topologies. Section 10 now
states this boundary explicitly. The binary results remain unchanged.

The first model-boundary milestone is pinned at source commit
[`9d9679908e09b1ed0c42e4898f11d797c6a979af`](https://github.com/Arthur742Ramos/TopologicalComputationalPaths/tree/9d9679908e09b1ed0c42e4898f11d797c6a979af).
`BinaryTimingCollision` proves an exact realization collision, distinct
scoped classes, and failure of T0 for both fixed-base and global binary
quotients. `CoherentRepresentativeElimination` proves fixed-endpoint
quotient homeomorphisms for matching binary observable and full-word trace
topologies. The general result needs continuity of realization and no
completeness assumption. The flat discreteness argument in the manuscript
remains mathematical exposition pending formalization. Global elimination
and final composable-pair elimination are also pending.

With the pinned dependencies available, run:

```text
lake build ComputationalPaths
lake env lean ModelBoundaryVerification.lean
```

The axiom-inspection output is recorded in
[`../../evidence/model-boundary-kernel.log`](../../evidence/model-boundary-kernel.log).
It contains only `propext`, `Classical.choice`, and `Quot.sound` for the new
declarations. Existing Comparator/NanoDa configurations select earlier
results and do not replay these new declarations.

The paper's earlier working-source Lean claims are reproducible from focused
repository commit [`09b20abe0a4f69b361846c2466bff8528044fa93`](https://github.com/Arthur742Ramos/TopologicalComputationalPaths/tree/09b20abe0a4f69b361846c2466bff8528044fa93)
with the checked-in Lean 4.32.0 toolchain and dependency manifest. The new
model-boundary declarations are pinned separately above.
From the repository root, run `lake build` to check every configured target.
The prior Palomar version 1 is pinned separately in Section 10 of the paper.

To build the manuscript from this directory, use either `latexmk` with a
LaTeX distribution or Tectonic:

```text
latexmk -xelatex -interaction=nonstopmode -halt-on-error main.tex
# or
tectonic main.tex
```

The figures live under [`figures/`](figures/). The Lean extraction in this
repository can be checked from its root with `lake build ComputationalPaths Solution Challenge`; the
broader parent artifact must be built in `ComputationalPathsLean`.

`igpl-cover-letter.txt` is a draft covering message for this revision. Before
sending it, the corresponding author must confirm every coauthor's approval
of the final manuscript and the paper's current journal-submission status.
The draft makes no claim about either unverified fact.
