# Topological semantics manuscript

This directory mirrors the revised LaTeX source from
[`ComputationalPathsLean`](https://github.com/Arthur742Ramos/ComputationalPathsLean),
branch `feat/full-omega-groupoid`, commit `b6f47117`. The bibliography is
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

`igpl-cover-letter.txt` is the parent snapshot's August 2026 submission
letter. Its page count and author-approval statements do not describe this
revision.
