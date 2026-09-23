# Topological semantics manuscript

This directory mirrors the revised LaTeX source from
[`ComputationalPathsLean`](https://github.com/Arthur742Ramos/ComputationalPathsLean),
branch `feat/full-omega-groupoid`, commit `b6f47117`. The bibliography is
[`../refs.bib`](../refs.bib). The manuscript cites the broader parent Lean
artifact and the immutable Palomar version 1; those are distinct from the
working-tree changes in this focused repository.

The revision in this repository adds an open-quotient compatibility criterion, a positive
universal-groupoid result based on the published theorem of Holkar, Hossain,
and Kulkarni, and a continuous-section criterion for collapse of the
trace-sensitive quotient topology. It also proves a general product theorem
for based completeness. Lean now checks the product sorting and based
completeness theorem for the presentation with whole-trace interchange. It
also checks finite-generator circle and torus trace choices, with their
quotient comparison conditional on scoped completeness. The remaining work is tracked in
[`../../ROADMAP.md`](../../ROADMAP.md).

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
