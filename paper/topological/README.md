# Topological semantics manuscript

The main paper is [main.tex](main.tex), with a compiled version at
[verified/main-35-pages.pdf](verified/main-35-pages.pdf). It uses the existing
10-point `amsart` layout and compiles to **35 pages including references**.
All nine original explanatory figures remain in the main paper, together with
new timing-model and conservative-generator diagrams (eleven figures total).
Figure captions are followed by authored alt text in the source and review PDF.
The [technical supplement](supplement.tex)
([PDF](verified/technical-supplement.pdf), 18 pages) holds the longer construction,
circle, torus and product calculations, and complete
maps of declarations, assumptions, models and verified source commits.

The 35-page working target is the user's editorial goal. The
[official IGPL instructions](https://academic.oup.com/jigpal/pages/General_Instructions)
ask for **about 30 printed pages**, an approximate target rather than an explicit
hard maximum. Our `amsart` PDF count is not a verified journal-typesetting count.
No mandatory IGPL LaTeX class or journal-specific supplement allowance was
verified. The main is therefore a reviewed working manuscript, not a claim of
submission-format approval; see [the guidance record](../../evidence/paper35/igpl-guidance.md).

The unabridged manuscript is preserved as [full-manuscript.tex](full-manuscript.tex)
and the previously inspected [51-page PDF](verified/geometric-rose-all-loops.pdf).
Its source is the manuscript at integrated main commit
[`4f48603a9309e4273438052d387cd967ffa695ca`](https://github.com/Arthur742Ramos/TopologicalComputationalPaths/tree/4f48603a9309e4273438052d387cd967ffa695ca).
The editorial revision does not change the Lean development. The
[latest editorial review](../../evidence/review-cleanup/README.md) records the
README cleanup, restored logical motivation and dated verification history.

The paper treats equal-slot flat signed words and distinguishes them from
recursive binary `Path.trans`. Both models have checked developments; weighted
homotopy invariance does not identify their observable topologies. Literal-word
correspondence, fixed and global coherent-representative elimination, final
composable-pair comparisons, variable-length substitution invariance, timing
collisions and the conservative abbreviation counterexample are checked.
Each theorem retains its specific continuity and rewrite hypotheses.

The geometric rose development constructs its edge covering and contracts the
Cayley graph, giving completeness and classification of all continuous based
loops. Its fundamental-group identification is algebraic: direct realization
is an antihomomorphism for Mathlib's multiplication convention, and inversion
gives the ordinary free-group isomorphism. It does not assert an unproved
topological fundamental-group comparison. The abstract complete-discrete-label
separation mechanism is checked; harmonic-archipelago facts and the stated
Hawaiian-earring inputs remain external hypotheses as explained in the paper.

The integrated source passed [exact-head CI](https://github.com/Arthur742Ramos/TopologicalComputationalPaths/actions/runs/37761277718):
the repository build, all five Comparator/NanoDa configurations and the direct
178-declaration model-boundary replay. The pinned toolchain is Lean 4.32.0 with
Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`. Checked declarations use
only `propext`, `Classical.choice` and `Quot.sound`.

From the repository root, with pinned dependencies available:

```text
lake build
lake env lean ModelBoundaryVerification.lean
```

The bibliography is [../refs.bib](../refs.bib), and figures are in
[figures/](figures/). Build the paper and supplement in order, from the repository
root, preserving the main auxiliary file for the supplement's external references:

```text
tectonic --keep-logs --keep-intermediates --outdir output/paper35 paper/topological/main.tex
tectonic --keep-logs --keep-intermediates --outdir output/paper35 paper/topological/supplement.tex
```

The links between the PDFs use `main-35-pages.pdf` and
`technical-supplement.pdf`; keep both published PDFs in the same directory.
Full historical verification records, including the distinct parent and
Palomar snapshots, are in supplement Section S4 and its declaration appendix.

`igpl-cover-letter.txt` remains a draft. Before sending it, the corresponding
author must confirm coauthor approval and the current submission status.
