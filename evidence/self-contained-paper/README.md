# Self-contained paper and typed examples, 14 October 2026

Base: `fb3da4d5772dc13c0d568c3a0844c8a86fe3bd35` (merged PR14).
Astra High authored the manuscript revision. A separate Astra High reviewer
accepted the integrated mathematical and self-containedness changes; the
coordinating agent independently read the diff and inspected every rendered page.

## Changes

- The introduction gives a simply typed lambda-calculus term with two beta
  reduction orders, typed intermediate terms, labelled witnesses, composition,
  reversal, and cancellation. Equality of endpoints does not silently identify
  the parallel witnesses.
- Nine proofs previously delegated to the supplement now contain their actual
  arguments: realization and operation continuity, weighted homotopy invariance,
  backtracking, universal and fixed-endpoint quotient comparisons, circle and
  torus classification, and product completeness.
- The main text defines tree syntax and its two observation topologies, gives
  product primitive-space topologies and continuous realizations, and specifies
  discrete primitive alphabets in the finite examples.
- The circle and torus proofs separately justify the actual global based
  subspace topology using descended variable-base winding maps. The quotient
  proofs do not assume that arbitrary restrictions of quotient maps are quotient.
- Section 9 states the binary/flat formalization boundary in the main paper.
  All supplement and archived-manuscript pointers are removed from the main.
  The supplement is ancillary: expanded calculations and historical verification
  records. Standard background results and credited external geometric inputs
  retain their explicit status.

## Validation and layout

The main paper is **38 pages including references**, the supplement **18 pages**.
The two-page increase from the reviewed baseline holds the typed example and
essential arguments. The existing 10-point font, margins, and preamble are
unchanged. No layout compression was used to conceal the added content.

Both PDFs were built serially with cached Tectonic 0.17.0. All 56 pages were
rendered and visually inspected; changed and dense pages were additionally
inspected at full size. All eleven figures remain in order, on the page of
their discussion or the following page, with unchanged art, captions and alt
text. No clipping, overlap, overfull boxes, unresolved references, or multiply
defined labels were found. All fonts are embedded and all internal and remote
PDF destinations resolve. Nonblocking underfull-box warnings remain.

The [inspection record](pdf-inspection.json) contains hashes, figure pages,
font/link checks, and preservation results. All 140 protected Lean, toolchain,
manifest, figure, bibliography and archived-source files match the base after
normalizing checkout line endings. The theorem, lemma, proposition and corollary
statements and every figure environment are unchanged. The archived 51-page PDF
is byte-for-byte unchanged.

No Lean development, proof assumptions or verification selection changed.
The independent review accepted the restored arguments and found no essential
residual supplement dependency; it did not claim a new local Lean replay.
Exact-head hosted CI belongs to the revision's pull request and is reported
there separately. This revision includes no journal/preprint submission or
Library upload.
