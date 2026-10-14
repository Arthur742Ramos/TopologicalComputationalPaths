# Paper review, 14 October 2026

This editorial revision starts from main commit
`7910b8bbb633ec8c606229f18c4b696ed1eea357`. Astra High prepared the changes;
a separate parent review checked the arguments and all rendered pages. A final
Astra read-only review found no blocking mathematical or editorial issue.

## Changes

- Theorem 5.4 now has a nondiscrete application over the cylinder: the primitive
  alphabet varies continuously with the real coordinate, and an abbreviation
  expands to two letters. The componentwise word codes are continuous; their
  lengths are locally constant. This is a mathematical application, not a claim
  of a new separately formalized Lean example.
- Remark 6.4 supplies the closed-fiber restriction argument transferring the
  Hawaiian-earring based obstruction to the global ordinary pair map.
- Supplement Table 1 explicitly distinguishes the mathematical proofs of
  general flat operations and final multiplication from the checked model
  bridges. No separate flat-operation declaration is claimed.
- Related work distinguishes algebraic/coherent Tietze results from continuity
  for the specified quotient topologies. The Henry–Mimram publication record
  and Mimram–Oleon reference are updated; DOI/arXiv identifiers are visible.

Primary bibliographic records checked:
[Henry–Mimram](https://link.springer.com/article/10.1007/s10485-021-09662-w),
[Mimram–Oleon](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2025.30).

## Preservation and validation

The computational-paths introduction, preamble, existing theorem/proof
environments, all eleven figure environments, captions and alt text are
unchanged. All 134 protected Lean, toolchain, manifest, figure-source and
archived-manuscript files match the base after normalizing checkout line endings.
The archived 51-page PDF is byte-for-byte unchanged.

Both PDFs were built serially with Tectonic 0.17.0 using cached dependencies.
The main paper has **36 pages**, including references; the supplement has
**18 pages**. The existing 10-point layout and margins are unchanged. Every
page was rendered and inspected; changed/dense pages were also inspected at
full size. No clipping or overlap was found. All fonts are embedded, all
internal and cross-PDF destinations resolve, all eleven figures and authored
alt texts remain, and there are no overfull boxes, unresolved references or
multiply defined labels. Nonblocking underfull-box warnings remain.

See [the PDF inspection record](pdf-inspection.json) for hashes, figure pages,
font and link checks. The main PDF is renamed `main-reviewed.pdf` so the
filename does not claim an obsolete page count. Keep it beside the supplement
and archival PDF to preserve cross-document links.

This revision changes no Lean source, toolchain, proof assumptions or statement
selection. Existing hosted verification evidence belongs to its recorded source
commits; it is not described as a new local Lean replay. Exact-head CI for this
revision is reported separately on its pull request. No journal or preprint
submission is part of this revision.
