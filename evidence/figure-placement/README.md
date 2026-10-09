# Figure-placement visual review — 9 October 2026

Baseline: `ffb148df0c16bab42045b38b47d7d8fc704ad8ff`. The complete 35-page main paper was reviewed visually against each figure's first reference, motivating discussion, facing-page context, caption, whitespace, and reading sequence. The expanded computational-path diagram was the primary focus.

| Figure | First reference | Before | Final | Decision |
|---|---:|---:|---:|---|
| 1: Labelled computation | 3 | 4 | 3 | Move beside the defined signed-step notation and before weighted concatenation. |
| 2: Coherence | 5 | 6 | 6 | Retain adjacent to the ambient-space example. |
| 3: Same geometry | 8 | 9 | 9 | Retain the facing-page explanation of quotient separation. |
| 4: Backtracking | 10 | 11 | 11 | Retain beside its contraction lemma and before Section 3. |
| 5: Final/ordinary domains | 14 | 15 | 15 | Retain with the comparison theorem. |
| 6: Timing models | 18 | 19 | 19 | Retain beside the timing counterexample. |
| 7: Redundant generator | 20 | 21 | 21 | Retain with its completed proof and before related work. |
| 8: Normal forms | 23 | 24 | 24 | Retain immediately after the two-obligation argument. |
| 9: Universal section | 25 | 25 | 25 | Retain its same-page motivating paragraph. |
| 10: Winding | 30 | 31 | 31 | Retain facing the completed winding arguments. |
| 11: Rose covering | 32 | 34 | 33 | Move beside the covering construction and immediately before the lift/endpoint argument. |

The original Figure 1 interrupted Example 2.1: its identity was on page 3, while the final sentence followed the float on page 4. The revised layout puts Figure 1 on page 3 and keeps the weighted-concatenation formula and complete example together on page 4. Moving the intact figure into the introduction was rejected because its reversal footer would precede the definitions of the signed copies and extended maps.

Figure 1 uses local float priority, a full-width caption with unchanged type size, 6pt in-text float spacing, and a 16pt local page allowance. Its artwork, caption wording, and alternative text are unchanged. Figure 11 is anchored after the paragraph constructing the Cayley realization and its projection. A 40pt local allowance keeps the contraction formula together with its introductory paragraph on page 33. No global page dimensions, font sizes, or figure scales were reduced. [Measured bottom margins](margin-check.json) and full-size visual inspection show adequate clearance on the affected pages.

The final main paper remains 35 pages with all 11 figures; the supplement remains 18 pages. Cached Tectonic 0.17.0 compiled serially with one OpenMP thread, and Poppler rendered all 53 pages. Both the owner and an independent reviewer inspected the final rendered flow, including full-size pages 3–4 and 32–35. No local Lean rebuild was launched. The PDF skill's container-specific artifact-start helper is unavailable in this Windows checkout/runtime; the authorized repository's existing compilation and visual-verification workflow was used.

[Protected-content checks](protected-content.json) confirm that removing only the exact new layout commands and unchanged float blocks restores the baseline main source modulo whitespace. Thus mathematical statements, proofs, formulas, prose, citation keys, declaration names, labels, and preambles are unchanged. Inline figures/captions/alternative text and external figure artwork are unchanged. The supplement source, bibliography, Lean sources, pinned toolchain, dependency/replay manifests, and archived 51-page PDF are unchanged.

[PDF inspection](pdf-inspection.json) records page counts, all figure numbers, source/PDF hashes, embedded fonts, and resolved internal/cross-PDF destinations. There are no overfull boxes, undefined references, or multiply defined labels. Existing underfull-box and Fontconfig diagnostics remain visible in the compile logs. Exact-head hosted results and the downloaded replay-artifact audit are recorded in draft PR 13 after publication.

No merge or journal, arXiv, or registry submission is included.
