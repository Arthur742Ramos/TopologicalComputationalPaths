# Computational-path introduction and related work

This editorial follow-up starts from draft PR #13 head
`81e897cdca336877acdf73420e29bb5dff323df0`. The introduction source was
independently reviewed at checkpoint
`4e92f6747151e93d1c3480f462a6fdc288e0815b`.

The introduction explains labelled equality judgements, finite derivations by
rewrites and substitutions, composition through an intermediate expression,
reversal and reflexivity. A concrete cancellation example distinguishes the
endpoint judgement from rewriting between its witnesses. It then introduces
the scoped geometric fragment, the two representative topologies,
presentation dependence, the invariance criterion and final-domain
composition with their existing boundaries.

The related-work paragraph cites the identity-type and weak-groupoid accounts,
earlier circle/torus/projective-plane calculations, and *Computational Paths:
The Calculus of Equality* by Ramos, de Queiroz, de Oliveira and Gabbay.
The book is foundational background; the introduction imports no general
termination, confluence or decidability result for arbitrary presentations.

## Primary-source checks

- [2016 propositional-equality article](https://www.sa-logic.org/sajl-v2-i2/05-De%20Queiroz-De%20Oliveira-Ramos-SAJL.pdf): labelled derivations and rewrite operations.
- [2017 identity-type article](https://academic.oup.com/jigpal/article/25/4/562/3891484): identity-type interpretation and groupoid structure.
- [Weak-groupoid article](https://academic.oup.com/logcom/article/35/5/exad071/7439608): four authors; published online 24 November 2023, JLC35(5), exad071 (2025); weak category/groupoid.
- [Topological application preprint](https://arxiv.org/abs/1906.09105): circle, torus and real projective plane; submitted 19 June 2019, version 4 revised 9 May 2021. The existing bibliography key is retained, but its unsupported forthcoming-journal status is replaced by this verified preprint metadata.
- [Publisher book description](https://www.collegepublications.co.uk/logic/mlf/?00037=): four authors, 11 May 2026, ISBN 978-1-84890-515-3. Only its explicit-witness background is cited; no uninspected chapter-specific assertion is used.

## Validation

Humanizer 3.0.0 was applied in embedded prose mode; one bounded wording edit
is recorded in humanizer-edits.json. Independent source review confirmed the
example endpoints and citation claims. The abstract, typography and all text
after the introduction are unchanged from 81e897c. Every figure source,
mathematical statement/proof, Lean source, toolchain, dependency and replay
manifest is unchanged. The targeted preprint entry is the only bibliography
edit. The 51-page archival PDF is unchanged.

Existing cached Tectonic 0.17.0 compiled serially: main 8.12 seconds, supplement
3.48 seconds. No local Lean rebuild or other task's process, lock or files was
accessed. The result remains 35 main pages with 11 figures and 18 supplement pages.
Both authoring and independent reviewers inspected all 53 rendered pages,
including full-size introduction and bibliography checks. No clipping,
overlap or unresolved references appeared. Compile logs record zero overfull
boxes, undefined references and multiply defined labels; nonfatal fontconfig
and underfull-box diagnostics remain.

pdf-inspection.json records final source/PDF hashes, embedded fonts, figure
pages and resolved internal/cross-PDF destinations. The updated draft PR must
record successful hosted exact-head build, all five Comparator/NanoDa
configurations and selected-declaration replay before the new head is called
verified. Prior proof evidence does not substitute for those checks. The PR
remains a draft; no merge or journal/arXiv/registry submission is included.
