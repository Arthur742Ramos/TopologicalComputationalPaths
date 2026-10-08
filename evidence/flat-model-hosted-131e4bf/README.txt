Hosted source: 131e4bf714f1693dc1353bc6164687c1d8b2f1e2
PR: https://github.com/Arthur742Ramos/TopologicalComputationalPaths/pull/7
Quality run: https://github.com/Arthur742Ramos/TopologicalComputationalPaths/actions/runs/37726628135
Status checked 2026-10-08 UTC: success for the full Lean build, five previous
Comparator/NanoDa configurations, and selected model-boundary NanoDa replay.
Registry mechanical preflight was skipped; no registration was requested.

The new direct export selects 19 actual declarations and recursively exports
11849 declarations. Export SHA256, independently recomputed after download:
0355c243497dda03f7d94956b1d8770da3bcf32a4ff52da31da5e0ce1c0e8ba4
Selected names/kinds, Lean/exporter metadata, safety and the permitted axiom
closure passed the audit. NanoDa reported no typechecker errors. It reported
one pretty-printer diagnostic, "Unable to print axioms"; this is preserved in
nanoda.log. The export audit enumerates the actual three standard axioms.
The full export and configuration are retained in the run's named artifact
model-boundary-replay-131e4bf714f1693dc1353bc6164687c1d8b2f1e2.

Published PDF:
https://github.com/Arthur742Ramos/TopologicalComputationalPaths/blob/131e4bf714f1693dc1353bc6164687c1d8b2f1e2/paper/topological/verified/equal-slot-model-boundary.pdf
Its downloaded bytes were checked against SHA256
d127c29f385fbf02570d3a01b574172ba885cd6dae4411abeeb62ce4c31d8dc0.

This evidence applies to that exact source revision. It does not verify later
unpublished word-interpretation or presentation-change declarations.
