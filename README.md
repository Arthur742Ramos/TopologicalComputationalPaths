# Topological Computational Paths

This repository develops topological semantics for the Calculus of
Computational Paths. A presentation gives primitive equality witnesses,
declared rewrites and continuous geometric realizations. The scoped quotient
retains the computational distinctions left by those rules. We study which
quotient topologies preserve them, and when changes of presentation preserve
the resulting semantics.

## Paper and verified artifacts

- [Main paper](paper/topological/verified/main-35-pages.pdf), 35 pages with eleven
  explanatory figures; [LaTeX source](paper/topological/main.tex).
- [Technical supplement](paper/topological/verified/technical-supplement.pdf),
  18 pages; [source](paper/topological/supplement.tex). It contains longer
  calculations and declaration/assumption/model/commit verification maps.
- [Manuscript overview and compilation commands](paper/topological/README.md).
- [Preserved full manuscript](paper/topological/full-manuscript.tex) and
  [51-page archival PDF](paper/topological/verified/geometric-rose-all-loops.pdf).

The 35-page count is the working manuscript target, including references and
visible review-copy alt text. IGPL asks for about 30 printed pages; the current
amsart count is not a verified journal production count. See the
[official-guidance record](evidence/paper35/igpl-guidance.md).

## Proved results and scope

| Result | Checked construction and boundary |
| --- | --- |
| Equal-slot realization | Each primitive occupies its prescribed equal slot. Equal signed words give equal parametrized flat realizations. Binary `Path.trans` is a separate model; homotopy does not identify its observable topology with the flat one. |
| Literal-word correspondence | An independent adjacent-cancellation/named-rule relation corresponds to tree rewriting. Compatible finite tuple strata retain the empty word's basepoint. Fixed-endpoint, global-arrow and final-composable-pair quotient comparisons are checked. |
| Coherent-representative elimination | The extra geometric representative can be eliminated homeomorphically in matching models, with fixed/global/final-pair comparisons. |
| Presentation invariance | Variable-length primitive word codes, named-rule preservation and scoped primitive roundtrips yield flat full-word quotient homeomorphisms at fixed endpoints, globally and on final composable-pair domains. Geometric compatibility has its explicit primitive homotopy hypothesis. |
| Timing dependence | A three-label circle has a non-T0 binary observable based quotient and a discrete flat one, excluding any homeomorphism between them. |
| Conservative abbreviation failure | Adding a generator defined by a word preserves the algebraic presentation. The canonical observable inverse is discontinuous; the flat full-word comparison is a homeomorphism under its proved conditions. This does not exclude every unrelated bijection. |
| Complete discrete-label separation | The all-path presentation is geometrically complete. Its flat observable based quotient recovers the ordinary loop quotient, while the full-word quotient is discrete. Nonhomeomorphism assumes the ordinary quotient is nondiscrete; harmonic-archipelago geometry remains external. |
| Composition topology | The generic certificates use the earlier binary package. Composition is continuous on the final quotient of explicitly composable representatives. Four equivalent conditions characterize agreement with the ordinary pair topology and imply ordinary continuity. Ordinary continuity alone is not asserted to force that agreement. An open arrow quotient is sufficient. |
| Universal positive case | In the earlier binary universal package, local path-connectedness and semilocal simple connectivity give openness of the path-class projection, ordinary-pair compatibility and continuous composition. The published open-map theorem is credited to Holkar, Hossain and Kulkarni. |
| Finite circle, torus and products | Exact scoped normal forms give circle/torus completeness. Named winding homeomorphisms and based-subspace comparisons use the earlier binary quotient package; primitive-interchange product completeness is checked. |
| Geometric nonabelian rose | An actual two-circle rose, interval-glued Cayley covering and jointly continuous contraction classify all continuous based loops by reduced words. Computational fixed-endpoint quotients are discrete. The ordinary fundamental-group identification is algebraic, with Mathlib's multiplication reversal handled through the opposite group and inversion. |

The ordinary quotient-topological fundamental group of the rose has no checked
homeomorphism to discrete F2 in this development. A flat operations package
parallel to the older binary generic groupoid interface is also further work.
These are extensions of the stated results; the
[optional-extension assessment](evidence/review-cleanup/optional-extensions.md)
gives their proof steps, costs and completion criteria. The Hawaiian-earring failures of
product quotientness and ordinary multiplication remain explicit external
hypotheses in their checked transfer.

Principal modules are under [ComputationalPaths/Path/Topology](ComputationalPaths/Path/Topology).
The supplement provides exact declaration maps instead of treating the paper
as a single formalized theorem. The separate
[Smith/preimage research prototype](PREIMAGE-RESEARCH-NOTE.md)
and [follow-up certificate](FOLLOWUP.md) retain their own scope.

## Current verification

The integrated source at
[`1922376`](https://github.com/Arthur742Ramos/TopologicalComputationalPaths/tree/1922376592442324448b474de068db6a09af18f8) passed
[all seven required CI jobs](https://github.com/Arthur742Ramos/TopologicalComputationalPaths/actions/runs/37777395615):
the Lean build and contract checks, five retained Comparator/NanoDa
configurations, and the direct model-boundary replay. The latter selects
**178 declarations: 127 theorems and 51 definitions** in
[model-boundary-replay.json](model-boundary-replay.json). Pinned NanoDa checked
the **20,013-declaration dependency closure** with zero typechecker errors.
Only `propext`, `Classical.choice` and `Quot.sound` occur as axioms.
NanoDa also emits a nonfatal axiom pretty-printer diagnostic.

Lean is pinned to **4.32.0**, kernel commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`; Mathlib is pinned to
`81a5d257c8e410db227a6665ed08f64fea08e997` in
[lake-manifest.json](lake-manifest.json). CI retains the exact source SHA,
selection, export digest, coverage/axiom audit and NanoDa log. Hosted proof
checking covers those declarations and their closure; it is not a proof of the
manuscript's prose or an endorsement of novelty.

## Reproduce

With the pinned Lean toolchain and dependencies, from the repository root:

```sh
lake build
lake env lean ModelBoundaryVerification.lean
bash scripts/check-palomar.sh --skip-build
bash scripts/check-followup.sh --skip-build
bash scripts/check-roadmap.sh --skip-build
python3 scripts/test_model_boundary_audit.py
bash scripts/verify-model-boundary.sh
```

The direct replay requires Python, Cargo, Git and Lake; it fetches the pinned
exporter and NanoDa revisions into ignored `.cache/` and checks the toolchain.
For each retained Comparator selection, also install Go and run:

```sh
bash scripts/verify-comparator.sh comparator.json
bash scripts/verify-comparator.sh comparator-followup.json
bash scripts/verify-comparator.sh comparator-preimage.json
bash scripts/verify-comparator.sh comparator-roadmap.json
bash scripts/verify-comparator.sh comparator-registry-roadmap.json
```

Build the paper first and retain its auxiliary file for supplement references:

```sh
mkdir -p output/paper35
tectonic --keep-logs --keep-intermediates --outdir output/paper35 paper/topological/main.tex
tectonic --keep-logs --keep-intermediates --outdir output/paper35 paper/topological/supplement.tex
```

Challenge-side statement placeholders are deliberate comparison interfaces.
Solution proofs and the substantive development contain no `sorry`, `admit`,
custom axioms or `native_decide`. The named selections have distinct scopes;
local or CI replay does not create a new Palomar registration.

## Dated milestones and source lineage

| Date | Milestone and preserved evidence |
| --- | --- |
| 29 August 2026 | [Palomar version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-08-29-000005&version=1), pinned to `8254c40d0de03ff469c7c9c05087b8bc154e9a87`; its narrower registered certificate remains distinct from later work. |
| 24 September 2026 | Working-source snapshot `09b20abe0a4f69b361846c2466bff8528044fa93`, including universal/finite-fiber and trace-topology extensions. |
| 8 October 2026 | Equal-slot milestone `404ac01`; the [42-page milestone PDF](paper/topological/verified/equal-slot-model-boundary.pdf), [kernel evidence](evidence/flat-model-kernel.log) and [19-declaration hosted evidence](evidence/flat-model-hosted-131e4bf/README.txt) are historical. |
| 8 October 2026 | Binary substitution/observable abbreviation milestone `d604b75`; [44-page milestone PDF](paper/topological/verified/presentation-change-model-boundary.pdf) and [kernel evidence](evidence/presentation-change-kernel.log). Its 37-declaration scope preceded general variable-length flat transport. |
| 8 October 2026 | Literal-word/variable-length milestone `0346c8e`, followed by geometric rose completeness `dbfe65e` and all-loop classification `3fd21d0`. The earlier 99- and 141-declaration selections were extended to 178. |
| 8 October 2026 | Integrated and independently reviewed paper revision `1922376`: 35-page main, eleven figures, 18-page supplement and exact-main CI success. |

The [historical README snapshot](README-HISTORY.md) preserves the prior progress
narrative, source lineage, baseline/follow-up certificate details and older
verification commands. Pending-work language there belongs to its recorded
milestone. [ROADMAP.md](ROADMAP.md) records the broader research program.
The parent [ComputationalPathsLean](https://github.com/Arthur742Ramos/ComputationalPathsLean)
repository remains the broader development; this repository is its focused
topological extraction. The supplement separates the parent Lean 4.24.0
archive, registered version 1 and later Lean 4.32.0 selections.

The [IGPL cover letter](paper/topological/igpl-cover-letter.txt) is a draft.
Submission status and coauthor approval require the corresponding author's
confirmation before it is sent.
