# Figure-rich 35-page manuscript revision

The main paper compiles to **35 pages including references and review-copy alt
text**, with **eleven explanatory figures**. The linked technical supplement is
**18 pages**. All nine original figures are in the main paper; two new vector
figures explain timing dependence and conservative generator elimination.
The original 51-page PDF remains byte-identical. `full-manuscript.tex` is the
exact manuscript source from integrated main
`4f48603a9309e4273438052d387cd967ffa695ca`.

## Editorial changes

The revision restores the seven explanatory figures moved to the supplement in
the earlier 32-page draft. Approximately 850 words of repeated framing,
construction recap and artifact history were cut to make room. Existing
10-point amsart typography, margins and original figure sizes are retained.
Figure references are resolved, and all eleven captions have authored alt text.
The journal guidance is recorded separately in `igpl-guidance.md`: IGPL asks
for about 30 printed pages, while 35 pages is the user's working target. The
present layout does not establish the eventual journal production page count.

The introduction and conclusion focus on presentation and parametrization
dependence. The central binary timing collision and coherent-representative
elimination appear in the mathematical sections. An added literal-word
correspondence proposition describes the independent signed-word relation,
typed tuple topology and checked fixed/global/final-pair bridges, with its
assumptions explicit. All 47 original statement/definition environments retain
their original mathematical content.

Two routine quotient-descent proofs are condensed: the final-domain groupoid
and comparison morphism. The central timing counterexample, substitution
invariance, abbreviation failure, ordinary/final criterion, global universal
open-map argument and geometric rose covering/contraction/all-loop proofs
remain in the main. The universal argument names openness of the path-class
projection and uses the actual continuous-section/endpoint-matched quotient
construction; a section alone does not imply openness of the enriched carrier
projection. The supplement retains the longer construction, circle, torus and
product calculations, complete declaration maps and historical verification
records. Essential explanatory diagrams remain in the main.

## Humanizer pass

After completing the figure restoration, the explicitly requested
`humanizer:humanizer` skill was read and applied to main-paper prose. The actual
skill source was
`C:/Users/arfreita/.codex/skills/humanizer/SKILL.md`, version 3.0.0.
Fourteen bounded replacements remove rhetorical openings, repeated framing and
inventory phrasing. `humanizer-edits.json` records the exact replacements.
Technical distinctions, including the flat/binary boundary and the one-way
ordinary-continuity implication, remain explicit.

Two independent source reviewers compared the final manuscript against the
saved pre-Humanizer baseline and exact edit log. Both found precisely the
fourteen replacements and no unlogged change. All 48 statements/definitions,
41 proof bodies, 690 inline formulas, 88 displayed formulas, citations,
figure/alt-text calls, Lean declaration references and link targets are
unchanged by this prose pass. The revised abstract correctly attributes
openness to the path-class projection. Neither reviewer found unsupported
claims or semantic losses.

## Independent mathematical and visual reviews

- `model_review` compared the original statements, model boundaries, relocated
  proofs and new literal-word proposition against source. It reviewed the two
  condensed quotient proofs and all eleven figures. Mathematical content and
  flat/binary, fixed/global, zero-length and fundamental-group boundaries pass.
- `proof_replay` checked statement preservation, proof relocation, the new
  timing and redundant-generator diagrams, references, external geometric
  hypotheses and all-loop classification claims. The final Humanizer source
  comparison also passes.
- `graph_feasibility` inspected every page of the 35-page main and 18-page
  supplement, all eleven figures at full size, the references and verification
  tables. It confirmed the official IGPL length/figure guidance and identified
  stale evidence from the earlier draft, now replaced by these records.
- The authoring agent inspected all 53 final rendered pages after the prose
  pass, with full-size follow-up checks of the abstract, timing and abbreviation
  diagrams, all-loop proof, rose figure and references.

## Artifact validation

Tectonic 0.17.0 compiled both documents, followed by Poppler page rendering.
Neither PDF has overfull boxes, unresolved references, duplicate labels or
literal question-mark reference markers. All 37 main-paper and 30 supplement
font subsets are embedded. Internal destinations and links between the paired
published PDFs and the preserved archival PDF resolve. Compiler logs retain
nonfatal underfull-box diagnostics; trailing whitespace is normalized in the
tracked copies. `pdf-inspection.json` records counts, hashes and destination
checks, and `figure-inventory.json` records the restored/new diagrams and pages.

No Lean source, verification manifest, toolchain or dependency changes in this
editorial revision. Exact-head hosted CI is required for publication separately;
the preserved proof source already passed integrated-main run 37761277718.
