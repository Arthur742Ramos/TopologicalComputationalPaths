# 35-page manuscript revision

The main paper compiles to **32 pages including references**, and the linked
technical supplement to **21 pages**. The original 51-page PDF remains byte
identical; `full-manuscript.tex` is the exact LF-normalized manuscript source
from integrated main `4f48603a9309e4273438052d387cd967ffa695ca`.

## Editorial changes

The introduction and conclusion now center on presentation and parametrization
dependence. The central binary timing collision and coherent-representative
elimination statements moved from the verification history into the mathematical
sections. A literal-word correspondence proposition describes the independent
signed-word relation, typed tuple topology and checked fixed/global/final-pair
bridges, with its assumptions explicit.

The supplement contains the full proofs of trace realization, coherent
operations, weighted concatenation, backtracking, universal projection and fiber
identification, circle/torus winding, and primitive product completeness.
Their main-paper statements remain. Additional diagrams, full declaration maps,
parent-artifact inventory and historical verification records also moved there.
The introduction, model overview and concluding inventory were condensed;
mathematical statements and assumptions were not shortened.

The main retains the presentation-change theorem, conservative abbreviation
counterexample, binary timing proof, ordinary/final criterion, published global
open-map argument, and genuine geometric rose covering/contraction/all-loop
classification. The universal composable-domain proof retains its actual
continuous-section and endpoint-matched quotient argument; it does not infer
openness of the enriched projection from the existence of a section.

## Independent reviews

- `model_review`: checked all 47 original statement environments (including
  definitions) unchanged and the added literal-word proposition against source.
  Flat/binary, based/global, and zero-length assumptions pass. Three relocation
  phrases in the supplement were corrected: reduction lemmas refer to the main
  paper, and the product proof starts with identity traces.
- `proof_replay`: checked all 40 original theorem/lemma/proposition/corollary
  statements and proofs across the main and compact supplement. All statements
  retain their assumptions; 39 proof bodies are exact, and the remaining
  normal-form proof changes only its figure reference. All references and
  bibliography keys resolve. Fabel inputs and algebraic/topological fundamental
  group boundaries pass.
- `graph_feasibility`: independently checked the six reviewed PR head SHAs,
  merge ancestry and tree equivalence; integrated-main CI has the exact merged
  SHA and all seven jobs pass.

## Artifact validation

Tectonic 0.17.0 compiled both documents with the existing main preamble,
10-point `amsart` typography and margins unchanged. Every page was rendered
with Poppler and visually inspected, including full-size checks of the research
counterexample, rose classification, main references and supplement tables.
Neither document has overfull boxes, unresolved references, duplicate labels or
literal `??` markers. All 31 main-paper and 36 supplement font subsets are
embedded. PDF internal destinations and links to the paired published PDFs and
archival PDF are valid. Compiler logs retain nonfatal underfull-box diagnostics.
Detailed page counts, hashes, source hashes and link checks are recorded in
`pdf-inspection.json`. Merge evidence is recorded in `merged-stack.json`.

No Lean source, theorem, verification manifest, toolchain or dependency changed
in this editorial revision. Exact-head hosted CI is required separately for the
new revision; the preserved proof source already passed integrated-main run
37761277718.
