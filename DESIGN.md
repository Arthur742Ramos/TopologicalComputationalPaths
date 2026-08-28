# Extraction design

## Core theorem family

The initial focused package will extract the following dependency chain from
the parent repository:

- `ScopedGeometricRewritePresentation` and scoped rewrite soundness;
- the quotient arrow space and its source, target, identity, inverse, and
  composition maps;
- the final composable domain and the ordinary pullback domain;
- `scopedFinalTopologicalGroupoidCertificate`;
- `scopedProductCompatibility_iff_four_way` and the associated final/ordinary
  comparison theorem; and
- the compact-Hausdorff and discrete sufficient conditions; and
- the concrete observable based fiber of the universal continuous-path
  presentation, its standard based-loop quotient homeomorphism, and its
  final/ordinary pair comparison; and
- the source-backed Hawaiian-earring transfer against the actual based loop
  quotient and quotient multiplication; and
- the genuine additive-circle winding classification and coordinatewise
  product-torus classification, proved from explicit covering and lifting
  constructions.

These declarations form one coherent result: the canonical final-domain
semantics is unconditional, while ordinary multiplication requires a precise
topological compatibility hypothesis.

## Supporting layers

The following layers are candidates for the first full release, but are not
part of the minimal extraction until they compile against the focused core:

- presentation functoriality;
- the geometric comparison/completeness criterion;
- the realized fundamental-groupoid bridge.

The Hawaiian-earring item now has two explicit layers.  First, the statement
constructs the based fiber of the universal continuous-path step system,
retains its computational trace and coherence witness, equips the observable
fiber with the geometric induced topology, and proves that its endpoint-fixed
homotopy quotient is homeomorphic to the standard based-loop quotient.  It
then constructs both the final pair quotient and the ordinary pair of
quotients, proves the canonical map is a continuous bijection but not a
quotient map under Fabel's input, and proves final-operation continuity versus
ordinary-operation discontinuity.  Second, the generic transfer connects
those concrete facts to the scoped presentation.  Fabel's non-quotient and
discontinuity facts remain explicit hypotheses; the Lean artifact proves only
their formal consequences.

## Palomar package

The focused project uses a dedicated Lean package rather than importing the
parent repository wholesale.  Its submission surface is:

```text
TopologicalComputationalPaths/
├── Challenge.lean
├── Solution.lean
├── comparator.json
├── formalization.yaml
├── lakefile.toml
├── lake-manifest.json
├── lean-toolchain
├── LICENSE
├── README.md
└── ComputationalPaths/
    └── Path/Topology/...
```

`Challenge.lean` is deliberately statement-oriented and self-contained.  The
Palomar challenge sandbox cannot import project-specific source, so it
duplicates the small statement-facing definition layer from Lean core and
Mathlib alone.  This lets the compared statement name the actual
endpoint-varying computational-path quotient rather than hide the result
behind a generic quotient interface.  Its publication-facing certificate is
the exact final-versus-ordinary topology comparison: continuous bijectivity,
raw quotient-map equivalence, a homeomorphism criterion, induced-topology
agreement, ordinary-composition continuity and its contrapositive obstruction,
plus compact--Hausdorff and discrete sufficient cases.  It also exposes the
concrete based-fiber carrier, its quotient homeomorphism, and the two pair
topologies in the Hawaiian-earring application.  The genuine circle and torus
fields are full additive-classification certificates, requiring identity and
composition additivity together with explicit standard representatives and
inverse laws.  `Solution.lean` repeats the same statement-side declaration and
fills it from the pinned, checked comparison construction.

The underlying result has three spaces: raw composable representatives, their
quotient final domain, and the ordinary composable-pair domain.  The selected
certificate compares the latter two exactly and isolates the missing
topological condition needed to transfer composition from the final domain to
the ordinary pullback.  It does not assert that the ordinary pullback is always
the correct domain.

The checked-in `comparator.json` selects
`TopologicalComputationalPaths.main_result`.  This theorem is the concrete
publication surface: its certificate exposes the canonical continuous
bijection, the raw quotient-map and homeomorphism criteria, equality of the
final and induced topologies, transfer of continuity to ordinary composition,
the discontinuity obstruction, and compact--Hausdorff and discrete sufficient
conditions.  It also selects and proves the concrete observable based-fiber
construction and its comparison with the standard based loop quotient; under
that homeomorphism, both Fabel obstructions transfer to the scoped ordinary
pair.  The selected result additionally requires full additive-classification
certificates for the genuine additive circle and product torus, supplied by
the universal-cover and coordinatewise proofs.  The external Fabel facts are
hypotheses, not silently reproved claims.
The automatic final-domain groupoid laws and the generic adapter remain
supporting material.

## Non-goals for the first submission

The initial package will not claim that:

- equal normal forms characterize scoped rewrite equality without a separately
  proved completeness hypothesis;
- the ordinary pullback is automatically the correct composable topology;
- an externally transferred Hawaiian-earring obstruction is a new proof of the
  underlying topology theorem; or
- a successful kernel check alone establishes mathematical novelty.

Those boundaries are essential for an honest publication record.

## Porting rule

Port one dependency layer at a time.  After each layer:

1. build the focused module with the target Lean toolchain;
2. check for unfinished proofs and custom axioms;
3. compare the extracted declarations with the parent source; and
4. preserve a small source-lineage note for any changed theorem statement.

The parent worktree's unrelated files and temporary directories are outside
the scope of this repository and must remain untouched.
