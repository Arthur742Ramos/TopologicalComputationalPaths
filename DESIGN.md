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
- the compact-Hausdorff and discrete sufficient conditions.

These declarations form one coherent result: the canonical final-domain
semantics is unconditional, while ordinary multiplication requires a precise
topological compatibility hypothesis.

## Supporting layers

The following layers are candidates for the first full release, but are not
part of the minimal extraction until they compile against the focused core:

- presentation functoriality;
- the geometric comparison/completeness criterion;
- the realized fundamental-groupoid bridge;
- the circle normal-form certificate and product-torus winding certificate;
- the finite trace-sensitive separation certificate; and
- the Hawaiian-earring obstruction transfer.

The last item depends on an externally supplied non-quotient theorem.  If it
is retained, the repository will label it as a transfer theorem and will not
present the external topological input as newly formalized here.

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
behind a generic quotient interface.  Its publication-facing certificate
lists the continuity and groupoid-law fields, rewrite soundness, and explicit
trace-level `Path`/`ScopedRwEq` witnesses.  `Solution.lean` repeats the same
statement-side declaration and fills it from the pinned, checked groupoid
construction.  The generic quotient/comparison adapter remains supporting
material for the exact final-versus-ordinary topology distinction.

The underlying result has three spaces: raw composable representatives, their
quotient final domain, and the ordinary composable-pair domain.  The concrete
certificate proves unconditional continuity on the final domain and all
topological groupoid laws there; the supporting comparison layer records the
exact quotient-map/inverse-continuity/topology equivalences for the ordinary
operation.  It does not assert that the ordinary pullback is always the
correct domain.

The checked-in `comparator.json` selects
`TopologicalComputationalPaths.main_result`.  This theorem is the concrete
publication surface: its certificate exposes source, target, identity,
inverse, and final-domain composition continuity; the unit, inverse, and
associativity laws; rewrite soundness; and explicit computational `Path` and
`ScopedRwEq` witnesses.  The generic quotient/comparison interface and its adapter
remain available in the solution source as supporting material.

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
