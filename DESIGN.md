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

## Palomar shape

The focused project will use a dedicated Lean package rather than importing
the parent repository wholesale.  Its submission surface is intended to be:

```text
TopologicalComputationalPaths/
├── Challenge.lean
├── Solution.lean
├── Comparator.lean
├── comparator.json
├── formalization.yaml
├── lakefile.lean
├── lake-manifest.json
├── lean-toolchain
├── README.md
└── TopologicalComputationalPaths/
    ├── Core.lean
    ├── Quotient.lean
    ├── Groupoid.lean
    └── Examples.lean
```

`Challenge.lean` will be deliberately small and statement-oriented.  The
definitions used by the statement will live in the focused package's
statement-safe core, not in the parent monorepo.  `Solution.lean` will import
that same statement surface and provide the checked proof through the pinned
focused sources.  This keeps the Challenge/Solution type identity transparent
to the independent comparator.

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
