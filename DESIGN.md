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

## Follow-up package

The follow-up has its own non-destructive Comparator and metadata surface.  It
does not present the classical identity `π₁(Tⁿ) ≅ ℤⁿ` as a new result.  Its
publication-facing center is the arbitrary-space quotient-topological
fundamental-group theory in
`ComputationalPaths/Path/Topology/QuotientFundamentalGroup.lean`:

- continuous maps induce continuous homomorphisms, coherently with identity
  and composition;
- homeomorphisms and paths between basepoints induce homeomorphisms of the
  quotient fundamental groups, with path reversal giving the inverse
  continuous multiplicative equivalence;
- binary products are preserved under the exact product-quotient hypothesis;
- inversion and both one-variable translations are continuous;
- translation homeomorphisms make the quotient homogeneous;
- discreteness is equivalent to openness of the null-homotopy class; and
- in the discrete case, the projection is open, its square is quotient, and
  multiplication is jointly continuous.

The all-finite-dimensional torus theorem is the concrete positive family.  It
proves the null-class hypothesis by explicit winding and supplies standard
representatives, completeness, additivity, and a continuous integer-lattice
classifier.  The classifier is additionally multiplicative for the actual
quotient fundamental-group operation (via `Multiplicative`), and transports
commutativity to every basepoint.  This architecture gives a direct positive
counterpart to the accepted package's failure of the product-quotient
condition without erasing the crucial distinction between separate and joint
continuity.  The generic transport layer also proves that an abelian target
quotient makes basepoint transport independent of the chosen path, even in the
absence of a homotopy between paths.  More precisely, it isolates centrality
of the relative loop as the exact necessary-and-sufficient condition; the finite-torus
classifier uses the abelian corollary to be canonical at each basepoint.
The identity, composition, and reversal laws therefore exhibit basepoint
transport as a genuine groupoid action on quotient fundamental groups.
The finite-torus classifier is also natural under every coordinate-selection
map between finite products: mapping a loop and then winding is exactly the
corresponding reindexing of its integer lattice vector, including after
quotienting.
The chosen standard representatives and the quotient decoder satisfy the same
reindexing equation, so both sides of the classification are functorial.
The coordinate maps also satisfy explicit identity and composition laws, so
the classifier's naturality is presented as a coherent contravariant action.
The continuous multiplicative lattice classifier satisfies the same
reindexing equation for maps between different dimensions, tying the actual
quotient group operation to that contravariant action.
At arbitrary torus basepoints, the path-based classifier satisfies the same
naturality square after the chosen basepoint path is mapped to the target;
this makes the transport-compatible statement explicit rather than limiting
it to the all-zero quotient.
The abelian-target path-independence theorem then removes that auxiliary path,
so the canonical classifier at each basepoint is natural as well.

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
