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

The follow-up has its own non-destructive Comparator and metadata surface.  The
selected declaration is
`TopologicalComputationalPathsFollowup.topological_smith_exactness` in
`FollowupSolution.lean`.  Its proposition is the nonemptiness of a certificate
with exactly nine top-level fields, grouped into three layers: (1) the
monodromy-stabilizer criterion, (2) the sharp product-quotient obstruction,
and (3) the rectangular winding-lattice cokernel short exact sequence and
first-isomorphism quotient, followed by (4) a coherent all-dimensional
winding-classifier family, including
representative winding, quotient multiplication, naturality for induced
integer-matrix maps, exact image/injectivity/surjectivity transfer, and their
quotient-level composition, plus a Smith-coordinate divisibility criterion for
membership in the image of every actual induced quotient map (including
rank-deficient zero factors), (5) canonical
integer-matrix composition, (6) rectangular lattice-cokernel
finiteness plus finite-cokernel cardinality and torsion-prime-support laws
with coprime-exponent composition, (7) an arbitrary-rank Smith classification
with explicit `ZMod 0` free factors, (8) the nonsingular square determinant
index, and (9) a finite prime-power refinement.  The lattice-cokernel fields are about the integer winding
lattice; the fourth field explicitly ties that lattice to induced maps of
finite-torus loop quotients and gives determinant criteria for square maps.
The declaration does not assert the repository's separate topological torus-map
short-exact wrappers, indexed-product preservation, or centrality.
The selected trace bridge is concrete rather than an abstract raw
presentation.  It fixes
`WindingWord n := List (Fin n -> Int)`, with `List.length` as its derived
trace cost, append as concatenation, and a recursive realization by the actual
standard torus loops.  The selected certificate proves representation by the
winding standard loop, homotopy iff winding equality, exact zero/one
minimality, matrix naturality and composition, normal-form sum/unit laws, and
the Smith-coordinate realizability iff for an induced quotient map.  Thus
the cost observable and its normal forms come from an independently typed
syntax and its topological semantics; no arbitrary raw family or
certificate-supplied cost is selected.

The surrounding winding classifier identifies actual quotient loop classes
with the integer lattice and transports image, kernel, injectivity,
surjectivity, rectangular exactness, and Smith finite/free consequences
through every rectangular matrix map.  Finite cardinality and torsion-prime
claims retain explicit finite-cokernel hypotheses, while zero Smith factors
remain free `ZMod 0` directions.  This is a compatibility/methods
contribution, not a first-discovery claim for classical winding, quotient
fundamental groups, or Smith normal form.  Provenance is bounded to the
exact checked synthesis and priority is recorded as unknown.

Everything below this boundary is repository-wide supporting inventory, not an
additional Comparator claim unless its declaration or selected nested field is
one of the two explicit topological criteria or nine top-level certificate fields listed above.  It is retained to document the reusable theory from which the
selected certificate was assembled.  In particular, it does not turn the
supporting quotient-topology or torus-map exactness results into selected
claims:

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
The integer-lattice reindexings are packaged as continuous additive
morphisms, and their identity and composition laws are checked at that
topological-algebra level.
When the index map is an equivalence, the coordinate-selection map is also
packaged as a torus homeomorphism and the lattice map as a continuous additive
equivalence, with the same coherence laws.
The arbitrary-basepoint classifier squares are additionally expressed through
the continuous additive reindexing map, for both path-based and canonical
classifiers.
The finite-index map is analyzed exactly as well: surjectivity gives
injectivity at the torus, lattice, and quotient levels, and injectivity gives
surjectivity via an explicit zero extension.
For an arbitrary index map, the image is characterized as precisely the
fiber-constant winding vectors, with an equivalent statement for quotient
loop classes.
The converse injectivity/surjectivity criteria are formalized as iff
theorems simultaneously for raw torus maps, lattice reindexings, and typed
quotient maps.  At the quotient level, coordinate selection is additionally
an additive contravariant functor, continuous for the discrete quotient
topologies, and its kernel is exactly the classes whose winding vanishes on
the index-map image.  Before choosing a classifier, the same
coordinate-selection maps at arbitrary basepoints are packaged as continuous
multiplicative homomorphisms between the corresponding quotient fundamental
groups, with explicit identity/composition coherence and a direct
classifier-naturality theorem.  The canonical classifiers also transport the
exact fiber-constant image, injectivity/surjectivity converse, and
vanishing-on-the-image kernel descriptions to arbitrary basepoints.
The homomorphism also commutes with explicit basepoint transport, so this
extension has a naturality square before any classifier is selected.

The latest finite-torus extension lifts this functorial interface from
coordinate selections to arbitrary integer matrices.  Rows act by integer
linear combinations of target coordinates, while winding vectors transform
by the matching row-by-column action.  The source checks continuity,
matrix identity/composition, standard-loop and quotient naturality, exact
image/kernel/injectivity/surjectivity transfer, and continuous additive
functoriality of both the lattice action and quotient maps for the discrete
quotient groups.  Each matrix map is also exposed as a continuous
multiplicative homomorphism at arbitrary torus basepoints, with a proved
basepoint-transport square.  The path-based classifier naturality theorem
keeps the endpoint cast from the mapped zero basepoint explicit.  Abelian
target path independence also yields the corresponding canonical classifier
square without a path parameter.  The canonical classifier transfers the
matrix image, kernel, injectivity, and surjectivity iff criteria to the
arbitrary-basepoint quotient homomorphisms, with each criterion exposed as an
explicit iff theorem.  Their typed contravariant composition and identity laws
are also proved pointwise, using explicit endpoint casts induced by
`matrixMap_comp` and `matrixMap_id`.
Given an explicit two-sided integer-matrix inverse, the interface upgrades to
a continuous additive lattice equivalence, a torus homeomorphism, and a
quotient homeomorphism and continuous additive equivalence for the transported
loop groups.  At every arbitrary torus basepoint, the same inverse yields a
continuous multiplicative equivalence of quotient fundamental groups, with
explicit injectivity and surjectivity corollaries.
For square matrices, the adjugate-based nonsingular inverse is canonical when
the determinant is a unit.  The lattice and canonical quotient actions then
have exact determinant criteria—nonzero determinant for injectivity and unit
determinant for surjectivity—and the canonical inverse drives all of the same
equivalence layers at arbitrary basepoints.
When the determinant is merely nonzero, the integer lattice cokernel is still
finite, with cardinality exactly `Int.natAbs (Matrix.det A)`; this quantitative
Smith-normal-form certificate complements the binary determinant criteria.
The canonical quotient homomorphism has the identical image index and finite
cokernel cardinality, making the determinant count visible on the actual
topological loop-class quotient as well.
For composable non-singular square matrices, these exact indices are proved
multiplicative under the matrix-composition law on both sides of the winding
classifier.
The composition law also has a canonical structural witness: `B` induces an
additive map from the cokernel of `A` into that of `B ∘ A`, and the map is
injective whenever the determinant of `B` is nonzero.  The same embedding is
proved directly for the topological quotient cokernels.  The projection from
the cokernel of `B ∘ A` onto the cokernel of `B` is surjective with precisely
that image as its kernel, yielding a short exact sequence on both sides.
The corresponding quotient of the composition cokernel by that kernel is
then identified with the second cokernel by an explicit first-isomorphism
additive equivalence, including its action on quotient representatives.
The argument is factored through a reusable first-isomorphism package for
arbitrary composable additive homomorphisms.  Thus rectangular integer
matrices in any composable dimensions inherit the same short-exact sequence
under injectivity of the second matrix action, and the finite-torus quotient
maps receive the matching transported theorem.
The abstract map also has an exact injectivity criterion: its kernel vanishes
precisely when the preimage of the composite image equals the first image.
Injectivity of the second map is therefore a clear sufficient specialization,
not an implicit extra assumption.
The rectangular composite ranges are proved equal to the ranges of the
canonical `matrixCompose` actions on both the lattice and finite-torus sides;
the exact-sequence and iff interfaces are available in that canonical form.
The subgroup transport is lifted to an explicit additive equivalence between
each rectangular finite-torus cokernel and its integer-lattice cokernel, and
both the composite embedding and complementary projection are verified natural
under that equivalence.  The named square-matrix `matrixCompose` maps expose
the same two naturality laws directly at their canonical target types.  A
diagram-level rectangular certificate packages the two exact sequences and
both commuting squares in one reusable theorem.
The abstract map and projection have explicit quotient-representative
formulas, so downstream proofs do not need to unfold `QuotientAddGroup.map`.
The equivalence also gives cardinality and finiteness transport for individual
rectangular matrices and their explicit composites.  The selected ordinary
cardinality claims are made only after finite-cokernel hypotheses; in an
infinite case Mathlib's totalized `Nat.card` is zero and is not called an
ordinary cardinality.
The lattice interface additionally exposes the corresponding finite cyclic
invariant-factor decomposition supplied by Smith normal form.  The same
decomposition is transported through the winding equivalence to the canonical
quotient cokernel, giving an explicit structural classification of the
topological obstruction, and the transport is packaged as an explicit additive
equivalence.  The Smith-normal-form interface now accepts arbitrary-rank
rectangular maps: zero `ZMod 0` factors retain the free cokernel summand while
nonzero factors describe torsion.  Under full target rank it gives the finite
cyclic-factor decomposition and exact ordinary product cardinality on both the
lattice and finite-torus sides; lattice finiteness is equivalent to that
full-rank hypothesis.  The arbitrary-rank factors also give a direct criterion
on both sides: the cokernel is finite exactly when every Smith modulus is
nonzero, equivalently when no `ZMod 0` free coordinate remains.
For square nonsingular maps, the invariant-factor product is also proved equal
to the determinant index `Int.natAbs (Matrix.det A)` on both sides.
The same Smith-product formula is proved without a rank assumption as a
totalized `Nat.card` identity; in the infinite cases a surviving `ZMod 0`
factor forces the value zero, which is not an ordinary finite-cardinality
claim.
The same arbitrary-rank presentation identifies the additive exponent with the
lcm of the Smith-factor moduli, so a zero factor forces exponent zero and
records the free summand both elementwise and globally.
Equivalently, exponent zero is characterized by a zero Smith factor; for both
rectangular lattice and finite-torus cokernels this is exactly failure of full
target rank.
More generally, a proposed global annihilator `k` is divisible by the Smith
exponent exactly when every Smith-factor modulus divides `k`; a zero factor
forces `k = 0`.
The sharp trivial-cokernel boundary is the exponent-one case: the exponent is
one exactly when every Smith factor has unit absolute value.
Consequently, a rectangular lattice or finite-torus matrix action is
surjective exactly when all of its Smith factors have unit absolute value.
For square matrices, the adjugate annihilator also gives the global bound
`AddMonoid.exponent (cokernel) ∣ Int.natAbs (Matrix.det A)`, including the
singular case.
The finite/infinite dichotomy is equivalently global: each Smith cokernel is
finite exactly when its exponent is nonzero, so the zero-exponent criterion is
also a complete finiteness test.
For any composable additive cokernel sequence, the composite cokernel
exponent divides the product of the two successive cokernel exponents,
without an injectivity hypothesis.  Rectangular lattice and finite-torus
matrix sequences inherit this bound, including their canonical
`matrixCompose` presentations.
When the second map is injective and both successive cokernels are finite,
exactness gives the ordinary multiplicative cardinality identity: the
composite cokernel has the product cardinality of the two successive
cokernels, in both rectangular presentations.  The supporting development's
unconditional `Nat.card` equation is only a totalized zero identity outside
that finite regime.
The finite-torus identity is additionally exposed from injectivity of the
underlying lattice action through the quotient-injectivity equivalence.
The same hypothesis gives a finiteness equivalence: the composite cokernel is
finite exactly when both successive cokernels are finite, including canonical
`matrixCompose` presentations.
The exact sequence also exposes the complementary lower bound: under
injectivity, the lcm of the successive exponents divides the composite
exponent.  Together with the product bound, this yields a sharp lcm-to-product
interval before any coprimality specialization.
When the successive cokernel exponents are coprime, injectivity of the second
map upgrades the exponent divisibility bound to equality with their product.
This sharpening is factored through the abstract exact sequence and exposed
for rectangular lattice and finite-torus maps, including explicit and
canonical `matrixCompose` notation and the lattice-action injectivity route
on the finite-torus side.
For square matrices, coprime determinant absolute values imply coprime
successive exponents by the adjugate bounds.  A nonzero determinant for the
second matrix therefore gives the exact exponent product directly on lattice
and finite-torus cokernels, including canonical `matrixCompose` forms.
In the finite-cokernel regime, the exponent bounds determine torsion-prime
support exactly: for every prime `p`, divisibility of the composite exponent
is equivalent to divisibility of at least one successive exponent.  This
finite prime-support theorem is exposed for rectangular lattice and
finite-torus maps, including canonical `matrixCompose` notation, and
interfaces directly with the prime-power Smith factors.  If a `ZMod 0` free
factor is present, the totalized exponent is zero and divisibility by every
prime is not interpreted as torsion-prime support.
For square maps, a nonzero determinant of the second factor supplies
injectivity, so determinant-based lattice and finite-torus corollaries expose
the same support law without requiring users to construct an injectivity proof.
At the Smith level, after finiteness is established, support is exact
factor-by-factor: a prime divides the cokernel exponent exactly when it
divides one of the Smith-factor moduli, for both lattice and finite-torus
presentations.  A zero modulus is instead the explicitly recorded free case
with exponent-zero totalization.
The corresponding image-membership interface is exact as well: after the
Smith basis change, each coordinate is divisible by its factor, with zero
factors imposing the complementary-coordinate equations.
The transported topological equivalence also has an explicit quotient-
representative formula, avoiding any hidden unfolding of the quotient map.
Whenever the Smith factors are nonzero, the cyclic factors are further
decomposed by the Chinese remainder theorem into an explicit product of
prime-power cyclic groups on both the lattice and finite-torus cokernels,
with a representative formula for the refined decoder.
The refined finite product has an exact ordinary-cardinality bridge: the
prime-power orders multiply back to each Smith modulus, and both finite
cokernel cardinalities equal the resulting full double product.
The additive exponent is also identified exactly with the least common
multiple of the Smith moduli, exposing the precise finite-cokernel annihilator.
When every Smith factor is nonzero, this lcm identity refines pointwise: the
`Nat.factorization` valuation at each prime is the supremum of the
factor valuations, and the theorem is transported to both rectangular lattice
and finite-torus matrix cokernels.  The nonzero hypothesis explicitly marks
the finite-torsion regime; a zero factor is a `ZMod 0` free component.
For an individual class in that regime, the factorization of its additive
order is likewise the pointwise supremum of the factorization profiles of its
decoded Smith-coordinate orders, with the same transport on both sides.
The same Smith coordinates give an elementwise annihilation criterion: a
multiple of a lattice or finite-torus cokernel class vanishes exactly when
each transformed coordinate is divisible by the corresponding multiple of
its Smith factor, including the zero-factor equations.
The corresponding class-order theorem identifies the additive order of each
class with the lcm of the additive orders of its decoded Smith coordinates;
a nonzero free `ZMod 0` coordinate records infinite order.
When all factors are nonzero, each coordinate order is refined to the explicit
Smith-modulus/gcd formula on the transformed integer coordinate.
For arbitrary rank, the free part is detected elementwise: a class has
infinite order exactly when a zero Smith factor carries a nonzero transformed
coordinate, with the criterion transported to lattice and finite-torus
matrix representatives.
Equivalently, a natural number is a multiple of a class's additive order
exactly when it satisfies the corresponding coordinatewise Smith divisibility
equations, including the free-coordinate vanishing constraints.
Conversely, a class has finite additive order exactly when every zero Smith
factor carries a zero transformed coordinate; this torsion test is exposed on
the lattice and finite-torus matrix representatives as well.
The square-matrix layer also has an adjugate annihilator certificate: applying
the matrix to `adjugate A` gives `det A` times the input, so determinant
multiples lie in the image and the determinant kills every lattice and
finite-torus cokernel class, without assuming `det A ≠ 0`.

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
