# Follow-up: computational-path winding normal forms and topological Smith obstructions

## Selected result

The Comparator selects
`TopologicalComputationalPathsFollowup.topological_smith_exactness` in
`FollowupSolution.lean`.  This declaration is a nonempty
`TopologicalSmithExactnessCertificate` with six top-level fields, including
the explicitly stated Smith-image and computational-path bridge fields:

1. `winding_matrix_compatibility` packages an all-dimensional family of
   complete winding classifiers: each classifier agrees with winding on loop
   representatives, identifies quotient concatenation with lattice addition
   through a continuous equivalence into the multiplicative lattice model,
   and commutes with the induced integer-matrix map on quotient loop groups.
   Its image, injectivity, and surjectivity are characterized by the same
   lattice action, including the square determinant criteria; matrix-map
   composition is also stated at the quotient level.  In addition, the image
   of an actual induced quotient map is decided by finite Smith-coordinate
   divisibility tests, including the zero-factor equations in rank-deficient
   cases.  The selected nested computational-path bridge instantiates the
   classifier on universal open geometric computational paths, preserves
   trace-length algebra under identity/composition/reversal, supplies a
   representative for every continuous loop, identifies the traced homotopy
   quotient with the ordinary loop quotient, and applies the same Smith test to
   the representative's geometric loop class.  Its winding and quotient
   classifier are tied to the selected outer certificate by explicit
   compatibility equalities.  It also supplies a canonical one-step
   representative for every winding vector, proves its trace length is one and
   its winding is the chosen vector, and proves every traced path is homotopic
   to the representative selected by its winding.  More strongly, a traced
   target path is homotopic to the matrix image of some source loop exactly
   when its Smith coordinates satisfy the displayed divisibility equations;
   this is a path-level realizability criterion, not only a quotient-image
   restatement;
2. `matrix_composition` proves that the canonical additive matrix action
   composes according to the stated row-by-column `matrixCompose` law;
3. `rectangular_composition_profile` proves the rectangular lattice-cokernel
   composition laws.  After both successive cokernels are known to be finite,
   their ordinary cardinalities multiply and their torsion-prime support is
   the union of the successive supports; the field also proves finiteness
   equivalence and coprime successive exponent multiplication;
4. `smith_cokernel_profile` gives an arbitrary-rank additive Smith
   equivalence, explicitly retaining `ZMod 0` free factors, and proves the
   finite/full-rank criterion and exponent-as-lcm formula.  Its prime-support
   law is stated only for finite cokernels;
5. `determinant_index` specializes the winding-lattice cokernel to
   nonsingular square matrices and identifies its cardinality with the
   absolute determinant;
6. `prime_power_torsion_profile` refines every full-rank rectangular lattice
   cokernel into explicit prime-power cyclic factors and proves the resulting
   product cardinality formula.

This is the selected mathematical contribution: a quantified topology-to-
arithmetic certificate for quotient fundamental groups of finite tori and
their winding-lattice cokernels.  It links the actual winding invariant and
quotient multiplication to the integer lattice, proves naturality and exact
image/injectivity/surjectivity transfer for induced matrix maps between
finite-torus loop quotients, and gives a concrete Smith-coordinate obstruction
for realizing any prescribed quotient loop class.  The computational-path
bridge makes this comparison apply to a concrete traced carrier and its
geometric realization, rather than to an arbitrary homeomorphism; its homotopy
quotient is explicitly equivalent to the ordinary loop quotient.  The bridge
also gives a winding-indexed one-step normal form for traced paths, with a
proved homotopy-completeness theorem, and a complete path-level Smith
realizability decision theorem: for every matrix and traced target, a source
loop with homotopic mapped geometric path exists iff the target winding
coordinates satisfy the Smith divisibility test.  This connects the arithmetic
obstruction to an explicit computational-path workflow.
The bridge also certifies the exact trace-complexity normal form: a homotopy
class has a zero-step representative exactly when its winding is zero, while
every nonzero-winding class has a one-step representative and every homotopic
representative has at least one step.  Matrix maps carry canonical standard
traces to canonical standard traces for the matrix-action winding up to
endpoint-fixed homotopy, and successive matrix maps agree up to homotopy on
every traced path.  These are path-level normalization and functoriality laws,
not properties of an unstructured quotient presentation.  The canonical
normal form is also compatible with the path-group operation: the standard
trace for `z + w` is homotopic to the concatenation of the standard traces for
`z` and `w`, and the zero-winding standard trace is homotopic to the traced
identity.  The remaining
fields give an arbitrary-rank free/torsion and prime-power description of every
lattice cokernel, with the determinant index as a square specialization.
The certificate reports ordinary cardinality and torsion-prime support only
in its explicitly finite-cokernel regimes.  A zero Smith modulus is a free
`ZMod 0` factor; the supporting totalized identities then use `Nat.card = 0`
and exponent `0`, rather than assigning ordinary finite-cardinality or
torsion-support meanings to those values.  Winding, quotient fundamental
groups, and Smith normal form are classical ingredients.  The selected
six-top-level-field bundle is recorded as an `original-proof` source with
relationship `other`; the local Lean files are its implementation, not a
circular mathematical source.  The exact priority of this synthesis is
unknown, so no first-presentation or priority claim is made.
The detailed general
quotient-topology and finite-torus developments below are supporting inventory,
not additional Comparator claims unless listed in `main_results.selected_fields`.

## Repository-wide supporting inventory (not selected by Comparator)

33. finite-torus winding is natural under every coordinate-selection map; the
    induced quotient classifier reindexes the integer lattice vector.
34. the coordinate-selection maps satisfy identity and composition coherence,
    giving the reindexing construction an explicit contravariant functorial
    interface.
35. the continuous multiplicative lattice classifier is natural under those
    coordinate selections, including maps between different finite dimensions.
36. reversing a basepoint path gives the inverse continuous multiplicative
    transport, completing the groupoid-action coherence.
37. the path-based finite-torus lattice classifiers are natural under
    coordinate selection at arbitrary basepoints, after transporting the
    chosen basepoint path.
38. the canonical arbitrary-basepoint classifiers satisfy the same naturality
    square without exposing any path choice.
39. lattice reindexing is packaged as a continuous additive morphism, with
    explicit identity and composition coherence and a classifier corollary.
40. finite index equivalences upgrade coordinate selection to a torus
    homeomorphism and lattice reindexing to a continuous additive equivalence,
    with matching identity and composition coherence.
41. the arbitrary-basepoint classifier naturality squares are also stated
    directly through the continuous additive reindexing morphism.
42. surjective and injective index maps have the corresponding exact
    injectivity and surjectivity behavior on torus coordinates, integer
    lattices, and typed quotient loop classes.
43. for an arbitrary index map, the image is characterized exactly by winding
    vectors constant on its fibers, both on the lattice and on quotient loop
    classes.
44. the torus, lattice, and typed quotient reindexing maps satisfy exact
    converse criteria: injectivity is equivalent to surjectivity of the index
    map, and surjectivity is equivalent to injectivity of the index map.
45. typed quotient coordinate maps compose contravariantly, preserve the
    transported additive loop-class structure continuously for the discrete
    quotient topologies, and package as additive homomorphisms with identity
    and composition coherence.
46. the kernel of every lattice or typed quotient coordinate map is described
    exactly by vanishing on the image of its index map.
47. at arbitrary torus basepoints, coordinate selection is exposed as a
    continuous multiplicative homomorphism of quotient fundamental groups,
    with explicit identity/composition coherence and classifier naturality;
    the exact image, converse, and kernel descriptions are transported there
    as well.
48. arbitrary integer matrices define continuous maps between finite tori,
    extending coordinate selections to genuine linear combinations of
    coordinates;
49. the matrix action on winding vectors is an additive homomorphism and
    satisfies explicit composition and identity laws;
50. standard winding representatives and the typed quotient classifier are
    natural for these matrix maps, including the endpoint cast back to the
    canonical target basepoint; and
51. the matrix quotient maps have exact image, kernel, injectivity, and
    surjectivity transfer criteria, and package as a continuous additive
    contravariant functor on the discrete quotient groups.
52. each matrix map also induces a continuous multiplicative homomorphism on
    quotient fundamental groups at arbitrary torus basepoints;
53. those arbitrary-basepoint homomorphisms commute with explicit path
    transport, before choosing any winding classifier; and
54. the path-based winding classifier is natural for matrix maps as well,
    with the mapped path's endpoint cast made explicit and checked.
55. by abelian-target path independence, the canonical arbitrary-basepoint
    winding classifier satisfies the same matrix naturality square without a
    path parameter.
56. at arbitrary basepoints, the image of a matrix-induced quotient map is
    exactly the image of the corresponding integer-lattice action;
57. its kernel is exactly the matrix-action kernel under the transported
    winding classifier; and
58. injectivity and surjectivity of the arbitrary-basepoint quotient map are
    each equivalent to the corresponding property of the matrix action.
59. the arbitrary-basepoint matrix image, kernel, injectivity, and
    surjectivity statements are all explicit iff theorems, not merely
    consequences left to reconstruction.
60. arbitrary-basepoint matrix homomorphisms satisfy contravariant composition
    and identity laws, with the endpoint equalities induced by map coherence
    transported explicitly at the quotient level.
61. an explicit two-sided integer-matrix inverse is upgraded to a continuous
    additive equivalence of winding lattices, a torus homeomorphism, and both
    a quotient homeomorphism and a continuous additive equivalence of the
    transported loop-class groups.
62. at every arbitrary torus basepoint, the same inverse produces a continuous
    multiplicative equivalence of quotient fundamental groups, with explicit
    injectivity and surjectivity corollaries for the induced homomorphism.
63. for square integer matrices, injectivity of the winding-lattice and
    canonical quotient actions is equivalent to a nonzero determinant, while
    surjectivity is equivalent to a unit determinant; the canonical
    nonsingular inverse of a unimodular matrix therefore supplies the lattice
    equivalence, torus homeomorphism, quotient homeomorphism, continuous
    additive quotient equivalence, and arbitrary-basepoint multiplicative
    quotient equivalence without an extra inverse witness.
64. for every non-singular square integer matrix, the winding-lattice cokernel
    is finite with exactly `Int.natAbs (Matrix.det A)` elements; the same
    theorem exposes finiteness explicitly, giving a quantitative index
    certificate rather than only injectivity or surjectivity criteria.
65. at the canonical finite-torus basepoint, the image of the induced quotient
    homomorphism has index and cokernel cardinality exactly
    `Int.natAbs (Matrix.det A)`, with an explicit finiteness theorem for that
    quotient; this identifies the topological quotient obstruction with the
    algebraic determinant index.
66. the non-singular lattice cokernel also has an explicit Smith-normal-form
    presentation as a finite product of cyclic `ZMod` groups, together with a
    proved full-rank image theorem supporting that decomposition.
67. the canonical finite-torus quotient cokernel itself is transported through
    the winding equivalence to the same explicit Smith-normal-form product of
    cyclic `ZMod` groups, so the determinant obstruction is classified at the
    topological quotient level rather than only counted.
68. for composable non-singular square matrices, the exact determinant index is
    multiplicative under matrix composition on both the winding lattice and the
    canonical quotient cokernel.
69. the canonical quotient cokernel is equipped with its transported abelian
    group structure and an explicit additive equivalence to that Smith product,
    making the topological classification structure-preserving rather than a
    bare type equivalence.
70. composition by a non-singular matrix `B` induces a canonical additive map
    from the cokernel of `A` to the cokernel of `B ∘ A`; this map is proved
    injective on both the winding lattice and the topological loop-class
    quotient, giving a structural explanation for the determinant-index law.
71. the canonical projection from the cokernel of `B ∘ A` onto the cokernel of
    `B` is surjective, with kernel exactly the image of the preceding map; with
    `det B ≠ 0`, these results package into an explicit short exact sequence on
    both sides of the winding classifier.
72. the first-isomorphism quotient of that short exact sequence is made
    explicit: quotienting the composition cokernel by the projection kernel is
    additively equivalent to the cokernel of `B`, and the equivalence is proved
    to send each quotient representative to its canonical projection image.
73. the cokernel argument is factored through a reusable first-isomorphism
    package for arbitrary composable additive homomorphisms.  Consequently,
    rectangular integer matrices in any composable dimensions satisfy the
    same short-exact sequence whenever the second matrix action is injective,
    and the corresponding finite-torus quotient maps satisfy the transported
    theorem as well.
74. the abstract induced cokernel map has an exact injectivity criterion:
    injectivity is equivalent to the preimage of the composite image being
    exactly the first image.  Injectivity of the second map is recorded as a
    transparent sufficient specialization of this criterion.
75. the rectangular composite-image subgroups are identified with the ranges
    of the canonical row-by-column `matrixCompose` maps on both the winding
    lattice and finite-torus quotient.  The short-exact sequence and exact
    injectivity-criterion APIs are exposed in this canonical notation as well.
76. the winding equivalence lifts the image-subgroup calculation to an
    explicit additive equivalence between every rectangular finite-torus
    cokernel and its integer-lattice cokernel, with a representative formula.
    The composite cokernel embedding and complementary projection are proved
    natural under these equivalences, giving a checked commutative diagram
    between both exact sequences.
77. the canonical square-matrix `matrixCompose` cokernel embedding and
    projection maps are each proved natural under the winding equivalence as
    named theorems, so clients can use the diagram without subgroup rewrites.
78. a single rectangular diagram certificate packages topological and lattice
    short exactness together with both winding-commuting squares under the
    shared injectivity hypothesis.
79. the reusable abstract cokernel map and projection expose simp-normalized
    formulas on quotient representatives, eliminating repeated quotient-map
    unfolding in downstream calculations.
80. `Nat.card` and `Finite` are transported across the rectangular winding
    equivalence for both individual matrices and explicit composites.  The
    selected ordinary-cardinality conclusions require finite cokernels; the
    supporting transport retains Mathlib's totalized `Nat.card = 0` value for
    infinite cases.
81. Smith normal form is generalized from nonsingular square matrices to any
    rectangular map with full target rank, and its finite cyclic product is
    transported to the corresponding finite-torus cokernel.
82. the lattice finite-cokernel criterion is proved exactly as equality of
    target finranks, making the full-rank hypothesis in the rectangular Smith
    decomposition sharp.
83. the Smith decomposition is extended to arbitrary-rank rectangular maps:
    complementary coordinates contribute explicit `ZMod 0` free factors,
    while the embedded Smith coordinates contribute the cyclic torsion
    factors; the finite full-rank specialization also exposes the exact
    ordinary product of Smith moduli as the lattice and torus cokernel
    cardinality.
84. the lattice and finite-torus cokernels receive an exact arbitrary-rank
    finiteness criterion in terms of the Smith data: they are finite exactly
    when every modulus is nonzero (equivalently, no `ZMod 0` free factor
    remains), which is itself equivalent to full target rank.
85. in the square nonsingular specialization, the product of Smith moduli is
    proved equal to the determinant index `Int.natAbs (Matrix.det A)` for both
    the lattice and canonical finite-torus cokernels.
86. the supporting arbitrary-rank Smith presentation also gives a totalized
    `Nat.card` product formula without a finiteness hypothesis: an infinite
    cokernel is represented by a `ZMod 0` factor and both sides evaluate to
    zero.  The selected account does not call that zero an ordinary finite
    cardinality.
87. Smith coordinates now provide exact image-membership tests for arbitrary
    rectangular matrices on both sides of the winding equivalence: every
    transformed coordinate is divisible by its factor, while zero factors
    impose the expected vanishing equations.
88. the topological arbitrary-rank Smith equivalence exposes a proved
    quotient-representative formula, so its coordinate decoder can be applied
    directly to loop classes.
89. the square-matrix adjugate identity is exposed at the winding-action
    level, giving an explicit preimage of every determinant multiple.
90. consequently, the determinant annihilates every lattice and finite-torus
    cokernel class, including singular matrices; this annihilator certificate
    is independent of the nonzero-determinant cardinality theorem.
91. whenever all Smith factors are nonzero, each cyclic `ZMod` factor is
    refined by the Chinese remainder theorem into an explicit indexed product
    of prime-power cyclic factors.
92. this prime-power refinement is packaged for arbitrary-rank lattice and
    finite-torus cokernels, with a proved representative formula for the
    refined decoder.
93. the refined finite prime-power product has an exact ordinary-cardinality
    bridge: the prime-power orders multiply back to each nonzero Smith modulus.
94. consequently, both finite lattice and finite-torus cokernel cardinalities
    are identified with the full double product of the prime-power orders.
95. the additive exponent of the finite Smith cokernel is proved exactly equal
    to the least common multiple of its Smith moduli.
96. the same exponent identity is transported through the refined lattice and
    finite-torus equivalences, identifying the precise finite-cokernel
    annihilator rather than only its cardinality.
97. a multiple of any arbitrary-rank Smith cokernel class vanishes exactly
    when every transformed coordinate is divisible by the corresponding
    multiple of its Smith factor, including zero-factor equations.
98. this elementwise annihilation criterion is transported to both lattice and
    finite-torus matrix cokernel representatives.
99. the additive order of each arbitrary-rank Smith cokernel class is exactly
    the lcm of the additive orders of its decoded Smith coordinates.
100. a nonzero `ZMod 0` coordinate is thereby detected as an infinite-order
     free component, while finite coordinates contribute their cyclic orders.
101. when all Smith factors are nonzero, each coordinate order has the explicit
     modulus-divided-by-gcd formula on the transformed integer coordinate.
102. the lattice and finite-torus class-order formulas expose this arithmetic
     refinement through their concrete matrix representatives.
103. an arbitrary-rank Smith cokernel class has infinite additive order exactly
     when a zero Smith factor carries a nonzero transformed coordinate.
104. this free-coordinate criterion is transported to both lattice and
    finite-torus matrix representatives.
105. a natural number is a multiple of an arbitrary-rank Smith cokernel
     class's additive order exactly when the corresponding coordinatewise
     Smith divisibility equations hold.
106. this order-divisibility criterion is transported to lattice and
    finite-torus matrix representatives, including zero-factor constraints.
107. a Smith cokernel class has finite additive order exactly when every zero
     Smith factor carries a zero transformed coordinate.
108. this finite-order torsion criterion is transported to lattice and
    finite-torus matrix representatives.
109. the exponent of an arbitrary-rank Smith cokernel is exactly the lcm of
     its Smith-factor moduli, with a zero factor forcing exponent zero.
110. this exponent identity is transported to arbitrary rectangular lattice
     and finite-torus matrix cokernels.
111. exponent zero is characterized exactly by the presence of a zero Smith
     factor in the arbitrary-rank decomposition.
112. for rectangular lattice and finite-torus matrix cokernels, exponent zero
     is equivalent to failure of full target rank.
113. a proposed global annihilator is divisible by the arbitrary-rank Smith
     exponent exactly when every Smith-factor modulus divides it.
114. a surviving zero Smith factor forces that global annihilator to be zero,
     matching the exponent-zero/rank-deficiency criterion.
115. the sharp trivial-cokernel boundary is the exponent-one case: it occurs
     exactly when every Smith factor has unit absolute value.
116. this unit-factor criterion is exposed on the generic, lattice, and
     finite-torus Smith presentations.
117. a rectangular lattice action is surjective exactly when all of its Smith
     factors have unit absolute value.
118. the same unit-factor surjectivity criterion is transported to the
     canonical finite-torus quotient action.
119. for every square matrix, the determinant annihilator sharpens to a global
     exponent bound: the cokernel exponent divides `Int.natAbs (Matrix.det A)`.
120. this determinant bound is proved on both winding-lattice and finite-torus
     cokernels and remains valid when the determinant is zero.
121. each arbitrary-rank Smith cokernel is finite exactly when its additive
     exponent is nonzero, making the exponent-zero criterion a complete
     finite/infinite test.
122. this finiteness/exponent equivalence is transported to lattice and
     finite-torus matrix cokernels.
123. for any composable additive homomorphisms, the composite cokernel
     exponent divides the product of the first and second cokernel exponents.
124. this product bound is proved without an injectivity hypothesis, using the
     projection kernel/image exactness.
125. rectangular matrix cokernel sequences inherit the product bound in
     lattice and finite-torus forms, including explicit homomorphism
     composition.
126. the same bound is exposed in canonical `matrixCompose` notation on both
     sides.
127. when the second map is injective and both successive cokernels are finite,
     the exact cokernel sequence multiplies ordinary cardinalities: the
     composite cardinality is the product of the successive cardinalities.
128. this finite-cardinality product is transported to rectangular lattice and
     finite-torus matrix cokernels under the same injectivity hypothesis; the
     supporting totalized equation outside the finite regime is only zero
     arithmetic.
129. the cardinality identity is also exposed for canonical `matrixCompose`
     ranges on both sides.
130. the finite-torus cardinality product is also available from injectivity
     of the underlying lattice action, using the quotient-injectivity iff.
131. under the same injectivity hypothesis, the composite cokernel is finite
     exactly when both successive cokernels are finite.
132. this finiteness equivalence is transported to rectangular lattice and
     finite-torus forms, including canonical `matrixCompose` presentations.
133. if the two successive cokernel exponents are coprime and the second map
     is injective, the composite cokernel exponent is exactly their product.
134. this coprime sharpening is proved abstractly from the injective cokernel
     embedding, surjective projection, and the product divisibility bound.
135. rectangular lattice and finite-torus matrix cokernels inherit the exact
     coprime exponent product, including explicit and canonical
     `matrixCompose` forms.
136. on the finite-torus side, the same equality is exposed from injectivity of
     the underlying lattice action through the quotient-injectivity iff.
137. under injectivity of the second map, each successive cokernel exponent
     divides the composite exponent, so their least common multiple divides it.
138. this lcm lower bound and the product upper bound give a sharp interval for
     the exponent of every additive cokernel short exact sequence.
139. rectangular lattice and finite-torus matrix wrappers expose the lcm bound
     in explicit composition and canonical `matrixCompose` notation.
140. the finite-torus lcm theorem is also available from injectivity of the
     underlying lattice action, via the quotient-injectivity equivalence.
141. for square matrices, the adjugate determinant bounds show that coprime
     determinant absolute values imply coprime successive cokernel exponents.
142. when the second determinant is nonzero, this arithmetic certificate
     yields the exact exponent product on the lattice and finite-torus sides.
143. the determinant-coprime equality is exposed in explicit composition and
     canonical `matrixCompose` notation for both cokernel presentations.
144. for every prime `p`, when both successive cokernels are finite, the
     composite exponent is divisible by `p` exactly when at least one
     successive exponent is.
145. rectangular lattice and finite-torus matrix cokernels inherit this finite
     torsion-prime-support law in explicit and canonical `matrixCompose` forms.
146. the finite law interfaces directly with the prime-power Smith
     decomposition, identifying the exact torsion-prime support of each
     composite obstruction; a free `ZMod 0` factor instead has totalized
     exponent zero.
147. for square matrices, a nonzero determinant of the second factor supplies
     the required injectivity automatically.
148. the prime-support law is therefore exposed directly from determinant
     hypotheses on both lattice and finite-torus cokernel presentations.
149. these determinant corollaries retain canonical `matrixCompose` forms,
     so arithmetic clients need no intermediate quotient-injectivity proof.
150. after the Smith cokernel is finite, its presentation sharpens torsion
     prime support to a factor-level test: `p` divides the exponent exactly
     when it divides one Smith modulus.
151. this finite criterion is transported to rectangular lattice and
     finite-torus matrix cokernels.
152. zero Smith moduli are explicitly treated as free `ZMod 0` coordinates;
     their exponent-zero totalization is not called torsion-prime support.
153. when every Smith modulus is nonzero, the exponent's `Nat.factorization`
     valuation at each prime is the `Finset.sup` of the Smith-factor valuations.
154. this full p-adic profile is transported to rectangular lattice and
     finite-torus matrix cokernels, refining the Boolean prime-support test.
155. the nonzero-modulus hypothesis is explicit, separating finite torsion
     profiles from zero-factor free components represented by `ZMod 0`.
156. for every finite-order Smith cokernel class, the factorization of its
     additive order is the pointwise supremum of its decoded coordinate-order
     factorizations.
157. the class-level p-adic profile is transported to rectangular lattice and
     finite-torus matrix cokernels through the existing Smith equivalences.
158. this elementwise refinement records prime-power class orders, not merely
     global exponent support, while retaining the explicit nonzero-factor gate.

The distinction between separate and joint continuity is essential.  The
formalization now proves that discontinuous quotient multiplication forces
the product of loop quotient maps not to be a quotient map, and instantiates
this theorem with the accepted package's Fabel-style Hawaiian-earring facts.
Thus the product hypothesis is formally sharp at the existing negative
example.  It also proves that the quotient topology itself is a genuine
topological-group topology exactly when multiplication is jointly continuous.

Covering maps additionally induce injective continuous homomorphisms on these
quotient fundamental groups, by unique path lifting.

## Selected finite-torus application

For every `n`, coordinate winding classifies genuine compact-open loops in
the finite torus `(Fin n → AddCircle 1)` modulo endpoint-fixed homotopy:

```text
Path.Homotopic.Quotient (0 : (Fin n → AddCircle 1)) 0 ≃ₜ (Fin n → ℤ).
```

The formalization constructs coordinatewise standard loops, proves winding
completeness and additivity, proves the null class open, and applies the
general criterion.  It obtains a discrete quotient, an open quotient map, a
quotient square, and continuous concatenation and reversal.  Internally,
winding is also packaged as a continuous additive equivalence, and the
transported addition is proved equal to path-class concatenation.  The same
classifier is exposed as a continuous multiplicative equivalence to
`Multiplicative (Fin n → ℤ)`, so the actual quotient multiplication is
identified with lattice addition and is commutative.  Dimensions `0` and `1`
are included uniformly.  The new basepoint-transport theorem
upgrades the discrete quotient statement from the zero basepoint to every
point of the torus; the resulting theorem packages semilocal simple
connectivity at all points for every finite torus.  The same transport gives a
continuous multiplicative equivalence (and hence commutativity) from every
based quotient to the same integer lattice, so the classification is
independent of the chosen basepoint as a topological and algebraic statement,
not only as a discreteness statement.  More strongly, the classifier may be
defined along any explicit path from the canonical basepoint, and all such
path-based classifiers are equal by the abelian-target transport theorem.

The selected finite-torus surface is exactly the six top-level certificate fields
and the explicitly named nested fields listed in `formalization.yaml`.  The
fixed-dimensional winding/basepoint
classifier and the broader topological matrix/Smith wrappers below are
repository support; they are not additional Comparator claims unless their
exact field names are listed in `main_results.selected_fields`.

### Repository-wide finite-torus extensions (not selected by Comparator)

The following inventory is intentionally broader than the headline selected
fields: it records useful repository declarations, while the Comparator
account is restricted to the exact field names in `main_results.selected_fields`.

The core classifier is also natural for every coordinate-selection map
`Fin m → Fin n`: the induced loop and quotient maps simply reindex the
integer winding vector (with the fixed-dimensional instance exposed in the
publication certificate).
The explicit standard-loop representatives and quotient decoder obey the same
reindexing equation.
The coordinate-selection maps themselves satisfy identity and composition
coherence, so this is an explicit contravariant functorial interface.
The multiplicative classifier obeys the same reindexing equation, even for
maps between different finite dimensions, so the actual quotient group model
is natural rather than only its underlying set-valued classifier.
The path-based classifiers satisfy the corresponding naturality square at
arbitrary torus basepoints: mapping a loop after transport along a chosen
basepoint path agrees with reindexing its transported lattice vector, and the
mapped path supplies the target transport.
Because the target quotient is abelian, the path choice can then be removed:
the canonical classifier defined by path-connectedness satisfies the same
naturality square at arbitrary basepoints.

The reindexing maps themselves are continuous additive morphisms for the
product topologies on the integer lattices, and their identity/composition
laws are proved at that continuous-morphism level as well.
For finite index equivalences, the coordinate maps are upgraded to
homeomorphisms and the lattice maps to continuous additive equivalences;
their identity and composition laws are proved in those stronger categories.
The path-based and canonical arbitrary-basepoint classifier squares are also
restated through the continuous additive reindexing map itself.
Finally, a surjective index map yields injective coordinate, lattice, and
quotient maps, while an injective index map yields surjective ones; the latter
is witnessed constructively by zero extension on missing coordinates.
More generally, the image of any coordinate-selection map is exactly the
fiber-constant part of the target winding lattice, and the same description
holds for the typed quotient map.
The converses are exact as well: the lattice and typed quotient maps are
injective exactly for surjective index maps and surjective exactly for
injective index maps.  At the quotient level, coordinate selection is a
contravariant additive functor: it preserves the transported zero and
addition and obeys identity/composition laws.  Its kernel consists precisely
of the classes whose winding vector vanishes on the coordinates hit by the
index map, matching the lattice kernel description; because the quotient
topologies are discrete, this additive functor is continuous as well.
At arbitrary torus basepoints, the same coordinate-selection operation is
also packaged before choosing a lattice classifier as a continuous
multiplicative homomorphism between the corresponding quotient fundamental
groups.  These maps obey the expected contravariant identity and composition
laws, and the canonical lattice-classifier square factors through the named
homomorphism directly.  The classifier equivalence also transports the exact
fiber-constant image criterion, injectivity/surjectivity converses, and
vanishing-on-the-image kernel criterion to these arbitrary-basepoint maps.
The homomorphism itself commutes with the explicit basepoint-change
equivalence, giving a naturality square before any classifier is chosen.

The finite-torus layer now also treats arbitrary integer matrices, not just
coordinate selections.  A matrix acts on a point of `(AddCircle 1)^n` by
integer linear combinations of coordinates, and its winding action is the
corresponding row-by-column integer matrix product.  The formalization checks
continuity of both the torus map and lattice action, matrix
identity/composition, standard-loop naturality, quotient classifier
naturality, and exact image/kernel/injectivity/surjectivity transfer.  The
resulting typed quotient maps are additive and continuous for the discrete
quotient topologies, with identity and composition coherence.
At arbitrary basepoints, the induced continuous multiplicative homomorphism
is natural for basepoint transport.  Along an explicit canonical-to-arbitrary
path, the winding classifier commutes with the matrix action; the endpoint
cast needed because a matrix preserves the zero basepoint propositionally is
part of the theorem rather than hidden in a definitional equality.
Path independence of the abelian target then removes the auxiliary path and
gives the same statement for the canonical classifier at every basepoint.
The same classifier transfers the exact matrix image and kernel descriptions,
as well as the injectivity and surjectivity iff criteria, from the integer
lattice action to the quotient homomorphism at every chosen basepoint.
These are stated as explicit iff theorems for image membership, the identity
fiber, injectivity, and surjectivity, so the arbitrary-basepoint interface
retains the same exactness guarantees as the canonical quotient map.
The arbitrary-basepoint homomorphisms also satisfy contravariant composition
and identity pointwise, with the endpoint equalities induced by
`matrixMap_comp` and `matrixMap_id` transported explicitly.
When a matrix is supplied with an explicit two-sided integer inverse, the same
coherence produces equivalences throughout: the lattice action is a continuous
additive equivalence, the torus map is a homeomorphism, and the canonical
quotient map is a homeomorphism and continuous additive equivalence for the
transported loop-class groups.
At every arbitrary torus basepoint, the same explicit inverse is also exposed
as a continuous multiplicative equivalence of quotient fundamental groups;
the induced homomorphism is therefore explicitly injective and surjective at
that basepoint.
For square matrices this inverse witness is canonical whenever the determinant
is a unit: the adjugate-based nonsingular inverse gives the two-sided equations
internally.  The lattice and quotient actions consequently have exact,
independent determinant criteria—nonzero determinant for injectivity and unit
determinant for surjectivity—at the canonical and every arbitrary basepoint.
Beyond these yes/no criteria, a nonzero determinant gives a finite lattice
cokernel whose cardinality is exactly `Int.natAbs (Matrix.det A)`.  Thus the
formalization records the full finite obstruction measured by the determinant,
including an explicit `Finite` instance for the cokernel.
The same count is transported through the canonical winding classifier: the
image of the induced quotient homomorphism has index and cokernel cardinality
`Int.natAbs (Matrix.det A)`, and the quotient is explicitly finite.
For composable non-singular square matrices, the determinant index is proved
multiplicative under matrix composition on both the lattice and canonical
quotient sides.
More structurally, composition by `B` induces a canonical additive map from
the cokernel of `A` into the cokernel of `B ∘ A`; when `det B ≠ 0`, the map is
proved injective on the winding lattice and on the topological loop-class
quotient.  The canonical projection from the cokernel of `B ∘ A` onto the
cokernel of `B` is surjective, and its kernel is exactly the image of that
embedding.  Thus the multiplicative index law is accompanied by an explicit
short exact sequence of finite abelian groups, not only a numerical identity.
The first-isomorphism theorem is also instantiated directly: after quotienting
the composition cokernel by the projection kernel, an explicit additive
equivalence identifies the result with the cokernel of `B`; its representative
formula is checked against the projection map itself.
This exactness mechanism is not restricted to square matrices: the source
also packages the additive first-isomorphism argument abstractly and applies
it to rectangular integer matrices of any composable dimensions, with
injectivity of the second action as the precise hypothesis.  The winding
equivalence transports the same statement to the finite-torus quotient loop
groups.
The abstract theorem also proves the converse criterion, identifying
injectivity with equality of the second map's preimage of the composite image
and the first image.
At the lattice level, the finite cokernel is further decomposed into the
finite cyclic invariant factors supplied by Smith normal form, rather than
only counted.  The canonical quotient cokernel is now transported through the
winding equivalence to that same explicit product of cyclic `ZMod` factors,
with an explicit additive equivalence preserving the finite abelian-group
operations.  This gives a structural topological classification of the
obstruction, not merely a cardinality or an unstructured equivalence.

## Literature and novelty boundary

The selected follow-up has a deliberately explicit mathematical boundary.
Hatcher and Norman are ingredient-only background for the classical winding
and Smith/invariant-factor material; they are not claimed as the origin of the
selected synthesis or as prior formalizations of it.  Brazas--Fabel and
Calcut--McCarthy provide the quotient-topological context, and the parent
computational-path manuscript provides the inherited setting; those entries
are recorded as `background`.  The selected `Topological Smith exactness,
image obstructions, and cokernel composition for finite-torus quotient maps`
entry is an `original-proof` source with relationship `other`: it records an
independently assembled proof artifact; the exact priority of this synthesis is
unknown, so no first-presentation or priority claim is made.  The local Lean
files are its implementation rather than a circular mathematical source.  The
`original-proof` label records the assembled proof artifact and its
trace-normalization method; it does not claim first presentation or priority
for the underlying winding, fundamental-group, or Smith results.

The selected theorem is intended for specialists who need a computable,
presentation-independent bridge from finite-torus quotient loop groups to
integer-lattice cokernels.  Its interest is the common topological object and
the reusable quantified interface: matrix composition supports rectangular
cokernel profiles, Smith factors expose free `ZMod 0` directions and finite
torsion, finite-cokernel prime support and coprime exponents give arithmetic
control, and the square nonsingular specialization recovers the determinant
index.  The finite/full-rank boundary and finite prime-power refinement are
stated uniformly for all dimensions and ranks; free cases retain explicit
zero-cardinality and zero-exponent conventions rather than ordinary finite
invariants.  Repository-wide centrality, product, torus-map short-exact,
first-isomorphism, CRT, and broader matrix developments remain useful
supporting material but are outside the selected Comparator surface.
The selected path theorem is the method-level part of that boundary: it gives
a canonical reduction of arbitrary traced representatives to a shortest
normal form, and the reduction is stable under the integer-matrix path action
and its composition.  This supplies a concrete semantics for trace complexity
and matrix transformations that is absent from the classical quotient and
lattice statements alone.  The selected `matrix_normal_form_minimal` field
adds an optimal image theorem: when the matrix-action winding is nonzero, the
mapped canonical trace has a one-step target representative, and every
homotopic target trace has at least one step.

The new follow-up proof closes the locally path-connected converse explicitly
at the compact-open level: a finite path subdivision, path-connected vertex
refinement, and finite homotopy ladder produce an open class around each loop.
It then transports quotient discreteness across the continuous quotient
equivalences induced by homotopy equivalences and basepoint paths, giving
homotopy invariance of semilocal simple connectivity in the stated locally
path-connected category.  The same multiplicative homeomorphisms transport
the boundary between separate and joint continuity, so the topological-group
failure is itself a homotopy-invariant quotient-topology phenomenon.  The
basepoint-change maps are also proved independent of the chosen path
representative whenever two paths are endpoint-fixed homotopic.
They satisfy the corresponding composition law for concatenated paths, so
the transport is coherent as well as homotopy-invariant.  Transport along a
constant path is separately identified with the identity equivalence, so the
coherence package has both its unit and composition laws explicitly.  Reversing
a path is also proved to give the inverse continuous multiplicative transport,
so these laws assemble into a genuine groupoid action.  Finally,
when the target quotient is abelian, the path-independence statement no longer
requires a homotopy between the paths; this is the mechanism that makes the
finite-torus lattice classifier canonical at each basepoint.
The formal proof actually characterizes equality by relative centrality, so
the abelian result is a corollary rather than the limit of the transport
argument.
Quotient functoriality is recorded at the path-composition level, and the
basepoint-change equivalences satisfy the resulting naturality square for
every continuous map.
The pointed homotopy-naturality law is also exposed: a homotopy between maps
relates their induced quotient maps by conjugation along the path traced at the
basepoint.
The same continuous multiplicative transport preserves the joint-continuity
boundary at any two basepoints connected by a path.
As a pointed specialization, when the homotopy is constant at the chosen
basepoint, the two induced based homomorphisms are equal after the canonical
endpoint cast.
For path-connected spaces, the basepoint result upgrades this to a global
criterion: the topological-group boundary may be checked at any one chosen
basepoint or simultaneously at all basepoints.
The same path-connected upgrade holds for discreteness, and the global
joint-continuity property is invariant under homotopy equivalences between
path-connected spaces.  In the locally path-connected setting, the
semilocal/discrete equivalence therefore reduces to a single chosen
basepoint.  The basepoint equivalence exposed by the certificate is
continuous and multiplicative, so these are algebraic-topological statements,
not only bare homeomorphism assertions.
The T1/closed-class boundary is transported by the same homotopy and path
equivalences.  Consequently, on path-connected spaces a single based quotient
detects the T1 status of every based quotient, and homotopy-equivalent
path-connected spaces have the same global T1 status.

The contribution is therefore a focused theorem package connecting actual
quotient fundamental groups to explicit integer-matrix invariants.  Kernel
checking is evidence that the selected statements are proved; the
research-interest claim rests on the rectangular topology--algebra
classification and its free/torsion/determinant boundary, not on proof size
alone.  Exact source relationships and the narrow originality claim are
recorded in `formalization-followup.yaml`.

## Verification surface

- `FollowupChallenge.lean` and `FollowupSolution.lean`;
- `ComputationalPaths/Path/Topology/QuotientFundamentalGroupFunctorial.lean`;
- `TopologicalComputationalPathsFollowup.topological_smith_exactness`;
- `comparator-followup.json`;
- `formalization-followup.yaml`;
- `scripts/check-followup.sh`; and
- `scripts/verify-comparator.sh comparator-followup.json`.

The challenge contains one deliberate statement-side `sorry`.  The solution
and substantive modules contain none.
