# Design contract: topological computational paths

Status: historical design baseline from the parent manuscript. The revised
claims and current Lean coverage are stated in `main.tex` and `ROADMAP.md`.

## 1. Working title and thesis

**Publication title.** *Topological Semantics for Scoped Computational Paths*

**Thesis.** A computational rewrite presentation with continuous geometric
realization has a canonical topological semantics. Its scoped rewrite quotient
is a groupoid whose multiplication is always continuous for the final topology
induced from composable representatives. It is an internal topological groupoid
for the ordinary pullback topology exactly when the explicitly proved
product-quotient comparison criterion holds. The ordinary-pullback upgrade is
not a standing assumption and is not needed for any headline result. Geometric
realization then induces a continuous comparison morphism to the
quotient-topologized fundamental groupoid, via an explicit realized arrow
carrier and its ambient fundamental-groupoid interpretation.

The mathematics, not the formalization, is the principal contribution. The
Lean development is an appendix-level verification and a reproducible artifact.
The strengthened result package includes a compact-Hausdorff positive
ordinary-pullback theorem, a discrete finite-presentation corollary, an
normal-form completeness criterion, a finite-generator circle
calculation, and the genuine product torus calculation.

## 2. Scope and non-goals

The paper studies computational paths as finite, explicitly rewritable traces
with a topological realization. It does not identify computational paths with
identity types, does not assume homotopy type theory, and does not treat a bare
equality proof carrying annotations as a presentation of arbitrary paths in a
space.

The central objects are:

1. raw computational traces;
2. classes modulo a scoped rewrite congruence;
3. classes modulo endpoint-fixed homotopy of geometric realizations; and
4. the classical quotient-topologized fundamental groupoid.

These four levels must never be conflated.

The paper will not claim that every quotient-topologized fundamental groupoid
is an internal topological groupoid with its ordinary pullback topology. It will
state the exact compatibility hypothesis whenever that stronger conclusion is
used.

The paper does contain a proved positive class: compact final composable
domains with Hausdorff ordinary composable domains, together with the discrete
finite-presentation corollary. The circle and torus examples use the
unconditional final-domain structure and do not infer discreteness from their
integer winding normal forms.

## 3. Continuous geometric rewrite presentations

Let \(I=[0,1]\), and give \(X^I\) the compact-open topology.

### Definition 3.1 (continuous geometric rewrite presentation)

A continuous geometric rewrite presentation \(\mathcal P\) over a topological
space \(X\) consists of:

- a topological space \(E\) of oriented primitive steps;
- continuous source and target maps \(s,t:E\to X\);
- a continuous realization map
  \[
  \rho:E\longrightarrow X^I
  \]
  such that \(\rho(e)(0)=s(e)\) and \(\rho(e)(1)=t(e)\);
- a family of directed rewrite generators \(r:p\Rightarrow q\) between
  parallel finite traces; and
- for every rewrite generator, an endpoint-fixed homotopy from the geometric
  realization of \(p\) to that of \(q\).

Let \(E^+\cong E\) be a positive copy and let \(E^-\) be a formal inverse
copy.  Write \(\widetilde E=E^+\sqcup E^-\), with endpoints interchanged and
realizations reversed on \(E^-\).  For \(n\geq 1\), let
\(W_n\subseteq\widetilde E^n\) be the composable-word subspace, and put
\(W_0=X\).  The topological trace carrier is
\[
\mathsf{Tr}_{\mathcal P}=\coprod_{n\geq 0} W_n,
\]
with the coproduct topology.  The length map is the coproduct index, and word
concatenation and reversal are the trace operations.  Their realizations use
the compact-open concatenation and reversal operations on \(X^I\).

Write \(\mathsf{Coh}_{\mathcal P}(p,\gamma)\) for the proposition that
\(\gamma\) is endpoint-fixed homotopic to the realization of \(p\).  The
coherent carrier is the set of pairs \((p,\gamma)\) satisfying the endpoint
conditions and \(\mathsf{Coh}_{\mathcal P}(p,\gamma)\); the homotopy witness is
not a field of the carrier.  Equip it with the initial topology for
\[
\kappa(p,\gamma)=(s(p),t(p),\ell(p),|p|,\gamma)
\in X\times X\times\mathbb N\times X^I\times X^I,
\]
where \(\mathbb N\) is discrete.  This is the coarsest topology making the
observable code continuous, and it is the topology used throughout the paper.

The identity insertion, reversal, and coherent concatenation maps are
continuous for this topology.  After applying \(\kappa\), their observable
codes are respectively \((a,a,0,c_a,c_a)\),
\((t(p),s(p),\ell(p),|p|^{-1},\gamma^{-1})\), and
\((s(p),t(q),\ell(p)+\ell(q),|p|\star|q|,\gamma\star\delta)\).  These are
continuous by the compact-open path operations and addition on the discrete
length coordinate.

The presentation includes the structural reductions needed for a groupoid:
unit insertion/removal, adjacent cancellation of \(e e^{-1}\) and
\(e^{-1}e\), and closure of generators under reversal and whiskering by
composable traces. Any additional computational reductions are explicitly
listed as part of \(\mathcal P\).

### Definition 3.2 (scoped rewrite equality)

For parallel traces \(p,q\), write
\[
p\simeq_{\mathcal P}q
\]
for the least equivalence congruence containing the rewrite generators and the
structural reductions of \(\mathcal P\). “Scoped” means that only generators
declared by \(\mathcal P\), together with the stated congruence rules, may be
used. No ambient equality-normalization principle is imported.

### Definition 3.3 (rewrite groupoid)

The rewrite groupoid \(G_{\mathrm{rw}}(\mathcal P)\) has object space \(X\)
and arrows
\[
G_{\mathrm{rw}}(\mathcal P)_1=T/\simeq_{\mathcal P}
\]
with the quotient topology, where (T) is the coherent carrier above and the
relation compares endpoints and scoped trace equality. Source and target
descend from trace endpoints; composition and inversion are induced by
concatenation and reversal.

### Definition 3.4 (geometric kernel and realized subgroupoid)

For parallel traces, define
\[
p\simeq_{\mathrm{geo}}q
\quad\Longleftrightarrow\quad
|p|\simeq_{\partial I}|q|,
\]
where the right side is endpoint-fixed path homotopy. The realized subgroupoid
\(\Pi_1^{\mathcal P}(X)\) is the subgroupoid of \(\Pi_1(X)\) whose arrows have
a representative in the image of trace realization. Its arrow topology is the
subspace topology inherited from the quotient-topologized fundamental
groupoid \(\Pi_1^{q}(X)\).

## 4. The two composable-pair topologies

Let \(G=G_{\mathrm{rw}}(\mathcal P)_1\), and let \(q:T\to G\)
be the quotient map.

### Definition 4.1 (ordinary composable-pair space)

The ordinary composable-pair space is the pullback
\[
C_{\mathrm{ord}}=G\times_XG
\]
with the subspace topology inherited from \(G\times G\).

### Definition 4.2 (final composable-pair space)

Let
\[
T_{\mathcal P}^{(2)}=T_{\mathcal P}\times_XT_{\mathcal P}.
\]
The final composable-pair space \(C_{\mathrm{fin}}\) is the quotient of
\(T_{\mathcal P}^{(2)}\) by componentwise scoped equivalence.  Write
\[
q_{\mathrm{fin}}^{(2)}:T_{\mathcal P}^{(2)}\longrightarrow C_{\mathrm{fin}}
\]
for its quotient map.  The ordinary composable-pair space \(C_{\mathrm{ord}}\)
has the same underlying set, with the subspace topology, and the raw map is
\[
q_{\mathrm{ord}}^{(2)}:T_{\mathcal P}^{(2)}\longrightarrow C_{\mathrm{ord}},
\qquad (p,r)\longmapsto([p],[r]).
\]
There is a unique bijection
\[
j:C_{\mathrm{fin}}\longrightarrow C_{\mathrm{ord}}
\]
such that
\[
q_{\mathrm{ord}}^{(2)}=j\circ q_{\mathrm{fin}}^{(2)}.
\]

The map \(j\) is always continuous. The reverse identity need not be
continuous.

The distinction can occur in a finite example.  Let (X=\{*\}), let the
primitive generator space be the discrete two-point set \(\{e,f\}\), let both
generators realize the constant path at \(*\), and impose no scoped rewrite
between the reduced one-letter traces (e) and (f).  The trace-sensitive
code separates these words, while the observable code records the same
endpoints, length, realization, and representative for both.  The identity
from the trace-sensitive two-point topology to the observable indiscrete
topology is continuous, but the reverse identity is not.  The scoped quotient
therefore retains two distinct, topologically inseparable classes.  This is a
finite separation certificate, not an appeal to a pathological infinite
space; the Lean declaration `TraceSensitiveSeparation.certificate` checks the
word separation, observable collapse, and the two continuity assertions.

### Definition 4.3 (product-quotient compatibility)

The presentation satisfies product-quotient compatibility when
\(q_{\mathrm{ord}}^{(2)}\) is a quotient map.  Since
\(q_{\mathrm{ord}}^{(2)}=j\circ q_{\mathrm{fin}}^{(2)}\) and
\(q_{\mathrm{fin}}^{(2)}\) is quotient, this is equivalent to \(j\) being
quotient, to continuity of \(j^{-1}\), and to \(j\) being a homeomorphism.
Equivalently, \(C_{\mathrm{ord}}\) and \(C_{\mathrm{fin}}\) have the same topology.

## 5. The theorem package

The paper is viable only if the following statements are proved at the stated
strength. The numbering below is provisional.

### Theorem A (realization soundness)

For every continuous geometric rewrite presentation \(\mathcal P\),
\[
p\simeq_{\mathcal P}q\quad\Longrightarrow\quad
p\simeq_{\mathrm{geo}}q.
\]
Consequently, geometric realization descends to a well-defined quotient-level
groupoid morphism
\[
R_{\mathcal P}:G_{\mathrm{rw}}(\mathcal P)
\longrightarrow \Pi_1^{\mathcal P}(X)
\hookrightarrow \Pi_1(X).
\]
The map on total arrow spaces is continuous for the quotient topologies. The
comparison also preserves source, target, identities, reversal, and the
canonical composable-quotient multiplication.

### Theorem B (canonical quotient-compatible groupoid)

For every \(\mathcal P\), source, target, identity, and inversion on
\(G_{\mathrm{rw}}(\mathcal P)\) are continuous, and multiplication
\[
m:C_{\mathrm{fin}}\longrightarrow G
\]
is continuous. Thus the rewrite quotient carries a canonical
**final-domain topological groupoid structure**.

This terminology is deliberately weaker than “topological groupoid,” because
the domain of multiplication need not have the ordinary pullback topology.

Formally, a **final-domain topological groupoid** consists of a topological
groupoid arrow space together with a specified topology on the set of
composable pairs, not necessarily the ordinary pullback topology, for which
multiplication is continuous and the groupoid laws hold.  The specified final
domain is part of the structure.

### Theorem C (ordinary/final topology comparison)

The following are equivalent (and each is equivalent to product-quotient
compatibility):

1. \(q_{\mathrm{ord}}^{(2)}:T_{\mathcal P}^{(2)}\to C_{\mathrm{ord}}\) is a
   quotient map;
2. \(j:C_{\mathrm{fin}}\to C_{\mathrm{ord}}\) is a quotient map;
3. \(j^{-1}:C_{\mathrm{ord}}\to C_{\mathrm{fin}}\) is continuous; and
4. \(j\) is a homeomorphism, equivalently the ordinary and final
   composable-pair topologies coincide.

The theorem is an exact classification of the ordinary-pullback upgrade. The
unconditional groupoid result in this paper is the final-domain result of
Theorem B; no example or headline theorem takes product-quotient compatibility
as an unproved premise. When the equivalent condition is established for a
separate presentation, the ordinary multiplication is recovered as a theorem.
The paper will not claim that the criterion is necessary for continuity of the
particular multiplication map.

The artifact also records the completed open-map sufficient criterion
(`scopedProductCompatibility_of_open_pair_map`) as a secondary diagnostic
theorem. It is not a pending assumption for the final-domain result.

### Theorem D (functoriality)

A morphism \(F:\mathcal P\to\mathcal Q\) consists of a continuous map on
objects, a continuous map on primitive steps preserving endpoints, inversion,
and realization, and an assignment carrying each generating rewrite of
\(\mathcal P\) to a rewrite derivation in \(\mathcal Q\). Every such morphism
induces a continuous functor
\[
G_{\mathrm{rw}}(F):G_{\mathrm{rw}}(\mathcal P)
\longrightarrow G_{\mathrm{rw}}(\mathcal Q),
\]
preserving identities and composition. These assignments are functorial in
identity morphisms and composition. This is a functor for the unconditional
final-domain groupoid structures; ordinary-pullback terminology is not needed
for the functoriality theorem.

### Theorem E (comparison and completeness)

The comparison morphism \(R_{\mathcal P}\) has the following properties:

- it is faithful exactly when
  \(p\simeq_{\mathrm{geo}}q\Rightarrow p\simeq_{\mathcal P}q\);
- it is full onto \(\Pi_1^{\mathcal P}(X)\) by definition;
- it is essentially surjective because both groupoids have object space \(X\);
  and
- it is an isomorphism of abstract groupoids exactly when the rewrite
  congruence is geometrically complete.

The proved topological comparison is the quotient-topology comparison on total
arrow spaces:
\[
R_{\mathcal P}:G_{\mathrm{rw}}(\mathcal P)
\cong \Pi_1^{\mathcal P}(X)
\]
is a homeomorphism on arrows whenever the rewrite congruence is geometrically
complete. No ordinary-pullback upgrade is included in this theorem.

### Theorem F (universal geometric presentation)

For the universal presentation, the projection from the coherent carrier to
the chosen representative path is a quotient map.  A continuous section sends
\(\gamma\in X^I\) to the one-letter universal trace carrying \(\gamma\), so
the quotient of coherent paths by endpoint-fixed homotopy is homeomorphic to
the standard quotient-topologized fundamental-groupoid arrow space.

There is a universal presentation \(\mathcal U_X\) whose primitive steps are
continuous paths in \(X\), whose rewrite generators include endpoint-fixed
homotopies, and whose scoped rewrite congruence is exactly endpoint-fixed path
homotopy. For this presentation, the comparison map
\[
G_{\mathrm{rw}}(\mathcal U_X)\longrightarrow\Pi_1^q(X)
\]
is an isomorphism of abstract groupoids and a homeomorphism on total arrow
spaces.

This theorem is the topological completion result: the classical fundamental
groupoid is recovered as the universal geometric completion of computational
rewrite traces. Its multiplication is understood through the unconditional
final-domain construction; no ordinary-pullback assumption is part of the
completion claim.

The based-loop form is obtained fiberwise: for fixed endpoints (a,b), the
coherent carrier is given its own subspace topology and its scoped quotient is
given its own quotient topology.  The restricted universal projection is
quotient by its one-letter continuous section.  Thus the fiberwise statement
does not rely on the generally invalid inference that restricting a global
quotient map to a fiber preserves quotientness.

### Theorem E' (normal forms)

An explicit normalizer into proof-irrelevant normal-form codes, together with
(i) a scoped derivation from every raw path to the chosen representative of
its code and (ii) separation of geometrically equal paths by equal codes,
proves geometric completeness. There is no separate equality-witness clause:
equal codes have equal chosen representatives, and scoped reflexivity closes
the proof. The finite-generator circle and torus word reductions instantiate
both clauses.

### Theorem G (positive ordinary-pullback class)

If the final composable domain is compact and the ordinary composable domain is
Hausdorff, the continuous identity from final to ordinary pairs is a
homeomorphism. Consequently the raw ordinary-pair map is a quotient map and
ordinary multiplication is continuous. Finite discrete presentations form an
explicit corollary class.

### Theorem H (circle and torus applications)

The actual additive circle is presented from one oriented generator and inverse
cancellation; its normal forms are derived integer powers and its based loop
quotient is \(\mathbb Z\), with a bijective homeomorphism to the scoped based
fiber. The actual torus is presented from two coordinate generators, inverse
cancellation, and the commuting square; its based loop quotient is
\(\mathbb Z^2\), again with a bijective homeomorphism to the scoped based
fiber. Both completeness proofs use the corresponding covering-space winding
invariants. The Lean artifact records the finite-generator presentation data,
the completed circle normal-form certificate, the sound torus commuting square,
and the genuine product-torus certificate. The minimal
cancellation/commutation derivations remain mathematical presentation-level
proofs.

## 6. Terminology contract

The manuscript must obey the following vocabulary.

- **Raw trace** means an element of \(T_{\mathcal P}\).
- **Rewrite class** means a class modulo \(\simeq_{\mathcal P}\).
- **Geometric class** means a class modulo endpoint-fixed homotopy of realized
  traces.
- **Fundamental-groupoid class** means an arrow of \(\Pi_1(X)\).
- **Final-domain topological groupoid** names the unconditional construction of
  Theorem B.
- **Topological groupoid** without qualification is reserved for multiplication
  continuous from the ordinary pullback topology.
- **Groupoid isomorphism**, **continuous groupoid morphism**, and **topological
  groupoid equivalence** are not interchangeable.
- **Computational path** may be used generically only when the relevant level
  is already fixed; otherwise “trace” or “rewrite class” is required.

## 7. Originality boundary

The companion Seifert--van Kampen manuscript is an unpublished arXiv
preprint. It already contains a related final-domain construction and an
ordinary-pullback discussion for a geometric path quotient. Those results are
prior project material, not the standalone paper’s complete novelty claim.

The standalone paper must add a coherent result unavailable from that
construction alone:

1. a genuinely scoped computational rewrite presentation;
2. realization soundness for its rewrite generators and congruence;
3. the rewrite quotient and its universal semantic comparison;
4. functoriality of presentation morphisms at quotient level;
5. an exact comparison of the ordinary and final composable-pair topologies,
   with useful sufficient hypotheses for their agreement;
6. a topological comparison or completion theorem, not merely a set-level
   equivalence; and
7. a worked circle example with an explicit quotient topology, continuous
   inclusion into the scoped arrow space, and a proved integer winding normal
   form; and
8. a genuine product-torus application with a two-coordinate winding
   classification.

The novelty is architectural rather than a claim to have invented quotient
topologies or recomputed the classical fundamental groups.  The standalone
contribution integrates scoped syntax, coherent representatives, the
trace-sensitive/observable topology comparison, the final/ordinary
composable-pair distinction, and the soundness/completeness interface into one
reusable semantic construction.  The circle and torus calculations validate
that interface; they are applications, not the novelty boundary itself.

The relationship to the unpublished Seifert--van Kampen preprint is stated
transparently, and the standalone paper does not duplicate its principal
theorem as if it were new.

## 8. Formalization boundary

The main mathematical sections will be written independently of Lean names and
implementation architecture. The appendix and artifact may provide:

- a theorem-to-declaration map;
- the exact Lean and library versions;
- build and audit commands;
- the assumptions used by each theorem;
- a statement that the checked development introduces no custom axioms and no
  unfinished proofs; and
- the immutable source snapshot for the artifact: tag
  `topological-paper-v12` in the public repository
  `https://github.com/Arthur742Ramos/ComputationalPathsLean`, archived under
  the permanent Zenodo concept DOI `10.5281/zenodo.21817207`.

Implementation-specific certificate records, source-file names, and phase
labels do not belong in theorem statements or the mathematical narrative.

### Checked declaration map

The Lean artifact checks the dependency chain as follows.

| Mathematical layer | Checked declarations |
| --- | --- |
| Presentation and soundness | `ScopedGeometricRewritePresentation`, `ScopedRwEq`, `ScopedRwEq.sound` |
| Weighted realization bridge | `WeightedSlotReparam`, `balancedSlotReparam`, `weightedConcatenationInvariant`, `weightedConcatenationInvariant_balanced` |
| Rewrite quotient | `scopedEquivalent`, `scopedClassTopologicalSpace`, `scopedSrc`, `scopedTgt`, `scopedSymm` |
| Final and ordinary composable domains | `ScopedComposableClass`, `ScopedComposablePair`, `scopedCompositionFromComposable`, `ScopedStrongComposablePair`, `scopedCompositionOnStrong`, `scopedPairToOrdinary`, `scopedOrdinaryToFinal`, `scopedOrdinaryPairMap` |
| Groupoid laws and topology comparison | `TopologicalWeakCompPathCertificate`, `topologicalWeakCompPathCertificate`, `TotalOpenGeometricCompPath.continuous_totalRefl`, `TotalOpenGeometricCompPath.continuous_totalTrans`, `TotalOpenGeometricCompPath.continuous_totalSymm`, `scopedFinalTopologicalGroupoidCertificate`, `scopedProductCompatibility_iff_four_way`, `scopedFinalOrdinaryHomeomorph`, `scopedProductCompatibility_of_open_pair_map`, `scopedProductCompatibility_of_compact_final_t2`, `scopedProductCompatibility_of_discrete_arrow_and_final_domain` |
| Trace-sensitive topology and finite separation | `TraceSensitiveTopologicalCompPath`, `continuous_fullTraceRealization`, `continuous_traceSensitive_to_observable`, `TraceSensitiveSeparation.oneLetter_e_ne_f`, `TraceSensitiveSeparation.observableCode_e_eq_f`, `TraceSensitiveSeparation.not_continuous_observable_to_trace`, `TraceSensitiveSeparation.certificate` |
| Geometric comparison and completeness | `toGeometricClass`, `toGeometricComposableClass`, `toGeometricStrongPair`, `toGeometricClass_composition_on_strong`, `GeometricCompleteness`, `ScopedGeometricNormalFormCertificate`, `geometricCompleteness_of_normalForm`, `toGeometricClass_injective_iff_geometricCompleteness`, `comparisonHomeomorph_of_complete`, `comparisonCompletenessCertificate`, `ComparisonFunctorCertificate` |
| Hawaiian-earring obstruction transfer | `QuotientObstructionTransfer`, `QuotientObstructionTransfer.external_isQuotientMap_of_source_isQuotientMap`, `QuotientObstructionTransfer.not_isQuotientMap_quotientMap`, `MultiplicationComparison`, `MultiplicationComparison.not_source_continuous_of_not_external_continuous`, `ScopedGeometricRewrite.not_productQuotientCompatibility_of_transfer`, `ScopedGeometricRewrite.not_final_topology_agreement_of_transfer` |
| Realized fundamental-groupoid bridge | `RealizedFundamentalArrow`, `realizedFundamentalArrowHomeomorph`, `PresentedRealizedFundamentalArrow`, `realizedFundamentalGroupoidArrow`, `RealizedFundamentalGroupoidCertificate`, `presentedRealizedFundamentalArrow_identity_mem`, `presentedRealizedFundamentalArrow_reversal_mem`, `presentedRealizedFundamentalArrow_composition_mem`, `universalRealizedFundamentalArrowHomeomorph` |
| Presentation functoriality | `PresentationMap`, `mapClass`, `ScopedPresentationFunctorCertificate`, `scopedPresentationFunctorCertificate_of_compatibility`, `PresentationFunctorIdentityCertificate`, `PresentationFunctorCompositionCertificate` |
| Finite-generator presentation data | `FiniteCircleTorusPresentation.circleStepSystem`, `FiniteCircleTorusPresentation.circleFinitePresentation`, `FiniteCircleTorusPresentation.circleCompletionEquivInt`, `FiniteCircleTorusPresentation.torusStepSystem`, `FiniteCircleTorusPresentation.torusFinitePresentation`, `FiniteCircleTorusPresentation.torusCompletionEquivIntProd`, `FiniteCircleTorusPresentation.torusFiniteCommutingSquare` |
| Completed circle instance | `circleLoopStepSystem`, `circleLoopRule`, `circleLoopRule_sound`, `circleTrace_normalizes`, `circleLoopPresentation`, `circleBasedNormalFormCertificate`, `circleFinalTopologicalGroupoidCertificate`, `circleLoopEquivInt` |
| Actual topological torus | `TopologicalTorus.standardLoop`, `TopologicalTorus.winding`, `TopologicalTorus.standardLoop_homotopic`, `TopologicalTorus.standardLoop_homotopic_sequentialLoop`, `TopologicalTorus.equivIntProd`, `TopologicalTorus.certificate` |

The root import hub includes the topological modules, and the complete
repository build checks them together. The implementation uses no custom
axiom declarations and no unfinished proofs. Each module also contains
an explicit computational `Path` or `RwEq` witness, so the topology layer is
not disconnected from the repository's path calculus.

## 9. Go/no-go gates

The following gates characterize a complete manuscript.

### Mathematical gates

- The scoped relation is nondegenerate: parallel traces are not all identified.
- The finite two-generator separation certificate demonstrates that the
  trace-sensitive-to-observable comparison need not be a homeomorphism.
- Realization soundness is proved by induction over the scoped congruence.
- Quotient multiplication is proved continuous on \(C_{\mathrm{fin}}\).
- The ordinary/final topology comparison is proved as an exact classification;
  the paper's certified groupoid structure uses the final domain
  unconditionally.
- The comparison is a continuous groupoid morphism, not just a function on
  classes.
- At least one result upgrades an abstract equivalence to a homeomorphism.
- Compact-Hausdorff compatibility and the discrete finite-presentation
  corollary are proved as a positive ordinary-pullback class.
- The normal-form criterion is proved; finite-generator trace-code and
  commuting-square certificates are checked, while the minimal circle and
  torus reductions are presented mathematically.
- The circle and genuine torus examples include covering-space winding
  classifications and explicit nondegeneracy/completeness witnesses.

### Expository gates

- The introduction gives a theorem-level novelty statement relative to the
  earlier computational-path and topological-groupoid literature.
- Every use of “topological groupoid” satisfies the terminology contract.
- The logical relevance comes from rewrite syntax, congruence, and semantics;
  it does not rest on the existence of a Lean artifact.
- The main paper is intelligible without opening the formalization appendix.

## 10. Proof dependency order

The implementation order is fixed by mathematical dependency:

1. define continuous geometric rewrite presentations and scoped rewrite
   equality;
2. prove realization soundness;
3. construct the rewrite quotient groupoid;
4. establish the final-domain continuity theorem;
5. prove the ordinary-pullback criterion and sufficient conditions;
6. prove quotient-level functoriality;
7. construct the comparison morphism and prove the completion theorem; and
8. formalize the circle normal-form certificate and the actual product-torus
   winding certificate.

The manuscript follows this dependency order from definitions to examples.

## 11. Design-contract criteria

This contract fixes:

- the four mathematical levels;
- the scoped rewrite relation;
- the two composable-pair topologies;
- the reserved terminology;
- the theorem dependency graph;
- the originality boundary; and
- the positive compact-Hausdorff ordinary-pullback class.

These items define the paper’s central claim rather than merely its
presentation.

## 12. Checked implementation

The contract is reflected in the checked implementation:

- scoped rewrite soundness is proved by induction;
- the rewrite quotient, final composable domain, and all groupoid laws are
  checked;
- the ordinary/final topology comparison is an exact four-way quotient-map
  classification theorem, with a general completeness iff injectivity
  criterion; the certified groupoid structure is unconditional on the final
  composable domain;
- comparison preserves the groupoid operations and is continuous;
- compact-Hausdorff and discrete positive ordinary-pullback theorems are
  checked;
- the normal-form certificate is checked and instantiated on the based circle
  fiber, with a separate finite-generator trace-code completion;
- the comparison is explicitly bridged to a realized fundamental-groupoid
  arrow carrier, and the universal presentation is homeomorphic to it;
- the topological-circle loop example has explicit zero/add/neg rewrite rules,
  generator soundness, induction normalization, a based normal-form
  certificate, a continuous arrow-space map, an integer winding normal form,
  a proved nondegeneracy theorem, and an unconditional final-domain groupoid
  certificate;
- the genuine topological torus has a checked product-winding equivalence and
  a path-level round-trip certificate.
- the finite trace-sensitive separation certificate checks that the full word
  topology can distinguish two generators whose observable code agrees.

The standalone manuscript source is `main.tex` and has been compiled from
this directory. The Lean-only artifact is version `0.6.1+lean-only-v3`,
archived at Zenodo DOI `10.5281/zenodo.21938980`; the permanent concept DOI is
`10.5281/zenodo.21817207`. The reproducible Lean artifact and the manuscript
PDF are packaged separately; independent mathematical review remains an
external submission step, not an unresolved Lean theorem.
