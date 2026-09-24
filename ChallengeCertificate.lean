import ChallengePrelude
namespace ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite
open scoped ContinuousMap Topology
universe u v
variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  {S : ContinuousGeometricStepSystem A Step}
  (P : ScopedGeometricRewritePresentation S)
theorem scopedSrc_symm (p : ScopedClass P) :
    scopedSrc P (scopedSymm P p) = scopedTgt P p := by
  refine Quotient.inductionOn p ?_
  intro p
  rfl
theorem scopedTgt_symm (p : ScopedClass P) :
    scopedTgt P (scopedSymm P p) = scopedSrc P p := by
  refine Quotient.inductionOn p ?_
  intro p
  rfl
noncomputable def strongLeftUnitPair (p : ScopedClass P) :
    ScopedStrongComposablePair P :=
  ⟨⟨scopedRefl P (scopedSrc P p), p⟩, by
    exact scopedTgt_refl P (scopedSrc P p)⟩
noncomputable def strongRightUnitPair (p : ScopedClass P) :
    ScopedStrongComposablePair P :=
  ⟨⟨p, scopedRefl P (scopedTgt P p)⟩, by
    exact (scopedSrc_refl P (scopedTgt P p)).symm⟩
noncomputable def strongRightInversePair (p : ScopedClass P) :
    ScopedStrongComposablePair P :=
  ⟨⟨p, scopedSymm P p⟩, by
    exact (scopedSrc_symm P p).symm⟩
noncomputable def strongLeftInversePair (p : ScopedClass P) :
    ScopedStrongComposablePair P :=
  ⟨⟨scopedSymm P p, p⟩, by
    exact scopedTgt_symm P p⟩
structure ScopedComposableTriple (P : ScopedGeometricRewritePresentation S) where
  src : A
  firstMid : A
  secondMid : A
  tgt : A
  first : OpenGeometricCompPath S.toGeometricStepSystem src firstMid
  second : OpenGeometricCompPath S.toGeometricStepSystem firstMid secondMid
  third : OpenGeometricCompPath S.toGeometricStepSystem secondMid tgt
noncomputable def tripleFirstSecond (t : ScopedComposableTriple P) :
    ScopedComposableRaw (S := S) :=
  ⟨t.src, t.firstMid, t.secondMid, t.first, t.second⟩
noncomputable def tripleSecondThird (t : ScopedComposableTriple P) :
    ScopedComposableRaw (S := S) :=
  ⟨t.firstMid, t.secondMid, t.tgt, t.second, t.third⟩
noncomputable def tripleLeftRaw (t : ScopedComposableTriple P) :
    ScopedComposableRaw (S := S) :=
  ⟨t.src, t.secondMid, t.tgt,
    openTrans S.toGeometricStepSystem t.first t.second,
    t.third⟩
noncomputable def tripleRightRaw (t : ScopedComposableTriple P) :
    ScopedComposableRaw (S := S) :=
  ⟨t.src, t.firstMid, t.tgt,
    t.first,
    openTrans S.toGeometricStepSystem t.second t.third⟩
noncomputable def tripleLeftPair (t : ScopedComposableTriple P) :
    ScopedStrongComposablePair P :=
  ⟨⟨scopedCompositionOnStrong P
        (scopedPairMap P (scopedComposableMk P (tripleFirstSecond P t))),
      scopedQuotientMk P
        ⟨t.secondMid, t.tgt, t.third⟩⟩, by
        rw [scopedCompositionOnStrong_mk]
        rfl⟩
noncomputable def tripleRightPair (t : ScopedComposableTriple P) :
    ScopedStrongComposablePair P :=
  ⟨⟨scopedQuotientMk P ⟨t.src, t.firstMid, t.first⟩,
      scopedCompositionOnStrong P
        (scopedPairMap P (scopedComposableMk P (tripleSecondThird P t)))⟩, by
        rw [scopedCompositionOnStrong_mk]
        rfl⟩
end ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite
namespace ComputationalPaths.Path.GeometricTopology.UniversalCompPathHomotopyEquivalence
variable {A : Type u} [TopologicalSpace A]
noncomputable abbrev UniversalSystem := continuousPathStepSystem A
abbrev UniversalOpen {a b : A} :=
  OpenGeometricCompPath UniversalSystem.toGeometricStepSystem a b
noncomputable def universalOpenSection {a b : A} (γ : _root_.Path a b) :
    UniversalOpen (A := A) (a := a) (b := b) :=
  { trace :=
      ContinuousGeometricStepSystemMap.castTrace
        (S := UniversalSystem) γ.source.symm γ.target.symm
        (GeometricTrace.single
          (S := UniversalSystem.toGeometricStepSystem) γ.toContinuousMap)
    geometric := γ
    coherent := by
      have hrealize :
          GeometricTrace.realize
              (ContinuousGeometricStepSystemMap.castTrace
                (S := UniversalSystem) γ.source.symm γ.target.symm
                (GeometricTrace.single
                  (S := UniversalSystem.toGeometricStepSystem) γ.toContinuousMap)) =
            γ := by
        rw [ContinuousGeometricStepSystemMap.castTrace_realize]
        ext t
        rfl
      rw [hrealize] }
theorem universalOpenSection_geometric {a b : A} (γ : _root_.Path a b) :
    (universalOpenSection γ).geometric = γ := rfl
theorem universalOpenSection_traceLength {a b : A} (γ : _root_.Path a b) :
    GeometricTrace.traceLength (universalOpenSection γ).trace = 1 := by
  change GeometricTrace.traceLength
      (ContinuousGeometricStepSystemMap.castTrace
        (S := UniversalSystem) γ.source.symm γ.target.symm
        (GeometricTrace.single
          (S := UniversalSystem.toGeometricStepSystem) γ.toContinuousMap)) = 1
  rw [ContinuousGeometricStepSystemMap.castTrace_length]
  rfl
theorem universalOpenSection_traceRealize {a b : A}
    (γ : _root_.Path a b) :
    GeometricTrace.realize (universalOpenSection γ).trace = γ := by
  change GeometricTrace.realize
      (ContinuousGeometricStepSystemMap.castTrace
        (S := UniversalSystem) γ.source.symm γ.target.symm
        (GeometricTrace.single
          (S := UniversalSystem.toGeometricStepSystem) γ.toContinuousMap)) = γ
  rw [ContinuousGeometricStepSystemMap.castTrace_realize]
  ext t
  rfl
end ComputationalPaths.Path.GeometricTopology.UniversalCompPathHomotopyEquivalence
namespace TopologicalComputationalPaths
open ComputationalPaths.Path.GeometricTopology
open ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite
universe u v
/-! ## The ordinary/final topology comparison
The canonical final composable domain is always mapped continuously and
bijectively to the ordinary pullback of quotient arrows.  The substantive
question is when its inverse is continuous, equivalently when the raw pair map
is quotient and when the two topologies agree. -/
noncomputable def finalToOrdinary
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    {S : ContinuousGeometricStepSystem A Step}
    (P : ScopedGeometricRewritePresentation S) :
    ScopedComposableClass P → ScopedComposablePair P :=
  fun c => (scopedPairMap P c).val
noncomputable def rawToOrdinary
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    {S : ContinuousGeometricStepSystem A Step}
    (P : ScopedGeometricRewritePresentation S) :
    ScopedComposableRaw (S := S) → ScopedComposablePair P :=
  fun c => finalToOrdinary P (scopedComposableMk P c)
noncomputable def ordinaryComposition
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    {S : ContinuousGeometricStepSystem A Step}
    (P : ScopedGeometricRewritePresentation S) :
    ScopedComposablePair P → ScopedClass P :=
  fun pq => scopedCompositionOnStrong P ⟨pq⟩
/-! A source-backed obstruction transfer packages the actual Hawaiian-earring
loop quotient used in the manuscript.  Fabel's non-quotient and discontinuity
theorems are explicit hypotheses; the selected consequences are the failures
of the scoped presentation's ordinary-pair quotient and multiplication. -/
noncomputable def hawaiianRadius (n : Nat) : ℝ := 1 / (n + 1)
def hawaiianEarringSet : Set (ℝ × ℝ) :=
  {p | ∃ n : Nat,
    (p.1 - hawaiianRadius n) ^ 2 + p.2 ^ 2 = hawaiianRadius n ^ 2}
abbrev HawaiianEarring := {p : ℝ × ℝ // p ∈ hawaiianEarringSet}
noncomputable def hawaiianBase : HawaiianEarring :=
  ⟨(0, 0), by
    refine ⟨0, ?_⟩
    norm_num [hawaiianEarringSet, hawaiianRadius]⟩
abbrev HawaiianLoop := _root_.Path hawaiianBase hawaiianBase
abbrev HawaiianLoopQuotient :=
  _root_.Path.Homotopic.Quotient hawaiianBase hawaiianBase
noncomputable def hawaiianLoopQuotientMap :
    HawaiianLoop → HawaiianLoopQuotient :=
  _root_.Path.Homotopic.Quotient.mk
noncomputable instance hawaiianLoopQuotientTopology :
    TopologicalSpace HawaiianLoopQuotient :=
  TopologicalSpace.coinduced hawaiianLoopQuotientMap inferInstance
noncomputable def hawaiianPairQuotientMap :
    HawaiianLoop × HawaiianLoop →
      HawaiianLoopQuotient × HawaiianLoopQuotient :=
  fun pq => (hawaiianLoopQuotientMap pq.1, hawaiianLoopQuotientMap pq.2)
noncomputable def hawaiianLoopQuotientMultiplication :
    HawaiianLoopQuotient × HawaiianLoopQuotient → HawaiianLoopQuotient :=
  fun pq => _root_.Path.Homotopic.Quotient.trans pq.1 pq.2
theorem continuous_hawaiianPairQuotientMap :
    Continuous hawaiianPairQuotientMap := by
  exact
    (continuous_coinduced_rng.comp continuous_fst).prodMk
      (continuous_coinduced_rng.comp continuous_snd)
/-- The two classical Hawaiian-earring facts are external inputs to the
transfer.  They are not claimed as newly proved by this Challenge. -/
structure FabelHawaiianEarringFacts : Prop where
  pair_not_quotient :
    ¬ Topology.IsQuotientMap hawaiianPairQuotientMap
  multiplication_not_continuous :
    ¬ Continuous hawaiianLoopQuotientMultiplication
/-! ## The concrete based fiber and its final/ordinary comparison -/
open ComputationalPaths.Path.GeometricTopology.UniversalCompPathHomotopyEquivalence
noncomputable abbrev HawaiianUniversalSystem :=
  continuousPathStepSystem HawaiianEarring
abbrev HawaiianUniversalOpen :=
  UniversalOpen (A := HawaiianEarring)
    (a := hawaiianBase) (b := hawaiianBase)
structure HawaiianObservableOpenFiber where
  val : HawaiianUniversalOpen
noncomputable def hawaiianObservableGeometric
    (p : HawaiianObservableOpenFiber) : HawaiianLoop :=
  p.val.geometric
noncomputable def hawaiianObservableTotal
    (p : HawaiianObservableOpenFiber) :
    TotalOpenGeometricCompPath HawaiianEarring
      (ContinuousPathStep HawaiianEarring) HawaiianUniversalSystem :=
  ⟨hawaiianBase, hawaiianBase, p.val⟩
/-- The based fiber has the subspace topology inherited from the observable
total carrier, including its trace-length and realization coordinates. -/
noncomputable instance hawaiianObservableOpenFiberTopology :
    TopologicalSpace HawaiianObservableOpenFiber :=
  TopologicalSpace.induced hawaiianObservableTotal inferInstance
theorem continuous_hawaiianObservableGeometric :
    Continuous (hawaiianObservableGeometric :
      HawaiianObservableOpenFiber → HawaiianLoop) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : HawaiianObservableOpenFiber =>
    TotalOpenGeometricCompPath.geometricMap HawaiianUniversalSystem
      (hawaiianObservableTotal p))
  exact (TotalOpenGeometricCompPath.continuous_geometricMap
    HawaiianUniversalSystem).comp continuous_induced_dom
noncomputable def hawaiianObservableSection (γ : HawaiianLoop) :
    HawaiianObservableOpenFiber :=
  ⟨universalOpenSection γ⟩
theorem hawaiianObservableSection_geometric (γ : HawaiianLoop) :
    hawaiianObservableGeometric (hawaiianObservableSection γ) = γ := by
  rfl
theorem continuous_hawaiianObservableSection :
    Continuous (hawaiianObservableSection : HawaiianLoop →
      HawaiianObservableOpenFiber) := by
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  have hloop : Continuous (fun γ : HawaiianLoop => γ.toContinuousMap) :=
    continuous_induced_dom
  have hobs :
      (fun γ : HawaiianLoop =>
        TotalOpenGeometricCompPath.observation HawaiianUniversalSystem
          (hawaiianObservableTotal (hawaiianObservableSection γ))) =
      (fun γ : HawaiianLoop =>
        (hawaiianBase, (hawaiianBase,
          (1, (γ.toContinuousMap, γ.toContinuousMap))))) := by
    funext γ
    simp only [hawaiianObservableTotal, hawaiianObservableSection,
      TotalOpenGeometricCompPath.observation,
      TotalOpenGeometricCompPath.trace,
      TotalOpenGeometricCompPath.traceMap,
      TotalOpenGeometricCompPath.geometricMap,
      TotalOpenGeometricCompPath.geometricPath,
      universalOpenSection_traceLength,
      universalOpenSection_traceRealize,
      universalOpenSection_geometric]
  change Continuous (fun γ : HawaiianLoop =>
    TotalOpenGeometricCompPath.observation HawaiianUniversalSystem
      (hawaiianObservableTotal (hawaiianObservableSection γ)))
  rw [hobs]
  exact continuous_const.prodMk
    (continuous_const.prodMk
      (continuous_const.prodMk (hloop.prodMk hloop)))
noncomputable instance hawaiianObservableSetoid :
    Setoid HawaiianObservableOpenFiber where
  r p q := _root_.Path.Homotopic
    (hawaiianObservableGeometric p) (hawaiianObservableGeometric q)
  iseqv :=
    { refl := fun p => _root_.Path.Homotopic.refl
        (hawaiianObservableGeometric p)
      symm := fun h => h.symm
      trans := fun h₁ h₂ => h₁.trans h₂ }
abbrev HawaiianObservableClass := Quotient hawaiianObservableSetoid
noncomputable def hawaiianObservableQuotientMk
    (p : HawaiianObservableOpenFiber) : HawaiianObservableClass :=
  Quotient.mk' p
noncomputable instance hawaiianObservableClassTopology :
    TopologicalSpace HawaiianObservableClass :=
  TopologicalSpace.coinduced hawaiianObservableQuotientMk inferInstance
noncomputable def hawaiianObservableToLoopQuotient :
    HawaiianObservableClass → HawaiianLoopQuotient :=
  Quotient.lift
    (fun p => hawaiianLoopQuotientMap (hawaiianObservableGeometric p))
    (by
      intro p q h
      exact Quotient.sound h)
noncomputable def loopQuotientToHawaiianObservable :
    HawaiianLoopQuotient → HawaiianObservableClass :=
  Quotient.lift
    (fun γ => hawaiianObservableQuotientMk (hawaiianObservableSection γ))
    (by
      intro γ₁ γ₂ h
      apply Quotient.sound
      change _root_.Path.Homotopic
        (hawaiianObservableGeometric (hawaiianObservableSection γ₁))
        (hawaiianObservableGeometric (hawaiianObservableSection γ₂))
      rw [hawaiianObservableSection_geometric,
        hawaiianObservableSection_geometric]
      exact h)
noncomputable def hawaiianObservableHomeomorph :
    HawaiianObservableClass ≃ₜ HawaiianLoopQuotient where
  toEquiv :=
    { toFun := hawaiianObservableToLoopQuotient
      invFun := loopQuotientToHawaiianObservable
      left_inv := by
        intro x
        refine Quotient.inductionOn x ?_
        intro p
        apply Quotient.sound
        change _root_.Path.Homotopic
          (hawaiianObservableGeometric
            (hawaiianObservableSection (hawaiianObservableGeometric p)))
          (hawaiianObservableGeometric p)
        rw [hawaiianObservableSection_geometric]
      right_inv := by
        intro y
        refine Quotient.inductionOn y ?_
        intro γ
        rfl }
  continuous_toFun := by
    apply (⟨⟨rfl⟩, Quotient.mk_surjective⟩ :
      Topology.IsQuotientMap hawaiianObservableQuotientMk).continuous_iff.2
    rw [show hawaiianObservableToLoopQuotient ∘
        hawaiianObservableQuotientMk =
        hawaiianLoopQuotientMap ∘ hawaiianObservableGeometric by
      funext p
      rfl]
    exact continuous_coinduced_rng.comp
      continuous_hawaiianObservableGeometric
  continuous_invFun := by
    apply (⟨⟨rfl⟩, Quotient.mk_surjective⟩ :
      Topology.IsQuotientMap hawaiianLoopQuotientMap).continuous_iff.2
    rw [show loopQuotientToHawaiianObservable ∘
        hawaiianLoopQuotientMap =
        hawaiianObservableQuotientMk ∘ hawaiianObservableSection by
      funext γ
      rfl]
    exact continuous_coinduced_rng.comp continuous_hawaiianObservableSection
noncomputable def hawaiianBasedPairQuotientMap :
    HawaiianObservableOpenFiber × HawaiianObservableOpenFiber →
      HawaiianObservableClass × HawaiianObservableClass :=
  fun pq => (hawaiianObservableQuotientMk pq.1,
    hawaiianObservableQuotientMk pq.2)
noncomputable def hawaiianBasedPairHomeomorph :
    (HawaiianObservableClass × HawaiianObservableClass) ≃ₜ
      (HawaiianLoopQuotient × HawaiianLoopQuotient) :=
  Homeomorph.prodCongr hawaiianObservableHomeomorph
    hawaiianObservableHomeomorph
noncomputable instance hawaiianBasedFinalPairSetoid :
    Setoid (HawaiianObservableOpenFiber × HawaiianObservableOpenFiber) where
  r p q := p.1 ≈ q.1 ∧ p.2 ≈ q.2
  iseqv :=
    { refl := fun _ => ⟨Setoid.refl _, Setoid.refl _⟩
      symm := fun h => ⟨Setoid.symm h.1, Setoid.symm h.2⟩
      trans := fun h₁ h₂ =>
        ⟨Setoid.trans h₁.1 h₂.1, Setoid.trans h₁.2 h₂.2⟩ }
abbrev HawaiianBasedFinalPair := Quotient hawaiianBasedFinalPairSetoid
noncomputable def hawaiianBasedFinalPairMk
    (pq : HawaiianObservableOpenFiber × HawaiianObservableOpenFiber) :
    HawaiianBasedFinalPair := Quotient.mk' pq
noncomputable instance hawaiianBasedFinalPairTopology :
    TopologicalSpace HawaiianBasedFinalPair :=
  TopologicalSpace.coinduced hawaiianBasedFinalPairMk inferInstance
noncomputable def hawaiianBasedFinalToOrdinary :
    HawaiianBasedFinalPair →
      HawaiianObservableClass × HawaiianObservableClass :=
  Quotient.lift hawaiianBasedPairQuotientMap (by
    intro p q h
    exact Prod.ext (Quotient.sound h.1) (Quotient.sound h.2))
noncomputable def hawaiianBasedRawTrans
    (pq : HawaiianObservableOpenFiber × HawaiianObservableOpenFiber) :
    HawaiianObservableOpenFiber :=
  ⟨openTrans HawaiianUniversalSystem.toGeometricStepSystem
      pq.1.val pq.2.val⟩
noncomputable def hawaiianBasedFinalOperation :
    HawaiianBasedFinalPair → HawaiianObservableClass :=
  Quotient.lift
    (fun pq => hawaiianObservableQuotientMk (hawaiianBasedRawTrans pq))
    (by
      intro p q h
      apply Quotient.sound
      change _root_.Path.Homotopic
        (hawaiianObservableGeometric (hawaiianBasedRawTrans p))
        (hawaiianObservableGeometric (hawaiianBasedRawTrans q))
      change _root_.Path.Homotopic
        ((hawaiianObservableGeometric p.1).trans
          (hawaiianObservableGeometric p.2))
        ((hawaiianObservableGeometric q.1).trans
          (hawaiianObservableGeometric q.2))
      exact h.1.hcomp h.2)
noncomputable def hawaiianBasedOrdinaryOperation :
    HawaiianObservableClass × HawaiianObservableClass → HawaiianObservableClass :=
  fun pq =>
    Quotient.map₂
      (fun p q => hawaiianBasedRawTrans (p, q))
      (by
        intro p p' hp q q' hq
        change _root_.Path.Homotopic
          ((hawaiianObservableGeometric p).trans
            (hawaiianObservableGeometric q))
          ((hawaiianObservableGeometric p').trans
            (hawaiianObservableGeometric q'))
        exact hp.hcomp hq)
      pq.1 pq.2
structure HawaiianBasedFiberCertificate
    (F : FabelHawaiianEarringFacts) : Prop where
  based_section : ∀ γ : HawaiianLoop,
    hawaiianObservableGeometric (hawaiianObservableSection γ) = γ
  observable_projection_continuous :
    Continuous hawaiianObservableGeometric
  observable_projection_quotient :
    Topology.IsQuotientMap hawaiianObservableGeometric
  quotient_homeomorph :
    Nonempty (HawaiianObservableClass ≃ₜ HawaiianLoopQuotient)
  pair_map_continuous : Continuous hawaiianBasedPairQuotientMap
  pair_map_not_quotient :
    ¬ Topology.IsQuotientMap hawaiianBasedPairQuotientMap
  final_to_ordinary_bijective :
    Function.Bijective hawaiianBasedFinalToOrdinary
  final_to_ordinary_continuous :
    Continuous hawaiianBasedFinalToOrdinary
  final_to_ordinary_not_quotient :
    ¬ Topology.IsQuotientMap hawaiianBasedFinalToOrdinary
  final_topology_not_induced :
    ¬ ((inferInstance : TopologicalSpace HawaiianBasedFinalPair) =
      TopologicalSpace.induced hawaiianBasedFinalToOrdinary
        (inferInstance : TopologicalSpace
          (HawaiianObservableClass × HawaiianObservableClass)))
  final_operation_continuous : Continuous hawaiianBasedFinalOperation
  ordinary_operation_not_continuous :
    ¬ Continuous hawaiianBasedOrdinaryOperation
  operation_commutes :
    hawaiianBasedFinalOperation =
      hawaiianBasedOrdinaryOperation ∘ hawaiianBasedFinalToOrdinary
structure HawaiianEarringObstructionTransfer
    (source : Type u) (target : Type v) (arrow : Type w)
    [TopologicalSpace source] [TopologicalSpace target]
    [TopologicalSpace arrow] where
  sourceMap : source → target
  representativeMap : source → HawaiianLoop × HawaiianLoop
  comparison : target ≃ₜ (HawaiianLoopQuotient × HawaiianLoopQuotient)
  sourceOperation : target → arrow
  arrowComparison : arrow ≃ₜ HawaiianLoopQuotient
  representative_continuous : Continuous representativeMap
  comparison_commutes :
    comparison ∘ sourceMap = hawaiianPairQuotientMap ∘ representativeMap
  operation_commutes :
    arrowComparison ∘ sourceOperation =
      hawaiianLoopQuotientMultiplication ∘ comparison
  external_facts : FabelHawaiianEarringFacts
abbrev GenuineCircleLoopQuotient := _root_.Path.Homotopic.Quotient (0 : AddCircle (1 : ℝ)) 0
abbrev GenuineTorusLoopQuotient :=
  _root_.Path.Homotopic.Quotient ((0 : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ)))
    ((0 : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ)))
structure AdditiveLoopClassification (Q : Type u) (K : Type v) [AddMonoid K] (compose : Q → Q → Q) (identity : Q) where
  invariant : Q → K
  standard : K → Q
  invariant_identity : invariant identity = 0
  invariant_compose : ∀ x y, invariant (compose x y) = invariant x + invariant y
  invariant_standard : ∀ k, invariant (standard k) = k
  standard_invariant : ∀ x, standard (invariant x) = x
abbrev GenuineCircleWindingClassification := AdditiveLoopClassification GenuineCircleLoopQuotient Int _root_.Path.Homotopic.Quotient.trans (_root_.Path.Homotopic.Quotient.mk (_root_.Path.refl (0 : AddCircle (1 : ℝ))))
abbrev GenuineTorusWindingClassification := AdditiveLoopClassification GenuineTorusLoopQuotient (Int × Int) _root_.Path.Homotopic.Quotient.trans (_root_.Path.Homotopic.Quotient.mk (_root_.Path.refl ((0 : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ)))))
structure OrdinaryTopologyComparisonCertificate
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    (S : ContinuousGeometricStepSystem A Step)
    (P : ScopedGeometricRewritePresentation S) : Prop where
  canonical_bijection : Function.Bijective (finalToOrdinary P)
  canonical_map_continuous : Continuous (finalToOrdinary P)
  raw_quotient_criterion :
    Topology.IsQuotientMap (finalToOrdinary P) ↔
      Topology.IsQuotientMap (rawToOrdinary P)
  homeomorphism_criterion :
    Topology.IsQuotientMap (finalToOrdinary P) ↔
      ∃ e : ScopedComposableClass P ≃ₜ ScopedComposablePair P,
        (e : ScopedComposableClass P → ScopedComposablePair P) =
          finalToOrdinary P
  topology_agreement_criterion :
    Topology.IsQuotientMap (finalToOrdinary P) ↔
      (inferInstance : TopologicalSpace (ScopedComposableClass P)) =
        TopologicalSpace.induced (finalToOrdinary P)
          (inferInstance : TopologicalSpace (ScopedComposablePair P))
  ordinary_composition_of_quotient :
    Topology.IsQuotientMap (finalToOrdinary P) →
      Continuous (ordinaryComposition P)
  open_arrow_recovers_ordinary :
    IsOpenMap (scopedQuotientMk P) →
      Topology.IsQuotientMap (finalToOrdinary P) ∧
        Continuous (ordinaryComposition P)
  final_projections_continuous :
    Continuous (fun c : ScopedComposableClass P =>
      (finalToOrdinary P c).val.1) ∧
    Continuous (fun c : ScopedComposableClass P =>
      (finalToOrdinary P c).val.2)
  discontinuity_obstructs_compatibility :
    ¬ Continuous (ordinaryComposition P) →
      ¬ Topology.IsQuotientMap (finalToOrdinary P)
  compact_hausdorff_recovers_ordinary :
    ∀ [CompactSpace (ScopedComposableClass P)]
      [T2Space (ScopedComposablePair P)],
      Topology.IsQuotientMap (finalToOrdinary P) ∧
        Continuous (ordinaryComposition P)
  discrete_recovers_ordinary :
    ∀ [DiscreteTopology (ScopedClass P)],
      Topology.IsQuotientMap (finalToOrdinary P) ∧
        Continuous (ordinaryComposition P)
  hawaiian_earring_obstruction :
    ∀ (C : HawaiianEarringObstructionTransfer
      (ScopedComposableRaw (S := S)) (ScopedComposablePair P)
      (ScopedClass P))
      (_hmap : C.sourceMap = rawToOrdinary P)
      (_hop : C.sourceOperation = ordinaryComposition P),
      ¬ Topology.IsQuotientMap (rawToOrdinary P) ∧
      ¬ Topology.IsQuotientMap (finalToOrdinary P) ∧
      ¬ ((inferInstance : TopologicalSpace (ScopedComposableClass P)) =
        TopologicalSpace.induced (finalToOrdinary P)
          (inferInstance : TopologicalSpace (ScopedComposablePair P))) ∧
      ¬ Continuous (ordinaryComposition P)
  hawaiian_based_fiber :
    ∀ F : FabelHawaiianEarringFacts, HawaiianBasedFiberCertificate F
  genuine_circle_winding : Nonempty GenuineCircleWindingClassification
  genuine_torus_winding : Nonempty GenuineTorusWindingClassification
end TopologicalComputationalPaths
