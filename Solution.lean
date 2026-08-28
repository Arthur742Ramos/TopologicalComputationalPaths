import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Path
import ComputationalPaths

/-!
# Solution: topological semantics of computational paths

The selected theorem compares the canonical final and ordinary topologies,
identifies quotient-map and homeomorphism criteria, transfers composition
continuity, and proves standard sufficient cases.  It also includes genuine,
unconditional additive-classification certificates for the circle and torus,
with identity, composition-additivity, explicit standard representatives, and
inverse laws proved by universal-cover lifting and coordinatewise arguments.
The Hawaiian-earring based-fiber transfer remains conditional on externally
supplied Fabel facts; the generic final-domain interface below supports the
extraction adapter.
-/

namespace TopologicalComputationalPaths

universe u v w

open ComputationalPaths.Path.GeometricTopology
open ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite
open ComputationalPaths.Path.GeometricTopology.UniversalCompPathHomotopyEquivalence
open scoped Topology
attribute [local instance] _root_.Path.Homotopic.setoid

/-! ## The ordinary/final topology comparison -/

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

/-! A Fabel-style source-backed obstruction transfer uses the actual
Hawaiian-earring loop quotient.  The external non-quotient and discontinuity
theorems are supplied as data; the checked conclusions locate their
consequences in the scoped final-versus-ordinary comparison. -/
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
transfer.  They are not claimed as newly proved by this solution. -/
structure FabelHawaiianEarringFacts : Prop where
  pair_not_quotient :
    ¬ Topology.IsQuotientMap hawaiianPairQuotientMap
  multiplication_not_continuous :
    ¬ Continuous hawaiianLoopQuotientMultiplication

/-! ## The concrete based fiber and its final/ordinary comparison -/

noncomputable abbrev HawaiianUniversalSystem :=
  continuousPathStepSystem HawaiianEarring

abbrev HawaiianUniversalOpen :=
  UniversalOpen (A := HawaiianEarring)
    (a := hawaiianBase) (b := hawaiianBase)

/-- The based fiber of the universal open computational-path system.  The
`val` field retains the trace and coherence witness; the observable topology
below records the geometric loop that the witness presents. -/
structure HawaiianObservableOpenFiber where
  val : HawaiianUniversalOpen

noncomputable def hawaiianObservableGeometric
    (p : HawaiianObservableOpenFiber) : HawaiianLoop :=
  p.val.geometric

noncomputable instance hawaiianObservableOpenFiberTopology :
    TopologicalSpace HawaiianObservableOpenFiber :=
  TopologicalSpace.induced hawaiianObservableGeometric inferInstance

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
  change Continuous (fun γ : HawaiianLoop =>
    hawaiianObservableGeometric (hawaiianObservableSection γ))
  rw [show (fun γ : HawaiianLoop =>
      hawaiianObservableGeometric (hawaiianObservableSection γ)) = id by
    funext γ
    exact hawaiianObservableSection_geometric γ]
  exact continuous_id

theorem continuous_hawaiianObservableGeometric :
    Continuous (hawaiianObservableGeometric :
      HawaiianObservableOpenFiber → HawaiianLoop) :=
  continuous_induced_dom

theorem surjective_hawaiianObservableGeometric :
    Function.Surjective hawaiianObservableGeometric := by
  intro γ
  exact ⟨hawaiianObservableSection γ, hawaiianObservableSection_geometric γ⟩

theorem quotient_hawaiianObservableGeometric :
    Topology.IsQuotientMap hawaiianObservableGeometric := by
  exact (Topology.IsInducing.induced hawaiianObservableGeometric).isQuotientMap_of_surjective
    surjective_hawaiianObservableGeometric

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

theorem quotient_hawaiianObservableQuotientMk :
    Topology.IsQuotientMap hawaiianObservableQuotientMk :=
  ⟨⟨rfl⟩, Quotient.mk_surjective⟩

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

theorem continuous_hawaiianLoopQuotientMap :
    Continuous hawaiianLoopQuotientMap :=
  continuous_coinduced_rng

theorem observableToLoopQuotient_fromLoopQuotient (γ : HawaiianLoop) :
    hawaiianObservableToLoopQuotient
        (loopQuotientToHawaiianObservable (Quotient.mk' γ)) =
      Quotient.mk' γ := by
  rfl

theorem loopQuotientToObservable_toLoopQuotient
    (x : HawaiianObservableClass) :
    loopQuotientToHawaiianObservable
        (hawaiianObservableToLoopQuotient x) = x := by
  refine Quotient.inductionOn x ?_
  intro p
  apply Quotient.sound
  change _root_.Path.Homotopic
    (hawaiianObservableGeometric
      (hawaiianObservableSection (hawaiianObservableGeometric p)))
    (hawaiianObservableGeometric p)
  rw [hawaiianObservableSection_geometric]

noncomputable def hawaiianObservableHomeomorph :
    HawaiianObservableClass ≃ₜ HawaiianLoopQuotient where
  toEquiv :=
    { toFun := hawaiianObservableToLoopQuotient
      invFun := loopQuotientToHawaiianObservable
      left_inv := loopQuotientToObservable_toLoopQuotient
      right_inv := by
        intro y
        refine Quotient.inductionOn y ?_
        intro γ
        exact observableToLoopQuotient_fromLoopQuotient γ }
  continuous_toFun := by
    apply quotient_hawaiianObservableQuotientMk.continuous_iff.2
    rw [show hawaiianObservableToLoopQuotient ∘
        hawaiianObservableQuotientMk =
        hawaiianLoopQuotientMap ∘ hawaiianObservableGeometric by
      funext p
      rfl]
    exact continuous_hawaiianLoopQuotientMap.comp
      continuous_hawaiianObservableGeometric
  continuous_invFun := by
    apply (⟨⟨rfl⟩, Quotient.mk_surjective⟩ :
      Topology.IsQuotientMap hawaiianLoopQuotientMap).continuous_iff.2
    rw [show loopQuotientToHawaiianObservable ∘
        hawaiianLoopQuotientMap =
        hawaiianObservableQuotientMk ∘ hawaiianObservableSection by
      funext γ
      rfl]
    exact quotient_hawaiianObservableQuotientMk.continuous.comp
      continuous_hawaiianObservableSection

noncomputable def hawaiianBasedPairProjection :
    HawaiianObservableOpenFiber × HawaiianObservableOpenFiber →
      HawaiianLoop × HawaiianLoop :=
  fun pq => (hawaiianObservableGeometric pq.1,
    hawaiianObservableGeometric pq.2)

noncomputable def hawaiianBasedPairQuotientMap :
    HawaiianObservableOpenFiber × HawaiianObservableOpenFiber →
      HawaiianObservableClass × HawaiianObservableClass :=
  fun pq => (hawaiianObservableQuotientMk pq.1,
    hawaiianObservableQuotientMk pq.2)

theorem continuous_hawaiianBasedPairProjection :
    Continuous hawaiianBasedPairProjection := by
  exact (continuous_hawaiianObservableGeometric.comp continuous_fst).prodMk
    (continuous_hawaiianObservableGeometric.comp continuous_snd)

theorem continuous_hawaiianObservableQuotientMk :
    Continuous hawaiianObservableQuotientMk :=
  continuous_coinduced_rng

theorem continuous_hawaiianBasedPairQuotientMap :
    Continuous hawaiianBasedPairQuotientMap := by
  exact (continuous_hawaiianObservableQuotientMk.comp continuous_fst).prodMk
    (continuous_hawaiianObservableQuotientMk.comp continuous_snd)

noncomputable def hawaiianBasedPairHomeomorph :
    (HawaiianObservableClass × HawaiianObservableClass) ≃ₜ
      (HawaiianLoopQuotient × HawaiianLoopQuotient) :=
  Homeomorph.prodCongr hawaiianObservableHomeomorph
    hawaiianObservableHomeomorph

@[simp] theorem hawaiianObservableHomeomorph_apply
    (x : HawaiianObservableClass) :
    hawaiianObservableHomeomorph x = hawaiianObservableToLoopQuotient x :=
  rfl

@[simp] theorem hawaiianBasedPairHomeomorph_apply
    (x y : HawaiianObservableClass) :
    hawaiianBasedPairHomeomorph (x, y) =
      (hawaiianObservableHomeomorph x,
        hawaiianObservableHomeomorph y) :=
  rfl

theorem hawaiianBasedPairComparison_commutes :
    hawaiianPairQuotientMap ∘ hawaiianBasedPairProjection =
      hawaiianBasedPairHomeomorph ∘ hawaiianBasedPairQuotientMap := by
  funext pq
  rfl

theorem hawaiianBasedPair_not_quotient (F : FabelHawaiianEarringFacts) :
    ¬ Topology.IsQuotientMap hawaiianBasedPairQuotientMap := by
  intro hq
  have hpost :
      Topology.IsQuotientMap
        (hawaiianBasedPairHomeomorph ∘ hawaiianBasedPairQuotientMap) :=
    hawaiianBasedPairHomeomorph.isQuotientMap.comp hq
  have hcomp :
      Topology.IsQuotientMap
        (hawaiianPairQuotientMap ∘ hawaiianBasedPairProjection) := by
    rw [hawaiianBasedPairComparison_commutes]
    exact hpost
  exact F.pair_not_quotient
    (Topology.IsQuotientMap.of_comp
      continuous_hawaiianBasedPairProjection
      continuous_hawaiianPairQuotientMap hcomp)

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

theorem quotient_hawaiianBasedFinalPairMk :
    Topology.IsQuotientMap hawaiianBasedFinalPairMk :=
  ⟨⟨rfl⟩, Quotient.mk_surjective⟩

noncomputable def hawaiianBasedFinalToOrdinary :
    HawaiianBasedFinalPair →
      HawaiianObservableClass × HawaiianObservableClass :=
  Quotient.lift hawaiianBasedPairQuotientMap (by
    intro p q h
    exact Prod.ext (Quotient.sound h.1) (Quotient.sound h.2))

theorem hawaiianBasedFinalToOrdinary_mk
    (pq : HawaiianObservableOpenFiber × HawaiianObservableOpenFiber) :
    hawaiianBasedFinalToOrdinary (hawaiianBasedFinalPairMk pq) =
      hawaiianBasedPairQuotientMap pq :=
  rfl

theorem continuous_hawaiianBasedFinalToOrdinary :
    Continuous hawaiianBasedFinalToOrdinary := by
  apply quotient_hawaiianBasedFinalPairMk.continuous_iff.2
  rw [show hawaiianBasedFinalToOrdinary ∘
      hawaiianBasedFinalPairMk = hawaiianBasedPairQuotientMap by
    funext pq
    rfl]
  exact continuous_hawaiianBasedPairQuotientMap

theorem bijective_hawaiianBasedFinalToOrdinary :
    Function.Bijective hawaiianBasedFinalToOrdinary := by
  constructor
  · intro x y hxy
    refine Quotient.inductionOn₂ x y ?_ hxy
    intro p q hxy
    apply Quotient.sound
    exact ⟨Quotient.exact (congrArg Prod.fst hxy),
      Quotient.exact (congrArg Prod.snd hxy)⟩
  · rintro ⟨x, y⟩
    refine Quotient.inductionOn₂ x y ?_
    intro p q
    exact ⟨hawaiianBasedFinalPairMk (p, q), rfl⟩

theorem not_quotient_hawaiianBasedFinalToOrdinary
    (F : FabelHawaiianEarringFacts) :
    ¬ Topology.IsQuotientMap hawaiianBasedFinalToOrdinary := by
  intro hfinal
  have hcomp :
      Topology.IsQuotientMap
        (hawaiianBasedFinalToOrdinary ∘ hawaiianBasedFinalPairMk) :=
    hfinal.comp quotient_hawaiianBasedFinalPairMk
  rw [show hawaiianBasedFinalToOrdinary ∘ hawaiianBasedFinalPairMk =
      hawaiianBasedPairQuotientMap by
    funext pq
    rfl] at hcomp
  exact hawaiianBasedPair_not_quotient F hcomp

theorem not_agree_hawaiianBasedFinalTopology
    (F : FabelHawaiianEarringFacts) :
    ¬ ((inferInstance : TopologicalSpace HawaiianBasedFinalPair) =
      TopologicalSpace.induced hawaiianBasedFinalToOrdinary
        (inferInstance : TopologicalSpace
          (HawaiianObservableClass × HawaiianObservableClass))) := by
  intro hagree
  have hind : Topology.IsInducing hawaiianBasedFinalToOrdinary :=
    ⟨hagree⟩
  have hquot := hind.isQuotientMap_of_surjective
    (bijective_hawaiianBasedFinalToOrdinary.surjective)
  exact not_quotient_hawaiianBasedFinalToOrdinary F hquot

noncomputable def hawaiianBasedRawTrans
    (pq : HawaiianObservableOpenFiber × HawaiianObservableOpenFiber) :
    HawaiianObservableOpenFiber :=
  ⟨openTrans HawaiianUniversalSystem.toGeometricStepSystem
      pq.1.val pq.2.val⟩

theorem continuous_hawaiianBasedRawTrans :
    Continuous hawaiianBasedRawTrans := by
  apply continuous_induced_rng.mpr
  change Continuous (fun pq : HawaiianObservableOpenFiber ×
      HawaiianObservableOpenFiber =>
    (hawaiianObservableGeometric pq.1).trans
      (hawaiianObservableGeometric pq.2))
  exact _root_.Path.continuous_trans.comp
    ((continuous_hawaiianObservableGeometric.comp continuous_fst).prodMk
      (continuous_hawaiianObservableGeometric.comp continuous_snd))

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

theorem continuous_hawaiianBasedFinalOperation :
    Continuous hawaiianBasedFinalOperation := by
  apply quotient_hawaiianBasedFinalPairMk.continuous_iff.2
  rw [show hawaiianBasedFinalOperation ∘ hawaiianBasedFinalPairMk =
      hawaiianObservableQuotientMk ∘ hawaiianBasedRawTrans by
    funext pq
    rfl]
  exact continuous_hawaiianObservableQuotientMk.comp
    continuous_hawaiianBasedRawTrans

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

@[simp] theorem hawaiianBasedOrdinaryOperation_mk
    (p q : HawaiianObservableOpenFiber) :
    hawaiianBasedOrdinaryOperation
        (hawaiianObservableQuotientMk p, hawaiianObservableQuotientMk q) =
      hawaiianObservableQuotientMk (hawaiianBasedRawTrans (p, q)) :=
  rfl

theorem hawaiianBasedOperation_commutes :
    hawaiianBasedFinalOperation =
      hawaiianBasedOrdinaryOperation ∘ hawaiianBasedFinalToOrdinary := by
  funext x
  refine Quotient.inductionOn x ?_
  intro pq
  change hawaiianObservableQuotientMk (hawaiianBasedRawTrans pq) =
    hawaiianBasedOrdinaryOperation (hawaiianBasedPairQuotientMap pq)
  rfl

theorem not_continuous_hawaiianBasedOrdinaryOperation
    (F : FabelHawaiianEarringFacts) :
    ¬ Continuous hawaiianBasedOrdinaryOperation := by
  intro hordinary
  have hcomp :
      Continuous
        (hawaiianLoopQuotientMultiplication ∘ hawaiianBasedPairHomeomorph) := by
    rw [← show hawaiianObservableHomeomorph ∘
        hawaiianBasedOrdinaryOperation =
        hawaiianLoopQuotientMultiplication ∘ hawaiianBasedPairHomeomorph by
      funext pq
      rcases pq with ⟨x, y⟩
      refine Quotient.inductionOn₂ x y ?_
      intro p q
      simp only [Function.comp_apply, hawaiianObservableHomeomorph_apply,
        hawaiianBasedPairHomeomorph_apply]
      change hawaiianLoopQuotientMap
          (hawaiianObservableGeometric (hawaiianBasedRawTrans (p, q))) =
        hawaiianLoopQuotientMultiplication
          (hawaiianLoopQuotientMap (hawaiianObservableGeometric p),
            hawaiianLoopQuotientMap (hawaiianObservableGeometric q))
      rfl]
    exact hawaiianObservableHomeomorph.continuous.comp hordinary
  exact F.multiplication_not_continuous
    (hawaiianBasedPairHomeomorph.isQuotientMap.continuous_iff.2 hcomp)

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

theorem hawaiianBasedFiberCertificate_of_facts
    (F : FabelHawaiianEarringFacts) :
    HawaiianBasedFiberCertificate F := by
  exact
    { based_section := hawaiianObservableSection_geometric
      observable_projection_continuous :=
        continuous_hawaiianObservableGeometric
      observable_projection_quotient :=
        quotient_hawaiianObservableGeometric
      quotient_homeomorph := ⟨hawaiianObservableHomeomorph⟩
      pair_map_continuous := continuous_hawaiianBasedPairQuotientMap
      pair_map_not_quotient := hawaiianBasedPair_not_quotient F
      final_to_ordinary_bijective :=
        bijective_hawaiianBasedFinalToOrdinary
      final_to_ordinary_continuous :=
        continuous_hawaiianBasedFinalToOrdinary
      final_to_ordinary_not_quotient :=
        not_quotient_hawaiianBasedFinalToOrdinary F
      final_topology_not_induced :=
        not_agree_hawaiianBasedFinalTopology F
      final_operation_continuous :=
        continuous_hawaiianBasedFinalOperation
      ordinary_operation_not_continuous :=
        not_continuous_hawaiianBasedOrdinaryOperation F
      operation_commutes := hawaiianBasedOperation_commutes }

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

namespace HawaiianEarringObstructionTransfer

theorem not_source_quotient
    {source : Type u} {target : Type v} {arrow : Type w}
    [TopologicalSpace source] [TopologicalSpace target]
    [TopologicalSpace arrow]
    (C : HawaiianEarringObstructionTransfer source target arrow) :
    ¬ Topology.IsQuotientMap C.sourceMap := by
  intro hsource
  have hcomparison :
      Topology.IsQuotientMap (C.comparison ∘ C.sourceMap) :=
    C.comparison.isQuotientMap.comp hsource
  have hcomposite :
      Topology.IsQuotientMap
        (hawaiianPairQuotientMap ∘ C.representativeMap) := by
    rw [← C.comparison_commutes]
    exact hcomparison
  exact C.external_facts.pair_not_quotient
    (Topology.IsQuotientMap.of_comp
      C.representative_continuous continuous_hawaiianPairQuotientMap hcomposite)

theorem not_source_operation_continuous
    {source : Type u} {target : Type v} {arrow : Type w}
    [TopologicalSpace source] [TopologicalSpace target]
    [TopologicalSpace arrow]
    (C : HawaiianEarringObstructionTransfer source target arrow) :
    ¬ Continuous C.sourceOperation := by
  intro hsource
  have hcomp :
      Continuous (hawaiianLoopQuotientMultiplication ∘ C.comparison) := by
    rw [← C.operation_commutes]
    exact C.arrowComparison.continuous.comp hsource
  exact C.external_facts.multiplication_not_continuous
    (C.comparison.isQuotientMap.continuous_iff.2 hcomp)

end HawaiianEarringObstructionTransfer

abbrev GenuineCircleLoopQuotient := _root_.Path.Homotopic.Quotient (0 : AddCircle (1 : ℝ)) 0
abbrev GenuineTorusLoopQuotient :=
  _root_.Path.Homotopic.Quotient ((0 : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ)))
    ((0 : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ)))

structure AdditiveLoopClassification
    (Q : Type u) (K : Type v) [AddMonoid K]
    (compose : Q → Q → Q) (identity : Q) where
  invariant : Q → K
  standard : K → Q
  invariant_identity : invariant identity = 0
  invariant_compose : ∀ x y, invariant (compose x y) = invariant x + invariant y
  invariant_standard : ∀ k, invariant (standard k) = k
  standard_invariant : ∀ x, standard (invariant x) = x
abbrev GenuineCircleWindingClassification :=
  AdditiveLoopClassification GenuineCircleLoopQuotient Int
    _root_.Path.Homotopic.Quotient.trans
    (_root_.Path.Homotopic.Quotient.mk (_root_.Path.refl (0 : AddCircle (1 : ℝ))))
abbrev GenuineTorusWindingClassification :=
  AdditiveLoopClassification GenuineTorusLoopQuotient (Int × Int)
    _root_.Path.Homotopic.Quotient.trans
    (_root_.Path.Homotopic.Quotient.mk (_root_.Path.refl
      ((0 : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ)))))

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
  discontinuity_obstructs_compatibility :
    ¬ Continuous (ordinaryComposition P) →
      ¬ Topology.IsQuotientMap (finalToOrdinary P)
  compact_hausdorff_recovers_ordinary :
    ∀ [CompactSpace (ScopedComposableClass P)]
      [T2Space (ScopedComposablePair P)],
      Topology.IsQuotientMap (finalToOrdinary P) ∧
        Continuous (ordinaryComposition P)
  discrete_recovers_ordinary :
    ∀ [DiscreteTopology (ScopedClass P)]
      [DiscreteTopology (ScopedComposableClass P)],
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

/-! The statement and solution use the same final topology on quotient domains. -/
noncomputable instance quotientFinalTopology
    {RawPair : Type u} [TopologicalSpace RawPair] (R : Setoid RawPair) :
    TopologicalSpace (Quotient R) :=
  TopologicalSpace.coinduced (Quotient.mk R) inferInstance

structure ScopedFinalPairData
    (RawPair : Type u) (OrdinaryPair : Type v)
    (Arrow : Type w)
    [TopologicalSpace RawPair]
    [TopologicalSpace OrdinaryPair] [TopologicalSpace Arrow] where
  relation : Setoid RawPair
  comparison : Quotient relation ≃ OrdinaryPair
  rawOperation : RawPair → Arrow
  ordinaryOperation : OrdinaryPair → Arrow
  operation_respects :
    ∀ {r s : RawPair}, relation.r r s → rawOperation r = rawOperation s
  comparison_continuous : Continuous comparison
  rawOperation_continuous : Continuous rawOperation
  ordinary_factor : ∀ r,
    ordinaryOperation (comparison (Quotient.mk relation r)) = rawOperation r

namespace ScopedFinalPairData

variable {RawPair : Type u} {OrdinaryPair : Type v} {Arrow : Type w}
  [TopologicalSpace RawPair]
  [TopologicalSpace OrdinaryPair] [TopologicalSpace Arrow]
  (D : ScopedFinalPairData RawPair OrdinaryPair Arrow)

def quotient : RawPair → Quotient D.relation := Quotient.mk D.relation

noncomputable def finalOperation : Quotient D.relation → Arrow :=
  Quotient.lift D.rawOperation (by
    intro r s h
    exact D.operation_respects h)

theorem quotient_is_quotient : Topology.IsQuotientMap D.quotient := by
  exact ⟨⟨rfl⟩, Quotient.mk_surjective⟩

def pairMap : RawPair → OrdinaryPair := D.comparison ∘ D.quotient

def topologyAgreement : Prop :=
  (inferInstance : TopologicalSpace (Quotient D.relation)) =
    TopologicalSpace.induced D.comparison
      (inferInstance : TopologicalSpace OrdinaryPair)

end ScopedFinalPairData

structure ScopedFinalSemanticsCertificate
    {RawPair : Type u} {OrdinaryPair : Type v} {Arrow : Type w}
    [TopologicalSpace RawPair]
    [TopologicalSpace OrdinaryPair] [TopologicalSpace Arrow]
    (D : ScopedFinalPairData RawPair OrdinaryPair Arrow) : Prop where
  final_operation_continuous : Continuous D.finalOperation
  pair_map_quotient_iff_comparison_quotient :
    Topology.IsQuotientMap (D.pairMap) ↔
      Topology.IsQuotientMap D.comparison
  comparison_quotient_iff_inverse_continuous :
    Topology.IsQuotientMap D.comparison ↔
      Continuous D.comparison.invFun
  inverse_continuous_iff_topology_agreement :
    Continuous D.comparison.invFun ↔ D.topologyAgreement
  ordinary_operation_continuous_of_inverse :
    Continuous D.comparison.invFun → Continuous D.ordinaryOperation

open ComputationalPaths.Path.GeometricTopology.ConcreteCircleWinding
open ComputationalPaths.Path.GeometricTopology.TopologicalTorus

theorem main_result
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    (S : ContinuousGeometricStepSystem A Step)
    (P : ScopedGeometricRewritePresentation S) :
    OrdinaryTopologyComparisonCertificate S P := by
  have hBijective : Function.Bijective (finalToOrdinary P) :=
    ⟨scopedPairToOrdinary_injective P,
      scopedPairToOrdinary_surjective P⟩
  have hContinuous : Continuous (finalToOrdinary P) :=
    continuous_scopedPairToOrdinary P
  have hComposition :
      Topology.IsQuotientMap (finalToOrdinary P) →
        Continuous (ordinaryComposition P) := by
    intro h
    exact continuous_scopedCompositionOnProduct P ⟨h⟩
  exact
    { canonical_bijection := hBijective
      canonical_map_continuous := hContinuous
      raw_quotient_criterion := by
        constructor
        · intro h
          exact
            (scopedProductCompatibility_iff_raw_pair_map_quotient P).1 ⟨h⟩
        · intro h
          exact
            ((scopedProductCompatibility_iff_raw_pair_map_quotient P).2 h).pair_map_is_quotient
      homeomorphism_criterion := by
        constructor
        · intro h
          exact ⟨scopedFinalOrdinaryHomeomorph P ⟨h⟩, rfl⟩
        · rintro ⟨e, he⟩
          simpa [he] using e.isQuotientMap
      topology_agreement_criterion := by
        constructor
        · intro h
          exact
            (scopedProductCompatibility_iff_final_topology_agreement P).1 ⟨h⟩
        · intro h
          exact
            ((scopedProductCompatibility_iff_final_topology_agreement P).2 h).pair_map_is_quotient
      ordinary_composition_of_quotient := hComposition
      discontinuity_obstructs_compatibility := by
        intro hnot hquot
        exact hnot (hComposition hquot)
      compact_hausdorff_recovers_ordinary := by
        intro _ _
        let h := scopedProductCompatibility_of_compact_final_t2 P
        exact ⟨h.pair_map_is_quotient,
          continuous_scopedCompositionOnProduct P h⟩
      discrete_recovers_ordinary := by
        intro _ _
        let h :=
          scopedProductCompatibility_of_discrete_arrow_and_final_domain P
        exact ⟨h.pair_map_is_quotient,
          continuous_scopedCompositionOnProduct P h⟩
      hawaiian_earring_obstruction := by
        intro C hmap hop
        have hraw_not :
            ¬ Topology.IsQuotientMap C.sourceMap :=
          HawaiianEarringObstructionTransfer.not_source_quotient C
        have hraw :
            ¬ Topology.IsQuotientMap (rawToOrdinary P) := by
          intro hquot
          apply hraw_not
          rw [hmap]
          exact hquot
        have hfinal :
            ¬ Topology.IsQuotientMap (finalToOrdinary P) := by
          intro hquot
          apply hraw_not
          rw [hmap]
          exact
            (scopedProductCompatibility_iff_raw_pair_map_quotient P).1
              ⟨hquot⟩
        have htop :
            ¬ ((inferInstance : TopologicalSpace (ScopedComposableClass P)) =
              TopologicalSpace.induced (finalToOrdinary P)
                (inferInstance : TopologicalSpace (ScopedComposablePair P))) := by
          intro hagree
          apply hfinal
          exact
            ((scopedProductCompatibility_iff_final_topology_agreement P).2
              hagree).pair_map_is_quotient
        have hoperation_not :
            ¬ Continuous C.sourceOperation :=
          HawaiianEarringObstructionTransfer.not_source_operation_continuous C
        have hordinary : ¬ Continuous (ordinaryComposition P) := by
          intro hcontinuous
          apply hoperation_not
          rw [hop]
          exact hcontinuous
        exact ⟨hraw, hfinal, htop, hordinary⟩
      hawaiian_based_fiber := fun F =>
        hawaiianBasedFiberCertificate_of_facts F
      genuine_circle_winding := by
        exact ⟨
          { invariant := topologicalWinding
            standard := decodeTopologicalWinding
            invariant_identity := topologicalWinding_identity
            invariant_compose := topologicalWinding_comp
            invariant_standard := topologicalWinding_decode
            standard_invariant := decode_topologicalWinding }⟩
      genuine_torus_winding := by
        exact ⟨
          { invariant := encode
            standard := decode
            invariant_identity := encode_identity
            invariant_compose := encode_trans
            invariant_standard := encode_decode
            standard_invariant := decode_encode }⟩ }

/-! The substantive repository contains the scoped quotient construction.  The
 following adapter makes the statement-side interface concrete: its raw
 operation is the actual quotient-level composition map, its final operation
 is the canonical descent of that raw map, and its comparison is the actual
 final-to-ordinary equivalence. -/

noncomputable def scopedFinalPairData
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    (S : _root_.ComputationalPaths.Path.GeometricTopology.ContinuousGeometricStepSystem A Step)
    (P : _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewritePresentation S) :
    ScopedFinalPairData
      (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedComposableRaw (S := S))
      (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedComposablePair P)
      (_root_.ComputationalPaths.Path.GeometricTopology.ScopedClass P) where
  relation := _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedComposableSetoid P
  comparison := _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedPairToOrdinaryEquiv P
  rawOperation := fun c =>
    _root_.ComputationalPaths.Path.GeometricTopology.scopedQuotientMk P
      (_root_.ComputationalPaths.Path.GeometricTopology.TotalOpenGeometricCompPath.totalTrans S c)
  ordinaryOperation := _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedCompositionOnProduct P
  operation_respects := by
    intro c d h
    exact Quotient.sound
      (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedEquivalent_totalTrans
        P h.1 h.2)
  comparison_continuous :=
    _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.continuous_scopedPairToOrdinary P
  rawOperation_continuous := by
    exact _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.continuous_scopedQuotientMk P |>.comp
      (_root_.ComputationalPaths.Path.GeometricTopology.TotalOpenGeometricCompPath.continuous_totalTrans S)
  ordinary_factor := by
    intro c
    change
      _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedCompositionOnProduct P
          (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedPairToOrdinary P
            (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedComposableMk P c)) =
        _root_.ComputationalPaths.Path.GeometricTopology.scopedQuotientMk P
          (_root_.ComputationalPaths.Path.GeometricTopology.TotalOpenGeometricCompPath.totalTrans S c)
    rw [_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedCompositionOnProduct_pairMap]
    rfl

theorem scoped_final_operation_agrees
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    (S : _root_.ComputationalPaths.Path.GeometricTopology.ContinuousGeometricStepSystem A Step)
    (P : _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewritePresentation S)
    (c : _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedComposableClass P) :
    ScopedFinalPairData.finalOperation (scopedFinalPairData S P) c =
      _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedCompositionFromComposable P c := by
  refine Quotient.inductionOn c ?_
  intro c
  rfl

theorem scoped_groupoid_core_is_available :
    ∀ {A : Type u} [TopologicalSpace A]
      {Step : Type v} [TopologicalSpace Step]
      (S : _root_.ComputationalPaths.Path.GeometricTopology.ContinuousGeometricStepSystem A Step)
      (P : _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewritePresentation S),
      Nonempty (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedFinalTopologicalGroupoidCertificate P) := by
  intro A instA Step instStep S P
  exact ⟨_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedFinalTopologicalGroupoidCertificate P⟩

theorem scoped_pair_data_is_well_formed :
    ∀ {A : Type u} [TopologicalSpace A]
      {Step : Type v} [TopologicalSpace Step]
      (S : _root_.ComputationalPaths.Path.GeometricTopology.ContinuousGeometricStepSystem A Step)
      (P : _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewritePresentation S),
      Nonempty (ScopedFinalPairData
        (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedComposableRaw (S := S))
        (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedComposablePair P)
        (_root_.ComputationalPaths.Path.GeometricTopology.ScopedClass P)) := by
  intro A instA Step instStep S P
  exact ⟨scopedFinalPairData S P⟩

end TopologicalComputationalPaths
