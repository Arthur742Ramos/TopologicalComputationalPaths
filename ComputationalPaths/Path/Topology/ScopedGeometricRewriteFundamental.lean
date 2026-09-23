import ComputationalPaths.Path.Topology.ScopedGeometricRewriteComparison
import ComputationalPaths.Path.Topology.TopologicalCompPathFundamentalGroupoid
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# The realized fundamental-groupoid arrow carrier

The scoped comparison initially lands in the quotient of realized open paths.
This file identifies that quotient with an explicit realized arrow carrier:
the range of the endpoint-and-homotopy code in the fundamental groupoid.  The
range is given its quotient topology from raw open paths, so the identification
is a homeomorphism rather than only a bijection of types.

The carrier also has a direct map into Mathlib's fundamental-groupoid hom types.
For the universal continuous-path presentation, every fundamental-groupoid
arrow is represented, and the universal scoped quotient is homeomorphic to the
realized carrier.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open CategoryTheory
open scoped ContinuousMap FundamentalGroupoid Topology

attribute [local instance] _root_.Path.Homotopic.setoid

universe u v

namespace ScopedGeometricRewrite

open TotalOpenGeometricCompPath

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  {S : ContinuousGeometricStepSystem A Step}
  {P : ScopedGeometricRewritePresentation S}

/-! ## The explicit realized arrow space -/

abbrev FundamentalArrowCode (A : Type u) [TopologicalSpace A] :=
  TotalPathCode A

abbrev RealizedFundamentalArrow (S : ContinuousGeometricStepSystem A Step) :=
  Set.range (fun p : ScopedRawPath (S := S) => totalCode S p)

noncomputable def realizedFundamentalArrowMk
    (p : ScopedRawPath (S := S)) : RealizedFundamentalArrow S :=
  ⟨totalCode S p, ⟨p, rfl⟩⟩

noncomputable instance realizedFundamentalArrowTopologicalSpace :
    TopologicalSpace (RealizedFundamentalArrow S) :=
  TopologicalSpace.coinduced (realizedFundamentalArrowMk (S := S)) inferInstance

theorem realizedFundamentalArrowMk_surjective :
    Function.Surjective (realizedFundamentalArrowMk (S := S) :
      ScopedRawPath (S := S) → RealizedFundamentalArrow S) := by
  intro x
  rcases x.property with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  exact hp

theorem realizedFundamentalArrowMk_isQuotient :
    Topology.IsQuotientMap (realizedFundamentalArrowMk (S := S) :
      ScopedRawPath (S := S) → RealizedFundamentalArrow S) :=
  ⟨⟨rfl⟩, realizedFundamentalArrowMk_surjective⟩

theorem totalQuotientMk_surjective :
    Function.Surjective (totalQuotientMk S :
      ScopedRawPath (S := S) → TotalHomotopyClass S) := by
  intro x
  refine Quot.inductionOn x ?_
  intro p
  exact ⟨p, rfl⟩

theorem totalQuotientMk_isQuotient :
    Topology.IsQuotientMap (totalQuotientMk S :
      ScopedRawPath (S := S) → TotalHomotopyClass S) :=
  ⟨⟨rfl⟩, totalQuotientMk_surjective (S := S)⟩

noncomputable def totalClassToRealizedFundamentalArrow :
    TotalHomotopyClass S → RealizedFundamentalArrow S :=
  Quotient.lift
    (realizedFundamentalArrowMk (S := S))
    (by
      intro p q h
      apply Subtype.ext
      exact h)

@[simp] theorem totalClassToRealizedFundamentalArrow_mk
    (p : ScopedRawPath (S := S)) :
    totalClassToRealizedFundamentalArrow (S := S) (totalQuotientMk S p) =
      realizedFundamentalArrowMk (S := S) p :=
  rfl

noncomputable def realizedFundamentalArrowToTotalClass :
    RealizedFundamentalArrow S → TotalHomotopyClass S :=
  fun x => totalQuotientMk S (Classical.choose x.property)

theorem realizedFundamentalArrowToTotalClass_mk
    (p : ScopedRawPath (S := S)) :
    realizedFundamentalArrowToTotalClass (S := S)
        (realizedFundamentalArrowMk (S := S) p) =
      totalQuotientMk S p := by
  apply Quotient.sound
  exact Classical.choose_spec
    (realizedFundamentalArrowMk (S := S) p).property

theorem realizedFundamentalArrowToTotalClass_toRealized
    (x : RealizedFundamentalArrow S) :
    totalClassToRealizedFundamentalArrow (S := S)
        (realizedFundamentalArrowToTotalClass (S := S) x) = x := by
  apply Subtype.ext
  exact Classical.choose_spec x.property

theorem continuous_totalClassToRealizedFundamentalArrow :
    Continuous (totalClassToRealizedFundamentalArrow (S := S) :
      TotalHomotopyClass S → RealizedFundamentalArrow S) := by
  apply (totalQuotientMk_isQuotient (S := S)).continuous_iff.2
  rw [show totalClassToRealizedFundamentalArrow (S := S) ∘
      totalQuotientMk S = realizedFundamentalArrowMk (S := S) by
    funext p
    rfl]
  exact continuous_coinduced_rng

theorem continuous_realizedFundamentalArrowToTotalClass :
    Continuous (realizedFundamentalArrowToTotalClass (S := S) :
      RealizedFundamentalArrow S → TotalHomotopyClass S) := by
  apply (realizedFundamentalArrowMk_isQuotient (S := S)).continuous_iff.2
  rw [show realizedFundamentalArrowToTotalClass (S := S) ∘
      realizedFundamentalArrowMk (S := S) = totalQuotientMk S by
    funext p
    exact realizedFundamentalArrowToTotalClass_mk (S := S) p]
  exact continuous_totalQuotientMk S

noncomputable def realizedFundamentalArrowHomeomorph :
    TotalHomotopyClass S ≃ₜ RealizedFundamentalArrow S where
  toEquiv :=
    { toFun := totalClassToRealizedFundamentalArrow (S := S)
      invFun := realizedFundamentalArrowToTotalClass (S := S)
      left_inv := by
        intro x
        refine Quotient.inductionOn x ?_
        intro p
        exact realizedFundamentalArrowToTotalClass_mk (S := S) p
      right_inv := realizedFundamentalArrowToTotalClass_toRealized (S := S) }
  continuous_toFun := continuous_totalClassToRealizedFundamentalArrow (S := S)
  continuous_invFun := continuous_realizedFundamentalArrowToTotalClass (S := S)

/-! ## Direct fundamental-groupoid interpretation -/

noncomputable def fundamentalGroupoidArrowOfCode
    (c : FundamentalArrowCode A) :
    Σ a : A, Σ b : A,
      (FundamentalGroupoid.fromTop (X := TopCat.of A) a ⟶
        FundamentalGroupoid.fromTop (X := TopCat.of A) b) := by
  rcases c with ⟨a, b, q⟩
  exact ⟨a, b, q⟩

noncomputable def fundamentalGroupoidHomOfCode
    (c : FundamentalArrowCode A) :
    FundamentalGroupoid.fromTop (X := TopCat.of A) c.1 ⟶
      FundamentalGroupoid.fromTop (X := TopCat.of A) c.2.1 := by
  rcases c with ⟨a, b, q⟩
  exact q

noncomputable def realizedFundamentalGroupoidArrow
    (x : RealizedFundamentalArrow S) :
    Σ a : A, Σ b : A,
      (FundamentalGroupoid.fromTop (X := TopCat.of A) a ⟶
        FundamentalGroupoid.fromTop (X := TopCat.of A) b) := by
  exact fundamentalGroupoidArrowOfCode x.1

/-! ## Ambient groupoid operations and computational witnesses -/

theorem fundamentalGroupoidArrowOfCode_totalCode
    (p : ScopedRawPath (S := S)) :
    fundamentalGroupoidHomOfCode (totalCode S p) =
      TotalOpenGeometricCompPath.fundamentalArrow S p :=
  rfl

theorem fundamentalGroupoidArrowOfCode_totalRefl (a : A) :
    fundamentalGroupoidHomOfCode (totalCode S
        (TotalOpenGeometricCompPath.totalRefl S a)) =
      𝟙 (FundamentalGroupoid.fromTop (X := TopCat.of A) a) := by
  exact TotalOpenGeometricCompPath.fundamentalArrow_totalRefl S a

theorem fundamentalGroupoidArrowOfCode_totalSymm
    (p : ScopedRawPath (S := S)) :
    fundamentalGroupoidHomOfCode (totalCode S
        (TotalOpenGeometricCompPath.totalSymm S p)) =
      CategoryTheory.Groupoid.inv
        (fundamentalGroupoidHomOfCode (totalCode S p)) := by
  rw [fundamentalGroupoidArrowOfCode_totalCode,
    fundamentalGroupoidArrowOfCode_totalCode]
  rw [TotalOpenGeometricCompPath.fundamentalArrow_totalSymm]
  rfl

theorem fundamentalGroupoidArrowOfCode_totalTrans
    (c : ScopedComposableRaw (S := S)) :
    fundamentalGroupoidHomOfCode (totalCode S
        (TotalOpenGeometricCompPath.totalTrans S c)) =
      fundamentalGroupoidHomOfCode (totalCode S
        (TotalOpenGeometricCompPath.leftTotal S c)) ≫
        fundamentalGroupoidHomOfCode (totalCode S
          (TotalOpenGeometricCompPath.rightTotal S c)) := by
  rw [fundamentalGroupoidArrowOfCode_totalCode,
    fundamentalGroupoidArrowOfCode_totalCode,
    fundamentalGroupoidArrowOfCode_totalCode]
  exact TotalOpenGeometricCompPath.fundamentalArrow_totalTrans S c

noncomputable def realizedFundamentalArrowTraceLengthPath
    (p : ScopedRawPath (S := S)) :
    ComputationalPaths.Path
      (GeometricTrace.traceLength p.trace)
      (GeometricTrace.traceLength p.trace) :=
  ComputationalPaths.Path.trans
    (ComputationalPaths.Path.refl (GeometricTrace.traceLength p.trace))
    (ComputationalPaths.Path.refl (GeometricTrace.traceLength p.trace))

noncomputable def realizedFundamentalArrowUnitRewrite (n : Nat) :
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl n)
        (ComputationalPaths.Path.refl n))
      (ComputationalPaths.Path.refl n) :=
  ComputationalPaths.Path.RwEq.step
    (ComputationalPaths.Path.Step.trans_refl_right
      (ComputationalPaths.Path.refl n))

theorem realizedFundamentalGroupoidArrow_eq_code
    (x : RealizedFundamentalArrow S) :
    realizedFundamentalGroupoidArrow (S := S) x =
      fundamentalGroupoidArrowOfCode x.1 :=
  rfl

theorem realizedFundamentalGroupoidArrow_src
    (x : RealizedFundamentalArrow S) :
    (realizedFundamentalGroupoidArrow (S := S) x).1 =
      (x.1).1 := by
  rcases x with ⟨⟨a, b, q⟩, hx⟩
  rfl

theorem realizedFundamentalGroupoidArrow_tgt
    (x : RealizedFundamentalArrow S) :
    (realizedFundamentalGroupoidArrow (S := S) x).2.1 =
      (x.1).2.1 := by
  rcases x with ⟨⟨a, b, q⟩, hx⟩
  rfl

/-! ## The presentation-specific realized subgroupoid carrier -/

noncomputable def presentationRealizedFundamentalArrow
    (P : ScopedGeometricRewritePresentation S) :
    ScopedClass P → RealizedFundamentalArrow S :=
  fun x => totalClassToRealizedFundamentalArrow (S := S)
    (toGeometricClass P x)

abbrev PresentedRealizedFundamentalArrow
    (P : ScopedGeometricRewritePresentation S) :=
  Set.range (presentationRealizedFundamentalArrow P)

noncomputable def comparisonToPresentedRealizedFundamentalArrow
    (P : ScopedGeometricRewritePresentation S) :
    ScopedClass P → PresentedRealizedFundamentalArrow P :=
  fun x => ⟨presentationRealizedFundamentalArrow P x, ⟨x, rfl⟩⟩

theorem continuous_presentationRealizedFundamentalArrow
    (P : ScopedGeometricRewritePresentation S) :
    Continuous (presentationRealizedFundamentalArrow P :
      ScopedClass P → RealizedFundamentalArrow S) :=
  (continuous_totalClassToRealizedFundamentalArrow (S := S)).comp
    (continuous_toGeometricClass P)

theorem continuous_comparisonToPresentedRealizedFundamentalArrow
    (P : ScopedGeometricRewritePresentation S) :
    Continuous (comparisonToPresentedRealizedFundamentalArrow P :
      ScopedClass P → PresentedRealizedFundamentalArrow P) := by
  exact (continuous_presentationRealizedFundamentalArrow P).subtype_mk
    (fun x => ⟨x, rfl⟩)

theorem comparisonToPresentedRealizedFundamentalArrow_surjective
    (P : ScopedGeometricRewritePresentation S) :
    Function.Surjective (comparisonToPresentedRealizedFundamentalArrow P :
      ScopedClass P → PresentedRealizedFundamentalArrow P) := by
  intro x
  rcases x.property with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  exact hy

theorem comparisonToPresentedRealizedFundamentalArrow_coe
    (P : ScopedGeometricRewritePresentation S) (x : ScopedClass P) :
    (comparisonToPresentedRealizedFundamentalArrow P x).1 =
      presentationRealizedFundamentalArrow P x :=
  rfl

theorem presentationRealizedFundamentalArrow_mk
    (P : ScopedGeometricRewritePresentation S)
    (p : ScopedRawPath (S := S)) :
    presentationRealizedFundamentalArrow P
        (scopedQuotientMk P p) =
      realizedFundamentalArrowMk (S := S) p := by
  rfl

theorem presentationRealizedFundamentalArrow_refl
    (P : ScopedGeometricRewritePresentation S) (a : A) :
    presentationRealizedFundamentalArrow P (scopedRefl P a) =
      realizedFundamentalArrowMk (S := S)
        (TotalOpenGeometricCompPath.totalRefl S a) := by
  rfl

theorem presentationRealizedFundamentalArrow_symm
    (P : ScopedGeometricRewritePresentation S)
    (p : ScopedRawPath (S := S)) :
    presentationRealizedFundamentalArrow P
        (scopedSymm P (scopedQuotientMk P p)) =
      realizedFundamentalArrowMk (S := S)
        (TotalOpenGeometricCompPath.totalSymm S p) := by
  rfl

theorem presentationRealizedFundamentalArrow_trans
    (P : ScopedGeometricRewritePresentation S)
    (c : ScopedComposableRaw (S := S)) :
    presentationRealizedFundamentalArrow P
        (scopedCompositionFromComposable P (scopedComposableMk P c)) =
      realizedFundamentalArrowMk (S := S)
        (TotalOpenGeometricCompPath.totalTrans S c) := by
  rfl

theorem presentedRealizedFundamentalArrow_identity_mem
    (P : ScopedGeometricRewritePresentation S) (a : A) :
    realizedFundamentalArrowMk (S := S)
        (TotalOpenGeometricCompPath.totalRefl S a) ∈
      PresentedRealizedFundamentalArrow P := by
  exact ⟨scopedRefl P a, presentationRealizedFundamentalArrow_refl P a⟩

theorem presentedRealizedFundamentalArrow_reversal_mem
    (P : ScopedGeometricRewritePresentation S)
    (p : ScopedRawPath (S := S)) :
    realizedFundamentalArrowMk (S := S)
        (TotalOpenGeometricCompPath.totalSymm S p) ∈
      PresentedRealizedFundamentalArrow P := by
  exact ⟨scopedSymm P (scopedQuotientMk P p),
    presentationRealizedFundamentalArrow_symm P p⟩

theorem presentedRealizedFundamentalArrow_composition_mem
    (P : ScopedGeometricRewritePresentation S)
    (c : ScopedComposableRaw (S := S)) :
    realizedFundamentalArrowMk (S := S)
        (TotalOpenGeometricCompPath.totalTrans S c) ∈
      PresentedRealizedFundamentalArrow P := by
  exact ⟨scopedCompositionFromComposable P (scopedComposableMk P c),
    presentationRealizedFundamentalArrow_trans P c⟩

/-! ## Universal completeness and the full fundamental-groupoid carrier -/

theorem universalGeometricCompleteness :
    GeometricCompleteness (universalPresentation (A := A)) := by
  intro p q h
  exact (universalScopedEquivalent_iff_totalEquivalent (A := A)).2 h

noncomputable def universalRealizedFundamentalArrowHomeomorph :
    ScopedClass (universalPresentation (A := A)) ≃ₜ
      RealizedFundamentalArrow (continuousPathStepSystem A) :=
  (comparisonHomeomorph_of_complete
      (universalPresentation (A := A)) universalGeometricCompleteness).trans
    (realizedFundamentalArrowHomeomorph
      (S := continuousPathStepSystem A))

theorem universalRealizedFundamentalArrow_code_surjective :
    Function.Surjective (fun x : RealizedFundamentalArrow
      (continuousPathStepSystem A) => x.1) := by
  intro c
  rcases c with ⟨a, b, q⟩
  refine Quotient.inductionOn q ?_
  intro γ
  refine ⟨realizedFundamentalArrowMk
      (S := continuousPathStepSystem A)
      ⟨a, b, UniversalCompPathHomotopyEquivalence.universalOpenSection γ⟩,
    ?_⟩
  rfl

noncomputable def universalRealizedFundamentalArrowCodeEquiv :
    RealizedFundamentalArrow (continuousPathStepSystem A) ≃
      FundamentalArrowCode A :=
  Equiv.ofBijective (fun x : RealizedFundamentalArrow
      (continuousPathStepSystem A) => x.1)
    ⟨fun _ _ h => Subtype.ext h,
      universalRealizedFundamentalArrow_code_surjective (A := A)⟩

structure RealizedFundamentalGroupoidCertificate
    (P : ScopedGeometricRewritePresentation S) where
  arrow_continuous : Continuous (presentationRealizedFundamentalArrow P)
  arrow_surjective : Function.Surjective
    (comparisonToPresentedRealizedFundamentalArrow P)
  ambient_identity : ∀ a : A,
    fundamentalGroupoidHomOfCode (totalCode S
        (TotalOpenGeometricCompPath.totalRefl S a)) =
      𝟙 (FundamentalGroupoid.fromTop (X := TopCat.of A) a)
  ambient_reversal : ∀ p : ScopedRawPath (S := S),
    fundamentalGroupoidHomOfCode (totalCode S
        (TotalOpenGeometricCompPath.totalSymm S p)) =
      CategoryTheory.Groupoid.inv
        (fundamentalGroupoidHomOfCode (totalCode S p))
  ambient_composition : ∀ c : ScopedComposableRaw (S := S),
    fundamentalGroupoidHomOfCode (totalCode S
        (TotalOpenGeometricCompPath.totalTrans S c)) =
      fundamentalGroupoidHomOfCode (totalCode S
        (TotalOpenGeometricCompPath.leftTotal S c)) ≫
        fundamentalGroupoidHomOfCode (totalCode S
          (TotalOpenGeometricCompPath.rightTotal S c))
  presented_identity : ∀ a : A,
    presentationRealizedFundamentalArrow P (scopedRefl P a) =
      realizedFundamentalArrowMk (S := S)
        (TotalOpenGeometricCompPath.totalRefl S a)
  presented_reversal : ∀ p : ScopedRawPath (S := S),
    presentationRealizedFundamentalArrow P
        (scopedSymm P (scopedQuotientMk P p)) =
      realizedFundamentalArrowMk (S := S)
        (TotalOpenGeometricCompPath.totalSymm S p)
  presented_composition : ∀ c : ScopedComposableRaw (S := S),
    presentationRealizedFundamentalArrow P
        (scopedCompositionFromComposable P (scopedComposableMk P c)) =
      realizedFundamentalArrowMk (S := S)
        (TotalOpenGeometricCompPath.totalTrans S c)
  presented_identity_mem : ∀ a : A,
    realizedFundamentalArrowMk (S := S)
        (TotalOpenGeometricCompPath.totalRefl S a) ∈
      PresentedRealizedFundamentalArrow P
  presented_reversal_mem : ∀ p : ScopedRawPath (S := S),
    realizedFundamentalArrowMk (S := S)
        (TotalOpenGeometricCompPath.totalSymm S p) ∈
      PresentedRealizedFundamentalArrow P
  presented_composition_mem : ∀ c : ScopedComposableRaw (S := S),
    realizedFundamentalArrowMk (S := S)
        (TotalOpenGeometricCompPath.totalTrans S c) ∈
      PresentedRealizedFundamentalArrow P
  trace_length_path : ∀ p : ScopedRawPath (S := S),
    ComputationalPaths.Path
      (GeometricTrace.traceLength p.trace)
      (GeometricTrace.traceLength p.trace)
  trace_unit_rewrite : ∀ n : Nat,
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl n)
        (ComputationalPaths.Path.refl n))
      (ComputationalPaths.Path.refl n)
  ambient_arrow : ∀ x : ScopedClass P,
    realizedFundamentalGroupoidArrow
      (S := S) (presentationRealizedFundamentalArrow P x) =
      fundamentalGroupoidArrowOfCode
        (presentationRealizedFundamentalArrow P x).1

noncomputable def realizedFundamentalGroupoidCertificate
    (P : ScopedGeometricRewritePresentation S) :
    RealizedFundamentalGroupoidCertificate P where
  arrow_continuous := continuous_presentationRealizedFundamentalArrow P
  arrow_surjective := comparisonToPresentedRealizedFundamentalArrow_surjective P
  ambient_identity := fundamentalGroupoidArrowOfCode_totalRefl (S := S)
  ambient_reversal := fundamentalGroupoidArrowOfCode_totalSymm (S := S)
  ambient_composition := fundamentalGroupoidArrowOfCode_totalTrans (S := S)
  presented_identity := presentationRealizedFundamentalArrow_refl (S := S) P
  presented_reversal := presentationRealizedFundamentalArrow_symm (S := S) P
  presented_composition := presentationRealizedFundamentalArrow_trans (S := S) P
  presented_identity_mem := presentedRealizedFundamentalArrow_identity_mem (S := S) P
  presented_reversal_mem := presentedRealizedFundamentalArrow_reversal_mem (S := S) P
  presented_composition_mem :=
    presentedRealizedFundamentalArrow_composition_mem (S := S) P
  trace_length_path := realizedFundamentalArrowTraceLengthPath (S := S)
  trace_unit_rewrite := realizedFundamentalArrowUnitRewrite
  ambient_arrow := fun x =>
    realizedFundamentalGroupoidArrow_eq_code
      (S := S) (presentationRealizedFundamentalArrow P x)

end ScopedGeometricRewrite
end GeometricTopology
end Path
end ComputationalPaths
