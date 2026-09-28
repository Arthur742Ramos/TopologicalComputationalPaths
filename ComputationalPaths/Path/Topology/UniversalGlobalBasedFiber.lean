import ComputationalPaths.Path.Topology.UniversalBasedFiber
import ComputationalPaths.Path.Topology.UniversalQuotientTransfer
import ComputationalPaths.Path.Topology.ScopedGeometricRewriteFundamental

/-!
# Based paths inside the compact-open path space

The fixed-endpoint path space is the subspace of the endpoint-varying
compact-open path space cut out by the two endpoint equations. This is the
first topology comparison needed to identify the based fiber of the global
universal quotient.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology
namespace ScopedGeometricRewrite

open scoped ContinuousMap Topology
attribute [local instance] _root_.Path.Homotopic.setoid

variable {A : Type*} [TopologicalSpace A]

def universalBasedPathSet (x : A) : Set (ContinuousPathStep A) :=
  {γ | γ 0 = x ∧ γ 1 = x}

noncomputable def basedPathSubspaceHomeomorph (x : A) :
    _root_.Path x x ≃ₜ universalBasedPathSet x where
  toFun γ := ⟨γ.toContinuousMap, ⟨γ.source, γ.target⟩⟩
  invFun γ := _root_.Path.mk γ.val γ.property.1 γ.property.2
  left_inv γ := by
    apply _root_.Path.ext
    funext t
    rfl
  right_inv γ := by
    apply Subtype.ext
    rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_induced_dom
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    exact continuous_subtype_val

def universalBasedArrowSet (x : A) :
    Set (ScopedClass (universalPresentation (A := A))) :=
  {c | scopedSrc (universalPresentation (A := A)) c = x ∧
    scopedTgt (universalPresentation (A := A)) c = x}

theorem universalBasedArrow_preimage (x : A) :
    universalPathClassProjection (A := A) ⁻¹' universalBasedArrowSet x =
      universalBasedPathSet x := by
  ext γ
  simp [universalBasedArrowSet, universalBasedPathSet,
    universalPathClassProjection, universalTraceSensitiveChoice]

/-- Under an open-map hypothesis, restricting the global quotient to its
based arrow subspace remains an open quotient. -/
theorem universalBasedRestricted_isOpenQuotient (x : A)
    (hopen : IsOpenMap (universalPathClassProjection (A := A))) :
    IsOpenQuotientMap
      ((universalBasedArrowSet x).restrictPreimage
        (universalPathClassProjection (A := A))) := by
  have hq : IsOpenQuotientMap (universalPathClassProjection (A := A)) :=
    { surjective := universalPathClassProjection_surjective (A := A)
      continuous := continuous_universalPathClassProjection (A := A)
      isOpenMap := hopen }
  exact hq.restrictPreimage _

noncomputable def basedPathPreimageHomeomorph (x : A) :
    _root_.Path x x ≃ₜ
      (universalPathClassProjection (A := A) ⁻¹' universalBasedArrowSet x) :=
  (basedPathSubspaceHomeomorph x).trans
    (Homeomorph.setCongr (universalBasedArrow_preimage x).symm)

noncomputable def basedGlobalProjection (x : A) :
    _root_.Path x x → universalBasedArrowSet x :=
  (universalBasedArrowSet x).restrictPreimage
    (universalPathClassProjection (A := A)) ∘
      basedPathPreimageHomeomorph x

theorem basedGlobalProjection_isOpenQuotient (x : A)
    (hopen : IsOpenMap (universalPathClassProjection (A := A))) :
    IsOpenQuotientMap (basedGlobalProjection x) := by
  let e := basedPathPreimageHomeomorph x
  have h := universalBasedRestricted_isOpenQuotient x hopen
  exact ⟨h.surjective.comp e.surjective,
    h.continuous.comp e.continuous,
    h.isOpenMap.comp e.isOpenMap⟩

theorem basedGlobalProjection_val (x : A) (γ : _root_.Path x x) :
    (basedGlobalProjection x γ).val =
      universalPathClassProjection (A := A) γ.toContinuousMap := rfl

private theorem fundamentalArrowCode_cast {a b a' b' : A}
    (ha : a = a') (hb : b = b')
    (q : _root_.Path.Homotopic.Quotient a b) :
    (⟨a, b, q⟩ : FundamentalArrowCode A) =
      ⟨a', b', q.cast ha.symm hb.symm⟩ := by
  cases ha
  cases hb
  simp

theorem basedGlobalProjection_code (x : A) (γ : _root_.Path x x) :
    (universalRealizedFundamentalArrowHomeomorph (A := A)
      (basedGlobalProjection x γ).val).val =
      (⟨x, x, Quotient.mk' γ⟩ : FundamentalArrowCode A) := by
  change TotalOpenGeometricCompPath.totalCode
    (continuousPathStepSystem A)
    (universalTraceSensitiveChoice (A := A) γ.toContinuousMap) = _
  let p : _root_.Path (γ 0) (γ 1) :=
    (continuousPathStep γ.toContinuousMap).geometric
  change (⟨γ 0, γ 1, Quotient.mk' p⟩ : FundamentalArrowCode A) =
    ⟨x, x, Quotient.mk' γ⟩
  rw [fundamentalArrowCode_cast γ.source γ.target]
  have hpath : p.cast γ.source.symm γ.target.symm = γ := by
    apply _root_.Path.ext
    funext t
    rfl
  have hq : (_root_.Path.Homotopic.Quotient.mk p).cast
      γ.source.symm γ.target.symm =
        _root_.Path.Homotopic.Quotient.mk γ := by
    rw [← _root_.Path.Homotopic.Quotient.mk_cast, hpath]
  exact _root_.congrArg (fun q : _root_.Path.Homotopic.Quotient x x =>
    (⟨x, x, q⟩ : FundamentalArrowCode A)) hq

theorem basedGlobalProjection_eq_iff (x : A)
    (γ δ : _root_.Path x x) :
    basedGlobalProjection x γ = basedGlobalProjection x δ ↔
      _root_.Path.Homotopic γ δ := by
  constructor
  · intro h
    have hcode :
        (⟨x, x, Quotient.mk' γ⟩ : FundamentalArrowCode A) =
          ⟨x, x, Quotient.mk' δ⟩ := by
      rw [← basedGlobalProjection_code x γ,
        ← basedGlobalProjection_code x δ]
      exact _root_.congrArg (fun c : ScopedClass
        (universalPresentation (A := A)) =>
        (universalRealizedFundamentalArrowHomeomorph (A := A) c).val)
        (_root_.congrArg Subtype.val h)
    have hrest :
        (⟨x, Quotient.mk' γ⟩ :
          Σ y : A, _root_.Path.Homotopic.Quotient x y) =
        ⟨x, Quotient.mk' δ⟩ := by
      exact eq_of_heq (Sigma.ext_iff.mp hcode).2
    have hq : Quotient.mk' γ = Quotient.mk' δ := by
      exact eq_of_heq (Sigma.ext_iff.mp hrest).2
    exact Quotient.exact hq
  · intro h
    apply Subtype.ext
    apply (universalRealizedFundamentalArrowHomeomorph
      (A := A)).injective
    apply Subtype.ext
    rw [basedGlobalProjection_code, basedGlobalProjection_code]
    exact _root_.congrArg (fun q : _root_.Path.Homotopic.Quotient x x =>
      (⟨x, x, q⟩ : FundamentalArrowCode A)) (Quotient.sound h)

noncomputable def basedGlobalClassMap (x : A) :
    QuotientFundamentalGroup.LoopQuot A x → universalBasedArrowSet x :=
  Quotient.lift (basedGlobalProjection x)
    (fun γ δ h => (basedGlobalProjection_eq_iff x γ δ).2 h)

theorem basedGlobalClassMap_mk (x : A) (γ : _root_.Path x x) :
    basedGlobalClassMap x (Quotient.mk' γ) =
      basedGlobalProjection x γ := rfl

theorem basedGlobalClassMap_injective (x : A) :
    Function.Injective (basedGlobalClassMap x) := by
  intro q r h
  revert h
  refine Quotient.inductionOn₂ q r ?_
  intro γ δ h
  exact Quotient.sound ((basedGlobalProjection_eq_iff x γ δ).1 h)

theorem basedGlobalClassMap_surjective (x : A)
    (hopen : IsOpenMap (universalPathClassProjection (A := A))) :
    Function.Surjective (basedGlobalClassMap x) := by
  intro c
  rcases (basedGlobalProjection_isOpenQuotient x hopen).surjective c with ⟨γ, rfl⟩
  exact ⟨Quotient.mk' γ, rfl⟩

theorem continuous_basedGlobalClassMap (x : A)
    (hopen : IsOpenMap (universalPathClassProjection (A := A))) :
    Continuous (basedGlobalClassMap x) := by
  apply Continuous.quotient_lift
  exact (basedGlobalProjection_isOpenQuotient x hopen).continuous

theorem isOpenMap_basedGlobalClassMap (x : A)
    (hopen : IsOpenMap (universalPathClassProjection (A := A))) :
    IsOpenMap (basedGlobalClassMap x) := by
  intro s hs
  have hpre : IsOpen ((Quotient.mk' : _root_.Path x x →
      QuotientFundamentalGroup.LoopQuot A x) ⁻¹' s) :=
    continuous_quotient_mk'.isOpen_preimage s hs
  have himage : basedGlobalClassMap x '' s =
      basedGlobalProjection x ''
        ((Quotient.mk' : _root_.Path x x →
          QuotientFundamentalGroup.LoopQuot A x) ⁻¹' s) := by
    ext c
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine Quotient.inductionOn q ?_ hq
      intro γ hγ
      exact ⟨γ, hγ, rfl⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨Quotient.mk' γ, hγ, rfl⟩
  rw [himage]
  exact (basedGlobalProjection_isOpenQuotient x hopen).isOpenMap _ hpre

noncomputable def basedGlobalFiberHomeomorph (x : A)
    (hopen : IsOpenMap (universalPathClassProjection (A := A))) :
    QuotientFundamentalGroup.LoopQuot A x ≃ₜ universalBasedArrowSet x where
  toEquiv := Equiv.ofBijective (basedGlobalClassMap x)
    ⟨basedGlobalClassMap_injective x,
      basedGlobalClassMap_surjective x hopen⟩
  continuous_toFun := continuous_basedGlobalClassMap x hopen
  continuous_invFun := by
    let e : QuotientFundamentalGroup.LoopQuot A x ≃
        universalBasedArrowSet x := Equiv.ofBijective (basedGlobalClassMap x)
          ⟨basedGlobalClassMap_injective x,
            basedGlobalClassMap_surjective x hopen⟩
    change Continuous e.symm
    exact (Equiv.continuous_symm_iff e).2
      (isOpenMap_basedGlobalClassMap x hopen)

theorem basedGlobalFiber_discrete (x : A)
    [LocallyPathConnectedSpace A]
    (hsemi : QuotientFundamentalGroup.SemilocallySimplyConnected A)
    (hopen : IsOpenMap (universalPathClassProjection (A := A))) :
    DiscreteTopology (universalBasedArrowSet x) := by
  letI := QuotientFundamentalGroup.quotientDiscreteTopology_of_semilocallySimplyConnected
    A hsemi x
  let e := basedGlobalFiberHomeomorph x hopen
  exact DiscreteTopology.of_continuous_injective
    e.symm.continuous e.symm.injective

end ScopedGeometricRewrite
end GeometricTopology
end Path
end ComputationalPaths
