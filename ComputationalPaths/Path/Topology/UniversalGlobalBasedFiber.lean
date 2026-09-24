import ComputationalPaths.Path.Topology.UniversalBasedFiber
import ComputationalPaths.Path.Topology.UniversalQuotientTransfer

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

end ScopedGeometricRewrite
end GeometricTopology
end Path
end ComputationalPaths
