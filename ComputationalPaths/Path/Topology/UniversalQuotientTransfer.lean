import ComputationalPaths.Path.Topology.TraceSensitiveUniversalCollapse
import ComputationalPaths.Path.Topology.ScopedGeometricRewriteGroupoid
import ComputationalPaths.Path.Topology.SectionOpenQuotient

/-!
# The compact-open path projection and the universal scoped quotient

The endpoint-varying continuous-path space has a continuous one-letter
section into the universal raw carrier.  The resulting map to the scoped
quotient is continuous and surjective, and the raw quotient factors through
the geometric-path projection.  These are the ingredients for transporting
an open-map hypothesis on path classes to the ordinary composable-pair map.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology
namespace ScopedGeometricRewrite

open scoped ContinuousMap Topology

variable {A : Type*} [TopologicalSpace A]

noncomputable def universalPathClassProjection :
    ContinuousPathStep A → ScopedClass (universalPresentation (A := A)) :=
  scopedQuotientMk (universalPresentation (A := A)) ∘
    universalTraceSensitiveChoice (A := A)

theorem continuous_universalTraceSensitiveChoice_observable :
    Continuous (universalTraceSensitiveChoice (A := A) :
      ContinuousPathStep A →
        ScopedRawPath (S := continuousPathStepSystem A)) := by
    have h := @Continuous.comp (ContinuousPathStep A)
      (ScopedRawPath (S := continuousPathStepSystem A))
      (ScopedRawPath (S := continuousPathStepSystem A))
      inferInstance
      (TotalOpenGeometricCompPath.traceSensitiveTopologicalSpace
        (continuousPathStepSystem A)) inferInstance
      (universalTraceSensitiveChoice (A := A)) id
      (TotalOpenGeometricCompPath.continuous_traceSensitive_to_observable
        (continuousPathStepSystem A))
      (continuous_universalTraceSensitiveChoice (A := A))
    simpa [Function.comp_def] using h

theorem continuous_universalPathClassProjection :
    Continuous (universalPathClassProjection (A := A)) := by
  exact (continuous_scopedQuotientMk (universalPresentation (A := A))).comp
    (continuous_universalTraceSensitiveChoice_observable (A := A))

theorem universalPathClassProjection_factor
    (p : ScopedRawPath (S := continuousPathStepSystem A)) :
    universalPathClassProjection (A := A)
      (universalChosenGeometricPath (A := A) p) =
      scopedQuotientMk (universalPresentation (A := A)) p :=
  universalTraceSensitiveChoice_factor (A := A) p

theorem universalPathClassProjection_surjective :
    Function.Surjective (universalPathClassProjection (A := A)) := by
  intro q
  rcases scopedQuotientMk_surjective (universalPresentation (A := A)) q
    with ⟨p, rfl⟩
  exact ⟨universalChosenGeometricPath (A := A) p,
    universalPathClassProjection_factor p⟩

/-- The universal scoped arrow topology is already final for the
compact-open continuous-path projection. -/
theorem universalPathClassProjection_isQuotient :
    Topology.IsQuotientMap (universalPathClassProjection (A := A)) := by
  have hcomp :
      universalPathClassProjection (A := A) ∘
        universalChosenGeometricPath (A := A) =
        scopedQuotientMk (universalPresentation (A := A)) := by
    funext p
    exact universalPathClassProjection_factor p
  have hq := scopedQuotientMk_isQuotient (universalPresentation (A := A))
  rw [← hcomp] at hq
  exact Topology.IsQuotientMap.of_comp
    (continuous_universalChosenGeometricPath (A := A))
    (continuous_universalPathClassProjection (A := A)) hq

/-- If the compact-open path-class map is open, the universal scoped
presentation has ordinary product-quotient compatibility. -/
theorem universalProductCompatibility_of_open_path_projection
    (hopen : IsOpenMap (universalPathClassProjection (A := A))) :
    ProductQuotientCompatibility (universalPresentation (A := A)) := by
  let P := universalPresentation (A := A)
  let S := continuousPathStepSystem A
  let C : Set (ScopedClass P × ScopedClass P) :=
    {pq | scopedTgt P pq.1 = scopedSrc P pq.2}
  have hq : IsOpenQuotientMap (universalPathClassProjection (A := A)) :=
    { surjective := universalPathClassProjection_surjective (A := A)
      continuous := continuous_universalPathClassProjection (A := A)
      isOpenMap := hopen }
  have hsection : ∀ γ : ContinuousPathStep A,
      universalChosenGeometricPath (A := A)
        (universalTraceSensitiveChoice (A := A) γ) = γ := by
    intro γ
    rfl
  have hraw : Topology.IsQuotientMap
      (C.restrictPreimage
        (Prod.map (scopedQuotientMk P) (scopedQuotientMk P))) := by
    have h := restricted_product_isQuotient_of_section_open
      (universalChosenGeometricPath (A := A))
      (universalTraceSensitiveChoice (A := A))
      (universalPathClassProjection (A := A))
      (continuous_universalChosenGeometricPath (A := A))
      (continuous_universalTraceSensitiveChoice_observable (A := A))
      hsection hq C
    have hfactor :
        universalPathClassProjection (A := A) ∘
          universalChosenGeometricPath (A := A) =
          scopedQuotientMk P := by
      funext p
      exact universalPathClassProjection_factor p
    rw [hfactor] at h
    exact h
  apply (scopedProductCompatibility_iff_raw_pair_map_quotient P).2
  rw [scopedOrdinaryPairMap_eq_restricted]
  exact hraw.comp (totalComposableRawPairHomeomorph S).isQuotientMap

theorem continuous_universalComposition_of_open_path_projection
    (hopen : IsOpenMap (universalPathClassProjection (A := A))) :
    Continuous (scopedCompositionOnProduct (universalPresentation (A := A)) :
      ScopedComposablePair (universalPresentation (A := A)) →
        ScopedClass (universalPresentation (A := A))) :=
  continuous_scopedCompositionOnProduct _
    (universalProductCompatibility_of_open_path_projection hopen)

end ScopedGeometricRewrite
end GeometricTopology
end Path
end ComputationalPaths
