import ComputationalPaths.Path.Topology.TraceSensitiveTopologicalCompPath
import ComputationalPaths.Path.Topology.ScopedGeometricRewriteComparison

/-!
# Collapse of trace-sensitive and observable quotients

The trace-sensitive topology retains the complete finite word, while the
observable topology retains only the semantic coordinates. A continuous
choice of trace, together with geometric completeness, makes the quotient
topologies agree. The universal presentation supplies such a choice.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

universe u v w

namespace ScopedGeometricRewrite

variable {A : Type u} [TopologicalSpace A]

/-- A continuous choice of coherent trace collapses the two scoped quotient
topologies when geometric equality implies scoped equality. The semantic
space can be the represented-path subspace, with `choose` a section of its
geometric projection. -/
noncomputable def traceSensitiveHomeomorph_of_complete_section
    {Step : Type v} [TopologicalSpace Step]
    {S : ContinuousGeometricStepSystem A Step}
    (P : ScopedGeometricRewritePresentation S)
    (H : GeometricCompleteness P)
    {C : Type w} [TopologicalSpace C]
    (realize : ScopedRawPath (S := S) → C)
    (choose : C → ScopedRawPath (S := S))
    (hrealize : Continuous realize)
    (hchoose : @Continuous C (ScopedRawPath (S := S))
      inferInstance
      (TotalOpenGeometricCompPath.traceSensitiveTopologicalSpace S)
      choose)
    (hgeometry : ∀ p, TotalOpenGeometricCompPath.totalEquivalent S
      (choose (realize p)) p) :
    @Homeomorph (ScopedClass P) (ScopedClass P)
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (scopedSetoid P)
        (TotalOpenGeometricCompPath.traceSensitiveTopologicalSpace S))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (scopedSetoid P) inferInstance) :=
  TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientComparisonHomeomorph_of_realization_section
    (scopedSetoid P)
    (TotalOpenGeometricCompPath.continuous_traceSensitive_to_observable S)
    realize choose hrealize hchoose
    (fun p => Quotient.sound (H (hgeometry p)))

noncomputable abbrev UniversalSystem := continuousPathStepSystem A
noncomputable abbrev UniversalPresentation := universalPresentation (A := A)
abbrev UniversalRaw :=
  TotalOpenGeometricCompPath A (ContinuousPathStep A) (UniversalSystem (A := A))
abbrev UniversalClass := ScopedClass (UniversalPresentation (A := A))

noncomputable def traceSensitiveScopedClassTopology
    (P : ScopedGeometricRewritePresentation (continuousPathStepSystem A)) :
    TopologicalSpace (ScopedClass P) :=
  TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (scopedSetoid P)
    (TotalOpenGeometricCompPath.traceSensitiveTopologicalSpace
      (continuousPathStepSystem A))

noncomputable def observableScopedClassTopology
    (P : ScopedGeometricRewritePresentation (continuousPathStepSystem A)) :
    TopologicalSpace (ScopedClass P) :=
  TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (scopedSetoid P) inferInstance

noncomputable def universalTraceSensitiveChoice
    (γ : ContinuousPathStep A) : UniversalRaw (A := A) :=
  ⟨γ 0, γ 1, continuousPathStep γ⟩

noncomputable def universalChosenGeometricPath
    (p : UniversalRaw (A := A)) : ContinuousPathStep A :=
  p.geometricMap (continuousPathStepSystem A)

theorem continuous_universalChosenGeometricPath :
    Continuous (universalChosenGeometricPath (A := A) :
      UniversalRaw (A := A) → ContinuousPathStep A) :=
  TotalOpenGeometricCompPath.continuous_geometricMap
    (continuousPathStepSystem A)

theorem continuous_universalTraceSensitiveChoice :
    @Continuous (ContinuousPathStep A) (UniversalRaw (A := A))
      inferInstance
      (TotalOpenGeometricCompPath.traceSensitiveTopologicalSpace
        (continuousPathStepSystem A))
      (universalTraceSensitiveChoice (A := A)) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun γ : ContinuousPathStep A =>
    TotalOpenGeometricCompPath.traceSensitiveObservation
      (continuousPathStepSystem A)
      (universalTraceSensitiveChoice (A := A) γ))
  change Continuous (fun γ : ContinuousPathStep A =>
    ((⟨1, fun _ => Sum.inl γ⟩ : FlatWord (ContinuousPathStep A)),
      (γ 0, (γ 1, (1, (γ, γ))))))
  have hflat :
      Continuous (fun γ : ContinuousPathStep A =>
        (⟨1, fun _ => Sum.inl γ⟩ : FlatWord (ContinuousPathStep A))) := by
    apply continuous_sigmaMk.comp
    apply continuous_pi
    intro i
    exact continuous_inl
  have hobs :
      Continuous (fun γ : ContinuousPathStep A =>
        (γ 0, (γ 1, (1, (γ, γ))))) := by
    exact (continuous_eval_const 0).prodMk <|
      (continuous_eval_const 1).prodMk <|
        continuous_const.prodMk (continuous_id.prodMk continuous_id)
  exact hflat.prodMk hobs

theorem universalTraceSensitiveChoice_factor
    (p : UniversalRaw (A := A)) :
    scopedQuotientMk (UniversalPresentation (A := A))
        (universalTraceSensitiveChoice
          (A := A) (universalChosenGeometricPath (A := A) p)) =
      scopedQuotientMk (UniversalPresentation (A := A)) p := by
  apply Quotient.sound
  apply (universalScopedEquivalent_iff_totalEquivalent (A := A)).2
  change TotalOpenGeometricCompPath.totalCode
      (continuousPathStepSystem A)
      (universalTraceSensitiveChoice
        (A := A) (universalChosenGeometricPath (A := A) p)) =
    TotalOpenGeometricCompPath.totalCode
      (continuousPathStepSystem A) p
  rcases p with ⟨p_src, p_tgt, p_path⟩
  rcases p_path with ⟨p_trace, p_geo, p_coherent⟩
  rcases p_geo with ⟨p_map, hp_src, hp_tgt⟩
  subst p_src
  subst p_tgt
  simp_all [TotalOpenGeometricCompPath.totalCode,
    universalTraceSensitiveChoice, universalChosenGeometricPath,
    TotalOpenGeometricCompPath.geometricMap]
  rfl

noncomputable def universalTraceSensitiveHomeomorph :
    @Homeomorph (UniversalClass (A := A)) (UniversalClass (A := A))
      (traceSensitiveScopedClassTopology (A := A)
        (UniversalPresentation (A := A)))
      (observableScopedClassTopology (A := A)
        (UniversalPresentation (A := A))) :=
  TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientComparisonHomeomorph_of_realization_section
    (scopedSetoid (UniversalPresentation (A := A)))
    (TotalOpenGeometricCompPath.continuous_traceSensitive_to_observable
      (continuousPathStepSystem A))
    (universalChosenGeometricPath (A := A))
    (universalTraceSensitiveChoice (A := A))
    (continuous_universalChosenGeometricPath (A := A))
    (continuous_universalTraceSensitiveChoice (A := A))
    (universalTraceSensitiveChoice_factor (A := A))

end ScopedGeometricRewrite
end GeometricTopology
end Path
end ComputationalPaths
