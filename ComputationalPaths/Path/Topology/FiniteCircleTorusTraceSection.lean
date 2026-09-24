import ComputationalPaths.Path.Topology.FiniteCircleTorusPresentation
import ComputationalPaths.Path.Topology.TopologicalWindingHomeomorph
import ComputationalPaths.Path.Topology.TraceSensitiveTopologicalCompPath

/-!
# A continuous finite-alphabet circle trace choice

The choice uses signed powers of the single generator. Its continuity uses
local constancy of winding; it does not assert completeness for a particular
set of scoped rules.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology
namespace FiniteCircleTorusPresentation

open scoped ContinuousMap Topology
open ConcreteCircleWinding

private theorem circleWinding_symm
    (γ : _root_.Path (0 : TopologicalCircle) 0) :
    windingPath γ.symm = -windingPath γ := by
  have h := windingPath_eq_of_homotopic (_root_.Path.Homotopic.trans_symm γ)
  rw [windingPath_trans, windingPath_refl] at h
  omega

theorem circleWinding_power (n : Nat) :
    windingPath (GeometricTrace.realize (circlePower n)) = (n : Int) := by
  induction n with
  | zero => exact windingPath_refl
  | succ n ih =>
      change windingPath ((GeometricTrace.realize (circlePower n)).trans
        (standardLoop 1)) = (n + 1 : Nat)
      rw [windingPath_trans, ih, windingPath_standardLoop]
      norm_num

theorem circleWinding_canonical (z : Int) :
    windingPath (GeometricTrace.realize (circleCanonical z)) = z := by
  cases z with
  | ofNat n => exact circleWinding_power n
  | negSucc n =>
      change windingPath (GeometricTrace.realize (circlePower (n + 1))).symm = _
      rw [circleWinding_symm, circleWinding_power]
      rfl

theorem circleCanonical_homotopic (γ : _root_.Path (0 : TopologicalCircle) 0) :
    _root_.Path.Homotopic
      (GeometricTrace.realize (circleCanonical (windingPath γ))) γ := by
  have h₁ := standardLoop_homotopic
    (GeometricTrace.realize (circleCanonical (windingPath γ)))
  have h₂ := standardLoop_homotopic γ
  rw [circleWinding_canonical] at h₁
  exact h₁.symm.trans h₂

abbrev FiniteCircleOpenLoop := OpenGeometricCompPath
  circleStepSystem.toGeometricStepSystem (0 : TopologicalCircle) 0

noncomputable def finiteCircleChosenTrace
    (γ : _root_.Path (0 : TopologicalCircle) 0) : FiniteCircleOpenLoop :=
  { trace := circleCanonical (windingPath γ)
    geometric := γ
    coherent := (circleCanonical_homotopic γ).symm }

noncomputable def finiteCircleTraceSensitiveTopology :
    TopologicalSpace FiniteCircleOpenLoop :=
  TopologicalSpace.induced
    (fun p : FiniteCircleOpenLoop =>
      (GeometricTrace.flatWord p.trace, (p.trace, p.geometric))) inferInstance

theorem continuous_finiteCircleChosenTrace :
    @Continuous (_root_.Path (0 : TopologicalCircle) 0) FiniteCircleOpenLoop
      inferInstance finiteCircleTraceSensitiveTopology
      finiteCircleChosenTrace := by
  apply continuous_induced_rng.mpr
  letI : TopologicalSpace FiniteCircleOpenLoop := finiteCircleTraceSensitiveTopology
  have hword : Continuous (fun z : Int =>
      GeometricTrace.flatWord (circleCanonical z)) :=
    continuous_of_discreteTopology
  have htrace : Continuous (circleCanonical : Int → CircleTrace) :=
    continuous_of_discreteTopology
  change Continuous (fun γ : _root_.Path (0 : TopologicalCircle) 0 =>
    (GeometricTrace.flatWord (circleCanonical (windingPath γ)),
      (circleCanonical (windingPath γ), γ)))
  exact (hword.comp ConcreteCircleWinding.continuous_windingPath).prodMk
    ((htrace.comp ConcreteCircleWinding.continuous_windingPath).prodMk continuous_id)

private theorem torusWinding_symm (γ : TopologicalTorus.Loop) :
    TopologicalTorus.winding γ.symm =
      (-(TopologicalTorus.winding γ).1,
        -(TopologicalTorus.winding γ).2) := by
  have h := TopologicalTorus.winding_eq_of_homotopic
    (_root_.Path.Homotopic.trans_symm γ)
  rw [TopologicalTorus.winding_trans, TopologicalTorus.winding_identity] at h
  apply Prod.ext <;> simp only [Prod.mk.injEq] at h ⊢
  · omega
  · omega

theorem torusWinding_power (g : TorusGenerator) (n : Nat) :
    TopologicalTorus.winding (GeometricTrace.realize (torusPower g n)) =
      (if g = .a then ((n : Int), 0) else (0, (n : Int))) := by
  induction n with
  | zero =>
      cases g <;> simp [torusPower, GeometricTrace.realize,
        TopologicalTorus.winding_identity]
  | succ n ih =>
      cases g with
      | a =>
          change TopologicalTorus.winding
            ((GeometricTrace.realize (torusPower .a n)).trans
              (TopologicalTorus.firstFactorLoop 1)) = _
          rw [TopologicalTorus.winding_trans, ih,
            TopologicalTorus.winding_firstFactorLoop]
          simp
      | b =>
          change TopologicalTorus.winding
            ((GeometricTrace.realize (torusPower .b n)).trans
              (TopologicalTorus.secondFactorLoop 1)) = _
          rw [TopologicalTorus.winding_trans, ih,
            TopologicalTorus.winding_secondFactorLoop]
          simp

theorem torusWinding_zpower (g : TorusGenerator) (z : Int) :
    TopologicalTorus.winding (GeometricTrace.realize (torusZPower g z)) =
      (if g = .a then (z, 0) else (0, z)) := by
  cases z with
  | ofNat n => exact torusWinding_power g n
  | negSucc n =>
      change TopologicalTorus.winding
        (GeometricTrace.realize (torusPower g (n + 1))).symm = _
      rw [torusWinding_symm, torusWinding_power]
      cases g <;> simp <;> omega

theorem torusWinding_canonical (z : Int × Int) :
    TopologicalTorus.winding (GeometricTrace.realize (torusCanonical z)) = z := by
  rcases z with ⟨m, n⟩
  change TopologicalTorus.winding
    ((GeometricTrace.realize (torusZPower .a m)).trans
      (GeometricTrace.realize (torusZPower .b n))) = (m, n)
  rw [TopologicalTorus.winding_trans,
    torusWinding_zpower, torusWinding_zpower]
  simp

theorem torusCanonical_homotopic (γ : TopologicalTorus.Loop) :
    _root_.Path.Homotopic
      (GeometricTrace.realize (torusCanonical (TopologicalTorus.winding γ))) γ := by
  have h₁ := TopologicalTorus.standardLoop_homotopic
    (GeometricTrace.realize (torusCanonical (TopologicalTorus.winding γ)))
  have h₂ := TopologicalTorus.standardLoop_homotopic γ
  rw [torusWinding_canonical] at h₁
  exact h₁.symm.trans h₂

abbrev FiniteTorusOpenLoop := OpenGeometricCompPath
  torusStepSystem.toGeometricStepSystem torusBase torusBase

noncomputable def finiteTorusChosenTrace
    (γ : TopologicalTorus.Loop) : FiniteTorusOpenLoop :=
  { trace := torusCanonical (TopologicalTorus.winding γ)
    geometric := γ
    coherent := (torusCanonical_homotopic γ).symm }

noncomputable def finiteTorusTraceSensitiveTopology :
    TopologicalSpace FiniteTorusOpenLoop :=
  TopologicalSpace.induced
    (fun p : FiniteTorusOpenLoop =>
      (GeometricTrace.flatWord p.trace, (p.trace, p.geometric))) inferInstance

theorem continuous_finiteTorusChosenTrace :
    @Continuous TopologicalTorus.Loop FiniteTorusOpenLoop
      inferInstance finiteTorusTraceSensitiveTopology
      finiteTorusChosenTrace := by
  apply continuous_induced_rng.mpr
  letI : TopologicalSpace FiniteTorusOpenLoop := finiteTorusTraceSensitiveTopology
  have hword : Continuous (fun z : Int × Int =>
      GeometricTrace.flatWord (torusCanonical z)) :=
    continuous_of_discreteTopology
  have htrace : Continuous (torusCanonical : Int × Int → TorusTrace) :=
    continuous_of_discreteTopology
  change Continuous (fun γ : TopologicalTorus.Loop =>
    (GeometricTrace.flatWord (torusCanonical (TopologicalTorus.winding γ)),
      (torusCanonical (TopologicalTorus.winding γ), γ)))
  exact (hword.comp TopologicalTorus.continuous_winding).prodMk
    ((htrace.comp TopologicalTorus.continuous_winding).prodMk continuous_id)

noncomputable def finiteCircleBasedSetoid
    (P : ScopedGeometricRewritePresentation circleStepSystem) :
    Setoid FiniteCircleOpenLoop where
  r p q := ScopedRwEq P p.trace q.trace
  iseqv := ⟨fun p => ScopedRwEq.refl p.trace,
    fun h => ScopedRwEq.symm h,
    fun h k => ScopedRwEq.trans h k⟩

noncomputable def finiteTorusBasedSetoid
    (P : ScopedGeometricRewritePresentation torusStepSystem) :
    Setoid FiniteTorusOpenLoop where
  r p q := ScopedRwEq P p.trace q.trace
  iseqv := ⟨fun p => ScopedRwEq.refl p.trace,
    fun h => ScopedRwEq.symm h,
    fun h k => ScopedRwEq.trans h k⟩

theorem continuous_finiteCircleTraceSensitive_to_observable :
    @Continuous FiniteCircleOpenLoop FiniteCircleOpenLoop
      finiteCircleTraceSensitiveTopology inferInstance id := by
  apply continuous_induced_rng.mpr
  have h : @Continuous FiniteCircleOpenLoop
      (FlatWord CircleGenerator ×
        (CircleTrace × _root_.Path (0 : TopologicalCircle) 0))
      finiteCircleTraceSensitiveTopology inferInstance
      (fun p => (GeometricTrace.flatWord p.trace, (p.trace, p.geometric))) :=
    continuous_induced_dom
  have hsnd : Continuous (fun z : FlatWord CircleGenerator ×
      (CircleTrace × _root_.Path (0 : TopologicalCircle) 0) => z.2) :=
    continuous_snd
  simpa [Function.comp_def] using
    (@Continuous.comp FiniteCircleOpenLoop _ _
      finiteCircleTraceSensitiveTopology inferInstance inferInstance
      _ _ hsnd h)

theorem continuous_finiteTorusTraceSensitive_to_observable :
    @Continuous FiniteTorusOpenLoop FiniteTorusOpenLoop
      finiteTorusTraceSensitiveTopology inferInstance id := by
  apply continuous_induced_rng.mpr
  have h : @Continuous FiniteTorusOpenLoop
      (FlatWord TorusGenerator ×
        (TorusTrace × TopologicalTorus.Loop))
      finiteTorusTraceSensitiveTopology inferInstance
      (fun p => (GeometricTrace.flatWord p.trace, (p.trace, p.geometric))) :=
    continuous_induced_dom
  have hsnd : Continuous (fun z : FlatWord TorusGenerator ×
      (TorusTrace × TopologicalTorus.Loop) => z.2) :=
    continuous_snd
  simpa [Function.comp_def] using
    (@Continuous.comp FiniteTorusOpenLoop _ _
      finiteTorusTraceSensitiveTopology inferInstance inferInstance
      _ _ hsnd h)

/-- The finite-generator circle choice collapses the two based quotient
topologies whenever the chosen scoped rules are based-complete. -/
noncomputable def finiteCircleTraceHomeomorph_of_complete
    (P : ScopedGeometricRewritePresentation circleStepSystem)
    (hcomplete : ∀ p q : FiniteCircleOpenLoop,
      _root_.Path.Homotopic p.geometric q.geometric →
        ScopedRwEq P p.trace q.trace) :
    @Homeomorph (Quotient (finiteCircleBasedSetoid P))
      (Quotient (finiteCircleBasedSetoid P))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (finiteCircleBasedSetoid P) finiteCircleTraceSensitiveTopology)
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (finiteCircleBasedSetoid P) inferInstance) :=
  TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientComparisonHomeomorph_of_realization_section
    (finiteCircleBasedSetoid P)
    continuous_finiteCircleTraceSensitive_to_observable
    (fun p : FiniteCircleOpenLoop => p.geometric) finiteCircleChosenTrace
    (continuous_open_geometric circleStepSystem.toGeometricStepSystem)
    continuous_finiteCircleChosenTrace
    (fun p => Quotient.sound
      (hcomplete (finiteCircleChosenTrace p.geometric) p
        (_root_.Path.Homotopic.refl p.geometric)))

/-- The analogous conditional comparison for the two-generator torus. -/
noncomputable def finiteTorusTraceHomeomorph_of_complete
    (P : ScopedGeometricRewritePresentation torusStepSystem)
    (hcomplete : ∀ p q : FiniteTorusOpenLoop,
      _root_.Path.Homotopic p.geometric q.geometric →
        ScopedRwEq P p.trace q.trace) :
    @Homeomorph (Quotient (finiteTorusBasedSetoid P))
      (Quotient (finiteTorusBasedSetoid P))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (finiteTorusBasedSetoid P) finiteTorusTraceSensitiveTopology)
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (finiteTorusBasedSetoid P) inferInstance) :=
  TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientComparisonHomeomorph_of_realization_section
    (finiteTorusBasedSetoid P)
    continuous_finiteTorusTraceSensitive_to_observable
    (fun p : FiniteTorusOpenLoop => p.geometric) finiteTorusChosenTrace
    (continuous_open_geometric torusStepSystem.toGeometricStepSystem)
    continuous_finiteTorusChosenTrace
    (fun p => Quotient.sound
      (hcomplete (finiteTorusChosenTrace p.geometric) p
        (_root_.Path.Homotopic.refl p.geometric)))

end FiniteCircleTorusPresentation
end GeometricTopology
end Path
end ComputationalPaths
