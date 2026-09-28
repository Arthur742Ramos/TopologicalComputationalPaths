import ComputationalPaths.Path.Topology.FiniteCircleScopedCompleteness
import ComputationalPaths.Path.Topology.ScopedGeometricRewriteGroupoid
import Mathlib.Topology.Algebra.Group.CompactOpen

/-! The finite-circle presentation has a continuous winding map on its full
scoped arrow quotient. Its actual based-arrow subspace is therefore discrete
and homeomorphic to the ordinary geometric loop quotient. -/

namespace ComputationalPaths.Path.GeometricTopology.FiniteCircleTorusPresentation
open scoped ContinuousMap Topology
open ConcreteCircleWinding
open ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite

abbrev CircleGlobalRaw := ScopedRawPath (S := circleStepSystem)

noncomputable def normalizedCircleLoop (p : CircleGlobalRaw) :
    _root_.Path (0 : TopologicalCircle) 0 :=
  { toContinuousMap :=
      p.geometricMap circleStepSystem - ContinuousMap.const _ p.src
    source' := by
      simp [TotalOpenGeometricCompPath.geometricMap,
        TotalOpenGeometricCompPath.geometricPath]
    target' := by
      have h := circleTraceEndpoints_eq p.trace
      simp [TotalOpenGeometricCompPath.geometricMap,
        TotalOpenGeometricCompPath.geometricPath, h] }

theorem continuous_normalizedCircleLoop :
    Continuous (normalizedCircleLoop : CircleGlobalRaw →
      _root_.Path (0 : TopologicalCircle) 0) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : CircleGlobalRaw =>
    p.geometricMap circleStepSystem - ContinuousMap.const _ p.src)
  exact (TotalOpenGeometricCompPath.continuous_geometricMap circleStepSystem).sub
    (ContinuousMap.continuous_const'.comp
      (TotalOpenGeometricCompPath.continuous_src circleStepSystem))

noncomputable def circleShift (x : TopologicalCircle) :
    C(TopologicalCircle, TopologicalCircle) :=
  ⟨fun y => y - x, continuous_id.sub continuous_const⟩

noncomputable def shiftCircleLoop (x : TopologicalCircle)
    (γ : _root_.Path x x) : _root_.Path (0 : TopologicalCircle) 0 :=
  (γ.map (circleShift x).continuous).cast (sub_self x).symm (sub_self x).symm

theorem shiftCircleLoop_homotopic (x : TopologicalCircle)
    {γ δ : _root_.Path x x} (h : _root_.Path.Homotopic γ δ) :
    _root_.Path.Homotopic (shiftCircleLoop x γ) (shiftCircleLoop x δ) := by
  exact (h.map (circleShift x)).pathCast (sub_self x).symm (sub_self x).symm

theorem normalizedCircleLoop_eq_shift (p : CircleGlobalRaw) :
    normalizedCircleLoop p =
      shiftCircleLoop p.src (p.geometricPath circleStepSystem |>.cast rfl
        (circleTraceEndpoints_eq p.trace)) := by
  ext t
  rfl

noncomputable def circleGlobalRawWinding (p : CircleGlobalRaw) : ℤ :=
  windingPath (normalizedCircleLoop p)

theorem continuous_circleGlobalRawWinding :
    Continuous circleGlobalRawWinding :=
  ConcreteCircleWinding.continuous_windingPath.comp
    continuous_normalizedCircleLoop

theorem circleGlobalRawWinding_eq_of_scopedEquivalent
    {p q : CircleGlobalRaw}
    (h : scopedEquivalent circleFinitePresentation p q) :
    circleGlobalRawWinding p = circleGlobalRawWinding q := by
  rcases p with ⟨a, b, p⟩
  rcases q with ⟨c, d, q⟩
  rcases h with ⟨hs, ht, h⟩
  cases hs
  cases ht
  have hh : _root_.Path.Homotopic p.geometric q.geometric :=
    p.coherent.trans ((ScopedRwEq.sound circleFinitePresentation h).trans
      q.coherent.symm)
  have hab : a = b := circleTraceEndpoints_eq p.trace
  cases hab
  have hshift := shiftCircleLoop_homotopic a hh
  have hpcast : p.geometric.cast rfl rfl = p.geometric := by ext t; rfl
  have hqcast : q.geometric.cast rfl rfl = q.geometric := by ext t; rfl
  apply windingPath_eq_of_homotopic
  simpa only [circleGlobalRawWinding, normalizedCircleLoop_eq_shift,
    TotalOpenGeometricCompPath.geometricPath, hpcast, hqcast] using hshift

noncomputable def circleGlobalWinding : ScopedClass circleFinitePresentation → ℤ :=
  Quotient.lift circleGlobalRawWinding
    (fun _ _ h => circleGlobalRawWinding_eq_of_scopedEquivalent h)

theorem continuous_circleGlobalWinding : Continuous circleGlobalWinding := by
  apply Continuous.quotient_lift
  exact continuous_circleGlobalRawWinding

theorem normalizedCircleLoop_at_base (p : CircleGlobalRaw)
    (h : p.src = (0 : TopologicalCircle)) :
    normalizedCircleLoop p =
      (p.geometricPath circleStepSystem).cast h.symm
        (h.symm.trans (circleTraceEndpoints_eq p.trace)) := by
  ext t
  simp [normalizedCircleLoop, TotalOpenGeometricCompPath.geometricMap,
    TotalOpenGeometricCompPath.geometricPath, _root_.Path.cast, h]

abbrev CircleGlobalBasedFiber :=
  {c : ScopedClass circleFinitePresentation //
    scopedSrc circleFinitePresentation c = (0 : TopologicalCircle) ∧
    scopedTgt circleFinitePresentation c = (0 : TopologicalCircle)}

noncomputable def circleGlobalBasedWinding : CircleGlobalBasedFiber → ℤ :=
  fun c => circleGlobalWinding c.1

theorem continuous_circleGlobalBasedWinding :
    Continuous circleGlobalBasedWinding :=
  continuous_circleGlobalWinding.comp continuous_subtype_val

theorem circleGlobalBasedWinding_injective :
    Function.Injective circleGlobalBasedWinding := by
  intro p q hwind
  apply Subtype.ext
  rcases p with ⟨p, hp⟩
  rcases q with ⟨q, hq⟩
  revert hp hq hwind
  refine Quotient.inductionOn₂ p q ?_
  intro p q hp hq hwind
  have hps : p.src = (0 : TopologicalCircle) := hp.1
  have hqs : q.src = (0 : TopologicalCircle) := hq.1
  have hpt : p.tgt = (0 : TopologicalCircle) := hp.2
  have hqt : q.tgt = (0 : TopologicalCircle) := hq.2
  rcases p with ⟨a, b, p⟩
  rcases q with ⟨c, d, q⟩
  cases hps
  cases hpt
  cases hqs
  cases hqt
  have hpnorm : normalizedCircleLoop (⟨0, 0, p⟩ : CircleGlobalRaw) =
      p.geometric := by
    ext t
    simp [normalizedCircleLoop, TotalOpenGeometricCompPath.geometricMap,
      TotalOpenGeometricCompPath.geometricPath]
  have hqnorm : normalizedCircleLoop (⟨0, 0, q⟩ : CircleGlobalRaw) =
      q.geometric := by
    ext t
    simp [normalizedCircleLoop, TotalOpenGeometricCompPath.geometricMap,
      TotalOpenGeometricCompPath.geometricPath]
  change circleGlobalRawWinding ⟨0, 0, p⟩ =
    circleGlobalRawWinding ⟨0, 0, q⟩ at hwind
  have hw : windingPath p.geometric = windingPath q.geometric := by
    simpa only [circleGlobalRawWinding, hpnorm, hqnorm] using hwind
  apply Quotient.sound
  refine ⟨rfl, rfl, ?_⟩
  apply circleFinite_basedComplete p q
  exact (standardLoop_homotopic p.geometric).symm.trans
    (by rw [hw]; exact standardLoop_homotopic q.geometric)

noncomputable def circleGlobalBasedCanonical (z : ℤ) :
    CircleGlobalBasedFiber :=
  ⟨scopedQuotientMk circleFinitePresentation
    ⟨0, 0, finiteCircleChosenTrace (standardLoop z)⟩,
    by simp [scopedSrc_mk, scopedTgt_mk]⟩

theorem circleGlobalBasedWinding_canonical (z : ℤ) :
    circleGlobalBasedWinding (circleGlobalBasedCanonical z) = z := by
  change circleGlobalRawWinding
    ⟨0, 0, finiteCircleChosenTrace (standardLoop z)⟩ = z
  have hn : normalizedCircleLoop
      (⟨0, 0, finiteCircleChosenTrace (standardLoop z)⟩ : CircleGlobalRaw) =
      standardLoop z := by
    ext t
    simp [normalizedCircleLoop, TotalOpenGeometricCompPath.geometricMap,
      TotalOpenGeometricCompPath.geometricPath, finiteCircleChosenTrace]
  simp [circleGlobalRawWinding, hn, windingPath_standardLoop]

noncomputable def circleGlobalBasedWindingHomeomorph :
    CircleGlobalBasedFiber ≃ₜ ℤ where
  toFun := circleGlobalBasedWinding
  invFun := circleGlobalBasedCanonical
  left_inv := by
    intro q
    apply circleGlobalBasedWinding_injective
    exact circleGlobalBasedWinding_canonical _
  right_inv := circleGlobalBasedWinding_canonical
  continuous_toFun := continuous_circleGlobalBasedWinding
  continuous_invFun := continuous_of_discreteTopology

noncomputable def circleGlobalBasedGeometricHomeomorph :
    CircleGlobalBasedFiber ≃ₜ ConcreteCircleWinding.TopologicalLoopQuot :=
  circleGlobalBasedWindingHomeomorph.trans
    ConcreteCircleWinding.topologicalLoopQuotHomeomorphInt.symm

end ComputationalPaths.Path.GeometricTopology.FiniteCircleTorusPresentation
