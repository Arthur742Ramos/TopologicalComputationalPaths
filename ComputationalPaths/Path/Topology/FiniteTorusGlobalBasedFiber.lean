import ComputationalPaths.Path.Topology.FiniteTorusScopedCompleteness
import ComputationalPaths.Path.Topology.ScopedGeometricRewriteGroupoid
import Mathlib.Topology.Algebra.Group.CompactOpen

/-! The global finite-torus scoped arrow quotient carries a continuous
variable-basepoint winding map. Restricting it to the actual based-arrow
subspace gives the expected discrete `ℤ × ℤ` classification. -/

namespace ComputationalPaths.Path.GeometricTopology.FiniteCircleTorusPresentation
open scoped ContinuousMap Topology
open ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite

abbrev TorusGlobalRaw := ScopedRawPath (S := torusStepSystem)

noncomputable def normalizedTorusLoop (p : TorusGlobalRaw) :
    TopologicalTorus.Loop :=
  { toContinuousMap :=
      p.geometricMap torusStepSystem - ContinuousMap.const _ p.src
    source' := by
      simp [TotalOpenGeometricCompPath.geometricMap,
        TotalOpenGeometricCompPath.geometricPath]
      rfl
    target' := by
      have h := torusTraceEndpoints_eq p.trace
      simp [TotalOpenGeometricCompPath.geometricMap,
        TotalOpenGeometricCompPath.geometricPath, h]
      rfl }

theorem continuous_normalizedTorusLoop :
    Continuous (normalizedTorusLoop : TorusGlobalRaw → TopologicalTorus.Loop) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : TorusGlobalRaw =>
    p.geometricMap torusStepSystem - ContinuousMap.const _ p.src)
  exact (TotalOpenGeometricCompPath.continuous_geometricMap torusStepSystem).sub
    (ContinuousMap.continuous_const'.comp
      (TotalOpenGeometricCompPath.continuous_src torusStepSystem))

noncomputable def torusShift (x : TorusCarrier) : C(TorusCarrier, TorusCarrier) :=
  ⟨fun y => y - x, continuous_id.sub continuous_const⟩

noncomputable def shiftTorusLoop (x : TorusCarrier)
    (γ : _root_.Path x x) : TopologicalTorus.Loop :=
  (γ.map (torusShift x).continuous).cast (sub_self x).symm (sub_self x).symm

theorem shiftTorusLoop_homotopic (x : TorusCarrier)
    {γ δ : _root_.Path x x} (h : _root_.Path.Homotopic γ δ) :
    _root_.Path.Homotopic (shiftTorusLoop x γ) (shiftTorusLoop x δ) := by
  exact (h.map (torusShift x)).pathCast (sub_self x).symm (sub_self x).symm

theorem normalizedTorusLoop_eq_shift (p : TorusGlobalRaw) :
    normalizedTorusLoop p =
      shiftTorusLoop p.src (p.geometricPath torusStepSystem |>.cast rfl
        (torusTraceEndpoints_eq p.trace)) := by
  ext t <;> simp [normalizedTorusLoop, shiftTorusLoop, torusShift,
    TopologicalTorus.base, Prod.sub_def,
    TotalOpenGeometricCompPath.geometricMap,
    TotalOpenGeometricCompPath.geometricPath, _root_.Path.cast] <;> rfl

noncomputable def torusGlobalRawWinding (p : TorusGlobalRaw) : ℤ × ℤ :=
  TopologicalTorus.winding (normalizedTorusLoop p)

theorem continuous_torusGlobalRawWinding : Continuous torusGlobalRawWinding :=
  TopologicalTorus.continuous_winding.comp continuous_normalizedTorusLoop

theorem torusGlobalRawWinding_eq_of_scopedEquivalent
    {p q : TorusGlobalRaw}
    (h : scopedEquivalent torusFinitePresentation p q) :
    torusGlobalRawWinding p = torusGlobalRawWinding q := by
  rcases p with ⟨a, b, p⟩
  rcases q with ⟨c, d, q⟩
  rcases h with ⟨hs, ht, h⟩
  cases hs
  cases ht
  have hh : _root_.Path.Homotopic p.geometric q.geometric :=
    p.coherent.trans ((ScopedRwEq.sound torusFinitePresentation h).trans
      q.coherent.symm)
  have hab : a = b := torusTraceEndpoints_eq p.trace
  cases hab
  have hshift := shiftTorusLoop_homotopic a hh
  have hpcast : p.geometric.cast rfl rfl = p.geometric := by ext t <;> rfl
  have hqcast : q.geometric.cast rfl rfl = q.geometric := by ext t <;> rfl
  apply TopologicalTorus.winding_eq_of_homotopic
  simpa only [torusGlobalRawWinding, normalizedTorusLoop_eq_shift,
    TotalOpenGeometricCompPath.geometricPath, hpcast, hqcast] using hshift

noncomputable def torusGlobalWinding : ScopedClass torusFinitePresentation → ℤ × ℤ :=
  Quotient.lift torusGlobalRawWinding
    (fun _ _ h => torusGlobalRawWinding_eq_of_scopedEquivalent h)

theorem continuous_torusGlobalWinding : Continuous torusGlobalWinding := by
  apply Continuous.quotient_lift
  exact continuous_torusGlobalRawWinding

abbrev TorusGlobalBasedFiber :=
  {c : ScopedClass torusFinitePresentation //
    scopedSrc torusFinitePresentation c = torusBase ∧
    scopedTgt torusFinitePresentation c = torusBase}

noncomputable def torusGlobalBasedWinding : TorusGlobalBasedFiber → ℤ × ℤ :=
  fun c => torusGlobalWinding c.1

theorem continuous_torusGlobalBasedWinding :
    Continuous torusGlobalBasedWinding :=
  continuous_torusGlobalWinding.comp continuous_subtype_val

theorem torusGlobalBasedWinding_injective :
    Function.Injective torusGlobalBasedWinding := by
  intro p q hwind
  apply Subtype.ext
  rcases p with ⟨p, hp⟩
  rcases q with ⟨q, hq⟩
  revert hp hq hwind
  refine Quotient.inductionOn₂ p q ?_
  intro p q hp hq hwind
  have hps : p.src = torusBase := hp.1
  have hqs : q.src = torusBase := hq.1
  have hpt : p.tgt = torusBase := hp.2
  have hqt : q.tgt = torusBase := hq.2
  rcases p with ⟨a, b, p⟩
  rcases q with ⟨c, d, q⟩
  cases hps
  cases hpt
  cases hqs
  cases hqt
  have hpnorm : normalizedTorusLoop (⟨torusBase, torusBase, p⟩ : TorusGlobalRaw) =
      p.geometric := by
    ext t <;>
    simp [normalizedTorusLoop, torusBase, TopologicalTorus.base, Prod.sub_def,
      TotalOpenGeometricCompPath.geometricMap,
      TotalOpenGeometricCompPath.geometricPath]
  have hqnorm : normalizedTorusLoop (⟨torusBase, torusBase, q⟩ : TorusGlobalRaw) =
      q.geometric := by
    ext t <;>
    simp [normalizedTorusLoop, torusBase, TopologicalTorus.base, Prod.sub_def,
      TotalOpenGeometricCompPath.geometricMap,
      TotalOpenGeometricCompPath.geometricPath]
  change torusGlobalRawWinding ⟨torusBase, torusBase, p⟩ =
    torusGlobalRawWinding ⟨torusBase, torusBase, q⟩ at hwind
  have hw : TopologicalTorus.winding p.geometric =
      TopologicalTorus.winding q.geometric := by
    simpa only [torusGlobalRawWinding, hpnorm, hqnorm] using hwind
  apply Quotient.sound
  refine ⟨rfl, rfl, ?_⟩
  apply torusFinite_basedComplete p q
  exact (TopologicalTorus.standardLoop_homotopic p.geometric).symm.trans
    (by rw [hw]; exact TopologicalTorus.standardLoop_homotopic q.geometric)

noncomputable def torusGlobalBasedCanonical (z : ℤ × ℤ) :
    TorusGlobalBasedFiber :=
  ⟨scopedQuotientMk torusFinitePresentation
    ⟨torusBase, torusBase,
      finiteTorusChosenTrace (TopologicalTorus.standardLoop z.1 z.2)⟩,
    by simp [scopedSrc_mk, scopedTgt_mk]⟩

theorem torusGlobalBasedWinding_canonical (z : ℤ × ℤ) :
    torusGlobalBasedWinding (torusGlobalBasedCanonical z) = z := by
  change torusGlobalRawWinding
    ⟨torusBase, torusBase,
      finiteTorusChosenTrace (TopologicalTorus.standardLoop z.1 z.2)⟩ = z
  have hn : normalizedTorusLoop
      (⟨torusBase, torusBase,
        finiteTorusChosenTrace (TopologicalTorus.standardLoop z.1 z.2)⟩ :
        TorusGlobalRaw) = TopologicalTorus.standardLoop z.1 z.2 := by
    ext t <;>
    simp [normalizedTorusLoop, torusBase, TopologicalTorus.base, Prod.sub_def,
      TotalOpenGeometricCompPath.geometricMap,
      TotalOpenGeometricCompPath.geometricPath, finiteTorusChosenTrace]
  simp [torusGlobalRawWinding, hn, TopologicalTorus.winding_standardLoop]

noncomputable def torusGlobalBasedWindingHomeomorph :
    TorusGlobalBasedFiber ≃ₜ (ℤ × ℤ) where
  toFun := torusGlobalBasedWinding
  invFun := torusGlobalBasedCanonical
  left_inv := by
    intro q
    apply torusGlobalBasedWinding_injective
    exact torusGlobalBasedWinding_canonical _
  right_inv := torusGlobalBasedWinding_canonical
  continuous_toFun := continuous_torusGlobalBasedWinding
  continuous_invFun := continuous_of_discreteTopology

noncomputable def torusGlobalBasedGeometricHomeomorph :
    TorusGlobalBasedFiber ≃ₜ TopologicalTorus.LoopQuot :=
  torusGlobalBasedWindingHomeomorph.trans
    TopologicalTorus.loopQuotHomeomorphIntProd.symm

end ComputationalPaths.Path.GeometricTopology.FiniteCircleTorusPresentation
