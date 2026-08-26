import ComputationalPaths.Path.Topology.TotalGeometricComputationalPath

/-!
# Continuous operations on the total computational-path space

This file lifts the fibrewise operations from `OpenGeometricComputationalPath`
to the endpoint-varying carrier.  The composable-pair carrier is topologized
by the endpoint, trace, and geometric coordinates of both factors.  Mathlib's
family-level continuity theorem for interval-path concatenation proves
continuity even while all three endpoints vary.

The final certificate deliberately records weak, rather than strict,
associativity: computational traces carry explicit `Path` witnesses for the
coherence laws, while geometric concatenation is the usual homotopy-level
operation on interval paths.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

universe u v

/-! ## The space of composable total paths -/

/-- Two coherent open paths with a shared middle endpoint. -/
structure TotalComposable
    (A : Type u) [TopologicalSpace A]
    (Step : Type v) [TopologicalSpace Step]
    (S : ContinuousGeometricStepSystem A Step) where
  src : A
  mid : A
  tgt : A
  left : OpenGeometricCompPath S.toGeometricStepSystem src mid
  right : OpenGeometricCompPath S.toGeometricStepSystem mid tgt

namespace TotalComposable

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  (S : ContinuousGeometricStepSystem A Step)

noncomputable def leftTraceMap (c : TotalComposable A Step S) : C(unitInterval, A) :=
  (GeometricTrace.realize c.left.trace).toContinuousMap

noncomputable def rightTraceMap (c : TotalComposable A Step S) : C(unitInterval, A) :=
  (GeometricTrace.realize c.right.trace).toContinuousMap

def leftGeometricMap (c : TotalComposable A Step S) : C(unitInterval, A) :=
  c.left.geometric.toContinuousMap

def rightGeometricMap (c : TotalComposable A Step S) : C(unitInterval, A) :=
  c.right.geometric.toContinuousMap

def leftTraceLength (c : TotalComposable A Step S) : Nat :=
  GeometricTrace.traceLength c.left.trace

def rightTraceLength (c : TotalComposable A Step S) : Nat :=
  GeometricTrace.traceLength c.right.trace

/-! A direct multi-step computational witness in this phase's carrier. -/
noncomputable def composableTraceLoopCertificate
    (c : TotalComposable A Step S) :
    ComputationalPaths.Path (leftTraceLength S c) (leftTraceLength S c) :=
  ComputationalPaths.Path.trans
    (ComputationalPaths.Path.refl (leftTraceLength S c))
    (ComputationalPaths.Path.refl (leftTraceLength S c))

/-- Coordinates for the topology on composable pairs. -/
abbrev Observation :=
  A × (A × (A × (Nat × (Nat ×
    (C(unitInterval, A) × (C(unitInterval, A) ×
      (C(unitInterval, A) × C(unitInterval, A))))))))

noncomputable def observation (c : TotalComposable A Step S) : Observation (A := A) :=
  (c.src, (c.mid, (c.tgt, (c.leftTraceLength, (c.rightTraceLength,
    (leftTraceMap S c, (rightTraceMap S c,
      (leftGeometricMap S c, rightGeometricMap S c))))))))

noncomputable instance instTopologicalSpace :
    TopologicalSpace (TotalComposable A Step S) :=
  TopologicalSpace.induced (observation S) inferInstance

theorem continuous_observation :
    Continuous (observation S : TotalComposable A Step S → Observation (A := A)) :=
  continuous_induced_dom

theorem continuous_src :
    Continuous (fun c : TotalComposable A Step S => c.src) :=
  continuous_fst.comp (continuous_observation S)

theorem continuous_mid :
    Continuous (fun c : TotalComposable A Step S => c.mid) := by
  exact continuous_fst.comp (continuous_snd.comp (continuous_observation S))

theorem continuous_tgt :
    Continuous (fun c : TotalComposable A Step S => c.tgt) := by
  exact continuous_fst.comp
    (continuous_snd.comp (continuous_snd.comp (continuous_observation S)))

theorem continuous_leftTraceLength :
    Continuous (fun c : TotalComposable A Step S => c.leftTraceLength) := by
  exact continuous_fst.comp
    (continuous_snd.comp
      (continuous_snd.comp (continuous_snd.comp (continuous_observation S))))

theorem continuous_rightTraceLength :
    Continuous (fun c : TotalComposable A Step S => c.rightTraceLength) := by
  exact continuous_fst.comp
    (continuous_snd.comp
      (continuous_snd.comp
        (continuous_snd.comp (continuous_snd.comp (continuous_observation S)))))

theorem continuous_leftTraceMap :
    Continuous (fun c : TotalComposable A Step S => c.leftTraceMap) := by
  exact continuous_fst.comp
    (continuous_snd.comp
      (continuous_snd.comp
        (continuous_snd.comp
          (continuous_snd.comp
            (continuous_snd.comp (continuous_observation S))))))

theorem continuous_rightTraceMap :
    Continuous (fun c : TotalComposable A Step S => c.rightTraceMap) := by
  have h1 := continuous_snd.comp (continuous_observation S)
  have h2 := continuous_snd.comp h1
  have h3 := continuous_snd.comp h2
  have h4 := continuous_snd.comp h3
  have h5 := continuous_snd.comp h4
  have h6 := continuous_snd.comp h5
  exact continuous_fst.comp h6

theorem continuous_leftGeometricMap :
    Continuous (fun c : TotalComposable A Step S => c.leftGeometricMap) := by
  have h1 := continuous_snd.comp (continuous_observation S)
  have h2 := continuous_snd.comp h1
  have h3 := continuous_snd.comp h2
  have h4 := continuous_snd.comp h3
  have h5 := continuous_snd.comp h4
  have h6 := continuous_snd.comp h5
  have h7 := continuous_snd.comp h6
  exact continuous_fst.comp h7

theorem continuous_rightGeometricMap :
    Continuous (fun c : TotalComposable A Step S => c.rightGeometricMap) := by
  have h1 := continuous_snd.comp (continuous_observation S)
  have h2 := continuous_snd.comp h1
  have h3 := continuous_snd.comp h2
  have h4 := continuous_snd.comp h3
  have h5 := continuous_snd.comp h4
  have h6 := continuous_snd.comp h5
  have h7 := continuous_snd.comp h6
  exact continuous_snd.comp h7

/-! ## Path families extracted from the coordinates -/

theorem continuous_leftTraceFamily :
    Continuous ↿(fun c : TotalComposable A Step S =>
      GeometricTrace.realize c.left.trace) := by
  change Continuous (fun pt : TotalComposable A Step S × unitInterval =>
    (leftTraceMap S pt.1) pt.2)
  exact ContinuousMap.continuous_uncurry_of_continuous
    (⟨fun c : TotalComposable A Step S => leftTraceMap S c,
      continuous_leftTraceMap S⟩ :
      C(TotalComposable A Step S, C(unitInterval, A)))

theorem continuous_rightTraceFamily :
    Continuous ↿(fun c : TotalComposable A Step S =>
      GeometricTrace.realize c.right.trace) := by
  change Continuous (fun pt : TotalComposable A Step S × unitInterval =>
    (rightTraceMap S pt.1) pt.2)
  exact ContinuousMap.continuous_uncurry_of_continuous
    (⟨fun c : TotalComposable A Step S => rightTraceMap S c,
      continuous_rightTraceMap S⟩ :
      C(TotalComposable A Step S, C(unitInterval, A)))

theorem continuous_leftGeometricFamily :
    Continuous ↿(fun c : TotalComposable A Step S => c.left.geometric) := by
  change Continuous (fun pt : TotalComposable A Step S × unitInterval =>
    (leftGeometricMap S pt.1) pt.2)
  exact ContinuousMap.continuous_uncurry_of_continuous
    (⟨fun c : TotalComposable A Step S => leftGeometricMap S c,
      continuous_leftGeometricMap S⟩ :
      C(TotalComposable A Step S, C(unitInterval, A)))

theorem continuous_rightGeometricFamily :
    Continuous ↿(fun c : TotalComposable A Step S => c.right.geometric) := by
  change Continuous (fun pt : TotalComposable A Step S × unitInterval =>
    (rightGeometricMap S pt.1) pt.2)
  exact ContinuousMap.continuous_uncurry_of_continuous
    (⟨fun c : TotalComposable A Step S => rightGeometricMap S c,
      continuous_rightGeometricMap S⟩ :
      C(TotalComposable A Step S, C(unitInterval, A)))

end TotalComposable

/-! ## Identity, composition, and reversal -/

namespace TotalOpenGeometricCompPath

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  (S : ContinuousGeometricStepSystem A Step)

noncomputable def totalRefl (a : A) :
    TotalOpenGeometricCompPath A Step S :=
  ⟨a, a, openRefl S.toGeometricStepSystem a⟩

noncomputable def totalTrans (c : TotalComposable A Step S) :
    TotalOpenGeometricCompPath A Step S :=
  ⟨c.src, c.tgt,
    openTrans S.toGeometricStepSystem c.left c.right⟩

noncomputable def totalSymm (p : TotalOpenGeometricCompPath A Step S) :
    TotalOpenGeometricCompPath A Step S :=
  ⟨p.tgt, p.src, openSymm S.toGeometricStepSystem p.path⟩

theorem continuous_totalRefl :
    Continuous (totalRefl S : A → TotalOpenGeometricCompPath A Step S) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun a : A =>
    (a, (a, (0, (ContinuousMap.const unitInterval a,
      ContinuousMap.const unitInterval a)))))
  exact continuous_id.prodMk <|
    continuous_id.prodMk <|
      continuous_const.prodMk
        (ContinuousMap.continuous_const'.prodMk ContinuousMap.continuous_const')

theorem continuous_totalTrans :
    Continuous (totalTrans S :
      TotalComposable A Step S → TotalOpenGeometricCompPath A Step S) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun c : TotalComposable A Step S =>
    (c.src, (c.tgt,
      (GeometricTrace.traceLength
          (GeometricTrace.trans c.left.trace c.right.trace),
        (((_root_.Path.trans (GeometricTrace.realize c.left.trace)
            (GeometricTrace.realize c.right.trace)).toContinuousMap),
          ((_root_.Path.trans c.left.geometric c.right.geometric).toContinuousMap))))))
  have hlength :
      Continuous (fun c : TotalComposable A Step S =>
        GeometricTrace.traceLength
          (GeometricTrace.trans c.left.trace c.right.trace)) := by
    have h := GeometricTrace.continuous_nat_add.comp
      ((TotalComposable.continuous_leftTraceLength S).prodMk
        (TotalComposable.continuous_rightTraceLength S))
    change Continuous (fun c : TotalComposable A Step S =>
      GeometricTrace.traceLength c.left.trace +
        GeometricTrace.traceLength c.right.trace) at h
    exact h
  have htraceFamily :
      Continuous ↿(fun c : TotalComposable A Step S =>
        _root_.Path.trans (GeometricTrace.realize c.left.trace)
          (GeometricTrace.realize c.right.trace)) :=
    _root_.Path.trans_continuous_family _
      (TotalComposable.continuous_leftTraceFamily S) _
      (TotalComposable.continuous_rightTraceFamily S)
  have htraceMap :
      Continuous (fun c : TotalComposable A Step S =>
        (_root_.Path.trans (GeometricTrace.realize c.left.trace)
          (GeometricTrace.realize c.right.trace)).toContinuousMap) :=
    ContinuousMap.continuous_of_continuous_uncurry _ htraceFamily
  have hgeometricFamily :
      Continuous ↿(fun c : TotalComposable A Step S =>
        _root_.Path.trans c.left.geometric c.right.geometric) :=
    _root_.Path.trans_continuous_family _
      (TotalComposable.continuous_leftGeometricFamily S) _
      (TotalComposable.continuous_rightGeometricFamily S)
  have hgeometricMap :
      Continuous (fun c : TotalComposable A Step S =>
        (_root_.Path.trans c.left.geometric c.right.geometric).toContinuousMap) :=
    ContinuousMap.continuous_of_continuous_uncurry _ hgeometricFamily
  exact (TotalComposable.continuous_src S).prodMk <|
    (TotalComposable.continuous_tgt S).prodMk <|
      hlength.prodMk (htraceMap.prodMk hgeometricMap)

theorem continuous_totalSymm :
    Continuous (totalSymm S :
      TotalOpenGeometricCompPath A Step S → TotalOpenGeometricCompPath A Step S) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : TotalOpenGeometricCompPath A Step S =>
    (p.tgt, (p.src,
      (GeometricTrace.traceLength (GeometricTrace.symm p.trace),
        (((_root_.Path.symm (GeometricTrace.realize p.trace)).toContinuousMap),
          ((_root_.Path.symm p.geometricPath).toContinuousMap))))))
  have hlength :
      Continuous (fun p : TotalOpenGeometricCompPath A Step S =>
        GeometricTrace.traceLength (GeometricTrace.symm p.trace)) := by
    simpa [GeometricTrace.traceLength] using
      (TotalOpenGeometricCompPath.continuous_traceLength S)
  have htraceFamily :
      Continuous ↿(fun p : TotalOpenGeometricCompPath A Step S =>
        _root_.Path.symm (GeometricTrace.realize p.trace)) :=
    _root_.Path.symm_continuous_family _
      (TotalOpenGeometricCompPath.continuous_traceFamily S)
  have htraceMap :
      Continuous (fun p : TotalOpenGeometricCompPath A Step S =>
        (_root_.Path.symm (GeometricTrace.realize p.trace)).toContinuousMap) :=
    ContinuousMap.continuous_of_continuous_uncurry _ htraceFamily
  have hgeometricFamily :
      Continuous ↿(fun p : TotalOpenGeometricCompPath A Step S =>
        _root_.Path.symm p.geometricPath) :=
    _root_.Path.symm_continuous_family _
      (TotalOpenGeometricCompPath.continuous_geometricFamily S)
  have hgeometricMap :
      Continuous (fun p : TotalOpenGeometricCompPath A Step S =>
        (_root_.Path.symm p.geometricPath).toContinuousMap) :=
    ContinuousMap.continuous_of_continuous_uncurry _ hgeometricFamily
  exact (TotalOpenGeometricCompPath.continuous_tgt S).prodMk <|
    (TotalOpenGeometricCompPath.continuous_src S).prodMk <|
      hlength.prodMk (htraceMap.prodMk hgeometricMap)

end TotalOpenGeometricCompPath

/-! ## The weak topological computational-path certificate -/

/-- Continuity and explicit computational coherence for the total path space.

The certificate stops at the mathematically correct weak level: the total
operations are continuous, and reassociation/unit/reversal laws are explicit
`ComputationalPaths.Path` witnesses on the trace coordinate.  Geometric
representatives retain their existing homotopy coherence in each
`OpenGeometricCompPath` value.
-/
structure TopologicalWeakCompPathCertificate
    (A : Type u) [TopologicalSpace A]
    (Step : Type v) [TopologicalSpace Step]
    (S : ContinuousGeometricStepSystem A Step) where
  source_continuous :
    Continuous (fun p : TotalOpenGeometricCompPath A Step S => p.src)
  target_continuous :
    Continuous (fun p : TotalOpenGeometricCompPath A Step S => p.tgt)
  identity_continuous :
    Continuous (TotalOpenGeometricCompPath.totalRefl S :
      A → TotalOpenGeometricCompPath A Step S)
  composition_continuous :
    Continuous (TotalOpenGeometricCompPath.totalTrans S :
      TotalComposable A Step S → TotalOpenGeometricCompPath A Step S)
  reversal_continuous :
    Continuous (TotalOpenGeometricCompPath.totalSymm S :
      TotalOpenGeometricCompPath A Step S → TotalOpenGeometricCompPath A Step S)
  reassociation_trace {a b c d : A}
      (p : OpenGeometricCompPath S.toGeometricStepSystem a b)
      (q : OpenGeometricCompPath S.toGeometricStepSystem b c)
      (r : OpenGeometricCompPath S.toGeometricStepSystem c d) :
      ComputationalPaths.Path
        (GeometricTrace.traceLength
          (GeometricTrace.trans (GeometricTrace.trans p.trace q.trace) r.trace))
        (GeometricTrace.traceLength p.trace +
          (GeometricTrace.traceLength q.trace + GeometricTrace.traceLength r.trace))
  left_unit_trace {a b : A}
      (p : OpenGeometricCompPath S.toGeometricStepSystem a b) :
      ComputationalPaths.Path
        (GeometricTrace.traceLength
          (GeometricTrace.trans (GeometricTrace.refl a) p.trace))
        (GeometricTrace.traceLength p.trace)
  right_unit_trace {a b : A}
      (p : OpenGeometricCompPath S.toGeometricStepSystem a b) :
      ComputationalPaths.Path
        (GeometricTrace.traceLength
          (GeometricTrace.trans p.trace (GeometricTrace.refl b)))
        (GeometricTrace.traceLength p.trace)
  reversal_trace {a b : A}
      (p : OpenGeometricCompPath S.toGeometricStepSystem a b) :
      ComputationalPaths.Path
        (GeometricTrace.traceLength (GeometricTrace.symm p.trace))
        (GeometricTrace.traceLength p.trace)
  path_coherence {a b : A}
      (p : OpenGeometricCompPath S.toGeometricStepSystem a b) :
      _root_.Path.Homotopic p.geometric (GeometricTrace.realize p.trace)

noncomputable def topologicalWeakCompPathCertificate
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    (S : ContinuousGeometricStepSystem A Step) :
    TopologicalWeakCompPathCertificate A Step S where
  source_continuous := TotalOpenGeometricCompPath.continuous_src S
  target_continuous := TotalOpenGeometricCompPath.continuous_tgt S
  identity_continuous := TotalOpenGeometricCompPath.continuous_totalRefl S
  composition_continuous := TotalOpenGeometricCompPath.continuous_totalTrans S
  reversal_continuous := TotalOpenGeometricCompPath.continuous_totalSymm S
  reassociation_trace := fun p q r =>
    GeometricTrace.traceLengthReassociationPath p.trace q.trace r.trace
  left_unit_trace := by
    intro a b p
    change ComputationalPaths.Path
      (0 + GeometricTrace.traceLength p.trace)
      (GeometricTrace.traceLength p.trace)
    exact ComputationalPaths.Path.ofEq (Nat.zero_add _)
  right_unit_trace := by
    intro a b p
    change ComputationalPaths.Path
      (GeometricTrace.traceLength p.trace + 0)
      (GeometricTrace.traceLength p.trace)
    exact ComputationalPaths.Path.ofEq (Nat.add_zero _)
  reversal_trace := fun p => GeometricTrace.traceLengthSymmPath p.trace
  path_coherence := fun p => p.coherent

/-- The maximal continuous-step model satisfies all three phases. -/
noncomputable def universalTopologicalWeakCompPathCertificate
    {A : Type u} [TopologicalSpace A] :
    TopologicalWeakCompPathCertificate A (ContinuousPathStep A)
      (continuousPathStepSystem A) :=
  topologicalWeakCompPathCertificate (continuousPathStepSystem A)

end GeometricTopology
end Path
end ComputationalPaths
