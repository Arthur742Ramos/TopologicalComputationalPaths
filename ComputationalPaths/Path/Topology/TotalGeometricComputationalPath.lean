import ComputationalPaths.Path.Topology.ContinuousGeometricStepSystem

/-!
# The total geometric computational-path space

The endpoint-indexed type
`OpenGeometricCompPath S a b` is a fibre.  To obtain a path space over a
topological ambient space, endpoints must be allowed to vary.  This file
packages the endpoint pair together with its coherent open path and equips the
result with the topology induced by the following observable coordinates:

* source and target in `A`;
* computational trace length;
* the continuous-map realization of the trace; and
* the continuous-map form of the chosen geometric path.

The last two coordinates are maps into the compact-open space `C(I, A)`, so
the construction remains sensitive to geometric motion and is not merely the
coarse trace-length topology.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

universe u v

/-! ## Total carrier and coordinates -/

/-- A coherent open geometric computational path with varying endpoints. -/
structure TotalOpenGeometricCompPath
    (A : Type u) [TopologicalSpace A]
    (Step : Type v) [TopologicalSpace Step]
    (S : ContinuousGeometricStepSystem A Step) where
  src : A
  tgt : A
  path : OpenGeometricCompPath S.toGeometricStepSystem src tgt

namespace TotalOpenGeometricCompPath

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  (S : ContinuousGeometricStepSystem A Step)

abbrev BasePath := OpenGeometricCompPath S.toGeometricStepSystem

/-- The finite computational trace carried by a total path. -/
def trace (p : TotalOpenGeometricCompPath A Step S) :
    GeometricTrace S.toGeometricStepSystem p.src p.tgt :=
  p.path.trace

/-- The chosen geometric representative carried by a total path. -/
def geometricPath (p : TotalOpenGeometricCompPath A Step S) :
    _root_.Path p.src p.tgt :=
  p.path.geometric

/-- The realized trace as a compact-open continuous map. -/
noncomputable def traceMap (p : TotalOpenGeometricCompPath A Step S) : C(unitInterval, A) :=
  (GeometricTrace.realize p.trace).toContinuousMap

/-- The geometric representative as a compact-open continuous map. -/
def geometricMap (p : TotalOpenGeometricCompPath A Step S) : C(unitInterval, A) :=
  p.geometricPath.toContinuousMap

/-- All coordinates used to topologize the total carrier. -/
abbrev Observation :=
  A × (A × (Nat × (C(unitInterval, A) × C(unitInterval, A))))

noncomputable def observation (p : TotalOpenGeometricCompPath A Step S) : Observation (A := A) :=
  (p.src, (p.tgt, (GeometricTrace.traceLength p.trace,
    (p.traceMap S, p.geometricMap S))))

noncomputable instance instTopologicalSpace :
    TopologicalSpace (TotalOpenGeometricCompPath A Step S) :=
  TopologicalSpace.induced (observation S) inferInstance

theorem continuous_observation :
    Continuous (observation S :
      TotalOpenGeometricCompPath A Step S → Observation (A := A)) :=
  continuous_induced_dom

theorem continuous_src :
    Continuous (fun p : TotalOpenGeometricCompPath A Step S => p.src) :=
  continuous_fst.comp (continuous_observation S)

theorem continuous_tgt :
    Continuous (fun p : TotalOpenGeometricCompPath A Step S => p.tgt) := by
  exact continuous_fst.comp (continuous_snd.comp (continuous_observation S))

theorem continuous_traceLength :
    Continuous (fun p : TotalOpenGeometricCompPath A Step S =>
      GeometricTrace.traceLength p.trace) := by
  exact continuous_fst.comp
    (continuous_snd.comp (continuous_snd.comp (continuous_observation S)))

theorem continuous_traceMap :
    Continuous (fun p : TotalOpenGeometricCompPath A Step S => p.traceMap S) := by
  exact continuous_fst.comp
    (continuous_snd.comp
      (continuous_snd.comp (continuous_snd.comp (continuous_observation S))))

theorem continuous_geometricMap :
    Continuous (fun p : TotalOpenGeometricCompPath A Step S => p.geometricMap S) := by
  exact continuous_snd.comp
    (continuous_snd.comp
      (continuous_snd.comp (continuous_snd.comp (continuous_observation S))))

theorem continuous_traceFamily :
    Continuous ↿(fun p : TotalOpenGeometricCompPath A Step S =>
      GeometricTrace.realize p.trace) := by
  change Continuous (fun pt :
      TotalOpenGeometricCompPath A Step S × unitInterval =>
      (traceMap S pt.1) pt.2)
  exact ContinuousMap.continuous_uncurry_of_continuous
    (⟨fun p : TotalOpenGeometricCompPath A Step S => traceMap S p,
      continuous_traceMap S⟩ :
      C(TotalOpenGeometricCompPath A Step S, C(unitInterval, A)))

theorem continuous_geometricFamily :
    Continuous ↿(fun p : TotalOpenGeometricCompPath A Step S =>
      p.geometricPath) := by
  change Continuous (fun pt :
      TotalOpenGeometricCompPath A Step S × unitInterval =>
      (geometricMap S pt.1) pt.2)
  exact ContinuousMap.continuous_uncurry_of_continuous
    (⟨fun p : TotalOpenGeometricCompPath A Step S => geometricMap S p,
      continuous_geometricMap S⟩ :
      C(TotalOpenGeometricCompPath A Step S, C(unitInterval, A)))

/-! ## Fibre inclusion -/

/-- Regard an endpoint-indexed path as a point of the total carrier. -/
def ofFiber {a b : A} (p : BasePath S a b) :
    TotalOpenGeometricCompPath A Step S :=
  ⟨a, b, p⟩

theorem continuous_fiberInclusion {a b : A} :
    Continuous (fun p : BasePath S a b => ofFiber S p) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : BasePath S a b =>
    (a, (b, (GeometricTrace.traceLength p.trace,
      ((GeometricTrace.realize p.trace).toContinuousMap, p.geometric.toContinuousMap)))))
  have htraceLength :
      Continuous (fun p : BasePath S a b =>
        GeometricTrace.traceLength p.trace) :=
    GeometricTrace.continuous_traceLength.comp (continuous_open_trace S.toGeometricStepSystem)
  have htraceMap :
      Continuous (fun p : BasePath S a b =>
        (GeometricTrace.realize p.trace).toContinuousMap) :=
    continuous_induced_dom.comp (continuous_open_realization S.toGeometricStepSystem)
  have hgeometricMap :
      Continuous (fun p : BasePath S a b => p.geometric.toContinuousMap) :=
    continuous_induced_dom.comp (continuous_open_geometric S.toGeometricStepSystem)
  exact continuous_const.prodMk <|
    continuous_const.prodMk <|
      htraceLength.prodMk (htraceMap.prodMk hgeometricMap)

/-! ## A direct computational certificate in the total carrier -/

noncomputable def totalPathLoopCertificate
    (p : TotalOpenGeometricCompPath A Step S) :
    ComputationalPaths.Path (GeometricTrace.traceLength p.trace)
      (GeometricTrace.traceLength p.trace) :=
  ComputationalPaths.Path.trans
    (ComputationalPaths.Path.refl (GeometricTrace.traceLength p.trace))
    (ComputationalPaths.Path.refl (GeometricTrace.traceLength p.trace))

/-- A genuine ambient interval path gives a point of the universal total
computational-path space, even when its endpoints are propositionally
distinct. -/
noncomputable def universalTotalPath
    {A : Type u} [TopologicalSpace A] {a b : A}
    (γ : _root_.Path a b) :
    TotalOpenGeometricCompPath A (ContinuousPathStep A)
      (continuousPathStepSystem A) :=
  ⟨a, b, by
    simpa only [_root_.Path.coe_toContinuousMap, _root_.Path.source,
      _root_.Path.target] using (continuousPathStep γ.toContinuousMap)⟩

end TotalOpenGeometricCompPath
end GeometricTopology
end Path
end ComputationalPaths
