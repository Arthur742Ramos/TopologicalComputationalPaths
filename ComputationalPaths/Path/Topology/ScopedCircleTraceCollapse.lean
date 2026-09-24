import ComputationalPaths.Path.Topology.ScopedGeometricRewriteCircle
import ComputationalPaths.Path.Topology.TraceSensitiveTopologicalCompPath

/-!
# Trace-sensitive and observable based circle quotients

For the integer-step circle presentation, winding selects a canonical
one-letter trace continuously.  The two quotient topologies on its fixed
basepoint loop carrier therefore agree.  These quotients are formed from the
fixed-endpoint carrier; the endpoint-varying scoped quotient has a separate
subspace topology.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology
namespace ScopedGeometricRewrite

open scoped ContinuousMap Topology
open ConcreteCircleWinding

noncomputable def circleLoopTraceSensitiveTopology :
    TopologicalSpace CircleOpenLoop :=
  TopologicalSpace.induced
    (fun p : CircleOpenLoop =>
      (GeometricTrace.flatWord p.trace, (p.trace, p.geometric))) inferInstance

theorem continuous_circleLoopTraceSensitive_to_observable :
    @Continuous CircleOpenLoop CircleOpenLoop
      circleLoopTraceSensitiveTopology inferInstance id := by
  apply continuous_induced_rng.mpr
  have h : @Continuous CircleOpenLoop
      (FlatWord ℤ × (CircleTrace × _root_.Path (0 : TopologicalCircle) 0))
      circleLoopTraceSensitiveTopology inferInstance
      (fun p => (GeometricTrace.flatWord p.trace, (p.trace, p.geometric))) :=
    continuous_induced_dom
  have hsnd : Continuous (fun z : FlatWord ℤ ×
      (CircleTrace × _root_.Path (0 : TopologicalCircle) 0) => z.2) :=
    continuous_snd
  simpa [Function.comp_def] using
    (@Continuous.comp CircleOpenLoop _ _ circleLoopTraceSensitiveTopology
      inferInstance inferInstance _ _ hsnd h)

noncomputable def circleChosenTrace
    (γ : _root_.Path (0 : TopologicalCircle) 0) : CircleOpenLoop :=
  circleStandardOpenLoop (ConcreteCircleWinding.windingPath γ)

theorem continuous_circleChosenTrace :
    @Continuous (_root_.Path (0 : TopologicalCircle) 0) CircleOpenLoop
      inferInstance circleLoopTraceSensitiveTopology circleChosenTrace := by
  have hchoice : @Continuous ℤ CircleOpenLoop inferInstance
      circleLoopTraceSensitiveTopology circleStandardOpenLoop := by
    letI : TopologicalSpace CircleOpenLoop := circleLoopTraceSensitiveTopology
    exact continuous_of_discreteTopology
  exact @Continuous.comp _ _ _ inferInstance inferInstance
    circleLoopTraceSensitiveTopology _ _ hchoice
      ConcreteCircleWinding.continuous_windingPath

theorem circleChosenTrace_equivalent (p : CircleOpenLoop) :
    circleLoopEquivalent (circleChosenTrace p.geometric) p :=
  ConcreteCircleWinding.standardLoop_homotopic p.geometric

noncomputable def circleLoopTraceSensitiveHomeomorph :
    @Homeomorph CircleLoopClass CircleLoopClass
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        circleLoopSetoid circleLoopTraceSensitiveTopology)
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        circleLoopSetoid inferInstance) :=
  TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientComparisonHomeomorph_of_realization_section
    circleLoopSetoid continuous_circleLoopTraceSensitive_to_observable
    (fun p : CircleOpenLoop => p.geometric) circleChosenTrace
    (continuous_open_geometric circleLoopStepSystem.toGeometricStepSystem)
    continuous_circleChosenTrace
    (fun p => Quotient.sound (circleChosenTrace_equivalent p))

end ScopedGeometricRewrite
end GeometricTopology
end Path
end ComputationalPaths
