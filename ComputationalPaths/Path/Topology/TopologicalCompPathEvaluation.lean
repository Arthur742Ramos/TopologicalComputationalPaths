import ComputationalPaths.Path.Topology.TopologicalCompPathOperations

/-!
# Evaluation and endpoint structure on total computational paths

The total carrier is not merely a set of endpoint-indexed fibres.  Its
geometric and trace realizations evaluate continuously in the ambient space.
This file records those evaluation maps and proves that evaluation at the two
ends recovers the endpoint map.

The result is the basic interface needed before constructing a genuine
topological path-groupoid bundle or comparing it with a simplicial nerve.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

universe u v

namespace TotalOpenGeometricCompPath

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  (S : ContinuousGeometricStepSystem A Step)

abbrev TotalPath := TotalOpenGeometricCompPath A Step S

/-- The endpoint map of the total computational-path space. -/
def endpoint (p : TotalPath S) : A × A :=
  (p.src, p.tgt)

theorem continuous_endpoint :
    Continuous (endpoint S : TotalPath S → A × A) :=
  (continuous_src S).prodMk (continuous_tgt S)

/-- Evaluation of the realized computational trace. -/
noncomputable def traceEvaluation
    (z : TotalPath S × unitInterval) : A :=
  (traceMap S z.1) z.2

/-- Evaluation of the chosen geometric representative. -/
noncomputable def geometricEvaluation
    (z : TotalPath S × unitInterval) : A :=
  (geometricMap S z.1) z.2

theorem continuous_traceEvaluation :
    Continuous (traceEvaluation S : TotalPath S × unitInterval → A) := by
  change Continuous (fun z : TotalPath S × unitInterval =>
    (traceMap S z.1) z.2)
  exact ContinuousEval.continuous_eval.comp
    ((continuous_traceMap S).prodMap continuous_id)

theorem continuous_geometricEvaluation :
    Continuous (geometricEvaluation S : TotalPath S × unitInterval → A) := by
  change Continuous (fun z : TotalPath S × unitInterval =>
    (geometricMap S z.1) z.2)
  exact ContinuousEval.continuous_eval.comp
    ((continuous_geometricMap S).prodMap continuous_id)

theorem traceEvaluation_zero (p : TotalPath S) :
    traceEvaluation S (p, (0 : unitInterval)) = p.src := by
  change (GeometricTrace.realize p.trace).toContinuousMap 0 = p.src
  exact (GeometricTrace.realize p.trace).source

theorem traceEvaluation_one (p : TotalPath S) :
    traceEvaluation S (p, (1 : unitInterval)) = p.tgt := by
  change (GeometricTrace.realize p.trace).toContinuousMap 1 = p.tgt
  exact (GeometricTrace.realize p.trace).target

theorem geometricEvaluation_zero (p : TotalPath S) :
    geometricEvaluation S (p, (0 : unitInterval)) = p.src := by
  change p.geometricPath.toContinuousMap 0 = p.src
  exact p.geometricPath.source

theorem geometricEvaluation_one (p : TotalPath S) :
    geometricEvaluation S (p, (1 : unitInterval)) = p.tgt := by
  change p.geometricPath.toContinuousMap 1 = p.tgt
  exact p.geometricPath.target

/-- The pair of geometric endpoint evaluations. -/
noncomputable def geometricEndpointEvaluation (p : TotalPath S) : A × A :=
  (geometricEvaluation S (p, (0 : unitInterval)),
    geometricEvaluation S (p, (1 : unitInterval)))

theorem continuous_geometricEndpointEvaluation :
    Continuous (geometricEndpointEvaluation S : TotalPath S → A × A) := by
  have hzero : Continuous (fun p : TotalPath S =>
      geometricEvaluation S (p, (0 : unitInterval))) :=
    (continuous_geometricEvaluation S).comp
      (continuous_id.prodMk continuous_const)
  have hone : Continuous (fun p : TotalPath S =>
      geometricEvaluation S (p, (1 : unitInterval))) :=
    (continuous_geometricEvaluation S).comp
      (continuous_id.prodMk continuous_const)
  exact hzero.prodMk hone

theorem geometricEndpointEvaluation_eq_endpoint (p : TotalPath S) :
    geometricEndpointEvaluation S p = endpoint S p := by
  exact Prod.ext (geometricEvaluation_zero S p) (geometricEvaluation_one S p)

theorem traceEndpointEvaluation_eq_endpoint (p : TotalPath S) :
    (traceEvaluation S (p, (0 : unitInterval)),
      traceEvaluation S (p, (1 : unitInterval))) = endpoint S p := by
  exact Prod.ext (traceEvaluation_zero S p) (traceEvaluation_one S p)

theorem endpoint_totalRefl (a : A) :
    endpoint S (totalRefl S a) = (a, a) := by
  rfl

/-! ## A compact phase-four certificate -/

structure TopologicalCompPathEvaluationCertificate where
  endpoint_continuous :
    Continuous (endpoint S : TotalPath S → A × A)
  trace_evaluation_continuous :
    Continuous (traceEvaluation S : TotalPath S × unitInterval → A)
  geometric_evaluation_continuous :
    Continuous (geometricEvaluation S : TotalPath S × unitInterval → A)
  geometric_endpoints_recover :
    ∀ p : TotalPath S, geometricEndpointEvaluation S p = endpoint S p
  trace_endpoints_recover :
    ∀ p : TotalPath S,
      (traceEvaluation S (p, (0 : unitInterval)),
        traceEvaluation S (p, (1 : unitInterval))) = endpoint S p
  identity_endpoint :
    ∀ a : A, endpoint S (totalRefl S a) = (a, a)

noncomputable def topologicalCompPathEvaluationCertificate :
    TopologicalCompPathEvaluationCertificate S where
  endpoint_continuous := continuous_endpoint S
  trace_evaluation_continuous := continuous_traceEvaluation S
  geometric_evaluation_continuous := continuous_geometricEvaluation S
  geometric_endpoints_recover := geometricEndpointEvaluation_eq_endpoint S
  trace_endpoints_recover := traceEndpointEvaluation_eq_endpoint S
  identity_endpoint := endpoint_totalRefl S

/-! A direct multi-step computational witness remains visible at this phase. -/
noncomputable def endpointLoopCertificate (p : TotalPath S) :
    ComputationalPaths.Path p.src p.src :=
  ComputationalPaths.Path.trans
    (ComputationalPaths.Path.refl p.src)
    (ComputationalPaths.Path.refl p.src)

end TotalOpenGeometricCompPath
end GeometricTopology
end Path
end ComputationalPaths
