import ComputationalPaths.Path.Topology.UniversalCompPathHomotopyEquivalence
import ComputationalPaths.Path.Topology.SemilocallySimplyConnected

/-!
# The universal presentation on fixed endpoint fibres

The one-letter section identifies the quotient of coherent paths with fixed
endpoints with the ordinary path-homotopy quotient.  This file records the
topological part of that comparison for based loops.  The topology here is
the final topology of the fixed endpoint raw carrier.  Identifying it with
the subspace topology inherited from the endpoint-varying quotient requires
an additional restriction argument.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

namespace UniversalCompPathHomotopyEquivalence

variable {A : Type*} [TopologicalSpace A] (x : A)

open QuotientFundamentalGroup

theorem continuous_toBasedPathClass :
    Continuous (toPathClass (A := A) (a := x) (b := x) :
      UniversalClass (A := A) (a := x) (b := x) →
        QuotientFundamentalGroup.LoopQuot A x) := by
  apply Continuous.quotient_lift
  exact continuous_quotient_mk'.comp
    (continuous_open_geometric
      (continuousPathStepSystem A).toGeometricStepSystem)

theorem continuous_fromBasedPathClass :
    Continuous (fromPathClass (A := A) (a := x) (b := x) :
      QuotientFundamentalGroup.LoopQuot A x →
        UniversalClass (A := A) (a := x) (b := x)) := by
  apply Continuous.quotient_lift
  exact (TotalOpenGeometricCompPath.continuous_quotientMk
    (continuousPathStepSystem A)).comp
      (continuous_universalOpenSection (A := A))

noncomputable def universalBasedFiberHomeomorph :
    UniversalClass (A := A) (a := x) (b := x) ≃ₜ
      QuotientFundamentalGroup.LoopQuot A x where
  toEquiv := quotientEquiv (A := A) (a := x) (b := x)
  continuous_toFun := continuous_toBasedPathClass x
  continuous_invFun := continuous_fromBasedPathClass x

theorem universalBasedFiber_discrete
    [LocallyPathConnectedSpace A]
    (hsemi : QuotientFundamentalGroup.SemilocallySimplyConnected A) :
    DiscreteTopology (UniversalClass (A := A) (a := x) (b := x)) := by
  letI := QuotientFundamentalGroup.quotientDiscreteTopology_of_semilocallySimplyConnected
    A hsemi x
  exact DiscreteTopology.of_continuous_injective
    (continuous_toBasedPathClass x)
    (quotientEquiv (A := A) (a := x) (b := x)).injective

/-- On fixed based fibres, the product of the two coherent-path quotient
maps is quotient. This identifies the final pair topology with the ordinary
product topology for the endpoint-fixed presentation. -/
theorem universalBasedPair_isQuotient
    [LocallyPathConnectedSpace A]
    (hsemi : QuotientFundamentalGroup.SemilocallySimplyConnected A) :
    Topology.IsQuotientMap
      (Prod.map
        (TotalOpenGeometricCompPath.quotientMk (continuousPathStepSystem A)
          (a := x) (b := x))
        (TotalOpenGeometricCompPath.quotientMk (continuousPathStepSystem A)
          (a := x) (b := x))) := by
  letI := universalBasedFiber_discrete x hsemi
  have hopen : IsOpenQuotientMap
      (TotalOpenGeometricCompPath.quotientMk (continuousPathStepSystem A)
        (a := x) (b := x)) :=
    { surjective := (isQuotientMap_quotient_mk').surjective
      continuous := TotalOpenGeometricCompPath.continuous_quotientMk _
      isOpenMap := fun _ _ => isOpen_discrete _ }
  exact (hopen.prodMap hopen).isQuotientMap

theorem continuous_universalBasedTrans
    [LocallyPathConnectedSpace A]
    (hsemi : QuotientFundamentalGroup.SemilocallySimplyConnected A) :
    Continuous (fun pq :
      UniversalClass (A := A) (a := x) (b := x) ×
        UniversalClass (A := A) (a := x) (b := x) =>
      TotalOpenGeometricCompPath.quotientTrans
        (continuousPathStepSystem A) pq.1 pq.2) := by
  letI := universalBasedFiber_discrete x hsemi
  exact continuous_of_discreteTopology

end UniversalCompPathHomotopyEquivalence
end GeometricTopology
end Path
end ComputationalPaths
