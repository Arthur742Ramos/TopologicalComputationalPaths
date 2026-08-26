import Mathlib.Topology.Constructions

/-!
# Challenge: final-domain topological semantics

Prove the certificate in `main_result`.  The data models a quotient of raw
composable representatives, its ordinary-pair comparison, and a descended
composition operation.  The result must distinguish unconditional continuity
on the final domain from continuity on the ordinary pullback domain.
-/

namespace TopologicalComputationalPaths

universe u v w

/-! `ScopedFinalPairData` is the statement-side abstraction of a quotient
of raw composable representatives.  The quotient has a final-domain
operation, while `comparison` identifies that domain with an ordinary
endpoint-compatible pair space. -/
structure ScopedFinalPairData
    (RawPair : Type u) (FinalPair : Type v) (OrdinaryPair : Type v)
    (Arrow : Type w)
    [TopologicalSpace RawPair] [TopologicalSpace FinalPair]
    [TopologicalSpace OrdinaryPair] [TopologicalSpace Arrow] where
  quotient : RawPair → FinalPair
  comparison : FinalPair ≃ OrdinaryPair
  rawOperation : RawPair → Arrow
  finalOperation : FinalPair → Arrow
  ordinaryOperation : OrdinaryPair → Arrow
  quotient_is_quotient : Topology.IsQuotientMap quotient
  comparison_continuous : Continuous comparison
  rawOperation_continuous : Continuous rawOperation
  final_factor : ∀ r, finalOperation (quotient r) = rawOperation r
  ordinary_factor : ∀ r,
    ordinaryOperation (comparison (quotient r)) = rawOperation r

namespace ScopedFinalPairData

variable {RawPair : Type u} {FinalPair OrdinaryPair : Type v} {Arrow : Type w}
  [TopologicalSpace RawPair] [TopologicalSpace FinalPair]
  [TopologicalSpace OrdinaryPair] [TopologicalSpace Arrow]
  (D : ScopedFinalPairData RawPair FinalPair OrdinaryPair Arrow)

/-! The raw map into the ordinary pair space. -/
def pairMap : RawPair → OrdinaryPair := D.comparison ∘ D.quotient

/-! The ordinary topology is the topology induced by the comparison map. -/
def topologyAgreement : Prop :=
  (inferInstance : TopologicalSpace FinalPair) =
    TopologicalSpace.induced D.comparison
      (inferInstance : TopologicalSpace OrdinaryPair)

end ScopedFinalPairData

/-! The topological and quotient-map consequences of the final-domain model. -/
structure ScopedFinalSemanticsCertificate
    {RawPair : Type u} {FinalPair OrdinaryPair : Type v} {Arrow : Type w}
    [TopologicalSpace RawPair] [TopologicalSpace FinalPair]
    [TopologicalSpace OrdinaryPair] [TopologicalSpace Arrow]
    (D : ScopedFinalPairData RawPair FinalPair OrdinaryPair Arrow) : Prop where
  final_operation_continuous : Continuous D.finalOperation
  pair_map_quotient_iff_comparison_quotient :
    Topology.IsQuotientMap (D.pairMap) ↔
      Topology.IsQuotientMap D.comparison
  comparison_quotient_iff_inverse_continuous :
    Topology.IsQuotientMap D.comparison ↔
      Continuous D.comparison.invFun
  inverse_continuous_iff_topology_agreement :
    Continuous D.comparison.invFun ↔ D.topologyAgreement
  ordinary_operation_continuous_of_inverse :
    Continuous D.comparison.invFun → Continuous D.ordinaryOperation

/-! Final-domain continuity is unconditional; ordinary-domain continuity is
available exactly through the inverse/comparison criterion recorded here. -/
theorem main_result
    {RawPair : Type u} {FinalPair OrdinaryPair : Type v} {Arrow : Type w}
    [TopologicalSpace RawPair] [TopologicalSpace FinalPair]
    [TopologicalSpace OrdinaryPair] [TopologicalSpace Arrow]
    (D : ScopedFinalPairData RawPair FinalPair OrdinaryPair Arrow) :
    ScopedFinalSemanticsCertificate D := by
  sorry

end TopologicalComputationalPaths
