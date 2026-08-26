import Mathlib.Topology.Constructions
import ComputationalPaths

/-!
# Solution: topological semantics of computational paths

The selected theorem is the exact comparison between the canonical final
composable topology and the ordinary pullback topology.  It identifies the
quotient-map, homeomorphism, and induced-topology criteria; transfers
continuity to ordinary composition; and proves compact--Hausdorff and discrete
sufficient cases.  The generic final-domain interface below remains supporting
notation for the extraction adapter.
-/

namespace TopologicalComputationalPaths

universe u v w

open ComputationalPaths.Path.GeometricTopology
open ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite

/-! ## The ordinary/final topology comparison -/

noncomputable def finalToOrdinary
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    {S : ContinuousGeometricStepSystem A Step}
    (P : ScopedGeometricRewritePresentation S) :
    ScopedComposableClass P → ScopedComposablePair P :=
  fun c => (scopedPairMap P c).val

noncomputable def rawToOrdinary
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    {S : ContinuousGeometricStepSystem A Step}
    (P : ScopedGeometricRewritePresentation S) :
    ScopedComposableRaw (S := S) → ScopedComposablePair P :=
  fun c => finalToOrdinary P (scopedComposableMk P c)

noncomputable def ordinaryComposition
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    {S : ContinuousGeometricStepSystem A Step}
    (P : ScopedGeometricRewritePresentation S) :
    ScopedComposablePair P → ScopedClass P :=
  fun pq => scopedCompositionOnStrong P ⟨pq⟩

structure OrdinaryTopologyComparisonCertificate
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    (S : ContinuousGeometricStepSystem A Step)
    (P : ScopedGeometricRewritePresentation S) : Prop where
  canonical_bijection : Function.Bijective (finalToOrdinary P)
  canonical_map_continuous : Continuous (finalToOrdinary P)
  raw_quotient_criterion :
    Topology.IsQuotientMap (finalToOrdinary P) ↔
      Topology.IsQuotientMap (rawToOrdinary P)
  homeomorphism_criterion :
    Topology.IsQuotientMap (finalToOrdinary P) ↔
      ∃ e : ScopedComposableClass P ≃ₜ ScopedComposablePair P,
        (e : ScopedComposableClass P → ScopedComposablePair P) =
          finalToOrdinary P
  topology_agreement_criterion :
    Topology.IsQuotientMap (finalToOrdinary P) ↔
      (inferInstance : TopologicalSpace (ScopedComposableClass P)) =
        TopologicalSpace.induced (finalToOrdinary P)
          (inferInstance : TopologicalSpace (ScopedComposablePair P))
  ordinary_composition_of_quotient :
    Topology.IsQuotientMap (finalToOrdinary P) →
      Continuous (ordinaryComposition P)
  discontinuity_obstructs_compatibility :
    ¬ Continuous (ordinaryComposition P) →
      ¬ Topology.IsQuotientMap (finalToOrdinary P)
  compact_hausdorff_recovers_ordinary :
    ∀ [CompactSpace (ScopedComposableClass P)]
      [T2Space (ScopedComposablePair P)],
      Topology.IsQuotientMap (finalToOrdinary P) ∧
        Continuous (ordinaryComposition P)
  discrete_recovers_ordinary :
    ∀ [DiscreteTopology (ScopedClass P)]
      [DiscreteTopology (ScopedComposableClass P)],
      Topology.IsQuotientMap (finalToOrdinary P) ∧
        Continuous (ordinaryComposition P)

/-! The statement and solution use the same final topology on quotient domains. -/
noncomputable instance quotientFinalTopology
    {RawPair : Type u} [TopologicalSpace RawPair] (R : Setoid RawPair) :
    TopologicalSpace (Quotient R) :=
  TopologicalSpace.coinduced (Quotient.mk R) inferInstance

structure ScopedFinalPairData
    (RawPair : Type u) (OrdinaryPair : Type v)
    (Arrow : Type w)
    [TopologicalSpace RawPair]
    [TopologicalSpace OrdinaryPair] [TopologicalSpace Arrow] where
  relation : Setoid RawPair
  comparison : Quotient relation ≃ OrdinaryPair
  rawOperation : RawPair → Arrow
  ordinaryOperation : OrdinaryPair → Arrow
  operation_respects :
    ∀ {r s : RawPair}, relation.r r s → rawOperation r = rawOperation s
  comparison_continuous : Continuous comparison
  rawOperation_continuous : Continuous rawOperation
  ordinary_factor : ∀ r,
    ordinaryOperation (comparison (Quotient.mk relation r)) = rawOperation r

namespace ScopedFinalPairData

variable {RawPair : Type u} {OrdinaryPair : Type v} {Arrow : Type w}
  [TopologicalSpace RawPair]
  [TopologicalSpace OrdinaryPair] [TopologicalSpace Arrow]
  (D : ScopedFinalPairData RawPair OrdinaryPair Arrow)

def quotient : RawPair → Quotient D.relation := Quotient.mk D.relation

noncomputable def finalOperation : Quotient D.relation → Arrow :=
  Quotient.lift D.rawOperation (by
    intro r s h
    exact D.operation_respects h)

theorem quotient_is_quotient : Topology.IsQuotientMap D.quotient := by
  exact ⟨⟨rfl⟩, Quotient.mk_surjective⟩

def pairMap : RawPair → OrdinaryPair := D.comparison ∘ D.quotient

def topologyAgreement : Prop :=
  (inferInstance : TopologicalSpace (Quotient D.relation)) =
    TopologicalSpace.induced D.comparison
      (inferInstance : TopologicalSpace OrdinaryPair)

end ScopedFinalPairData

structure ScopedFinalSemanticsCertificate
    {RawPair : Type u} {OrdinaryPair : Type v} {Arrow : Type w}
    [TopologicalSpace RawPair]
    [TopologicalSpace OrdinaryPair] [TopologicalSpace Arrow]
    (D : ScopedFinalPairData RawPair OrdinaryPair Arrow) : Prop where
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

theorem main_result
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    (S : ContinuousGeometricStepSystem A Step)
    (P : ScopedGeometricRewritePresentation S) :
    OrdinaryTopologyComparisonCertificate S P := by
  have hBijective : Function.Bijective (finalToOrdinary P) :=
    ⟨scopedPairToOrdinary_injective P,
      scopedPairToOrdinary_surjective P⟩
  have hContinuous : Continuous (finalToOrdinary P) :=
    continuous_scopedPairToOrdinary P
  have hComposition :
      Topology.IsQuotientMap (finalToOrdinary P) →
        Continuous (ordinaryComposition P) := by
    intro h
    exact continuous_scopedCompositionOnProduct P ⟨h⟩
  exact
    { canonical_bijection := hBijective
      canonical_map_continuous := hContinuous
      raw_quotient_criterion := by
        constructor
        · intro h
          exact
            (scopedProductCompatibility_iff_raw_pair_map_quotient P).1 ⟨h⟩
        · intro h
          exact
            ((scopedProductCompatibility_iff_raw_pair_map_quotient P).2 h).pair_map_is_quotient
      homeomorphism_criterion := by
        constructor
        · intro h
          exact ⟨scopedFinalOrdinaryHomeomorph P ⟨h⟩, rfl⟩
        · rintro ⟨e, he⟩
          simpa [he] using e.isQuotientMap
      topology_agreement_criterion := by
        constructor
        · intro h
          exact
            (scopedProductCompatibility_iff_final_topology_agreement P).1 ⟨h⟩
        · intro h
          exact
            ((scopedProductCompatibility_iff_final_topology_agreement P).2 h).pair_map_is_quotient
      ordinary_composition_of_quotient := hComposition
      discontinuity_obstructs_compatibility := by
        intro hnot hquot
        exact hnot (hComposition hquot)
      compact_hausdorff_recovers_ordinary := by
        intro _ _
        let h := scopedProductCompatibility_of_compact_final_t2 P
        exact ⟨h.pair_map_is_quotient,
          continuous_scopedCompositionOnProduct P h⟩
      discrete_recovers_ordinary := by
        intro _ _
        let h :=
          scopedProductCompatibility_of_discrete_arrow_and_final_domain P
        exact ⟨h.pair_map_is_quotient,
          continuous_scopedCompositionOnProduct P h⟩ }

/-! The substantive repository contains the scoped quotient construction.  The
 following adapter makes the statement-side interface concrete: its raw
 operation is the actual quotient-level composition map, its final operation
 is the canonical descent of that raw map, and its comparison is the actual
 final-to-ordinary equivalence. -/

noncomputable def scopedFinalPairData
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    (S : _root_.ComputationalPaths.Path.GeometricTopology.ContinuousGeometricStepSystem A Step)
    (P : _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewritePresentation S) :
    ScopedFinalPairData
      (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedComposableRaw (S := S))
      (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedComposablePair P)
      (_root_.ComputationalPaths.Path.GeometricTopology.ScopedClass P) where
  relation := _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedComposableSetoid P
  comparison := _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedPairToOrdinaryEquiv P
  rawOperation := fun c =>
    _root_.ComputationalPaths.Path.GeometricTopology.scopedQuotientMk P
      (_root_.ComputationalPaths.Path.GeometricTopology.TotalOpenGeometricCompPath.totalTrans S c)
  ordinaryOperation := _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedCompositionOnProduct P
  operation_respects := by
    intro c d h
    exact Quotient.sound
      (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedEquivalent_totalTrans
        P h.1 h.2)
  comparison_continuous :=
    _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.continuous_scopedPairToOrdinary P
  rawOperation_continuous := by
    exact _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.continuous_scopedQuotientMk P |>.comp
      (_root_.ComputationalPaths.Path.GeometricTopology.TotalOpenGeometricCompPath.continuous_totalTrans S)
  ordinary_factor := by
    intro c
    change
      _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedCompositionOnProduct P
          (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedPairToOrdinary P
            (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedComposableMk P c)) =
        _root_.ComputationalPaths.Path.GeometricTopology.scopedQuotientMk P
          (_root_.ComputationalPaths.Path.GeometricTopology.TotalOpenGeometricCompPath.totalTrans S c)
    rw [_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedCompositionOnProduct_pairMap]
    rfl

theorem scoped_final_operation_agrees
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    (S : _root_.ComputationalPaths.Path.GeometricTopology.ContinuousGeometricStepSystem A Step)
    (P : _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewritePresentation S)
    (c : _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedComposableClass P) :
    ScopedFinalPairData.finalOperation (scopedFinalPairData S P) c =
      _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedCompositionFromComposable P c := by
  refine Quotient.inductionOn c ?_
  intro c
  rfl

theorem scoped_groupoid_core_is_available :
    ∀ {A : Type u} [TopologicalSpace A]
      {Step : Type v} [TopologicalSpace Step]
      (S : _root_.ComputationalPaths.Path.GeometricTopology.ContinuousGeometricStepSystem A Step)
      (P : _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewritePresentation S),
      Nonempty (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedFinalTopologicalGroupoidCertificate P) := by
  intro A instA Step instStep S P
  exact ⟨_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedFinalTopologicalGroupoidCertificate P⟩

theorem scoped_pair_data_is_well_formed :
    ∀ {A : Type u} [TopologicalSpace A]
      {Step : Type v} [TopologicalSpace Step]
      (S : _root_.ComputationalPaths.Path.GeometricTopology.ContinuousGeometricStepSystem A Step)
      (P : _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewritePresentation S),
      Nonempty (ScopedFinalPairData
        (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedComposableRaw (S := S))
        (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedComposablePair P)
        (_root_.ComputationalPaths.Path.GeometricTopology.ScopedClass P)) := by
  intro A instA Step instStep S P
  exact ⟨scopedFinalPairData S P⟩

end TopologicalComputationalPaths
