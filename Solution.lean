import Mathlib.Topology.Constructions
import ComputationalPaths

/-!
# Solution: topological semantics of computational paths

The selected theorem is the concrete scoped geometric rewrite quotient result:
its final-domain operations form a topological groupoid, the rewrite relation
is sound for geometric realization, and explicit trace witnesses remain
available.  The generic final-domain/comparison interface below is retained as
supporting notation for the extraction adapter.
-/

namespace TopologicalComputationalPaths

universe u v w

open ComputationalPaths.Path.GeometricTopology
open ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite

/-! The publication-facing certificate keeps the concrete quotient groupoid
and its computational-path witnesses visible in the theorem type. -/

structure ScopedTopologicalComputationalPathCertificate
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    (S : ContinuousGeometricStepSystem A Step)
    (P : ScopedGeometricRewritePresentation S) : Prop where
  source_continuous : Continuous (scopedSrc P)
  target_continuous : Continuous (scopedTgt P)
  identity_continuous : Continuous (scopedRefl P)
  inverse_continuous : Continuous (scopedSymm P)
  final_composition_continuous :
    Continuous (scopedCompositionOnStrong P :
      ScopedStrongComposablePair P → ScopedClass P)
  left_unit : ∀ p : ScopedClass P,
    scopedCompositionOnStrong P (strongLeftUnitPair P p) = p
  right_unit : ∀ p : ScopedClass P,
    scopedCompositionOnStrong P (strongRightUnitPair P p) = p
  right_inverse : ∀ p : ScopedClass P,
    scopedCompositionOnStrong P (strongRightInversePair P p) =
      scopedRefl P (scopedSrc P p)
  left_inverse : ∀ p : ScopedClass P,
    scopedCompositionOnStrong P (strongLeftInversePair P p) =
      scopedRefl P (scopedTgt P p)
  associativity : ∀ t : ScopedComposableTriple P,
    scopedCompositionOnStrong P (tripleLeftPair P t) =
      scopedCompositionOnStrong P (tripleRightPair P t)
  rewrite_sound :
    ∀ {p q : ScopedRawPath (S := S)},
      scopedEquivalent P p q →
        ∃ hs : q.src = p.src, ∃ ht : q.tgt = p.tgt,
          _root_.Path.Homotopic
            (GeometricTrace.realize (castScopedTrace hs ht))
            (GeometricTrace.realize q.trace)
  trace_composition : ∀ c : ScopedComposableRaw (S := S),
    GeometricTrace.traceLength
        (GeometricTrace.trans c.left.trace c.right.trace) =
      GeometricTrace.traceLength c.left.trace +
        GeometricTrace.traceLength c.right.trace
  trace_unit_rewrite : ∀ p : ScopedRawPath (S := S),
    ScopedRwEq P
      (GeometricTrace.trans (GeometricTrace.refl p.src) p.trace)
      p.trace

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
    ScopedTopologicalComputationalPathCertificate S P := by
  let G := scopedFinalTopologicalGroupoidCertificate P
  exact
    { source_continuous := G.source_continuous
      target_continuous := G.target_continuous
      identity_continuous := G.identity_continuous
      inverse_continuous := G.inverse_continuous
      final_composition_continuous := G.final_composition_continuous
      left_unit := G.left_unit
      right_unit := G.right_unit
      right_inverse := G.right_inverse
      left_inverse := G.left_inverse
      associativity := G.associativity
      rewrite_sound := by
        intro p q h
        exact scopedEquivalent_sound P h
      trace_composition := by
        intro c
        rfl
      trace_unit_rewrite := by
        intro p
        exact ScopedRwEq.refl_trans p.trace }

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
