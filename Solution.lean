import Mathlib.Topology.Constructions
import ComputationalPaths

/-!
# Solution: final-domain topological semantics

The proof is written against the statement-only interface and uses only
quotient-map and topological-equivalence facts.  The focused computational-path
development supplies the corresponding scoped quotient construction; see the
bridge theorem below for the concrete connection.
-/

namespace TopologicalComputationalPaths

universe u v w

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
    {RawPair : Type u} {OrdinaryPair : Type v} {Arrow : Type w}
    [TopologicalSpace RawPair]
    [TopologicalSpace OrdinaryPair] [TopologicalSpace Arrow]
    (D : ScopedFinalPairData RawPair OrdinaryPair Arrow) :
    ScopedFinalSemanticsCertificate D := by
  let q := D.quotient
  let e := D.comparison
  have hq : Topology.IsQuotientMap q := by
    exact ScopedFinalPairData.quotient_is_quotient D
  have he : Continuous e := D.comparison_continuous
  have hq_continuous : Continuous q := hq.continuous
  have hfinal : Continuous D.finalOperation := by
    apply hq.continuous_iff.2
    convert D.rawOperation_continuous using 1
    funext r
    rfl
  have hpair_iff_comparison :
      Topology.IsQuotientMap (e ∘ q) ↔ Topology.IsQuotientMap e := by
    constructor
    · intro hcomp
      apply Topology.IsQuotientMap.of_comp hq_continuous he hcomp
    · intro hcomparison
      exact hcomparison.comp hq
  have hcomparison_iff_inverse :
      Topology.IsQuotientMap e ↔ Continuous e.invFun := by
    constructor
    · intro hcomparison
      apply hcomparison.continuous_iff.2
      have hcomp : e.invFun ∘ e = id := by
        funext x
        exact e.left_inv x
      rw [hcomp]
      exact continuous_id
    · intro hinverse
      let E : Quotient D.relation ≃ₜ OrdinaryPair :=
        { toEquiv := e
          continuous_toFun := he
          continuous_invFun := hinverse }
      exact E.isQuotientMap
  have hinverse_iff_topology :
      Continuous e.invFun ↔ D.topologyAgreement := by
    constructor
    · intro hinverse
      let E : Quotient D.relation ≃ₜ OrdinaryPair :=
        { toEquiv := e
          continuous_toFun := he
          continuous_invFun := hinverse }
      exact E.isInducing.eq_induced
    · intro htop
      have hinducing : Topology.IsInducing e := Topology.IsInducing.mk htop
      have hcomparison : Topology.IsQuotientMap e :=
        hinducing.isQuotientMap_of_surjective e.surjective
      exact hcomparison_iff_inverse.mp hcomparison
  have hordinary : Continuous e.invFun → Continuous D.ordinaryOperation := by
    intro hinverse
    have hdesc : Continuous (D.ordinaryOperation ∘ e) := by
      apply hq.continuous_iff.2
      convert D.rawOperation_continuous using 1
      funext r
      exact D.ordinary_factor r
    simpa [Function.comp_def] using hdesc.comp hinverse
  exact
    { final_operation_continuous := hfinal
      pair_map_quotient_iff_comparison_quotient := hpair_iff_comparison
      comparison_quotient_iff_inverse_continuous := hcomparison_iff_inverse
      inverse_continuous_iff_topology_agreement := hinverse_iff_topology
      ordinary_operation_continuous_of_inverse := hordinary }

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
