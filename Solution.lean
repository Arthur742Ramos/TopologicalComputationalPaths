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

def pairMap : RawPair → OrdinaryPair := D.comparison ∘ D.quotient

def topologyAgreement : Prop :=
  (inferInstance : TopologicalSpace FinalPair) =
    TopologicalSpace.induced D.comparison
      (inferInstance : TopologicalSpace OrdinaryPair)

end ScopedFinalPairData

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

theorem main_result
    {RawPair : Type u} {FinalPair OrdinaryPair : Type v} {Arrow : Type w}
    [TopologicalSpace RawPair] [TopologicalSpace FinalPair]
    [TopologicalSpace OrdinaryPair] [TopologicalSpace Arrow]
    (D : ScopedFinalPairData RawPair FinalPair OrdinaryPair Arrow) :
    ScopedFinalSemanticsCertificate D := by
  let q := D.quotient
  let e := D.comparison
  have hq : Topology.IsQuotientMap q := D.quotient_is_quotient
  have he : Continuous e := D.comparison_continuous
  have hq_continuous : Continuous q := hq.continuous
  have hfinal : Continuous D.finalOperation := by
    apply hq.continuous_iff.2
    convert D.rawOperation_continuous using 1
    funext r
    exact D.final_factor r
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
      let E : FinalPair ≃ₜ OrdinaryPair :=
        { toEquiv := e
          continuous_toFun := he
          continuous_invFun := hinverse }
      exact E.isQuotientMap
  have hinverse_iff_topology :
      Continuous e.invFun ↔ D.topologyAgreement := by
    constructor
    · intro hinverse
      let E : FinalPair ≃ₜ OrdinaryPair :=
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
following adapter makes the statement-side interface concrete: its raw and
final operations are the actual quotient-level composition maps, and its
comparison is the actual final-to-ordinary equivalence. -/

noncomputable def scopedFinalPairData
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    (S : _root_.ComputationalPaths.Path.GeometricTopology.ContinuousGeometricStepSystem A Step)
    (P : _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewritePresentation S) :
    ScopedFinalPairData
      (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedComposableRaw (S := S))
      (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedComposableClass P)
      (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedComposablePair P)
      (_root_.ComputationalPaths.Path.GeometricTopology.ScopedClass P) where
  quotient := _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedComposableMk P
  comparison := _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedPairToOrdinaryEquiv P
  rawOperation := fun c =>
    _root_.ComputationalPaths.Path.GeometricTopology.scopedQuotientMk P
      (_root_.ComputationalPaths.Path.GeometricTopology.TotalOpenGeometricCompPath.totalTrans S c)
  finalOperation := _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedCompositionFromComposable P
  ordinaryOperation := _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedCompositionOnProduct P
  quotient_is_quotient :=
    _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedComposableMk_isQuotient P
  comparison_continuous :=
    _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.continuous_scopedPairToOrdinary P
  rawOperation_continuous := by
    exact _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.continuous_scopedQuotientMk P |>.comp
      (_root_.ComputationalPaths.Path.GeometricTopology.TotalOpenGeometricCompPath.continuous_totalTrans S)
  final_factor := by
    intro c
    exact _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedCompositionFromComposable_mk P c
  ordinary_factor := by
    intro c
    exact _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedCompositionOnProduct_pairMap P
      (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedComposableMk P c)

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
        (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedComposableClass P)
        (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedComposablePair P)
        (_root_.ComputationalPaths.Path.GeometricTopology.ScopedClass P)) := by
  intro A instA Step instStep S P
  exact ⟨scopedFinalPairData S P⟩

end TopologicalComputationalPaths
