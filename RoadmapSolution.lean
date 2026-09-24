import ComputationalPaths

/-! A selection of the checked roadmap results. The substantive proofs live in
the imported development; this declaration pins their joint statement for
Comparator replay. -/

namespace TopologicalComputationalPathsRoadmap

open scoped ContinuousMap Topology
open ComputationalPaths.Path.GeometricTopology
open ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite
open ComputationalPaths.Path.GeometricTopology.FiniteCircleTorusPresentation

universe u v w z

structure RoadmapCertificate : Prop where
  universal_projection_quotient :
    ∀ {A : Type u} [TopologicalSpace A],
      Topology.IsQuotientMap (universalPathClassProjection (A := A))
  universal_projection_open :
    ∀ {A : Type u} [TopologicalSpace A] [LocallyPathConnectedSpace A],
      QuotientFundamentalGroup.SemilocallySimplyConnected A →
        IsOpenMap (universalPathClassProjection (A := A))
  universal_product_unconditional :
    ∀ {A : Type u} [TopologicalSpace A] [LocallyPathConnectedSpace A],
      QuotientFundamentalGroup.SemilocallySimplyConnected A →
        ProductQuotientCompatibility (universalPresentation (A := A))
  universal_composition_unconditional :
    ∀ {A : Type u} [TopologicalSpace A] [LocallyPathConnectedSpace A],
      QuotientFundamentalGroup.SemilocallySimplyConnected A →
        Continuous (scopedCompositionOnProduct (universalPresentation (A := A)) :
          ScopedComposablePair (universalPresentation (A := A)) →
            ScopedClass (universalPresentation (A := A)))
  universal_based_fiber_unconditional :
    ∀ {A : Type u} [TopologicalSpace A] [LocallyPathConnectedSpace A]
      (hsemi : QuotientFundamentalGroup.SemilocallySimplyConnected A) (x : A),
      Nonempty (QuotientFundamentalGroup.LoopQuot A x ≃ₜ
        universalBasedArrowSet x)
  universal_totally_disconnected_homeomorph :
    ∀ {A : Type u} [TopologicalSpace A] [TotallyDisconnectedSpace A],
      IsHomeomorph (universalPathClassProjection (A := A))
  open_arrow_product :
    ∀ {A : Type u} [TopologicalSpace A]
      {Step : Type v} [TopologicalSpace Step]
      {S : ContinuousGeometricStepSystem A Step}
      (P : ScopedGeometricRewritePresentation S),
      IsOpenMap (scopedQuotientMk P) → ProductQuotientCompatibility P
  final_projections :
    ∀ {A : Type u} [TopologicalSpace A]
      {Step : Type v} [TopologicalSpace Step]
      {S : ContinuousGeometricStepSystem A Step}
      (P : ScopedGeometricRewritePresentation S),
      Continuous (fun c : ScopedComposableClass P =>
        (scopedPairToOrdinary P c).val.1) ∧
      Continuous (fun c : ScopedComposableClass P =>
        (scopedPairToOrdinary P c).val.2)
  universal_open_product :
    ∀ {A : Type u} [TopologicalSpace A],
      IsOpenMap (universalPathClassProjection (A := A)) →
        ProductQuotientCompatibility (universalPresentation (A := A))
  universal_based_fiber :
    ∀ {A : Type u} [TopologicalSpace A] (x : A),
      IsOpenMap (universalPathClassProjection (A := A)) →
        Nonempty (QuotientFundamentalGroup.LoopQuot A x ≃ₜ
          universalBasedArrowSet x)
  universal_based_discrete :
    ∀ {A : Type u} [TopologicalSpace A]
      [LocallyPathConnectedSpace A] (x : A)
      (hsemi : QuotientFundamentalGroup.SemilocallySimplyConnected A),
      IsOpenMap (universalPathClassProjection (A := A)) →
        DiscreteTopology (universalBasedArrowSet x)
  product_based_complete :
    ∀ {X : Type u} [TopologicalSpace X]
      {Y : Type w} [TopologicalSpace Y]
      {E : Type v} [TopologicalSpace E]
      {F : Type z} [TopologicalSpace F]
      {S : ContinuousGeometricStepSystem X E}
      {T : ContinuousGeometricStepSystem Y F}
      (P : ScopedGeometricRewritePresentation S)
      (Q : ScopedGeometricRewritePresentation T)
      (x : X) (y : Y),
      (∀ {p q : GeometricTrace S.toGeometricStepSystem x x},
        _root_.Path.Homotopic (GeometricTrace.realize p)
          (GeometricTrace.realize q) → ScopedRwEq P p q) →
      (∀ {p q : GeometricTrace T.toGeometricStepSystem y y},
        _root_.Path.Homotopic (GeometricTrace.realize p)
          (GeometricTrace.realize q) → ScopedRwEq Q p q) →
      ∀ {p q : GeometricTrace (ProductSystem S T).toGeometricStepSystem
        (x, y) (x, y)},
        _root_.Path.Homotopic (GeometricTrace.realize p)
          (GeometricTrace.realize q) →
          ScopedRwEq (productScopedPresentation P Q) p q
  primitive_product_rewrite_equivalence :
    ∀ {X : Type u} [TopologicalSpace X]
      {Y : Type w} [TopologicalSpace Y]
      {E : Type v} [TopologicalSpace E]
      {F : Type z} [TopologicalSpace F]
      {S : ContinuousGeometricStepSystem X E}
      {T : ContinuousGeometricStepSystem Y F}
      (P : ScopedGeometricRewritePresentation S)
      (Q : ScopedGeometricRewritePresentation T)
      {a b : X × Y}
      {p q : GeometricTrace (ProductSystem S T).toGeometricStepSystem a b},
      ScopedRwEq (primitiveProductPresentation P Q) p q ↔
        ScopedRwEq (productScopedPresentation P Q) p q
  primitive_product_based_complete :
    ∀ {X : Type u} [TopologicalSpace X]
      {Y : Type w} [TopologicalSpace Y]
      {E : Type v} [TopologicalSpace E]
      {F : Type z} [TopologicalSpace F]
      {S : ContinuousGeometricStepSystem X E}
      {T : ContinuousGeometricStepSystem Y F}
      (P : ScopedGeometricRewritePresentation S)
      (Q : ScopedGeometricRewritePresentation T)
      (x : X) (y : Y),
      (∀ {p q : GeometricTrace S.toGeometricStepSystem x x},
        _root_.Path.Homotopic (GeometricTrace.realize p)
          (GeometricTrace.realize q) → ScopedRwEq P p q) →
      (∀ {p q : GeometricTrace T.toGeometricStepSystem y y},
        _root_.Path.Homotopic (GeometricTrace.realize p)
          (GeometricTrace.realize q) → ScopedRwEq Q p q) →
      ∀ {p q : GeometricTrace (ProductSystem S T).toGeometricStepSystem
        (x, y) (x, y)},
        _root_.Path.Homotopic (GeometricTrace.realize p)
          (GeometricTrace.realize q) →
          ScopedRwEq (primitiveProductPresentation P Q) p q
  finite_circle_complete :
    ∀ (p q : FiniteCircleOpenLoop),
      _root_.Path.Homotopic p.geometric q.geometric →
        ScopedRwEq circleFinitePresentation p.trace q.trace
  finite_torus_complete :
    ∀ (p q : FiniteTorusOpenLoop),
      _root_.Path.Homotopic p.geometric q.geometric →
        ScopedRwEq torusFinitePresentation p.trace q.trace
  circle_trace_comparison :
    Nonempty (@Homeomorph CircleFiniteBasedQuotient CircleFiniteBasedQuotient
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (finiteCircleBasedSetoid circleFinitePresentation)
        finiteCircleTraceSensitiveTopology)
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (finiteCircleBasedSetoid circleFinitePresentation) inferInstance))
  torus_trace_comparison :
    Nonempty (@Homeomorph TorusFiniteBasedQuotient TorusFiniteBasedQuotient
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (finiteTorusBasedSetoid torusFinitePresentation)
        finiteTorusTraceSensitiveTopology)
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (finiteTorusBasedSetoid torusFinitePresentation) inferInstance))
  circle_global_fiber :
    Nonempty (CircleGlobalBasedFiber ≃ₜ
      ConcreteCircleWinding.TopologicalLoopQuot)
  torus_global_fiber :
    Nonempty (TorusGlobalBasedFiber ≃ₜ TopologicalTorus.LoopQuot)
  trace_section_criterion :
    ∀ {A : Type u} [TopologicalSpace A]
      {Step : Type v} [TopologicalSpace Step]
      {S : ContinuousGeometricStepSystem A Step}
      (P : ScopedGeometricRewritePresentation S)
      (H : GeometricCompleteness P)
      {C : Type w} [TopologicalSpace C]
      (realize : ScopedRawPath (S := S) → C)
      (choose : C → ScopedRawPath (S := S))
      (hrealize : Continuous realize)
      (hchoose : @Continuous C (ScopedRawPath (S := S))
        inferInstance
        (TotalOpenGeometricCompPath.traceSensitiveTopologicalSpace S)
        choose)
      (hgeometry : ∀ p, TotalOpenGeometricCompPath.totalEquivalent S
        (choose (realize p)) p),
      Nonempty (@Homeomorph (ScopedClass P) (ScopedClass P)
        (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
          (scopedSetoid P)
          (TotalOpenGeometricCompPath.traceSensitiveTopologicalSpace S))
        (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
          (scopedSetoid P) inferInstance))
  duplicate_forward :
    @Continuous
      (ScopedClass TraceSensitiveSeparation.duplicateCirclePresentation)
      (ScopedClass TraceSensitiveSeparation.duplicateCirclePresentation)
      TraceSensitiveSeparation.duplicateTraceQuotientTopology
      TraceSensitiveSeparation.duplicateObservableQuotientTopology id
  duplicate_reverse_fails :
    ¬ @Continuous
      (ScopedClass TraceSensitiveSeparation.duplicateCirclePresentation)
      (ScopedClass TraceSensitiveSeparation.duplicateCirclePresentation)
      TraceSensitiveSeparation.duplicateObservableQuotientTopology
      TraceSensitiveSeparation.duplicateTraceQuotientTopology id
  discrete_arrow_product :
    ∀ {A : Type u} [TopologicalSpace A]
      {Step : Type v} [TopologicalSpace Step]
      {S : ContinuousGeometricStepSystem A Step}
      (P : ScopedGeometricRewritePresentation S)
      [DiscreteTopology (ScopedClass P)],
      ProductQuotientCompatibility P

theorem roadmap_result : RoadmapCertificate := by
  refine {
    universal_projection_quotient := ?_
    universal_projection_open := ?_
    universal_product_unconditional := ?_
    universal_composition_unconditional := ?_
    universal_based_fiber_unconditional := ?_
    universal_totally_disconnected_homeomorph := ?_
    open_arrow_product := ?_
    final_projections := ?_
    universal_open_product := ?_
    universal_based_fiber := ?_
    universal_based_discrete := ?_
    product_based_complete := ?_
    primitive_product_rewrite_equivalence := ?_
    primitive_product_based_complete := ?_
    finite_circle_complete := ?_
    finite_torus_complete := ?_
    circle_trace_comparison := ⟨circleFiniteTraceHomeomorph⟩
    torus_trace_comparison := ⟨torusFiniteTraceHomeomorph⟩
    circle_global_fiber := ⟨circleGlobalBasedGeometricHomeomorph⟩
    torus_global_fiber := ⟨torusGlobalBasedGeometricHomeomorph⟩
    trace_section_criterion := ?_
    duplicate_forward :=
      TraceSensitiveSeparation.duplicateQuotientComparison_continuous
    duplicate_reverse_fails :=
      TraceSensitiveSeparation.duplicateQuotientComparison_not_continuous
    discrete_arrow_product := ?_ }
  · exact universalPathClassProjection_isQuotient
  · intro A _ _ hsemi
    exact universalPathClassProjection_isOpenMap_of_semilocallySimplyConnected hsemi
  · intro A _ _ hsemi
    exact universalProductCompatibility_of_semilocallySimplyConnected hsemi
  · intro A _ _ hsemi
    exact continuous_universalComposition_of_semilocallySimplyConnected hsemi
  · intro A _ _ hsemi x
    exact ⟨universalBasedFiberHomeomorph_of_semilocallySimplyConnected hsemi x⟩
  · intro A _ _
    exact universalPathClassProjection_isHomeomorph_of_totallyDisconnected
  · exact scopedProductCompatibility_of_open_arrow
  · intro A _ Step _ S P
    have h : Continuous (fun c : ScopedComposableClass P =>
        (scopedPairToOrdinary P c).val) :=
      continuous_subtype_val.comp (continuous_scopedPairToOrdinary P)
    exact ⟨h.fst, h.snd⟩
  · exact universalProductCompatibility_of_open_path_projection
  · intro A _ x hopen
    exact ⟨basedGlobalFiberHomeomorph x hopen⟩
  · intro A _ _ x hsemi hopen
    exact basedGlobalFiber_discrete x hsemi hopen
  · exact productBasedTraceCompleteness
  · exact primitiveProduct_rwEq_iff_full
  · exact primitiveProductBasedTraceCompleteness
  · exact circleFinite_basedComplete
  · exact torusFinite_basedComplete
  · intro A _ Step _ S P H C _ realize choose hrealize hchoose hgeometry
    exact ⟨traceSensitiveHomeomorph_of_complete_section P H
      realize choose hrealize hchoose hgeometry⟩
  · exact scopedProductCompatibility_of_discrete_arrow

end TopologicalComputationalPathsRoadmap
