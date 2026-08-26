import ComputationalPaths.Path.Topology.ScopedGeometricRewriteQuotient

/-!
# The scoped rewrite groupoid

This file completes the algebraic and topological groupoid interface of the
scoped quotient.  Every law is discharged by the explicit scoped coherence
constructors, and every unconditional continuity statement uses the final
composable domain.  The ordinary pullback topology is retained as a separate
object with an explicit quotient-map comparison theorem.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

universe u v

namespace ScopedGeometricRewrite

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  {S : ContinuousGeometricStepSystem A Step}
  (P : ScopedGeometricRewritePresentation S)

/-! The final-domain groupoid retains the trace-length composition witness. -/

noncomputable def scopedGroupoidCompositionTracePath
    (c : ScopedComposableRaw (S := S)) :
    ComputationalPaths.Path
      (GeometricTrace.traceLength
        (GeometricTrace.trans c.left.trace c.right.trace))
      (GeometricTrace.traceLength c.left.trace +
        GeometricTrace.traceLength c.right.trace) :=
  GeometricTrace.traceLengthTransPath c.left.trace c.right.trace

/-! ## Descended endpoint identities -/

@[simp] theorem scopedSrc_symm (p : ScopedClass P) :
    scopedSrc P (scopedSymm P p) = scopedTgt P p := by
  refine Quotient.inductionOn p ?_
  intro p
  rfl

@[simp] theorem scopedTgt_symm (p : ScopedClass P) :
    scopedTgt P (scopedSymm P p) = scopedSrc P p := by
  refine Quotient.inductionOn p ?_
  intro p
  rfl

/-! ## Ordinary composable pairs and product composition -/

noncomputable def scopedPairToOrdinary (c : ScopedComposableClass P) :
    ScopedComposablePair P :=
  (scopedPairMap P c).val

theorem scopedPairToOrdinary_surjective :
    Function.Surjective (scopedPairToOrdinary P :
      ScopedComposableClass P → ScopedComposablePair P) := by
  intro c
  rcases scopedPairMap_surjective P
      ({ val := c } : ScopedStrongComposablePair P) with ⟨d, hd⟩
  refine ⟨d, ?_⟩
  exact _root_.congrArg (fun z : ScopedStrongComposablePair P => z.val) hd

theorem continuous_scopedPairToOrdinary :
    Continuous (scopedPairToOrdinary P :
      ScopedComposableClass P → ScopedComposablePair P) := by
  exact continuous_scopedStrongToOrdinary P |>.comp
    (continuous_scopedPairMap P)

noncomputable def scopedCompositionOnProduct
    (pq : ScopedComposablePair P) : ScopedClass P :=
  scopedCompositionOnStrong P ⟨pq⟩

theorem scopedCompositionOnProduct_pairMap
    (c : ScopedComposableClass P) :
    scopedCompositionOnProduct P (scopedPairToOrdinary P c) =
      scopedCompositionFromComposable P c := by
  refine Quotient.inductionOn c ?_
  intro c
  change scopedCompositionOnStrong P
      (scopedPairMap P (scopedComposableMk P c)) =
    scopedCompositionFromComposable P (scopedComposableMk P c)
  exact scopedCompositionOnStrong_mk P c

/-! ## The exact ordinary/final topology comparison -/

structure ProductQuotientCompatibility : Prop where
  pair_map_is_quotient :
    Topology.IsQuotientMap (scopedPairToOrdinary P :
      ScopedComposableClass P → ScopedComposablePair P)

theorem scopedStrongComposablePair_ext
    {a b : ScopedStrongComposablePair P}
    (h : a.val = b.val) : a = b := by
  cases a
  cases b
  cases h
  rfl

theorem scopedPairMap_injective :
    Function.Injective (scopedPairMap P :
      ScopedComposableClass P → ScopedStrongComposablePair P) := by
  intro c d h
  refine Quotient.inductionOn₂ c d ?_ h
  intro c d h
  apply Quotient.sound
  have hleft :
      scopedQuotientMk P (leftRaw c) = scopedQuotientMk P (leftRaw d) := by
    exact _root_.congrArg
      (fun z : ScopedStrongComposablePair P => z.val.val.1) h
  have hright :
      scopedQuotientMk P (rightRaw c) = scopedQuotientMk P (rightRaw d) := by
    exact _root_.congrArg
      (fun z : ScopedStrongComposablePair P => z.val.val.2) h
  exact ⟨Quotient.exact hleft, Quotient.exact hright⟩

noncomputable def scopedPairMapEquiv :
    ScopedComposableClass P ≃ ScopedStrongComposablePair P :=
  Equiv.ofBijective (scopedPairMap P)
    ⟨scopedPairMap_injective P, scopedPairMap_surjective P⟩

theorem scopedPairToOrdinary_injective :
    Function.Injective (scopedPairToOrdinary P :
      ScopedComposableClass P → ScopedComposablePair P) := by
  intro c d h
  apply scopedPairMap_injective P
  apply scopedStrongComposablePair_ext P
  exact h

noncomputable def scopedPairToOrdinaryEquiv :
    ScopedComposableClass P ≃ ScopedComposablePair P :=
  Equiv.ofBijective (scopedPairToOrdinary P)
    ⟨scopedPairToOrdinary_injective P, scopedPairToOrdinary_surjective P⟩

noncomputable def scopedOrdinaryToFinal :
    ScopedComposablePair P → ScopedComposableClass P :=
  (scopedPairToOrdinaryEquiv P).symm

theorem scopedOrdinaryToFinal_pairToOrdinary (c : ScopedComposableClass P) :
    scopedOrdinaryToFinal P (scopedPairToOrdinary P c) = c := by
  exact (scopedPairToOrdinaryEquiv P).symm_apply_apply c

theorem scopedPairToOrdinary_ordinaryToFinal (pq : ScopedComposablePair P) :
    scopedPairToOrdinary P (scopedOrdinaryToFinal P pq) = pq := by
  exact (scopedPairToOrdinaryEquiv P).apply_symm_apply pq

/-! ## The raw ordinary-pair quotient map -/

noncomputable def scopedOrdinaryPairMap
    (c : ScopedComposableRaw (S := S)) : ScopedComposablePair P :=
  scopedPairToOrdinary P (scopedComposableMk P c)

theorem scopedOrdinaryPairMap_eq_composed :
    (scopedOrdinaryPairMap P : ScopedComposableRaw (S := S) →
      ScopedComposablePair P) =
      scopedPairToOrdinary P ∘ scopedComposableMk P := by
  rfl

theorem continuous_scopedOrdinaryPairMap :
    Continuous (scopedOrdinaryPairMap P :
      ScopedComposableRaw (S := S) → ScopedComposablePair P) := by
  rw [scopedOrdinaryPairMap_eq_composed]
  exact (continuous_scopedPairToOrdinary P).comp
    (continuous_scopedComposableMk P)

theorem scopedOrdinaryPairMap_surjective :
    Function.Surjective (scopedOrdinaryPairMap P :
      ScopedComposableRaw (S := S) → ScopedComposablePair P) := by
  intro pq
  rcases scopedPairToOrdinary_surjective P pq with ⟨c, rfl⟩
  rcases scopedComposableMk_surjective P c with ⟨c', hc'⟩
  refine ⟨c', ?_⟩
  rw [scopedOrdinaryPairMap, hc']

theorem scopedProductCompatibility_iff_raw_pair_map_quotient :
    ProductQuotientCompatibility P ↔
      Topology.IsQuotientMap (scopedOrdinaryPairMap P :
        ScopedComposableRaw (S := S) → ScopedComposablePair P) := by
  constructor
  · intro H
    rw [scopedOrdinaryPairMap_eq_composed]
    exact H.pair_map_is_quotient.comp (scopedComposableMk_isQuotient P)
  · intro hraw
    have hclass :
        Topology.IsQuotientMap
          (scopedPairToOrdinary P :
            ScopedComposableClass P → ScopedComposablePair P) := by
      apply Topology.IsQuotientMap.of_comp
        (continuous_scopedComposableMk P)
        (continuous_scopedPairToOrdinary P)
        hraw
    exact ⟨hclass⟩

theorem scopedProductCompatibility_iff_ordinary_to_final_continuous :
    ProductQuotientCompatibility P ↔
      Continuous (scopedOrdinaryToFinal P :
        ScopedComposablePair P → ScopedComposableClass P) := by
  constructor
  · intro H
    apply H.pair_map_is_quotient.continuous_iff.2
    convert continuous_id using 1
    funext c
    exact scopedOrdinaryToFinal_pairToOrdinary P c
  · intro h
    let e : ScopedComposableClass P ≃ₜ ScopedComposablePair P :=
      { toEquiv := scopedPairToOrdinaryEquiv P
        continuous_toFun := continuous_scopedPairToOrdinary P
        continuous_invFun := h }
    exact ⟨by
      simpa [e, scopedPairToOrdinaryEquiv] using e.isQuotientMap⟩

theorem scopedProductCompatibility_iff_final_topology_agreement :
    ProductQuotientCompatibility P ↔
      (inferInstance : TopologicalSpace (ScopedComposableClass P)) =
        TopologicalSpace.induced (scopedPairToOrdinary P)
          (inferInstance : TopologicalSpace (ScopedComposablePair P)) := by
  constructor
  · intro H
    let e : ScopedComposableClass P ≃ₜ ScopedComposablePair P :=
      { toEquiv := scopedPairToOrdinaryEquiv P
        continuous_toFun := continuous_scopedPairToOrdinary P
        continuous_invFun :=
          (scopedProductCompatibility_iff_ordinary_to_final_continuous P).1 H }
    exact e.isInducing.eq_induced
  · intro htop
    exact ⟨(Topology.IsInducing.mk htop).isQuotientMap_of_surjective
      (scopedPairToOrdinary_surjective P)⟩

noncomputable def scopedFinalOrdinaryHomeomorph
    (H : ProductQuotientCompatibility P) :
    ScopedComposableClass P ≃ₜ ScopedComposablePair P :=
  { toEquiv := scopedPairToOrdinaryEquiv P
    continuous_toFun := continuous_scopedPairToOrdinary P
    continuous_invFun :=
      (scopedProductCompatibility_iff_ordinary_to_final_continuous P).1 H }

theorem scopedProductCompatibility_iff_four_way :
    ProductQuotientCompatibility P ↔
      (Topology.IsQuotientMap (scopedOrdinaryPairMap P :
          ScopedComposableRaw (S := S) → ScopedComposablePair P) ∧
        Topology.IsQuotientMap (scopedPairToOrdinary P :
          ScopedComposableClass P → ScopedComposablePair P) ∧
        Continuous (scopedOrdinaryToFinal P :
          ScopedComposablePair P → ScopedComposableClass P) ∧
        (inferInstance : TopologicalSpace (ScopedComposableClass P)) =
          TopologicalSpace.induced (scopedPairToOrdinary P)
            (inferInstance : TopologicalSpace (ScopedComposablePair P))) := by
  constructor
  · intro H
    exact ⟨
      (scopedProductCompatibility_iff_raw_pair_map_quotient P).1 H,
      H.pair_map_is_quotient,
      (scopedProductCompatibility_iff_ordinary_to_final_continuous P).1 H,
      (scopedProductCompatibility_iff_final_topology_agreement P).1 H⟩
  · rintro ⟨_, hpair, _, _⟩
    exact ⟨hpair⟩

theorem continuous_scopedCompositionOnProduct
    (H : ProductQuotientCompatibility P) :
    Continuous (scopedCompositionOnProduct P :
      ScopedComposablePair P → ScopedClass P) := by
  apply H.pair_map_is_quotient.continuous_iff.2
  have hfactor :
      scopedCompositionOnProduct P ∘ scopedPairToOrdinary P =
        scopedCompositionFromComposable P := by
    funext c
    exact scopedCompositionOnProduct_pairMap P c
  rw [hfactor]
  exact continuous_scopedCompositionFromComposable P

theorem scopedProductCompatibility_iff_topology_agreement :
    ProductQuotientCompatibility P ↔
      TopologicalSpace.coinduced (scopedPairToOrdinary P)
          (inferInstance : TopologicalSpace (ScopedComposableClass P)) =
        (inferInstance : TopologicalSpace (ScopedComposablePair P)) := by
  constructor
  · intro H
    exact H.pair_map_is_quotient.eq_coinduced.symm
  · intro htop
    refine ⟨Topology.IsQuotientMap.mk ⟨?_⟩
      (scopedPairToOrdinary_surjective P)⟩
    exact htop.symm

theorem scopedProductCompatibility_of_open_pair_map
    (hopen : IsOpenMap (scopedPairToOrdinary P)) :
    ProductQuotientCompatibility P := by
  exact ⟨hopen.isQuotientMap
    (continuous_scopedPairToOrdinary P)
    (scopedPairToOrdinary_surjective P)⟩

/-! ## A positive ordinary-pullback theorem -/

theorem scopedProductCompatibility_of_compact_final_t2
    [CompactSpace (ScopedComposableClass P)]
    [T2Space (ScopedComposablePair P)] :
    ProductQuotientCompatibility P := by
  exact ⟨Topology.IsQuotientMap.of_surjective_continuous
    (scopedPairToOrdinary_surjective P)
    (continuous_scopedPairToOrdinary P)⟩

theorem scopedProductCompatibility_of_compact_final_t2_ordinary_composition
    [CompactSpace (ScopedComposableClass P)]
    [T2Space (ScopedComposablePair P)] :
    Continuous (scopedCompositionOnProduct P :
      ScopedComposablePair P → ScopedClass P) := by
  exact continuous_scopedCompositionOnProduct P
    (scopedProductCompatibility_of_compact_final_t2 P)

theorem scopedProductCompatibility_of_discrete_arrow_and_final_domain
    [DiscreteTopology (ScopedClass P)]
    [DiscreteTopology (ScopedComposableClass P)] :
    ProductQuotientCompatibility P := by
  apply scopedProductCompatibility_of_open_pair_map P
  intro U hU
  exact isOpen_discrete _

/-! ## Canonical strong composable pairs -/

noncomputable def strongLeftUnitPair (p : ScopedClass P) :
    ScopedStrongComposablePair P :=
  ⟨⟨scopedRefl P (scopedSrc P p), p⟩, by
    exact scopedTgt_refl P (scopedSrc P p)⟩

noncomputable def strongRightUnitPair (p : ScopedClass P) :
    ScopedStrongComposablePair P :=
  ⟨⟨p, scopedRefl P (scopedTgt P p)⟩, by
    exact (scopedSrc_refl P (scopedTgt P p)).symm⟩

noncomputable def strongRightInversePair (p : ScopedClass P) :
    ScopedStrongComposablePair P :=
  ⟨⟨p, scopedSymm P p⟩, by
    exact (scopedSrc_symm P p).symm⟩

noncomputable def strongLeftInversePair (p : ScopedClass P) :
    ScopedStrongComposablePair P :=
  ⟨⟨scopedSymm P p, p⟩, by
    exact scopedTgt_symm P p⟩

theorem scopedCompositionOnStrong_leftUnit (p : ScopedClass P) :
    scopedCompositionOnStrong P (strongLeftUnitPair P p) = p := by
  refine Quotient.inductionOn p ?_
  intro p
  let c : ScopedComposableRaw (S := S) :=
    ⟨p.src, p.src, p.tgt,
      openRefl S.toGeometricStepSystem p.src,
      p.path⟩
  change scopedCompositionOnStrong P
      (strongLeftUnitPair P (scopedQuotientMk P p)) =
    scopedQuotientMk P p
  have hpair : strongLeftUnitPair P (scopedQuotientMk P p) =
      scopedPairMap P (scopedComposableMk P c) := by
    apply _root_.congrArg (fun z : ScopedComposablePair P =>
      (⟨z⟩ : ScopedStrongComposablePair P))
    apply Subtype.ext
    apply Prod.ext <;> rfl
  rw [hpair, scopedCompositionOnStrong_mk]
  apply Quotient.sound
  exact ⟨rfl, rfl, ScopedRwEq.refl_trans p.trace⟩

theorem scopedCompositionOnStrong_rightUnit (p : ScopedClass P) :
    scopedCompositionOnStrong P (strongRightUnitPair P p) = p := by
  refine Quotient.inductionOn p ?_
  intro p
  let c : ScopedComposableRaw (S := S) :=
    ⟨p.src, p.tgt, p.tgt, p.path,
      openRefl S.toGeometricStepSystem p.tgt⟩
  change scopedCompositionOnStrong P
      (strongRightUnitPair P (scopedQuotientMk P p)) =
    scopedQuotientMk P p
  have hpair : strongRightUnitPair P (scopedQuotientMk P p) =
      scopedPairMap P (scopedComposableMk P c) := by
    apply _root_.congrArg (fun z : ScopedComposablePair P =>
      (⟨z⟩ : ScopedStrongComposablePair P))
    apply Subtype.ext
    apply Prod.ext <;> rfl
  rw [hpair, scopedCompositionOnStrong_mk]
  apply Quotient.sound
  exact ⟨rfl, rfl, ScopedRwEq.trans_refl p.trace⟩

theorem scopedCompositionOnStrong_rightInverse (p : ScopedClass P) :
    scopedCompositionOnStrong P (strongRightInversePair P p) =
      scopedRefl P (scopedSrc P p) := by
  refine Quotient.inductionOn p ?_
  intro p
  let c : ScopedComposableRaw (S := S) :=
    ⟨p.src, p.tgt, p.src, p.path,
      openSymm S.toGeometricStepSystem p.path⟩
  change scopedCompositionOnStrong P
      (strongRightInversePair P (scopedQuotientMk P p)) =
    scopedRefl P (scopedSrc P (scopedQuotientMk P p))
  have hpair : strongRightInversePair P (scopedQuotientMk P p) =
      scopedPairMap P (scopedComposableMk P c) := by
    apply _root_.congrArg (fun z : ScopedComposablePair P =>
      (⟨z⟩ : ScopedStrongComposablePair P))
    apply Subtype.ext
    apply Prod.ext <;> rfl
  rw [hpair, scopedCompositionOnStrong_mk]
  change scopedQuotientMk P (TotalOpenGeometricCompPath.totalTrans S c) =
    scopedQuotientMk P (TotalOpenGeometricCompPath.totalRefl S p.src)
  apply Quotient.sound
  exact ⟨rfl, rfl, ScopedRwEq.trans_symm p.trace⟩

theorem scopedCompositionOnStrong_leftInverse (p : ScopedClass P) :
    scopedCompositionOnStrong P (strongLeftInversePair P p) =
      scopedRefl P (scopedTgt P p) := by
  refine Quotient.inductionOn p ?_
  intro p
  let c : ScopedComposableRaw (S := S) :=
    ⟨p.tgt, p.src, p.tgt,
      openSymm S.toGeometricStepSystem p.path,
      p.path⟩
  change scopedCompositionOnStrong P
      (strongLeftInversePair P (scopedQuotientMk P p)) =
    scopedRefl P (scopedTgt P (scopedQuotientMk P p))
  have hpair : strongLeftInversePair P (scopedQuotientMk P p) =
      scopedPairMap P (scopedComposableMk P c) := by
    apply _root_.congrArg (fun z : ScopedComposablePair P =>
      (⟨z⟩ : ScopedStrongComposablePair P))
    apply Subtype.ext
    apply Prod.ext <;> rfl
  rw [hpair, scopedCompositionOnStrong_mk]
  change scopedQuotientMk P (TotalOpenGeometricCompPath.totalTrans S c) =
    scopedQuotientMk P (TotalOpenGeometricCompPath.totalRefl S p.tgt)
  apply Quotient.sound
  exact ⟨rfl, rfl, ScopedRwEq.symm_trans p.trace⟩

/-! ## Associativity -/

structure ScopedComposableTriple (P : ScopedGeometricRewritePresentation S) where
  src : A
  firstMid : A
  secondMid : A
  tgt : A
  first : OpenGeometricCompPath S.toGeometricStepSystem src firstMid
  second : OpenGeometricCompPath S.toGeometricStepSystem firstMid secondMid
  third : OpenGeometricCompPath S.toGeometricStepSystem secondMid tgt

noncomputable def tripleFirstSecond (t : ScopedComposableTriple P) :
    ScopedComposableRaw (S := S) :=
  ⟨t.src, t.firstMid, t.secondMid, t.first, t.second⟩

noncomputable def tripleSecondThird (t : ScopedComposableTriple P) :
    ScopedComposableRaw (S := S) :=
  ⟨t.firstMid, t.secondMid, t.tgt, t.second, t.third⟩

noncomputable def tripleLeftRaw (t : ScopedComposableTriple P) :
    ScopedComposableRaw (S := S) :=
  ⟨t.src, t.secondMid, t.tgt,
    openTrans S.toGeometricStepSystem t.first t.second,
    t.third⟩

noncomputable def tripleRightRaw (t : ScopedComposableTriple P) :
    ScopedComposableRaw (S := S) :=
  ⟨t.src, t.firstMid, t.tgt,
    t.first,
    openTrans S.toGeometricStepSystem t.second t.third⟩

noncomputable def tripleLeftPair (t : ScopedComposableTriple P) :
    ScopedStrongComposablePair P :=
  ⟨⟨scopedCompositionOnStrong P
        (scopedPairMap P (scopedComposableMk P (tripleFirstSecond P t))),
      scopedQuotientMk P
        ⟨t.secondMid, t.tgt, t.third⟩⟩, by
        rw [scopedCompositionOnStrong_mk]
        rfl⟩

noncomputable def tripleRightPair (t : ScopedComposableTriple P) :
    ScopedStrongComposablePair P :=
  ⟨⟨scopedQuotientMk P ⟨t.src, t.firstMid, t.first⟩,
      scopedCompositionOnStrong P
        (scopedPairMap P (scopedComposableMk P (tripleSecondThird P t)))⟩, by
        rw [scopedCompositionOnStrong_mk]
        rfl⟩

theorem tripleLeftPair_eq_pairMap (t : ScopedComposableTriple P) :
    tripleLeftPair P t =
      scopedPairMap P (scopedComposableMk P (tripleLeftRaw P t)) := by
  apply scopedStrongComposablePair_ext
  apply Subtype.ext
  apply Prod.ext
  · change scopedCompositionOnStrong P
        (scopedPairMap P
          (scopedComposableMk P (tripleFirstSecond P t))) =
      scopedQuotientMk P (leftRaw (tripleLeftRaw P t))
    rw [scopedCompositionOnStrong_mk]
    rfl
  · rfl

theorem tripleRightPair_eq_pairMap (t : ScopedComposableTriple P) :
    tripleRightPair P t =
      scopedPairMap P (scopedComposableMk P (tripleRightRaw P t)) := by
  apply scopedStrongComposablePair_ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change scopedCompositionOnStrong P
        (scopedPairMap P
          (scopedComposableMk P (tripleSecondThird P t))) =
      scopedQuotientMk P (rightRaw (tripleRightRaw P t))
    rw [scopedCompositionOnStrong_mk]
    rfl

theorem scopedCompositionOnStrong_assoc (t : ScopedComposableTriple P) :
    scopedCompositionOnStrong P (tripleLeftPair P t) =
      scopedCompositionOnStrong P (tripleRightPair P t) := by
  rw [tripleLeftPair_eq_pairMap, tripleRightPair_eq_pairMap]
  rw [scopedCompositionOnStrong_mk, scopedCompositionOnStrong_mk]
  apply Quotient.sound
  exact ⟨rfl, rfl, ScopedRwEq.trans_assoc t.first.trace t.second.trace t.third.trace⟩

/-! ## A complete unconditional groupoid certificate -/

structure ScopedFinalTopologicalGroupoidCertificate where
  source_continuous : Continuous (scopedSrc P)
  target_continuous : Continuous (scopedTgt P)
  identity_continuous : Continuous (scopedRefl P)
  inverse_continuous : Continuous (scopedSymm P)
  final_composition_continuous :
    Continuous (scopedCompositionOnStrong P :
      ScopedStrongComposablePair P → ScopedClass P)
  left_unit : ∀ p, scopedCompositionOnStrong P (strongLeftUnitPair P p) = p
  right_unit : ∀ p, scopedCompositionOnStrong P (strongRightUnitPair P p) = p
  right_inverse : ∀ p,
    scopedCompositionOnStrong P (strongRightInversePair P p) =
      scopedRefl P (scopedSrc P p)
  left_inverse : ∀ p,
    scopedCompositionOnStrong P (strongLeftInversePair P p) =
      scopedRefl P (scopedTgt P p)
  associativity : ∀ t : ScopedComposableTriple P,
    scopedCompositionOnStrong P (tripleLeftPair P t) =
      scopedCompositionOnStrong P (tripleRightPair P t)

noncomputable def scopedFinalTopologicalGroupoidCertificate :
    ScopedFinalTopologicalGroupoidCertificate P where
  source_continuous := continuous_scopedSrc P
  target_continuous := continuous_scopedTgt P
  identity_continuous := continuous_scopedRefl P
  inverse_continuous := continuous_scopedSymm P
  final_composition_continuous := continuous_scopedCompositionOnStrong P
  left_unit := scopedCompositionOnStrong_leftUnit P
  right_unit := scopedCompositionOnStrong_rightUnit P
  right_inverse := scopedCompositionOnStrong_rightInverse P
  left_inverse := scopedCompositionOnStrong_leftInverse P
  associativity := scopedCompositionOnStrong_assoc P

end ScopedGeometricRewrite
end GeometricTopology
end Path
end ComputationalPaths
