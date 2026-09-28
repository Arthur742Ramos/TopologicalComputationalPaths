import ComputationalPaths.Path.Topology.ScopedGeometricRewriteComparison

/-!
# Functorial transport of scoped geometric presentations

A presentation map consists of a continuous geometric step-system map together
with a proof that every named source generator is sent into the scoped target
rewrite congruence.  The latter condition is deliberately a proof field, not a
typeclass or an informal side condition: the induced quotient map is therefore
defined only after all rewrite compatibility has been discharged.

The file proves transport of the complete scoped closure, continuity on the
quotient arrow spaces, endpoint preservation, and compatibility with the
canonical composable quotient.  It is the functorial layer needed to regard
the construction as a topological groupoid construction rather than an
isolated quotient.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

universe u v u' v' u'' v''

namespace ScopedGeometricRewrite

open TotalOpenGeometricCompPath

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  {B : Type u'} [TopologicalSpace B]
  {Step' : Type v'} [TopologicalSpace Step']
  {S : ContinuousGeometricStepSystem A Step}
  {T : ContinuousGeometricStepSystem B Step'}
  {P : ScopedGeometricRewritePresentation S}
  {Q : ScopedGeometricRewritePresentation T}

/-! ## Presentation maps and transport of derivations -/

structure PresentationMap
    (P : ScopedGeometricRewritePresentation S)
    (Q : ScopedGeometricRewritePresentation T) where
  systemMap : ContinuousGeometricStepSystemMap S T
  rule_map : ∀ {a b : A}
    {p q : GeometricTrace S.toGeometricStepSystem a b},
    P.rule p q →
      ScopedRwEq Q
        (ContinuousGeometricStepSystemMap.mapTrace systemMap p)
        (ContinuousGeometricStepSystemMap.mapTrace systemMap q)

theorem mapScopedRwEq
    (F : PresentationMap P Q)
    {a b : A}
    {p q : GeometricTrace S.toGeometricStepSystem a b}
    (h : ScopedRwEq P p q) :
    ScopedRwEq Q
      (ContinuousGeometricStepSystemMap.mapTrace F.systemMap p)
      (ContinuousGeometricStepSystemMap.mapTrace F.systemMap q) := by
  induction h with
  | refl p => exact ScopedRwEq.refl _
  | generator h => exact F.rule_map h
  | symm h ih => exact ScopedRwEq.symm ih
  | trans h₁ h₂ ih₁ ih₂ => exact ScopedRwEq.trans ih₁ ih₂
  | trans_congr h₁ h₂ ih₁ ih₂ =>
      exact ScopedRwEq.trans_congr ih₁ ih₂
  | symm_congr h ih => exact ScopedRwEq.symm_congr ih
  | refl_trans p =>
      exact ScopedRwEq.refl_trans
        (ContinuousGeometricStepSystemMap.mapTrace F.systemMap p)
  | trans_refl p =>
      exact ScopedRwEq.trans_refl
        (ContinuousGeometricStepSystemMap.mapTrace F.systemMap p)
  | trans_assoc p q r =>
      exact ScopedRwEq.trans_assoc
        (ContinuousGeometricStepSystemMap.mapTrace F.systemMap p)
        (ContinuousGeometricStepSystemMap.mapTrace F.systemMap q)
        (ContinuousGeometricStepSystemMap.mapTrace F.systemMap r)
  | symm_trans p =>
      exact ScopedRwEq.symm_trans
        (ContinuousGeometricStepSystemMap.mapTrace F.systemMap p)
  | trans_symm p =>
      exact ScopedRwEq.trans_symm
        (ContinuousGeometricStepSystemMap.mapTrace F.systemMap p)
  | symm_symm p =>
      exact ScopedRwEq.symm_symm
        (ContinuousGeometricStepSystemMap.mapTrace F.systemMap p)
  | symm_refl a => exact ScopedRwEq.symm_refl (F.systemMap.map a)
  | symm_comp p q =>
      exact ScopedRwEq.symm_comp
        (ContinuousGeometricStepSystemMap.mapTrace F.systemMap p)
        (ContinuousGeometricStepSystemMap.mapTrace F.systemMap q)

/-! A presentation map transports the explicit trace-length composition path. -/

noncomputable def presentationMapTraceCompositionPath
    (F : PresentationMap P Q)
    {a b c : A}
    (p : GeometricTrace S.toGeometricStepSystem a b)
    (q : GeometricTrace S.toGeometricStepSystem b c) :
    ComputationalPaths.Path
      (GeometricTrace.traceLength
        (GeometricTrace.trans
          (ContinuousGeometricStepSystemMap.mapTrace F.systemMap p)
          (ContinuousGeometricStepSystemMap.mapTrace F.systemMap q)))
      (GeometricTrace.traceLength
          (ContinuousGeometricStepSystemMap.mapTrace F.systemMap p) +
        GeometricTrace.traceLength
          (ContinuousGeometricStepSystemMap.mapTrace F.systemMap q)) :=
  GeometricTrace.traceLengthTransPath
    (ContinuousGeometricStepSystemMap.mapTrace F.systemMap p)
    (ContinuousGeometricStepSystemMap.mapTrace F.systemMap q)

theorem mapScopedEquivalent
    (F : PresentationMap P Q)
    {p q : ScopedRawPath (S := S)}
    (h : scopedEquivalent P p q) :
    scopedEquivalent Q
      (ContinuousGeometricStepSystemMap.mapTotal F.systemMap p)
      (ContinuousGeometricStepSystemMap.mapTotal F.systemMap q) := by
  rcases p with ⟨p_src, p_tgt, p_path⟩
  rcases q with ⟨q_src, q_tgt, q_path⟩
  rcases h with ⟨hs, ht, h⟩
  cases hs
  cases ht
  exact ⟨rfl, rfl, mapScopedRwEq F h⟩

/-! ## Quotient arrow maps -/

noncomputable def mapClass (F : PresentationMap P Q) :
    ScopedClass P → ScopedClass Q :=
  Quotient.lift
    (fun p : ScopedRawPath (S := S) =>
      scopedQuotientMk Q
        (ContinuousGeometricStepSystemMap.mapTotal F.systemMap p))
    (by
      intro p q h
      apply Quotient.sound
      exact mapScopedEquivalent F h)

@[simp] theorem mapClass_mk
    (F : PresentationMap P Q) (p : ScopedRawPath (S := S)) :
    mapClass F (scopedQuotientMk P p) =
      scopedQuotientMk Q
        (ContinuousGeometricStepSystemMap.mapTotal F.systemMap p) :=
  rfl

theorem continuous_mapClass (F : PresentationMap P Q) :
    Continuous (mapClass F : ScopedClass P → ScopedClass Q) := by
  apply (scopedQuotientMk_isQuotient P).continuous_iff.2
  exact continuous_scopedQuotientMk Q |>.comp
    (ContinuousGeometricStepSystemMap.continuous_mapTotal F.systemMap)

theorem mapClass_src (F : PresentationMap P Q) (x : ScopedClass P) :
    scopedSrc Q (mapClass F x) = F.systemMap.map (scopedSrc P x) := by
  refine Quotient.inductionOn x ?_
  intro p
  rfl

theorem mapClass_tgt (F : PresentationMap P Q) (x : ScopedClass P) :
    scopedTgt Q (mapClass F x) = F.systemMap.map (scopedTgt P x) := by
  refine Quotient.inductionOn x ?_
  intro p
  rfl

/-! ## The composable quotient also transports -/

noncomputable def mapComposableRaw (F : PresentationMap P Q)
    (c : ScopedComposableRaw (S := S)) : ScopedComposableRaw (S := T) :=
  { src := F.systemMap.map c.src
    mid := F.systemMap.map c.mid
    tgt := F.systemMap.map c.tgt
    left := ContinuousGeometricStepSystemMap.mapOpen F.systemMap c.left
    right := ContinuousGeometricStepSystemMap.mapOpen F.systemMap c.right }

theorem mapTotal_trans
    (F : PresentationMap P Q) (c : ScopedComposableRaw (S := S)) :
    ContinuousGeometricStepSystemMap.mapTotal F.systemMap
        (TotalOpenGeometricCompPath.totalTrans S c) =
      TotalOpenGeometricCompPath.totalTrans T (mapComposableRaw F c) := by
  change
    (⟨F.systemMap.map c.src, F.systemMap.map c.tgt,
      ContinuousGeometricStepSystemMap.mapOpen F.systemMap
        (openTrans S.toGeometricStepSystem c.left c.right)⟩ :
      TotalOpenGeometricCompPath B Step' T) =
    ⟨F.systemMap.map c.src, F.systemMap.map c.tgt,
      openTrans T.toGeometricStepSystem
        (ContinuousGeometricStepSystemMap.mapOpen F.systemMap c.left)
        (ContinuousGeometricStepSystemMap.mapOpen F.systemMap c.right)⟩
  congr 1
  exact ContinuousGeometricStepSystemMap.mapOpen_trans
    F.systemMap c.left c.right

theorem mapTotal_refl (F : PresentationMap P Q) (a : A) :
    ContinuousGeometricStepSystemMap.mapTotal F.systemMap
        (TotalOpenGeometricCompPath.totalRefl S a) =
      TotalOpenGeometricCompPath.totalRefl T (F.systemMap.map a) := by
  change
    (⟨F.systemMap.map a, F.systemMap.map a,
      ContinuousGeometricStepSystemMap.mapOpen F.systemMap
        (openRefl S.toGeometricStepSystem a)⟩ :
      TotalOpenGeometricCompPath B Step' T) =
    ⟨F.systemMap.map a, F.systemMap.map a,
      openRefl T.toGeometricStepSystem (F.systemMap.map a)⟩
  congr 1

theorem mapTotal_symm
    (F : PresentationMap P Q) (p : ScopedRawPath (S := S)) :
    ContinuousGeometricStepSystemMap.mapTotal F.systemMap
        (TotalOpenGeometricCompPath.totalSymm S p) =
      TotalOpenGeometricCompPath.totalSymm T
        (ContinuousGeometricStepSystemMap.mapTotal F.systemMap p) := by
  change
    (⟨F.systemMap.map p.tgt, F.systemMap.map p.src,
      ContinuousGeometricStepSystemMap.mapOpen F.systemMap
        (openSymm S.toGeometricStepSystem p.path)⟩ :
      TotalOpenGeometricCompPath B Step' T) =
    ⟨F.systemMap.map p.tgt, F.systemMap.map p.src,
      openSymm T.toGeometricStepSystem
        (ContinuousGeometricStepSystemMap.mapOpen F.systemMap p.path)⟩
  congr 1

theorem mapScopedComposableEquivalent
    (F : PresentationMap P Q)
    {c d : ScopedComposableRaw (S := S)}
    (h : scopedComposableEquivalent P c d) :
    scopedComposableEquivalent Q (mapComposableRaw F c) (mapComposableRaw F d) := by
  exact ⟨mapScopedEquivalent F h.1, mapScopedEquivalent F h.2⟩

noncomputable def mapComposableClass (F : PresentationMap P Q) :
    ScopedComposableClass P → ScopedComposableClass Q :=
  Quotient.lift
    (fun c : ScopedComposableRaw (S := S) =>
      scopedComposableMk Q (mapComposableRaw F c))
    (by
      intro c d h
      apply Quotient.sound
      exact mapScopedComposableEquivalent F h)

@[simp] theorem mapComposableClass_mk
    (F : PresentationMap P Q) (c : ScopedComposableRaw (S := S)) :
    mapComposableClass F (scopedComposableMk P c) =
      scopedComposableMk Q (mapComposableRaw F c) :=
  rfl

theorem continuous_mapComposableClass (F : PresentationMap P Q) :
    Continuous (mapComposableClass F :
      ScopedComposableClass P → ScopedComposableClass Q) := by
  apply (scopedComposableMk_isQuotient P).continuous_iff.2
  change Continuous (fun c : ScopedComposableRaw (S := S) =>
    scopedComposableMk Q (mapComposableRaw F c))
  apply continuous_scopedComposableMk Q |>.comp
  apply continuous_induced_rng.mpr
  change Continuous (fun c : ScopedComposableRaw (S := S) =>
    (F.systemMap.map c.src,
      (F.systemMap.map c.mid,
        (F.systemMap.map c.tgt,
          (GeometricTrace.traceLength
              (ContinuousGeometricStepSystemMap.mapTrace F.systemMap c.left.trace),
            (GeometricTrace.traceLength
              (ContinuousGeometricStepSystemMap.mapTrace F.systemMap c.right.trace),
              (TotalComposable.leftTraceMap T (mapComposableRaw F c),
                (TotalComposable.rightTraceMap T (mapComposableRaw F c),
                  (TotalComposable.leftGeometricMap T (mapComposableRaw F c),
                    TotalComposable.rightGeometricMap T (mapComposableRaw F c))))))))))
  have hsrc : Continuous (fun c : ScopedComposableRaw (S := S) =>
      F.systemMap.map c.src) :=
    F.systemMap.map.continuous.comp (TotalComposable.continuous_src S)
  have hmid : Continuous (fun c : ScopedComposableRaw (S := S) =>
      F.systemMap.map c.mid) :=
    F.systemMap.map.continuous.comp (TotalComposable.continuous_mid S)
  have htgt : Continuous (fun c : ScopedComposableRaw (S := S) =>
      F.systemMap.map c.tgt) :=
    F.systemMap.map.continuous.comp (TotalComposable.continuous_tgt S)
  have hleftLength : Continuous (fun c : ScopedComposableRaw (S := S) =>
      GeometricTrace.traceLength
        (ContinuousGeometricStepSystemMap.mapTrace F.systemMap c.left.trace)) := by
    simpa only [ContinuousGeometricStepSystemMap.mapTrace_length,
      TotalComposable.leftTraceLength] using
      (TotalComposable.continuous_leftTraceLength S)
  have hrightLength : Continuous (fun c : ScopedComposableRaw (S := S) =>
      GeometricTrace.traceLength
        (ContinuousGeometricStepSystemMap.mapTrace F.systemMap c.right.trace)) := by
    simpa only [ContinuousGeometricStepSystemMap.mapTrace_length,
      TotalComposable.rightTraceLength] using
      (TotalComposable.continuous_rightTraceLength S)
  have hleftTraceMap : Continuous (fun c : ScopedComposableRaw (S := S) =>
      TotalComposable.leftTraceMap T (mapComposableRaw F c)) := by
    rw [show (fun c : ScopedComposableRaw (S := S) =>
        TotalComposable.leftTraceMap T (mapComposableRaw F c)) =
      (fun c => F.systemMap.map.comp (TotalComposable.leftTraceMap S c)) by
        funext c
        apply ContinuousMap.ext
        intro t
        change GeometricTrace.realize
            (ContinuousGeometricStepSystemMap.mapTrace F.systemMap c.left.trace) t =
          F.systemMap.map (GeometricTrace.realize c.left.trace t)
        rw [ContinuousGeometricStepSystemMap.mapTrace_realize]
        rfl]
    exact ContinuousMap.continuous_postcomp F.systemMap.map |>.comp
      (TotalComposable.continuous_leftTraceMap S)
  have hrightTraceMap : Continuous (fun c : ScopedComposableRaw (S := S) =>
      TotalComposable.rightTraceMap T (mapComposableRaw F c)) := by
    rw [show (fun c : ScopedComposableRaw (S := S) =>
        TotalComposable.rightTraceMap T (mapComposableRaw F c)) =
      (fun c => F.systemMap.map.comp (TotalComposable.rightTraceMap S c)) by
        funext c
        apply ContinuousMap.ext
        intro t
        change GeometricTrace.realize
            (ContinuousGeometricStepSystemMap.mapTrace F.systemMap c.right.trace) t =
          F.systemMap.map (GeometricTrace.realize c.right.trace t)
        rw [ContinuousGeometricStepSystemMap.mapTrace_realize]
        rfl]
    exact ContinuousMap.continuous_postcomp F.systemMap.map |>.comp
      (TotalComposable.continuous_rightTraceMap S)
  have hleftGeomMap : Continuous (fun c : ScopedComposableRaw (S := S) =>
      TotalComposable.leftGeometricMap T (mapComposableRaw F c)) := by
    rw [show (fun c : ScopedComposableRaw (S := S) =>
        TotalComposable.leftGeometricMap T (mapComposableRaw F c)) =
      (fun c => F.systemMap.map.comp (TotalComposable.leftGeometricMap S c)) by
        funext c
        apply ContinuousMap.ext
        intro t
        rfl]
    exact ContinuousMap.continuous_postcomp F.systemMap.map |>.comp
      (TotalComposable.continuous_leftGeometricMap S)
  have hrightGeomMap : Continuous (fun c : ScopedComposableRaw (S := S) =>
      TotalComposable.rightGeometricMap T (mapComposableRaw F c)) := by
    rw [show (fun c : ScopedComposableRaw (S := S) =>
        TotalComposable.rightGeometricMap T (mapComposableRaw F c)) =
      (fun c => F.systemMap.map.comp (TotalComposable.rightGeometricMap S c)) by
        funext c
        apply ContinuousMap.ext
        intro t
        rfl]
    exact ContinuousMap.continuous_postcomp F.systemMap.map |>.comp
      (TotalComposable.continuous_rightGeometricMap S)
  exact hsrc.prodMk (hmid.prodMk (htgt.prodMk
    (hleftLength.prodMk (hrightLength.prodMk
      (hleftTraceMap.prodMk (hrightTraceMap.prodMk
        (hleftGeomMap.prodMk hrightGeomMap)))))))

theorem continuous_mapComposableClass' (F : PresentationMap P Q) :
    Continuous (mapComposableClass F :
      ScopedComposableClass P → ScopedComposableClass Q) :=
  continuous_mapComposableClass F

theorem mapClass_composition_from_composable
    (F : PresentationMap P Q) (c : ScopedComposableClass P) :
    mapClass F (scopedCompositionFromComposable P c) =
      scopedCompositionFromComposable Q (mapComposableClass F c) := by
  refine Quotient.inductionOn c ?_
  intro c
  change scopedQuotientMk Q
      (ContinuousGeometricStepSystemMap.mapTotal F.systemMap
        (TotalOpenGeometricCompPath.totalTrans S c)) =
    scopedQuotientMk Q (TotalOpenGeometricCompPath.totalTrans T
      (mapComposableRaw F c))
  rw [mapTotal_trans]

/-! ## Functoriality on the groupoid operations -/

theorem mapClass_refl (F : PresentationMap P Q) (a : A) :
    mapClass F (scopedRefl P a) = scopedRefl Q (F.systemMap.map a) := by
  change mapClass F
      (scopedQuotientMk P (TotalOpenGeometricCompPath.totalRefl S a)) = _
  rw [mapClass_mk, mapTotal_refl]
  rfl

theorem mapClass_symm (F : PresentationMap P Q) (x : ScopedClass P) :
    mapClass F (scopedSymm P x) = scopedSymm Q (mapClass F x) := by
  refine Quotient.inductionOn x ?_
  intro p
  change mapClass F
      (scopedQuotientMk P (TotalOpenGeometricCompPath.totalSymm S p)) = _
  rw [mapClass_mk, mapTotal_symm]
  rfl

theorem scopedCompositionOnStrong_pairMap (P : ScopedGeometricRewritePresentation S)
    (c : ScopedComposableClass P) :
    scopedCompositionOnStrong P (scopedPairMap P c) =
      scopedCompositionFromComposable P c := by
  refine Quotient.inductionOn c ?_
  intro c
  exact scopedCompositionOnStrong_mk P c

noncomputable def mapStrongPair (F : PresentationMap P Q)
    (c : ScopedStrongComposablePair P) : ScopedStrongComposablePair Q :=
  ⟨⟨mapClass F c.val.val.1, mapClass F c.val.val.2⟩, by
    rw [mapClass_tgt, mapClass_src]
    exact _root_.congrArg F.systemMap.map c.val.property⟩

theorem mapStrongPair_pairMap
    (F : PresentationMap P Q) (c : ScopedComposableClass P) :
    mapStrongPair F (scopedPairMap P c) =
      scopedPairMap Q (mapComposableClass F c) := by
  refine Quotient.inductionOn c ?_
  intro c
  apply scopedStrongComposablePair_ext
  apply Subtype.ext
  apply Prod.ext <;> rfl

theorem mapClass_composition_on_strong
    (F : PresentationMap P Q) (c : ScopedStrongComposablePair P) :
    mapClass F (scopedCompositionOnStrong P c) =
      scopedCompositionOnStrong Q (mapStrongPair F c) := by
  rcases scopedPairMap_surjective P c with ⟨d, hd⟩
  rw [← hd, scopedCompositionOnStrong_pairMap P,
    mapClass_composition_from_composable F d,
    mapStrongPair_pairMap F d, scopedCompositionOnStrong_pairMap Q]

/-! ## Ordinary composable pairs and a complete functor certificate -/

noncomputable def mapOrdinaryPair (F : PresentationMap P Q)
    (pq : ScopedComposablePair P) : ScopedComposablePair Q :=
  ⟨(mapClass F pq.val.1, mapClass F pq.val.2), by
    rw [mapClass_tgt, mapClass_src]
    exact _root_.congrArg F.systemMap.map pq.property⟩

theorem continuous_mapOrdinaryPair (F : PresentationMap P Q) :
    Continuous (mapOrdinaryPair F :
      ScopedComposablePair P → ScopedComposablePair Q) := by
  have hleft : Continuous (fun pq : ScopedComposablePair P =>
      mapClass F pq.val.1) :=
    (continuous_mapClass F).comp
      (continuous_fst.comp continuous_subtype_val)
  have hright : Continuous (fun pq : ScopedComposablePair P =>
      mapClass F pq.val.2) :=
    (continuous_mapClass F).comp
      (continuous_snd.comp continuous_subtype_val)
  apply (hleft.prodMk hright).subtype_mk

theorem mapOrdinaryPair_pairToOrdinary
    (F : PresentationMap P Q) (c : ScopedComposableClass P) :
    mapOrdinaryPair F (scopedPairToOrdinary P c) =
      scopedPairToOrdinary Q (mapComposableClass F c) := by
  refine Quotient.inductionOn c ?_
  intro c
  apply Subtype.ext
  apply Prod.ext
  · change mapClass F (scopedQuotientMk P (leftRaw c)) =
      scopedQuotientMk Q (leftRaw (mapComposableRaw F c))
    rw [mapClass_mk]
    rfl
  · change mapClass F (scopedQuotientMk P (rightRaw c)) =
      scopedQuotientMk Q (rightRaw (mapComposableRaw F c))
    rw [mapClass_mk]
    rfl

theorem mapClass_composition_on_product
    (F : PresentationMap P Q) (pq : ScopedComposablePair P) :
    mapClass F (scopedCompositionOnProduct P pq) =
      scopedCompositionOnProduct Q (mapOrdinaryPair F pq) := by
  rcases scopedPairToOrdinary_surjective P pq with ⟨c, hc⟩
  rw [← hc, scopedCompositionOnProduct_pairMap P,
    mapClass_composition_from_composable F c,
    mapOrdinaryPair_pairToOrdinary F c,
    scopedCompositionOnProduct_pairMap Q]

structure ScopedPresentationFunctorCertificate
    (F : PresentationMap P Q) where
  arrow_continuous : Continuous (mapClass F : ScopedClass P → ScopedClass Q)
  final_pair_continuous : Continuous (mapStrongPair F :
    ScopedStrongComposablePair P → ScopedStrongComposablePair Q)
  ordinary_pair_continuous : Continuous (mapOrdinaryPair F :
    ScopedComposablePair P → ScopedComposablePair Q)
  source_preserved : ∀ x,
    scopedSrc Q (mapClass F x) = F.systemMap.map (scopedSrc P x)
  target_preserved : ∀ x,
    scopedTgt Q (mapClass F x) = F.systemMap.map (scopedTgt P x)
  identity_preserved : ∀ a,
    mapClass F (scopedRefl P a) = scopedRefl Q (F.systemMap.map a)
  reversal_preserved : ∀ x,
    mapClass F (scopedSymm P x) = scopedSymm Q (mapClass F x)
  final_composition_preserved : ∀ c,
    mapClass F (scopedCompositionOnStrong P c) =
      scopedCompositionOnStrong Q (mapStrongPair F c)
  ordinary_composition_preserved : ∀ pq,
    mapClass F (scopedCompositionOnProduct P pq) =
      scopedCompositionOnProduct Q (mapOrdinaryPair F pq)

theorem continuous_mapStrongPair (F : PresentationMap P Q) :
    Continuous (mapStrongPair F :
      ScopedStrongComposablePair P → ScopedStrongComposablePair Q) := by
  apply (scopedPairMap_isQuotient P).continuous_iff.2
  have hfactor :
      mapStrongPair F ∘ scopedPairMap P =
        scopedPairMap Q ∘ mapComposableClass F := by
    funext c
    exact mapStrongPair_pairMap F c
  rw [hfactor]
  exact (continuous_scopedPairMap Q).comp
    (continuous_mapComposableClass F)

noncomputable def scopedPresentationFunctorCertificate
    (F : PresentationMap P Q) :
    ScopedPresentationFunctorCertificate F where
  arrow_continuous := continuous_mapClass F
  final_pair_continuous := continuous_mapStrongPair F
  ordinary_pair_continuous := continuous_mapOrdinaryPair F
  source_preserved := mapClass_src F
  target_preserved := mapClass_tgt F
  identity_preserved := mapClass_refl F
  reversal_preserved := mapClass_symm F
  final_composition_preserved := mapClass_composition_on_strong F
  ordinary_composition_preserved := mapClass_composition_on_product F

theorem scopedPresentationFunctorCertificate_of_compatibility
    (F : PresentationMap P Q)
    (HP : ProductQuotientCompatibility P)
    (HQ : ProductQuotientCompatibility Q) :
    Continuous (mapClass F : ScopedClass P → ScopedClass Q) ∧
    Continuous (mapOrdinaryPair F :
      ScopedComposablePair P → ScopedComposablePair Q) ∧
      Continuous (scopedCompositionOnProduct P :
        ScopedComposablePair P → ScopedClass P) ∧
      Continuous (scopedCompositionOnProduct Q :
        ScopedComposablePair Q → ScopedClass Q) ∧
      (∀ pq, mapClass F (scopedCompositionOnProduct P pq) =
        scopedCompositionOnProduct Q (mapOrdinaryPair F pq)) := by
  exact ⟨continuous_mapClass F, continuous_mapOrdinaryPair F,
    continuous_scopedCompositionOnProduct P HP,
    continuous_scopedCompositionOnProduct Q HQ,
    mapClass_composition_on_product F⟩

/-! ## Identity and composition of presentation maps -/

noncomputable def identitySystemMap
    (S : ContinuousGeometricStepSystem A Step) :
    ContinuousGeometricStepSystemMap S S where
  map := ContinuousMap.id A
  stepMap := id
  map_src := by intro s; rfl
  map_tgt := by intro s; rfl
  map_realize := by
    intro s
    exact _root_.Path.map_id (S.realize s)

theorem identitySystemMap_mapTrace
    (S : ContinuousGeometricStepSystem A Step)
    {a b : A} (t : GeometricTrace S.toGeometricStepSystem a b) :
    ContinuousGeometricStepSystemMap.mapTrace (identitySystemMap S) t = t := by
  induction t with
  | refl a => rfl
  | single s => rfl
  | trans p q ihp ihq => simp [ContinuousGeometricStepSystemMap.mapTrace, ihp, ihq]; rfl
  | symm p ih => simp [ContinuousGeometricStepSystemMap.mapTrace, ih]; rfl

noncomputable def identityPresentationMap
    (P : ScopedGeometricRewritePresentation S) :
    PresentationMap P P where
  systemMap := identitySystemMap S
  rule_map := by
    intro a b p q h
    rw [identitySystemMap_mapTrace, identitySystemMap_mapTrace]
    exact ScopedRwEq.generator h

theorem mapClass_identity
    (P : ScopedGeometricRewritePresentation S) (x : ScopedClass P) :
    mapClass (identityPresentationMap P) x = x := by
  refine Quotient.inductionOn x ?_
  intro p
  apply Quotient.sound
  refine ⟨rfl, rfl, ?_⟩
  change ScopedRwEq P
    (ContinuousGeometricStepSystemMap.mapTrace
      (identitySystemMap S) p.trace) p.trace
  rw [identitySystemMap_mapTrace]
  exact ScopedRwEq.refl _

section Composition

variable {C : Type u''} [TopologicalSpace C]
  {Step'' : Type v''} [TopologicalSpace Step'']
  {U : ContinuousGeometricStepSystem C Step''}
  {R : ScopedGeometricRewritePresentation U}

noncomputable def systemMapComp
    (N : ContinuousGeometricStepSystemMap T U)
    (M : ContinuousGeometricStepSystemMap S T) :
    ContinuousGeometricStepSystemMap S U where
  map := N.map.comp M.map
  stepMap := N.stepMap ∘ M.stepMap
  map_src := by
    intro s
    calc
      U.src (N.stepMap (M.stepMap s)) =
          N.map (T.src (M.stepMap s)) := N.map_src (M.stepMap s)
      _ = N.map (M.map (S.src s)) :=
        _root_.congrArg N.map (M.map_src s)
      _ = (N.map.comp M.map) (S.src s) := rfl
  map_tgt := by
    intro s
    calc
      U.tgt (N.stepMap (M.stepMap s)) =
          N.map (T.tgt (M.stepMap s)) := N.map_tgt (M.stepMap s)
      _ = N.map (M.map (S.tgt s)) :=
        _root_.congrArg N.map (M.map_tgt s)
      _ = (N.map.comp M.map) (S.tgt s) := rfl
  map_realize := by
    intro s
    change (S.realize s).map
      (N.map.continuous.comp M.map.continuous) = _
    rw [← _root_.Path.map_map (S.realize s)
      M.map.continuous N.map.continuous]
    rw [M.map_realize]
    have hmapcast : ∀ {x y x' y' : B}
        (γ : _root_.Path x y) (hx : x' = x) (hy : y' = y),
        (γ.cast hx hy).map N.map.continuous =
          (γ.map N.map.continuous).cast
            (_root_.congrArg N.map hx) (_root_.congrArg N.map hy) := by
      intro x y x' y' γ hx hy
      cases hx
      cases hy
      rfl
    rw [hmapcast]
    rw [N.map_realize]
    have hcast : ∀ {x y x' y' x'' y'' : C}
        (γ : _root_.Path x y) (hx : x' = x) (hy : y' = y)
        (hx' : x'' = x') (hy' : y'' = y'),
        (γ.cast hx hy).cast hx' hy' =
          γ.cast (hx'.trans hx) (hy'.trans hy) := by
      intro x y x' y' x'' y'' γ hx hy hx' hy'
      cases hx
      cases hy
      cases hx'
      cases hy'
      rfl
    rw [hcast]
    rfl

theorem systemMapComp_mapTrace
    (N : ContinuousGeometricStepSystemMap T U)
    (M : ContinuousGeometricStepSystemMap S T)
    {a b : A} (t : GeometricTrace S.toGeometricStepSystem a b) :
    ContinuousGeometricStepSystemMap.mapTrace
        (systemMapComp N M) t =
      ContinuousGeometricStepSystemMap.mapTrace N
        (ContinuousGeometricStepSystemMap.mapTrace M t) := by
  have mapTrace_cast : ∀ {X : Type u'} [TopologicalSpace X]
      {Y : Type u''} [TopologicalSpace Y]
      {SX : ContinuousGeometricStepSystem X Step'}
      {SY : ContinuousGeometricStepSystem Y Step''}
      (N : ContinuousGeometricStepSystemMap SX SY)
      {a b a' b' : X} (ha : a' = a) (hb : b' = b)
      (t : GeometricTrace SX.toGeometricStepSystem a b),
      ContinuousGeometricStepSystemMap.mapTrace N
          (ContinuousGeometricStepSystemMap.castTrace ha hb t) =
        ContinuousGeometricStepSystemMap.castTrace
          (_root_.congrArg N.map ha) (_root_.congrArg N.map hb)
          (ContinuousGeometricStepSystemMap.mapTrace N t) := by
    intro X _ Y _ SX SY N a b a' b' ha hb t
    cases ha
    cases hb
    rfl
  have castTrace_irrel : ∀ {X : Type u'} [TopologicalSpace X]
      {SX : ContinuousGeometricStepSystem X Step'}
      {a b a' b' : X}
      (t : GeometricTrace SX.toGeometricStepSystem a b)
      (ha ha' : a' = a) (hb hb' : b' = b),
      ContinuousGeometricStepSystemMap.castTrace ha hb t =
        ContinuousGeometricStepSystemMap.castTrace ha' hb' t := by
    intro X _ SX a b a' b' t ha ha' hb hb'
    congr
  have castTrace_cast : ∀ {a b a' b' a'' b'' : C}
      (t : GeometricTrace U.toGeometricStepSystem a b)
      (ha : a' = a) (hb : b' = b)
      (ha' : a'' = a') (hb' : b'' = b'),
      ContinuousGeometricStepSystemMap.castTrace ha' hb'
          (ContinuousGeometricStepSystemMap.castTrace ha hb t) =
        ContinuousGeometricStepSystemMap.castTrace
          (ha'.trans ha) (hb'.trans hb) t := by
    intro a b a' b' a'' b'' t ha hb ha' hb'
    cases ha
    cases hb
    cases ha'
    cases hb'
    rfl
  have castTrace_irrel_U : ∀ {a b a' b' : C}
      (t : GeometricTrace U.toGeometricStepSystem a b)
      (ha ha' : a' = a) (hb hb' : b' = b),
      ContinuousGeometricStepSystemMap.castTrace ha hb t =
        ContinuousGeometricStepSystemMap.castTrace ha' hb' t := by
    intro a b a' b' t ha ha' hb hb'
    congr
  induction t with
  | refl a => rfl
  | single s =>
      simp only [ContinuousGeometricStepSystemMap.mapTrace, systemMapComp,
        Function.comp_apply]
      rw [mapTrace_cast]
      simp only [ContinuousGeometricStepSystemMap.mapTrace]
      rw [castTrace_cast]
      rfl
  | trans p q ihp ihq => simp [ContinuousGeometricStepSystemMap.mapTrace, ihp, ihq]; rfl
  | symm p ih => simp [ContinuousGeometricStepSystemMap.mapTrace, ih]; rfl

noncomputable def presentationMapComp
    (N : PresentationMap Q R)
    (M : PresentationMap P Q) :
    PresentationMap P R where
  systemMap := systemMapComp N.systemMap M.systemMap
  rule_map := by
    intro a b p q h
    rw [systemMapComp_mapTrace, systemMapComp_mapTrace]
    exact mapScopedRwEq N
      (mapScopedRwEq M (ScopedRwEq.generator h))

theorem mapTotal_comp_scopedEquivalent
    (N : ContinuousGeometricStepSystemMap T U)
    (M : ContinuousGeometricStepSystemMap S T)
    (p : ScopedRawPath (S := S)) :
    scopedEquivalent R
      (ContinuousGeometricStepSystemMap.mapTotal (systemMapComp N M) p)
      (ContinuousGeometricStepSystemMap.mapTotal N
        (ContinuousGeometricStepSystemMap.mapTotal M p)) := by
  refine ⟨rfl, rfl, ?_⟩
  change ScopedRwEq R
    (ContinuousGeometricStepSystemMap.mapTrace (systemMapComp N M) p.trace)
    (ContinuousGeometricStepSystemMap.mapTrace N
      (ContinuousGeometricStepSystemMap.mapTrace M p.trace))
  rw [systemMapComp_mapTrace]
  exact ScopedRwEq.refl _

theorem presentationMapComp_mapClass
    (N : PresentationMap Q R) (M : PresentationMap P Q)
    (x : ScopedClass P) :
    mapClass (presentationMapComp N M) x =
      mapClass N (mapClass M x) := by
  refine Quotient.inductionOn x ?_
  intro p
  apply Quotient.sound
  exact mapTotal_comp_scopedEquivalent N.systemMap M.systemMap p

theorem presentationMapComp_mapComposableClass
    (N : PresentationMap Q R) (M : PresentationMap P Q)
    (x : ScopedComposableClass P) :
    mapComposableClass (presentationMapComp N M) x =
      mapComposableClass N (mapComposableClass M x) := by
  refine Quotient.inductionOn x ?_
  intro c
  apply Quotient.sound
  exact ⟨
    mapTotal_comp_scopedEquivalent N.systemMap M.systemMap (leftRaw c),
    mapTotal_comp_scopedEquivalent N.systemMap M.systemMap (rightRaw c)⟩

structure PresentationFunctorIdentityCertificate
    (P : ScopedGeometricRewritePresentation S) where
  arrow_identity : ∀ x,
    mapClass (identityPresentationMap P) x = x
  composable_identity : ∀ c,
    mapComposableClass (identityPresentationMap P) c = c

noncomputable def presentationFunctorIdentityCertificate
    (P : ScopedGeometricRewritePresentation S) :
    PresentationFunctorIdentityCertificate P where
  arrow_identity := mapClass_identity P
  composable_identity := by
    intro c
    refine Quotient.inductionOn c ?_
    intro c
    apply Quotient.sound
    refine ⟨?_, ?_⟩
    · change scopedEquivalent P
        (leftRaw (mapComposableRaw (identityPresentationMap P) c))
        (leftRaw c)
      refine ⟨rfl, rfl, ?_⟩
      change ScopedRwEq P
        (ContinuousGeometricStepSystemMap.mapTrace
          (identitySystemMap S) c.left.trace) c.left.trace
      rw [identitySystemMap_mapTrace]
      exact ScopedRwEq.refl _
    · change scopedEquivalent P
        (rightRaw (mapComposableRaw (identityPresentationMap P) c))
        (rightRaw c)
      refine ⟨rfl, rfl, ?_⟩
      change ScopedRwEq P
        (ContinuousGeometricStepSystemMap.mapTrace
          (identitySystemMap S) c.right.trace) c.right.trace
      rw [identitySystemMap_mapTrace]
      exact ScopedRwEq.refl _

structure PresentationFunctorCompositionCertificate
    (N : PresentationMap Q R) (M : PresentationMap P Q) where
  arrow_composition : ∀ x,
    mapClass (presentationMapComp N M) x =
      mapClass N (mapClass M x)
  composable_composition : ∀ c,
    mapComposableClass (presentationMapComp N M) c =
      mapComposableClass N (mapComposableClass M c)

noncomputable def presentationFunctorCompositionCertificate
    (N : PresentationMap Q R) (M : PresentationMap P Q) :
    PresentationFunctorCompositionCertificate N M where
  arrow_composition := presentationMapComp_mapClass N M
  composable_composition := presentationMapComp_mapComposableClass N M

end Composition

end ScopedGeometricRewrite
end GeometricTopology
end Path
end ComputationalPaths
