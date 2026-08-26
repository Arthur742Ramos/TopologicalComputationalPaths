import ComputationalPaths.Path.Topology.ScopedGeometricRewriteGroupoid
import ComputationalPaths.Path.Topology.UniversalCompPathHomotopyEquivalence

/-!
# Realization and universal completion

The scoped quotient maps continuously to the geometric endpointwise homotopy
quotient.  The map is defined from the explicit coherence witnesses carried by
raw paths and the induction theorem for scoped rewrite equality.

For the maximal continuous step system, the universal presentation declares
endpoint-fixed geometric homotopy itself as the named scoped rule.  Its scoped
quotient and the existing geometric homotopy quotient are then proved
homeomorphic, not merely equivalent as types.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

universe u v w

namespace ScopedGeometricRewrite

open TotalOpenGeometricCompPath
attribute [local instance] _root_.Path.Homotopic.setoid

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  {S : ContinuousGeometricStepSystem A Step}
  (P : ScopedGeometricRewritePresentation S)

/-! The comparison keeps the explicit reassociation witness on traces. -/

noncomputable def comparisonTraceReassociationPath
    {a b c d : A}
    (p : GeometricTrace S.toGeometricStepSystem a b)
    (q : GeometricTrace S.toGeometricStepSystem b c)
    (r : GeometricTrace S.toGeometricStepSystem c d) :
    ComputationalPaths.Path
      (GeometricTrace.traceLength
        (GeometricTrace.trans (GeometricTrace.trans p q) r))
      (GeometricTrace.traceLength p +
        (GeometricTrace.traceLength q + GeometricTrace.traceLength r)) :=
  GeometricTrace.traceLengthReassociationPath p q r

/-! ## Geometric soundness on the total carrier -/

theorem scopedEquivalent_geometric
    {p q : ScopedRawPath (S := S)}
    (h : scopedEquivalent P p q) :
    totalEquivalent S p q := by
  rcases p with ⟨p_src, p_tgt, p_path⟩
  rcases q with ⟨q_src, q_tgt, q_path⟩
  rcases h with ⟨hs, ht, h⟩
  cases hs
  cases ht
  rcases p_path.coherent with ⟨hp⟩
  rcases q_path.coherent with ⟨hq⟩
  rcases ScopedRwEq.sound P h with ⟨hr⟩
  have hr' : _root_.Path.Homotopy
      (GeometricTrace.realize p_path.trace)
      (GeometricTrace.realize q_path.trace) := by
    simpa [castScopedTrace] using hr
  have hgeom : _root_.Path.Homotopic p_path.geometric q_path.geometric :=
    ⟨hp.trans (hr'.trans hq.symm)⟩
  change totalCode S
      { src := p_src, tgt := p_tgt, path := p_path } =
    totalCode S { src := p_src, tgt := p_tgt, path := q_path }
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  exact Quotient.sound hgeom

/-! ## The realization comparison -/

noncomputable def toGeometricClass : ScopedClass P →
    TotalHomotopyClass S :=
  Quotient.lift
    (fun p : ScopedRawPath (S := S) => totalQuotientMk S p)
    (by
      intro p q h
      change scopedEquivalent P p q at h
      exact Quotient.sound (scopedEquivalent_geometric P h))

@[simp] theorem toGeometricClass_mk (p : ScopedRawPath (S := S)) :
    toGeometricClass P (scopedQuotientMk P p) = totalQuotientMk S p :=
  rfl

theorem continuous_toGeometricClass :
    Continuous (toGeometricClass P : ScopedClass P → TotalHomotopyClass S) := by
  apply (scopedQuotientMk_isQuotient P).continuous_iff.2
  exact TotalOpenGeometricCompPath.continuous_totalQuotientMk S

/-! ## Exact completeness criterion -/

def GeometricCompleteness : Prop :=
  ∀ {p q : ScopedRawPath (S := S)},
    totalEquivalent S p q → scopedEquivalent P p q

/-! ## Effective normal-form certificates -/

structure ScopedGeometricNormalFormCertificate where
  NF : Type w
  representative : NF → ScopedRawPath (S := S)
  normal : ScopedRawPath (S := S) → NF
  normal_scoped : ∀ p,
    scopedEquivalent P p (representative (normal p))
  geometric_normal_eq : ∀ {p q},
    totalEquivalent S p q → normal p = normal q

theorem geometricCompleteness_of_normalForm
    (C : ScopedGeometricNormalFormCertificate P) :
    GeometricCompleteness P := by
  intro p q hgeo
  exact (scopedSetoid P).iseqv.trans (C.normal_scoped p) <|
    (scopedSetoid P).iseqv.trans
      (by
        rw [C.geometric_normal_eq hgeo]) <|
        (scopedSetoid P).iseqv.symm (C.normal_scoped q)

theorem toGeometricClass_surjective :
    Function.Surjective (toGeometricClass P :
      ScopedClass P → TotalHomotopyClass S) := by
  intro x
  refine Quotient.inductionOn x ?_
  intro p
  exact ⟨scopedQuotientMk P p, rfl⟩

theorem toGeometricClass_injective_of_complete
    (H : GeometricCompleteness P) :
    Function.Injective (toGeometricClass P :
      ScopedClass P → TotalHomotopyClass S) := by
  intro x y hxy
  refine Quotient.inductionOn₂ x y ?_ hxy
  intro p q hxy
  apply Quotient.sound
  change totalQuotientMk S p = totalQuotientMk S q at hxy
  exact H (Quotient.exact hxy)

theorem geometricCompleteness_of_toGeometricClass_injective
    (H : Function.Injective (toGeometricClass P :
      ScopedClass P → TotalHomotopyClass S)) :
    GeometricCompleteness P := by
  intro p q htotal
  have hclass : scopedQuotientMk P p = scopedQuotientMk P q := by
    apply H
    rw [toGeometricClass_mk, toGeometricClass_mk]
    exact Quotient.sound htotal
  exact Quotient.exact hclass

theorem toGeometricClass_injective_iff_geometricCompleteness :
    Function.Injective (toGeometricClass P :
      ScopedClass P → TotalHomotopyClass S) ↔
      GeometricCompleteness P := by
  constructor
  · exact geometricCompleteness_of_toGeometricClass_injective P
  · exact toGeometricClass_injective_of_complete P

noncomputable def fromGeometricClass
    (H : GeometricCompleteness P) :
    TotalHomotopyClass S → ScopedClass P :=
  Quotient.lift
    (fun p : ScopedRawPath (S := S) => scopedQuotientMk P p)
    (by
      intro p q h
      exact Quotient.sound (H h))

@[simp] theorem fromGeometricClass_mk
    (H : GeometricCompleteness P) (p : ScopedRawPath (S := S)) :
    fromGeometricClass P H (totalQuotientMk S p) =
      scopedQuotientMk P p :=
  rfl

theorem continuous_fromGeometricClass
    (H : GeometricCompleteness P) :
    Continuous (fromGeometricClass P H :
      TotalHomotopyClass S → ScopedClass P) := by
  apply Continuous.quotient_lift
  exact continuous_scopedQuotientMk P

theorem fromGeometricClass_toGeometricClass
    (H : GeometricCompleteness P) (x : ScopedClass P) :
    fromGeometricClass P H (toGeometricClass P x) = x := by
  refine Quotient.inductionOn x ?_
  intro p
  rfl

theorem toGeometricClass_fromGeometricClass
    (H : GeometricCompleteness P) (x : TotalHomotopyClass S) :
    toGeometricClass P (fromGeometricClass P H x) = x := by
  refine Quotient.inductionOn x ?_
  intro p
  rfl

noncomputable def comparisonHomeomorph_of_complete
    (H : GeometricCompleteness P) :
    ScopedClass P ≃ₜ TotalHomotopyClass S where
  toEquiv :=
    { toFun := toGeometricClass P
      invFun := fromGeometricClass P H
      left_inv := fromGeometricClass_toGeometricClass P H
      right_inv := toGeometricClass_fromGeometricClass P H }
  continuous_toFun := continuous_toGeometricClass P
  continuous_invFun := continuous_fromGeometricClass P H

structure ComparisonCompletenessCertificate where
  arrow_continuous : Continuous (toGeometricClass P)
  arrow_surjective : Function.Surjective (toGeometricClass P)
  faithful_iff_complete :
    Function.Injective (toGeometricClass P) ↔ GeometricCompleteness P
  complete_homeomorph : ∀ (_ : GeometricCompleteness P),
    ScopedClass P ≃ₜ TotalHomotopyClass S

noncomputable def comparisonCompletenessCertificate :
    ComparisonCompletenessCertificate P where
  arrow_continuous := continuous_toGeometricClass P
  arrow_surjective := toGeometricClass_surjective P
  faithful_iff_complete := toGeometricClass_injective_iff_geometricCompleteness P
  complete_homeomorph := comparisonHomeomorph_of_complete P

/-! ## The comparison is a quotient-level groupoid functor -/

theorem scopedComposableEquivalent_geometric
    {c d : ScopedComposableRaw (S := S)}
    (h : scopedComposableEquivalent P c d) :
    TotalOpenGeometricCompPath.composableEquivalent S c d := by
  change TotalOpenGeometricCompPath.composableCode S c =
    TotalOpenGeometricCompPath.composableCode S d
  apply TotalOpenGeometricCompPath.composableCode_ext_of_component_codes
  · have hleft := scopedEquivalent_geometric P h.1
    simpa [leftRaw, TotalOpenGeometricCompPath.leftTotal] using hleft
  · have hright := scopedEquivalent_geometric P h.2
    simpa [rightRaw, TotalOpenGeometricCompPath.rightTotal] using hright

noncomputable def toGeometricComposableClass :
    ScopedComposableClass P →
      TotalOpenGeometricCompPath.ComposableHomotopyClass S :=
  Quotient.lift
    (fun c : ScopedComposableRaw (S := S) =>
      TotalOpenGeometricCompPath.composableQuotientMk S c)
    (by
      intro c d h
      apply Quotient.sound
      exact scopedComposableEquivalent_geometric P h)

theorem continuous_toGeometricComposableClass :
    Continuous (toGeometricComposableClass P :
      ScopedComposableClass P →
        TotalOpenGeometricCompPath.ComposableHomotopyClass S) := by
  apply (scopedComposableMk_isQuotient P).continuous_iff.2
  exact TotalOpenGeometricCompPath.continuous_composableQuotientMk S

@[simp] theorem toGeometricComposableClass_mk
    (c : ScopedComposableRaw (S := S)) :
    toGeometricComposableClass P (scopedComposableMk P c) =
      TotalOpenGeometricCompPath.composableQuotientMk S c :=
  rfl

theorem quotientSrc_toGeometricClass (x : ScopedClass P) :
    TotalOpenGeometricCompPath.quotientSrc S (toGeometricClass P x) =
      scopedSrc P x := by
  refine Quotient.inductionOn x ?_
  intro p
  rfl

theorem quotientTgt_toGeometricClass (x : ScopedClass P) :
    TotalOpenGeometricCompPath.quotientTgt S (toGeometricClass P x) =
      scopedTgt P x := by
  refine Quotient.inductionOn x ?_
  intro p
  rfl

theorem toGeometricClass_refl (a : A) :
    toGeometricClass P (scopedRefl P a) =
      TotalOpenGeometricCompPath.totalQuotientRefl S a := by
  rfl

theorem toGeometricClass_symm (x : ScopedClass P) :
    toGeometricClass P (scopedSymm P x) =
      TotalOpenGeometricCompPath.totalQuotientSymm S
        (toGeometricClass P x) := by
  refine Quotient.inductionOn x ?_
  intro p
  rfl

theorem toGeometricClass_composition (c : ScopedComposableClass P) :
    toGeometricClass P (scopedCompositionFromComposable P c) =
      TotalOpenGeometricCompPath.quotientTransFromComposable S
        (toGeometricComposableClass P c) := by
  refine Quotient.inductionOn c ?_
  intro c
  rfl

/-! ## The comparison on the final composable domain -/

noncomputable def toGeometricStrongPair
    (c : ScopedStrongComposablePair P) :
    TotalOpenGeometricCompPath.StrongComposablePair S :=
  ⟨⟨toGeometricClass P c.val.val.1,
      toGeometricClass P c.val.val.2⟩, by
    rw [quotientTgt_toGeometricClass, quotientSrc_toGeometricClass]
    exact c.val.property⟩

theorem toGeometricStrongPair_pairMap (c : ScopedComposableClass P) :
    toGeometricStrongPair P (scopedPairMap P c) =
      TotalOpenGeometricCompPath.strongPairMap S
        (toGeometricComposableClass P c) := by
  refine Quotient.inductionOn c ?_
  intro c
  rfl

theorem continuous_toGeometricStrongPair :
    Continuous (toGeometricStrongPair P :
      ScopedStrongComposablePair P →
        TotalOpenGeometricCompPath.StrongComposablePair S) := by
  apply (scopedPairMap_isQuotient P).continuous_iff.2
  have hfactor :
      toGeometricStrongPair P ∘ scopedPairMap P =
        TotalOpenGeometricCompPath.strongPairMap S ∘
          toGeometricComposableClass P := by
    funext c
    exact toGeometricStrongPair_pairMap P c
  rw [hfactor]
  exact continuous_coinduced_rng.comp
    (continuous_toGeometricComposableClass P)

theorem scopedCompositionOnStrong_pairMap_for_comparison
    (c : ScopedComposableClass P) :
    scopedCompositionOnStrong P (scopedPairMap P c) =
      scopedCompositionFromComposable P c := by
  refine Quotient.inductionOn c ?_
  intro c
  exact scopedCompositionOnStrong_mk P c

theorem toGeometricClass_composition_on_strong
    (c : ScopedStrongComposablePair P) :
    toGeometricClass P (scopedCompositionOnStrong P c) =
      TotalOpenGeometricCompPath.quotientTransOnStrongPair S
        (toGeometricStrongPair P c) := by
  rcases scopedPairMap_surjective P c with ⟨d, hd⟩
  rw [← hd, scopedCompositionOnStrong_pairMap_for_comparison P,
    toGeometricClass_composition P,
    toGeometricStrongPair_pairMap P]
  exact (TotalOpenGeometricCompPath.quotientTransOnStrongPair_strongPairMap
    S (toGeometricComposableClass P d)).symm

structure ComparisonFunctorCertificate where
  arrow_continuous : Continuous (toGeometricClass P)
  composable_continuous : Continuous (toGeometricComposableClass P)
  final_pair_continuous : Continuous (toGeometricStrongPair P)
  source_preserved : ∀ x,
    TotalOpenGeometricCompPath.quotientSrc S (toGeometricClass P x) =
      scopedSrc P x
  target_preserved : ∀ x,
    TotalOpenGeometricCompPath.quotientTgt S (toGeometricClass P x) =
      scopedTgt P x
  identity_preserved : ∀ a,
    toGeometricClass P (scopedRefl P a) =
      TotalOpenGeometricCompPath.totalQuotientRefl S a
  reversal_preserved : ∀ x,
    toGeometricClass P (scopedSymm P x) =
      TotalOpenGeometricCompPath.totalQuotientSymm S
        (toGeometricClass P x)
  composition_preserved : ∀ c,
    toGeometricClass P (scopedCompositionFromComposable P c) =
      TotalOpenGeometricCompPath.quotientTransFromComposable S
        (toGeometricComposableClass P c)
  final_composition_preserved : ∀ c,
    toGeometricClass P (scopedCompositionOnStrong P c) =
      TotalOpenGeometricCompPath.quotientTransOnStrongPair S
        (toGeometricStrongPair P c)

noncomputable def comparisonFunctorCertificate :
    ComparisonFunctorCertificate P where
  arrow_continuous := continuous_toGeometricClass P
  composable_continuous := continuous_toGeometricComposableClass P
  final_pair_continuous := continuous_toGeometricStrongPair P
  source_preserved := quotientSrc_toGeometricClass P
  target_preserved := quotientTgt_toGeometricClass P
  identity_preserved := toGeometricClass_refl P
  reversal_preserved := toGeometricClass_symm P
  composition_preserved := toGeometricClass_composition P
  final_composition_preserved := toGeometricClass_composition_on_strong P

/-! ## Universal presentation -/

noncomputable def universalPresentation :
    ScopedGeometricRewritePresentation (continuousPathStepSystem A) where
  rule := fun {a b} p q =>
    _root_.Path.Homotopic
      (GeometricTrace.realize p) (GeometricTrace.realize q)
  sound_rule := by
    intro a b p q h
    exact h

theorem universalScopedRwEq_iff_geometric
    {a b : A}
    {p q : GeometricTrace
      (continuousPathStepSystem A).toGeometricStepSystem a b} :
    ScopedRwEq (universalPresentation (A := A)) p q ↔
      _root_.Path.Homotopic
        (GeometricTrace.realize p) (GeometricTrace.realize q) := by
  constructor
  · exact ScopedRwEq.sound (universalPresentation (A := A))
  · intro h
    exact ScopedRwEq.generator h

theorem universalScopedEquivalent_iff_totalEquivalent
    {p q : ScopedRawPath
      (S := continuousPathStepSystem A)} :
    scopedEquivalent (universalPresentation (A := A)) p q ↔
      totalEquivalent (continuousPathStepSystem A) p q := by
  constructor
  · exact scopedEquivalent_geometric (universalPresentation (A := A))
  · intro h
    rcases p with ⟨p_src, p_tgt, p_path⟩
    rcases q with ⟨q_src, q_tgt, q_path⟩
    change totalCode (continuousPathStepSystem A)
        { src := p_src, tgt := p_tgt, path := p_path } =
      totalCode (continuousPathStepSystem A)
        { src := q_src, tgt := q_tgt, path := q_path } at h
    have hsrc : p_src = q_src := _root_.congrArg Sigma.fst h
    cases hsrc
    have hrest :
        (⟨p_tgt, Quotient.mk' p_path.geometric⟩ :
          Σ x : A, _root_.Path.Homotopic.Quotient p_src x) =
          ⟨q_tgt, Quotient.mk' q_path.geometric⟩ := by
      exact eq_of_heq (Sigma.ext_iff.mp h).2
    have htgt : p_tgt = q_tgt := _root_.congrArg Sigma.fst hrest
    cases htgt
    have hclass :
        Quotient.mk' p_path.geometric = Quotient.mk' q_path.geometric := by
      exact eq_of_heq (Sigma.ext_iff.mp hrest).2
    have hgeom : _root_.Path.Homotopic p_path.geometric q_path.geometric :=
      Quotient.exact hclass
    rcases p_path.coherent with ⟨hp⟩
    rcases q_path.coherent with ⟨hq⟩
    have hrealize : _root_.Path.Homotopic
        (GeometricTrace.realize p_path.trace)
        (GeometricTrace.realize q_path.trace) :=
      by
        rcases hgeom with ⟨hgeom⟩
        exact ⟨hp.symm.trans (hgeom.trans hq)⟩
    exact ⟨rfl, rfl,
      (universalScopedRwEq_iff_geometric (A := A)).2 hrealize⟩

/-! ## Universal homeomorphism -/

noncomputable def universalFromGeometricClass :
    TotalHomotopyClass (continuousPathStepSystem A) →
      ScopedClass (universalPresentation (A := A)) :=
  Quotient.lift
    (fun p : ScopedRawPath
      (S := continuousPathStepSystem A) =>
      scopedQuotientMk (universalPresentation (A := A)) p)
    (by
      intro p q h
      change totalEquivalent (continuousPathStepSystem A) p q at h
      apply Quotient.sound
      exact (universalScopedEquivalent_iff_totalEquivalent (A := A)).2 h)

@[simp] theorem universalFromGeometricClass_mk
    (p : ScopedRawPath (S := continuousPathStepSystem A)) :
    universalFromGeometricClass (A := A) (totalQuotientMk
      (continuousPathStepSystem A) p) =
      scopedQuotientMk (universalPresentation (A := A)) p :=
  rfl

theorem continuous_universalFromGeometricClass :
    Continuous (universalFromGeometricClass (A := A) :
      TotalHomotopyClass (continuousPathStepSystem A) →
        ScopedClass (universalPresentation (A := A))) := by
  apply Continuous.quotient_lift
  exact continuous_scopedQuotientMk (universalPresentation (A := A))

theorem universal_to_from
    (x : TotalHomotopyClass (continuousPathStepSystem A)) :
    toGeometricClass (universalPresentation (A := A))
        (universalFromGeometricClass (A := A) x) = x := by
  refine Quotient.inductionOn x ?_
  intro p
  rfl

theorem universal_from_to
    (x : ScopedClass (universalPresentation (A := A))) :
    universalFromGeometricClass (A := A)
        (toGeometricClass (universalPresentation (A := A)) x) = x := by
  refine Quotient.inductionOn x ?_
  intro p
  rfl

noncomputable def universalHomeomorph :
    ScopedClass (universalPresentation (A := A)) ≃ₜ
      TotalHomotopyClass (continuousPathStepSystem A) where
  toEquiv :=
    { toFun := toGeometricClass (universalPresentation (A := A))
      invFun := universalFromGeometricClass (A := A)
      left_inv := universal_from_to (A := A)
      right_inv := universal_to_from (A := A) }
  continuous_toFun := continuous_toGeometricClass
    (universalPresentation (A := A))
  continuous_invFun := continuous_universalFromGeometricClass (A := A)

end ScopedGeometricRewrite
end GeometricTopology
end Path
end ComputationalPaths
