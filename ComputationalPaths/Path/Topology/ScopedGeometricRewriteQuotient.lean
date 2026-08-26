import ComputationalPaths.Path.Topology.ScopedGeometricRewrite
import ComputationalPaths.Path.Topology.TopologicalCompPathOperations
import ComputationalPaths.Path.Topology.TopologicalCompPathGroupoidInterface

/-!
# Quotients of scoped geometric rewrite systems

The quotient in this file is the semantic arrow space of a scoped geometric
rewrite presentation.  Its topology is the quotient topology induced by the
continuous total raw carrier.  Composition is first constructed on the
quotient of the explicit composable carrier; this is the canonical final
composable domain and has no product-quotient hypothesis.

The ordinary composable-pair space and the final composable-pair space are both
made explicit.  The former is used for the standard topological-groupoid
criterion; the latter is the unconditional domain on which the composition
map is continuous.
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

/-! The quotient carrier retains an explicit computational witness. -/

noncomputable def scopedQuotientUnitRewrite
    (p : ScopedRawPath (S := S)) :
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl
          (GeometricTrace.traceLength p.trace))
        (ComputationalPaths.Path.refl
          (GeometricTrace.traceLength p.trace)))
      (ComputationalPaths.Path.refl (GeometricTrace.traceLength p.trace)) :=
  ComputationalPaths.Path.RwEq.step
    (ComputationalPaths.Path.Step.trans_refl_right
      (ComputationalPaths.Path.refl (GeometricTrace.traceLength p.trace)))

/-! ## Quotient arrow space -/

noncomputable instance scopedClassTopologicalSpace :
    TopologicalSpace (ScopedClass P) :=
  TopologicalSpace.coinduced (scopedQuotientMk P) inferInstance

theorem scopedQuotientMk_surjective :
    Function.Surjective (scopedQuotientMk P : ScopedRawPath (S := S) →
      ScopedClass P) := by
  intro x
  refine Quot.inductionOn x ?_
  intro p
  exact ⟨p, rfl⟩

theorem scopedQuotientMk_isQuotient :
    Topology.IsQuotientMap (scopedQuotientMk P :
      ScopedRawPath (S := S) → ScopedClass P) :=
  ⟨⟨rfl⟩, scopedQuotientMk_surjective P⟩

theorem continuous_scopedQuotientMk :
    Continuous (scopedQuotientMk P : ScopedRawPath (S := S) → ScopedClass P) :=
  continuous_coinduced_rng

noncomputable def scopedSrc : ScopedClass P → A :=
  Quot.lift (fun p : ScopedRawPath (S := S) => p.src)
    (by
      intro p q h
      change scopedEquivalent P p q at h
      exact (Classical.choose h).symm)

noncomputable def scopedTgt : ScopedClass P → A :=
  Quot.lift (fun p : ScopedRawPath (S := S) => p.tgt)
    (by
      intro p q h
      change scopedEquivalent P p q at h
      exact (Classical.choose (Classical.choose_spec h)).symm)

@[simp] theorem scopedSrc_mk (p : ScopedRawPath (S := S)) :
    scopedSrc P (scopedQuotientMk P p) = p.src :=
  rfl

@[simp] theorem scopedTgt_mk (p : ScopedRawPath (S := S)) :
    scopedTgt P (scopedQuotientMk P p) = p.tgt :=
  rfl

theorem continuous_scopedSrc : Continuous (scopedSrc P) := by
  apply (scopedQuotientMk_isQuotient P).continuous_iff.2
  exact TotalOpenGeometricCompPath.continuous_src S

theorem continuous_scopedTgt : Continuous (scopedTgt P) := by
  apply (scopedQuotientMk_isQuotient P).continuous_iff.2
  exact TotalOpenGeometricCompPath.continuous_tgt S

noncomputable def scopedRefl (a : A) : ScopedClass P :=
  scopedQuotientMk P (TotalOpenGeometricCompPath.totalRefl S a)

@[simp] theorem scopedSrc_refl (a : A) : scopedSrc P (scopedRefl P a) = a :=
  rfl

@[simp] theorem scopedTgt_refl (a : A) : scopedTgt P (scopedRefl P a) = a :=
  rfl

theorem continuous_scopedRefl : Continuous (scopedRefl P : A → ScopedClass P) := by
  exact continuous_scopedQuotientMk P |>.comp
    (TotalOpenGeometricCompPath.continuous_totalRefl S)

/-! ## Compatibility of the scoped relation with groupoid operations -/

theorem scopedEquivalent_symm
    {p q : ScopedRawPath (S := S)}
    (h : scopedEquivalent P p q) :
    scopedEquivalent P
      (TotalOpenGeometricCompPath.totalSymm S p)
      (TotalOpenGeometricCompPath.totalSymm S q) := by
  rcases p with ⟨p_src, p_tgt, p_path⟩
  rcases q with ⟨q_src, q_tgt, q_path⟩
  rcases h with ⟨hs, ht, h⟩
  cases hs
  cases ht
  exact ⟨rfl, rfl, ScopedRwEq.symm_congr h⟩

def leftRaw (c : TotalComposable A Step S) : ScopedRawPath (S := S) :=
  ⟨c.src, c.mid, c.left⟩

def rightRaw (c : TotalComposable A Step S) : ScopedRawPath (S := S) :=
  ⟨c.mid, c.tgt, c.right⟩

theorem scopedEquivalent_totalTrans
    {c d : TotalComposable A Step S}
    (hl : scopedEquivalent P (leftRaw c) (leftRaw d))
    (hr : scopedEquivalent P (rightRaw c) (rightRaw d)) :
    scopedEquivalent P
      (TotalOpenGeometricCompPath.totalTrans S c)
      (TotalOpenGeometricCompPath.totalTrans S d) := by
  rcases c with ⟨c_src, c_mid, c_tgt, c_left, c_right⟩
  rcases d with ⟨d_src, d_mid, d_tgt, d_left, d_right⟩
  rcases hl with ⟨hls, hlt, hl⟩
  rcases hr with ⟨hrs, hrt, hr⟩
  cases hls
  cases hlt
  cases hrs
  cases hrt
  exact ⟨rfl, rfl, ScopedRwEq.trans_congr hl hr⟩

noncomputable def scopedSymm (p : ScopedClass P) : ScopedClass P :=
  Quot.lift
    (fun p : ScopedRawPath (S := S) =>
      scopedQuotientMk P (TotalOpenGeometricCompPath.totalSymm S p))
    (by
      intro p q h
      apply Quot.sound
      exact scopedEquivalent_symm P h)
    p

@[simp] theorem scopedSymm_mk (p : ScopedRawPath (S := S)) :
    scopedSymm P (scopedQuotientMk P p) =
      scopedQuotientMk P (TotalOpenGeometricCompPath.totalSymm S p) :=
  rfl

theorem continuous_scopedSymm : Continuous (scopedSymm P : ScopedClass P →
    ScopedClass P) := by
  apply (scopedQuotientMk_isQuotient P).continuous_iff.2
  exact continuous_scopedQuotientMk P |>.comp
    (TotalOpenGeometricCompPath.continuous_totalSymm S)

/-! ## Explicit composable quotient -/

abbrev ScopedComposablePair :=
  {pq : ScopedClass P × ScopedClass P //
    scopedTgt P pq.1 = scopedSrc P pq.2}

abbrev ScopedComposableRaw := TotalComposable A Step S

def scopedComposableEquivalent
    (c d : ScopedComposableRaw (S := S)) : Prop :=
  scopedEquivalent P (leftRaw c) (leftRaw d) ∧
    scopedEquivalent P (rightRaw c) (rightRaw d)

noncomputable def scopedComposableSetoid : Setoid (ScopedComposableRaw (S := S)) where
  r := scopedComposableEquivalent P
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro c
      exact ⟨(scopedSetoid P).iseqv.refl _,
        (scopedSetoid P).iseqv.refl _⟩
    · intro c d h
      exact ⟨(scopedSetoid P).iseqv.symm h.1,
        (scopedSetoid P).iseqv.symm h.2⟩
    · intro c d e h₁ h₂
      exact ⟨(scopedSetoid P).iseqv.trans h₁.1 h₂.1,
        (scopedSetoid P).iseqv.trans h₁.2 h₂.2⟩

abbrev ScopedComposableClass : Type _ :=
  Quotient (scopedComposableSetoid P)

noncomputable def scopedComposableMk (c : ScopedComposableRaw (S := S)) :
    ScopedComposableClass P :=
  Quotient.mk (scopedComposableSetoid P) c

noncomputable instance scopedComposableClassTopologicalSpace :
    TopologicalSpace (ScopedComposableClass P) :=
  TopologicalSpace.coinduced (scopedComposableMk P) inferInstance

theorem scopedComposableMk_surjective :
    Function.Surjective (scopedComposableMk P :
      ScopedComposableRaw (S := S) → ScopedComposableClass P) := by
  intro x
  refine Quot.inductionOn x ?_
  intro c
  exact ⟨c, rfl⟩

theorem scopedComposableMk_isQuotient :
    Topology.IsQuotientMap (scopedComposableMk P :
      ScopedComposableRaw (S := S) → ScopedComposableClass P) :=
  ⟨⟨rfl⟩, scopedComposableMk_surjective P⟩

theorem continuous_scopedComposableMk :
    Continuous (scopedComposableMk P :
      ScopedComposableRaw (S := S) → ScopedComposableClass P) :=
  continuous_coinduced_rng

/-! ## Final and ordinary composable domains -/

structure ScopedStrongComposablePair where
  val : ScopedComposablePair P

noncomputable def scopedPairMap (c : ScopedComposableClass P) :
    ScopedStrongComposablePair P :=
  Quot.lift
    (fun c : ScopedComposableRaw (S := S) =>
      ⟨⟨scopedQuotientMk P (leftRaw c),
          scopedQuotientMk P (rightRaw c)⟩, rfl⟩)
    (by
      intro c d h
      change scopedComposableEquivalent P c d at h
      apply _root_.congrArg (fun z : ScopedComposablePair P =>
        (⟨z⟩ : ScopedStrongComposablePair P))
      apply Subtype.ext
      apply Prod.ext
      · apply Quot.sound
        exact h.1
      · apply Quot.sound
        exact h.2)
    c

@[simp] theorem scopedPairMap_mk (c : ScopedComposableRaw (S := S)) :
    scopedPairMap P (scopedComposableMk P c) =
      ⟨⟨scopedQuotientMk P (leftRaw c),
          scopedQuotientMk P (rightRaw c)⟩, rfl⟩ :=
  rfl

theorem scopedPairMap_surjective :
    Function.Surjective (scopedPairMap P :
      ScopedComposableClass P → ScopedStrongComposablePair P) := by
  intro x
  rcases x with ⟨⟨p, q⟩, h⟩
  revert h
  refine Quot.inductionOn p ?_
  intro p h
  revert h
  refine Quot.inductionOn q ?_
  intro q h
  rcases q with ⟨q_src, q_tgt, q_path⟩
  change scopedTgt P (scopedQuotientMk P p) =
    scopedSrc P (scopedQuotientMk P
      (⟨q_src, q_tgt, q_path⟩ : ScopedRawPath (S := S))) at h
  rw [scopedTgt_mk, scopedSrc_mk] at h
  cases h
  let c : ScopedComposableRaw (S := S) :=
    ⟨p.src, p.tgt, q_tgt, p.path, q_path⟩
  refine ⟨scopedComposableMk P c, ?_⟩
  rfl

noncomputable def scopedCompositionFromComposable
    (c : ScopedComposableClass P) : ScopedClass P :=
  Quot.lift
    (fun c : ScopedComposableRaw (S := S) =>
      scopedQuotientMk P (TotalOpenGeometricCompPath.totalTrans S c))
    (by
      intro c d h
      apply Quot.sound
      exact scopedEquivalent_totalTrans P h.1 h.2)
    c

@[simp] theorem scopedCompositionFromComposable_mk
    (c : ScopedComposableRaw (S := S)) :
    scopedCompositionFromComposable P (scopedComposableMk P c) =
      scopedQuotientMk P (TotalOpenGeometricCompPath.totalTrans S c) :=
  rfl

theorem continuous_scopedCompositionFromComposable :
    Continuous (scopedCompositionFromComposable P :
      ScopedComposableClass P → ScopedClass P) := by
  apply (scopedComposableMk_isQuotient P).continuous_iff.2
  exact continuous_scopedQuotientMk P |>.comp
    (TotalOpenGeometricCompPath.continuous_totalTrans S)

noncomputable instance scopedStrongComposablePairTopologicalSpace :
    TopologicalSpace (ScopedStrongComposablePair P) :=
  TopologicalSpace.coinduced (scopedPairMap P) inferInstance

theorem scopedPairMap_isQuotient :
    Topology.IsQuotientMap (scopedPairMap P :
      ScopedComposableClass P → ScopedStrongComposablePair P) :=
  ⟨⟨rfl⟩, scopedPairMap_surjective P⟩

theorem continuous_scopedPairMap :
    Continuous (scopedPairMap P :
      ScopedComposableClass P → ScopedStrongComposablePair P) :=
  continuous_coinduced_rng

noncomputable def scopedStrongToOrdinary :
    ScopedStrongComposablePair P → ScopedComposablePair P :=
  fun p => p.val

theorem continuous_scopedStrongToOrdinary :
    Continuous (scopedStrongToOrdinary P :
      ScopedStrongComposablePair P → ScopedComposablePair P) := by
  apply (scopedPairMap_isQuotient P).continuous_iff.2
  apply (scopedComposableMk_isQuotient P).continuous_iff.2
  change Continuous (fun c : ScopedComposableRaw (S := S) =>
    (⟨(scopedQuotientMk P (leftRaw c),
      scopedQuotientMk P (rightRaw c)), rfl⟩ : ScopedComposablePair P))
  have hleft : Continuous (fun c : ScopedComposableRaw (S := S) =>
      scopedQuotientMk P (leftRaw c)) :=
    continuous_scopedQuotientMk P |>.comp
      (by
        convert (TotalOpenGeometricCompPath.continuous_leftTotal S) using 1
        funext c
        rfl)
  have hright : Continuous (fun c : ScopedComposableRaw (S := S) =>
      scopedQuotientMk P (rightRaw c)) :=
    continuous_scopedQuotientMk P |>.comp
      (by
        convert (TotalOpenGeometricCompPath.continuous_rightTotal S) using 1
        funext c
        rfl)
  exact (hleft.prodMk hright).subtype_mk (by intro c; rfl)

noncomputable def scopedCompositionOnStrong
    (c : ScopedStrongComposablePair P) : ScopedClass P :=
  scopedCompositionFromComposable P
    (Classical.choose (scopedPairMap_surjective P c))

theorem scopedCompositionOnStrong_mk
    (c : ScopedComposableRaw (S := S)) :
    scopedCompositionOnStrong P (scopedPairMap P (scopedComposableMk P c)) =
      scopedCompositionFromComposable P (scopedComposableMk P c) := by
  let d := Classical.choose
    (scopedPairMap_surjective P (scopedPairMap P (scopedComposableMk P c)))
  have hd : scopedPairMap P d = scopedPairMap P (scopedComposableMk P c) :=
    Classical.choose_spec
      (scopedPairMap_surjective P (scopedPairMap P (scopedComposableMk P c)))
  change scopedCompositionFromComposable P d =
    scopedCompositionFromComposable P (scopedComposableMk P c)
  revert hd
  refine Quot.inductionOn d ?_
  intro d hd
  change scopedPairMap P (scopedComposableMk P d) =
    scopedPairMap P (scopedComposableMk P c) at hd
  rw [scopedPairMap_mk, scopedPairMap_mk] at hd
  have hleft :
      scopedQuotientMk P (leftRaw d) = scopedQuotientMk P (leftRaw c) := by
    exact _root_.congrArg
      (fun z : ScopedStrongComposablePair P => z.val.val.1) hd
  have hright :
      scopedQuotientMk P (rightRaw d) = scopedQuotientMk P (rightRaw c) := by
    exact _root_.congrArg
      (fun z : ScopedStrongComposablePair P => z.val.val.2) hd
  have hcd : scopedComposableEquivalent P d c :=
    ⟨Quotient.exact hleft, Quotient.exact hright⟩
  exact Quotient.sound (scopedEquivalent_totalTrans P hcd.1 hcd.2)

theorem continuous_scopedCompositionOnStrong :
    Continuous (scopedCompositionOnStrong P :
      ScopedStrongComposablePair P → ScopedClass P) := by
  apply (scopedPairMap_isQuotient P).continuous_iff.2
  have hfactor :
      scopedCompositionOnStrong P ∘ scopedPairMap P =
        scopedCompositionFromComposable P := by
    funext c
    refine Quot.inductionOn c ?_
    intro c
    exact scopedCompositionOnStrong_mk P c
  rw [hfactor]
  exact continuous_scopedCompositionFromComposable P

end ScopedGeometricRewrite
end GeometricTopology
end Path
end ComputationalPaths
