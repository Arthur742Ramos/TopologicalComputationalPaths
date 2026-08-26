import Mathlib.Topology.Constructions
import Mathlib.Topology.Path
import Mathlib.Topology.Homotopy.Path

/-!
# Challenge: topological semantics of computational paths

This is the statement-only surface of the result.  The endpoint-varying
geometric trace, its scoped rewrite quotient, and the final composable domain
are defined here from Lean core and Mathlib alone.  The proof-side module
contains the corresponding checked development and is compared against this
surface by Comparator.

The selected result solves the comparison problem between the canonical final
composable topology and the ordinary pullback topology.  It characterizes
exactly when the canonical continuous bijection is a homeomorphism, derives
ordinary composition continuity, records the corresponding obstruction, and
proves compact--Hausdorff and discrete sufficient cases.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

universe u v

/-! ## Endpoint-varying geometric traces -/

structure GeometricStepSystem (A : Type u) [TopologicalSpace A] (Step : Type v) where
  src : Step → A
  tgt : Step → A
  realize : (s : Step) → _root_.Path (src s) (tgt s)

inductive GeometricTrace {A : Type u} [TopologicalSpace A] {Step : Type v}
    (S : GeometricStepSystem A Step) : A → A → Type (max u v) where
  | refl (a : A) : GeometricTrace S a a
  | single (s : Step) : GeometricTrace S (S.src s) (S.tgt s)
  | trans {a b c : A} :
      GeometricTrace S a b → GeometricTrace S b c → GeometricTrace S a c
  | symm {a b : A} : GeometricTrace S a b → GeometricTrace S b a

namespace GeometricTrace

variable {A : Type u} [TopologicalSpace A] {Step : Type v}
  {S : GeometricStepSystem A Step}

noncomputable def realize {a b : A} : GeometricTrace S a b → _root_.Path a b
  | .refl a => _root_.Path.refl a
  | .single s => S.realize s
  | .trans p q => _root_.Path.trans (realize p) (realize q)
  | .symm p => _root_.Path.symm (realize p)

def traceLength {a b : A} : GeometricTrace S a b → Nat
  | .refl _ => 0
  | .single _ => 1
  | .trans p q => traceLength p + traceLength q
  | .symm p => traceLength p

end GeometricTrace

structure OpenGeometricCompPath {A : Type u} [TopologicalSpace A]
    {Step : Type v} (S : GeometricStepSystem A Step) (a b : A) where
  trace : GeometricTrace S a b
  geometric : _root_.Path a b
  coherent : _root_.Path.Homotopic geometric (GeometricTrace.realize trace)

noncomputable def openRefl {A : Type u} [TopologicalSpace A] {Step : Type v}
    (S : GeometricStepSystem A Step) (a : A) :
    OpenGeometricCompPath S a a :=
  { trace := GeometricTrace.refl a
    geometric := _root_.Path.refl a
    coherent := by
      change _root_.Path.Homotopic (_root_.Path.refl a) (_root_.Path.refl a)
      exact _root_.Path.Homotopic.refl _ }

noncomputable def openTrans {A : Type u} [TopologicalSpace A] {Step : Type v}
    {a b c : A} (S : GeometricStepSystem A Step)
    (p : OpenGeometricCompPath S a b) (q : OpenGeometricCompPath S b c) :
    OpenGeometricCompPath S a c :=
  { trace := GeometricTrace.trans p.trace q.trace
    geometric := _root_.Path.trans p.geometric q.geometric
    coherent := by
      rcases p.coherent with ⟨hp⟩
      rcases q.coherent with ⟨hq⟩
      exact ⟨hp.hcomp hq⟩ }

noncomputable def openSymm {A : Type u} [TopologicalSpace A] {Step : Type v}
    {a b : A} (S : GeometricStepSystem A Step)
    (p : OpenGeometricCompPath S a b) :
    OpenGeometricCompPath S b a :=
  { trace := GeometricTrace.symm p.trace
    geometric := _root_.Path.symm p.geometric
    coherent := by
      rcases p.coherent with ⟨hp⟩
      exact ⟨hp.symm₂⟩ }

/-! ## Continuous systems and total carriers -/

structure ContinuousGeometricStepSystem (A : Type u) [TopologicalSpace A]
    (Step : Type v) [TopologicalSpace Step]
    extends GeometricStepSystem A Step where
  continuous_src : Continuous src
  continuous_tgt : Continuous tgt
  continuous_realize :
    Continuous (fun s => (realize s).toContinuousMap)

structure TotalOpenGeometricCompPath
    (A : Type u) [TopologicalSpace A]
    (Step : Type v) [TopologicalSpace Step]
    (S : ContinuousGeometricStepSystem A Step) where
  src : A
  tgt : A
  path : OpenGeometricCompPath S.toGeometricStepSystem src tgt

namespace TotalOpenGeometricCompPath

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  (S : ContinuousGeometricStepSystem A Step)

def trace (p : TotalOpenGeometricCompPath A Step S) :
    GeometricTrace S.toGeometricStepSystem p.src p.tgt :=
  p.path.trace

def geometricPath (p : TotalOpenGeometricCompPath A Step S) :
    _root_.Path p.src p.tgt :=
  p.path.geometric

noncomputable def traceMap (p : TotalOpenGeometricCompPath A Step S) : C(unitInterval, A) :=
  (GeometricTrace.realize p.trace).toContinuousMap

def geometricMap (p : TotalOpenGeometricCompPath A Step S) : C(unitInterval, A) :=
  p.geometricPath.toContinuousMap

abbrev Observation :=
  A × (A × (Nat × (C(unitInterval, A) × C(unitInterval, A))))

noncomputable def observation (p : TotalOpenGeometricCompPath A Step S) :
    Observation (A := A) :=
  (p.src, (p.tgt, (GeometricTrace.traceLength p.trace,
    (p.traceMap S, p.geometricMap S))))

noncomputable instance instTopologicalSpace :
    TopologicalSpace (TotalOpenGeometricCompPath A Step S) :=
  TopologicalSpace.induced (observation S) inferInstance

noncomputable def totalRefl (a : A) :
    TotalOpenGeometricCompPath A Step S :=
  ⟨a, a, openRefl S.toGeometricStepSystem a⟩

noncomputable def totalSymm
    (p : TotalOpenGeometricCompPath A Step S) :
    TotalOpenGeometricCompPath A Step S :=
  ⟨p.tgt, p.src, openSymm S.toGeometricStepSystem p.path⟩

end TotalOpenGeometricCompPath

structure TotalComposable
    (A : Type u) [TopologicalSpace A]
    (Step : Type v) [TopologicalSpace Step]
    (S : ContinuousGeometricStepSystem A Step) where
  src : A
  mid : A
  tgt : A
  left : OpenGeometricCompPath S.toGeometricStepSystem src mid
  right : OpenGeometricCompPath S.toGeometricStepSystem mid tgt

namespace TotalOpenGeometricCompPath

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  (S : ContinuousGeometricStepSystem A Step)

noncomputable def totalTrans
    (c : TotalComposable A Step S) :
    TotalOpenGeometricCompPath A Step S :=
  ⟨c.src, c.tgt, openTrans S.toGeometricStepSystem c.left c.right⟩

end TotalOpenGeometricCompPath

namespace TotalComposable

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  (S : ContinuousGeometricStepSystem A Step)

noncomputable def leftTraceMap (c : TotalComposable A Step S) : C(unitInterval, A) :=
  (GeometricTrace.realize c.left.trace).toContinuousMap

noncomputable def rightTraceMap (c : TotalComposable A Step S) : C(unitInterval, A) :=
  (GeometricTrace.realize c.right.trace).toContinuousMap

def leftGeometricMap (c : TotalComposable A Step S) : C(unitInterval, A) :=
  c.left.geometric.toContinuousMap

def rightGeometricMap (c : TotalComposable A Step S) : C(unitInterval, A) :=
  c.right.geometric.toContinuousMap

def leftTraceLength (c : TotalComposable A Step S) : Nat :=
  GeometricTrace.traceLength c.left.trace

def rightTraceLength (c : TotalComposable A Step S) : Nat :=
  GeometricTrace.traceLength c.right.trace

abbrev Observation :=
  A × (A × (A × (Nat × (Nat ×
    (C(unitInterval, A) × (C(unitInterval, A) ×
      (C(unitInterval, A) × C(unitInterval, A))))))))

noncomputable def observation (c : TotalComposable A Step S) :
    Observation (A := A) :=
  (c.src, (c.mid, (c.tgt, (c.leftTraceLength, (c.rightTraceLength,
    (leftTraceMap S c, (rightTraceMap S c,
      (leftGeometricMap S c, rightGeometricMap S c))))))))

noncomputable instance instTopologicalSpace :
    TopologicalSpace (TotalComposable A Step S) :=
  TopologicalSpace.induced (observation S) inferInstance

end TotalComposable

/-! ## Scoped rewrite presentations -/

namespace ContinuousGeometricStepSystemMap

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  {S : ContinuousGeometricStepSystem A Step}

noncomputable def castTrace
    {a b a' b' : A} (ha : a' = a) (hb : b' = b)
    (t : GeometricTrace S.toGeometricStepSystem a b) :
    GeometricTrace S.toGeometricStepSystem a' b' :=
  Eq.mp (by cases ha; cases hb; rfl) t

end ContinuousGeometricStepSystemMap

structure ScopedGeometricRewritePresentation
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    (S : ContinuousGeometricStepSystem A Step) where
  rule : ∀ {a b : A},
    GeometricTrace S.toGeometricStepSystem a b →
      GeometricTrace S.toGeometricStepSystem a b → Prop
  sound_rule : ∀ {a b : A}
    {p q : GeometricTrace S.toGeometricStepSystem a b},
    rule p q →
      _root_.Path.Homotopic
        (GeometricTrace.realize p) (GeometricTrace.realize q)

inductive ScopedRwEq
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    {S : ContinuousGeometricStepSystem A Step}
    (P : ScopedGeometricRewritePresentation S) :
    {a b : A} →
      GeometricTrace S.toGeometricStepSystem a b →
        GeometricTrace S.toGeometricStepSystem a b → Prop
  | refl {a b : A}
      (p : GeometricTrace S.toGeometricStepSystem a b) :
      ScopedRwEq P p p
  | generator {a b : A}
      {p q : GeometricTrace S.toGeometricStepSystem a b} :
      P.rule p q → ScopedRwEq P p q
  | symm {a b : A}
      {p q : GeometricTrace S.toGeometricStepSystem a b} :
      ScopedRwEq P p q → ScopedRwEq P q p
  | trans {a b : A}
      {p q r : GeometricTrace S.toGeometricStepSystem a b} :
      ScopedRwEq P p q → ScopedRwEq P q r → ScopedRwEq P p r
  | trans_congr {a b c : A}
      {p p' : GeometricTrace S.toGeometricStepSystem a b}
      {q q' : GeometricTrace S.toGeometricStepSystem b c} :
      ScopedRwEq P p p' → ScopedRwEq P q q' →
        ScopedRwEq P (GeometricTrace.trans p q) (GeometricTrace.trans p' q')
  | symm_congr {a b : A}
      {p q : GeometricTrace S.toGeometricStepSystem a b} :
      ScopedRwEq P p q →
        ScopedRwEq P (GeometricTrace.symm p) (GeometricTrace.symm q)
  | refl_trans {a b : A}
      (p : GeometricTrace S.toGeometricStepSystem a b) :
      ScopedRwEq P
        (GeometricTrace.trans (GeometricTrace.refl a) p) p
  | trans_refl {a b : A}
      (p : GeometricTrace S.toGeometricStepSystem a b) :
      ScopedRwEq P
        (GeometricTrace.trans p (GeometricTrace.refl b)) p
  | trans_assoc {a b c d : A}
      (p : GeometricTrace S.toGeometricStepSystem a b)
      (q : GeometricTrace S.toGeometricStepSystem b c)
      (r : GeometricTrace S.toGeometricStepSystem c d) :
      ScopedRwEq P
        (GeometricTrace.trans (GeometricTrace.trans p q) r)
        (GeometricTrace.trans p (GeometricTrace.trans q r))
  | symm_trans {a b : A}
      (p : GeometricTrace S.toGeometricStepSystem a b) :
      ScopedRwEq P
        (GeometricTrace.trans (GeometricTrace.symm p) p)
        (GeometricTrace.refl b)
  | trans_symm {a b : A}
      (p : GeometricTrace S.toGeometricStepSystem a b) :
      ScopedRwEq P
        (GeometricTrace.trans p (GeometricTrace.symm p))
        (GeometricTrace.refl a)
  | symm_symm {a b : A}
      (p : GeometricTrace S.toGeometricStepSystem a b) :
      ScopedRwEq P
        (GeometricTrace.symm (GeometricTrace.symm p)) p
  | symm_refl (a : A) :
      ScopedRwEq P
        (GeometricTrace.symm (GeometricTrace.refl a))
        (GeometricTrace.refl a)
  | symm_comp {a b c : A}
      (p : GeometricTrace S.toGeometricStepSystem a b)
      (q : GeometricTrace S.toGeometricStepSystem b c) :
      ScopedRwEq P
        (GeometricTrace.symm (GeometricTrace.trans p q))
        (GeometricTrace.trans (GeometricTrace.symm q)
          (GeometricTrace.symm p))

abbrev ScopedRawPath
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    {S : ContinuousGeometricStepSystem A Step} :=
  TotalOpenGeometricCompPath A Step S

noncomputable def castScopedTrace
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    {S : ContinuousGeometricStepSystem A Step}
    {p q : ScopedRawPath (S := S)}
    (hs : q.src = p.src) (ht : q.tgt = p.tgt) :
    GeometricTrace S.toGeometricStepSystem q.src q.tgt :=
  ContinuousGeometricStepSystemMap.castTrace hs ht p.trace

def scopedEquivalent
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    {S : ContinuousGeometricStepSystem A Step}
    (P : ScopedGeometricRewritePresentation S)
    (p q : ScopedRawPath (S := S)) : Prop :=
  ∃ hs : q.src = p.src, ∃ ht : q.tgt = p.tgt,
    ScopedRwEq P (castScopedTrace hs ht) q.trace

noncomputable def scopedSetoid
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    {S : ContinuousGeometricStepSystem A Step}
    (P : ScopedGeometricRewritePresentation S) :
    Setoid (ScopedRawPath (S := S)) where
  r := scopedEquivalent P
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact ⟨rfl, rfl, ScopedRwEq.refl p.trace⟩
    · intro p q h
      rcases p with ⟨p_src, p_tgt, p_path⟩
      rcases q with ⟨q_src, q_tgt, q_path⟩
      rcases h with ⟨hs, ht, h⟩
      cases hs
      cases ht
      exact ⟨rfl, rfl, ScopedRwEq.symm h⟩
    · intro p q r h₁ h₂
      rcases p with ⟨p_src, p_tgt, p_path⟩
      rcases q with ⟨q_src, q_tgt, q_path⟩
      rcases r with ⟨r_src, r_tgt, r_path⟩
      rcases h₁ with ⟨hs₁, ht₁, h₁⟩
      rcases h₂ with ⟨hs₂, ht₂, h₂⟩
      cases hs₁
      cases ht₁
      cases hs₂
      cases ht₂
      exact ⟨rfl, rfl, ScopedRwEq.trans h₁ h₂⟩

abbrev ScopedClass
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    {S : ContinuousGeometricStepSystem A Step}
    (P : ScopedGeometricRewritePresentation S) : Type _ :=
  Quotient (scopedSetoid P)

noncomputable def scopedQuotientMk
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    {S : ContinuousGeometricStepSystem A Step}
    (P : ScopedGeometricRewritePresentation S)
    (p : ScopedRawPath (S := S)) : ScopedClass P :=
  Quotient.mk (scopedSetoid P) p

end GeometricTopology
end Path
end ComputationalPaths

namespace ComputationalPaths.Path.GeometricTopology

open scoped ContinuousMap Topology

universe u v

namespace ScopedGeometricRewrite

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  {S : ContinuousGeometricStepSystem A Step}
  (P : ScopedGeometricRewritePresentation S)

noncomputable instance scopedClassTopologicalSpace :
    TopologicalSpace (ScopedClass P) :=
  TopologicalSpace.coinduced (scopedQuotientMk P) inferInstance

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
    scopedSrc P (scopedQuotientMk P p) = p.src := rfl

@[simp] theorem scopedTgt_mk (p : ScopedRawPath (S := S)) :
    scopedTgt P (scopedQuotientMk P p) = p.tgt := rfl

noncomputable def scopedRefl (a : A) : ScopedClass P :=
  scopedQuotientMk P (TotalOpenGeometricCompPath.totalRefl S a)

@[simp] theorem scopedSrc_refl (a : A) : scopedSrc P (scopedRefl P a) = a := rfl

@[simp] theorem scopedTgt_refl (a : A) : scopedTgt P (scopedRefl P a) = a := rfl

def leftRaw (c : TotalComposable A Step S) : ScopedRawPath (S := S) :=
  ⟨c.src, c.mid, c.left⟩

def rightRaw (c : TotalComposable A Step S) : ScopedRawPath (S := S) :=
  ⟨c.mid, c.tgt, c.right⟩

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
      scopedQuotientMk P (TotalOpenGeometricCompPath.totalSymm S p) := rfl

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

abbrev ScopedComposablePair :=
  {pq : ScopedClass P × ScopedClass P //
    scopedTgt P pq.1 = scopedSrc P pq.2}

abbrev ScopedComposableRaw := TotalComposable A Step S

def scopedComposableEquivalent
    (c d : ScopedComposableRaw (S := S)) : Prop :=
  scopedEquivalent P (leftRaw c) (leftRaw d) ∧
    scopedEquivalent P (rightRaw c) (rightRaw d)

noncomputable def scopedComposableSetoid :
    Setoid (ScopedComposableRaw (S := S)) where
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
          scopedQuotientMk P (rightRaw c)⟩, rfl⟩ := rfl

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

noncomputable instance scopedStrongComposablePairTopologicalSpace :
    TopologicalSpace (ScopedStrongComposablePair P) :=
  TopologicalSpace.coinduced (scopedPairMap P) inferInstance

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

end ScopedGeometricRewrite
end ComputationalPaths.Path.GeometricTopology

namespace ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite

open scoped ContinuousMap Topology

universe u v

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  {S : ContinuousGeometricStepSystem A Step}
  (P : ScopedGeometricRewritePresentation S)

theorem scopedSrc_symm (p : ScopedClass P) :
    scopedSrc P (scopedSymm P p) = scopedTgt P p := by
  refine Quotient.inductionOn p ?_
  intro p
  rfl

theorem scopedTgt_symm (p : ScopedClass P) :
    scopedTgt P (scopedSymm P p) = scopedSrc P p := by
  refine Quotient.inductionOn p ?_
  intro p
  rfl

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

end ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite

namespace TopologicalComputationalPaths

open ComputationalPaths.Path.GeometricTopology
open ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite

universe u v

/-! ## The ordinary/final topology comparison

The canonical final composable domain is always mapped continuously and
bijectively to the ordinary pullback of quotient arrows.  The substantive
question is when its inverse is continuous, equivalently when the raw pair map
is quotient and when the two topologies agree. -/

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

theorem main_result
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    (S : ContinuousGeometricStepSystem A Step)
    (P : ScopedGeometricRewritePresentation S) :
    OrdinaryTopologyComparisonCertificate S P := by
  sorry

end TopologicalComputationalPaths
