import ComputationalPaths.Path.Topology.ScopedGeometricRewriteFunctor
import ComputationalPaths.Path.Topology.ConcreteCircleWinding
import ComputationalPaths.Path.Topology.TopologicalWindingHomeomorph

/-!
# A concrete topological-circle presentation

The abstract construction is instantiated with the actual unit additive
circle.  Primitive steps are standard loops indexed by integers, so the
geometric carrier is genuinely nonconstant.  The named scoped generators are
endpoint-fixed geometric homotopies between integer-loop traces.

The named scoped generators are the explicit zero, integer-concatenation, and
reversal rules.  Their geometric soundness is proved from the covering-space
winding theorem, and an induction normalizes every trace to one integer
singleton.  The loop fibre of the resulting presented carrier is then
classified by the existing winding theorem.  This gives a concrete `ℤ`
normal form for a nontrivial topological example while retaining the full
scoped rewrite and quotient infrastructure.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

universe u

namespace ScopedGeometricRewrite

open ConcreteCircleWinding

attribute [local instance] _root_.Path.Homotopic.setoid

private theorem windingPath_symm (γ : _root_.Path (0 : TopologicalCircle) 0) :
    windingPath γ.symm = -windingPath γ := by
  have h := windingPath_eq_of_homotopic (_root_.Path.Homotopic.trans_symm γ)
  rw [windingPath_trans, windingPath_refl] at h
  omega

/-! ## Integer standard-loop step system -/

noncomputable def circleLoopStepSystem :
    ContinuousGeometricStepSystem TopologicalCircle ℤ where
  src := fun _ => (0 : TopologicalCircle)
  tgt := fun _ => (0 : TopologicalCircle)
  realize := fun n => standardLoop n
  continuous_src := continuous_const
  continuous_tgt := continuous_const
  continuous_realize := by
    exact continuous_of_discreteTopology

abbrev CircleTrace :=
  GeometricTrace circleLoopStepSystem.toGeometricStepSystem
    (0 : TopologicalCircle) (0 : TopologicalCircle)

def circleSingle (n : ℤ) : CircleTrace :=
  GeometricTrace.single n

/-! ## Explicit circle rewrite rules -/

def circleTraceWinding :
    {a b : TopologicalCircle} →
      GeometricTrace circleLoopStepSystem.toGeometricStepSystem a b → ℤ
  | _, _, GeometricTrace.refl _ => 0
  | _, _, GeometricTrace.single n => n
  | _, _, GeometricTrace.trans p q => circleTraceWinding p + circleTraceWinding q
  | _, _, GeometricTrace.symm p => -circleTraceWinding p

theorem circleTraceEndpoints_eq
    {a b : TopologicalCircle}
    (p : GeometricTrace circleLoopStepSystem.toGeometricStepSystem a b) :
    a = b := by
  induction p with
  | refl a => rfl
  | single n => simp [circleLoopStepSystem]
  | trans p q ihp ihq => exact ihp.trans ihq
  | symm p ih => exact ih.symm

noncomputable def circleTraceCast
    {a b : TopologicalCircle}
    (ha : a = (0 : TopologicalCircle))
    (hb : b = (0 : TopologicalCircle))
    (p : GeometricTrace circleLoopStepSystem.toGeometricStepSystem a b) :
    CircleTrace := by
  cases ha
  cases hb
  exact p

def circleLoopRule
    {a b : TopologicalCircle}
    (p q : GeometricTrace circleLoopStepSystem.toGeometricStepSystem a b) : Prop :=
  ∃ (ha : a = (0 : TopologicalCircle))
    (hb : b = (0 : TopologicalCircle)),
    (∃ n m : ℤ,
        circleTraceCast ha hb p = GeometricTrace.trans
          (GeometricTrace.single n : CircleTrace)
          (GeometricTrace.single m : CircleTrace) ∧
        circleTraceCast ha hb q =
          (GeometricTrace.single (n + m) : CircleTrace)) ∨
      (circleTraceCast ha hb p =
          (GeometricTrace.refl (0 : TopologicalCircle) : CircleTrace) ∧
        circleTraceCast ha hb q = (GeometricTrace.single 0 : CircleTrace)) ∨
      (∃ n : ℤ,
        circleTraceCast ha hb p = GeometricTrace.symm
          (GeometricTrace.single n : CircleTrace) ∧
        circleTraceCast ha hb q =
          (GeometricTrace.single (-n) : CircleTrace))

theorem circleLoopRule_add (n m : ℤ) :
    circleLoopRule
      (GeometricTrace.trans
      (GeometricTrace.single n : CircleTrace)
      (GeometricTrace.single m : CircleTrace))
      (GeometricTrace.single (n + m) : CircleTrace) :=
  ⟨rfl, rfl, Or.inl ⟨n, m, rfl, rfl⟩⟩

theorem circleLoopRule_zero :
    circleLoopRule
      (GeometricTrace.refl (0 : TopologicalCircle) : CircleTrace)
      (GeometricTrace.single 0 : CircleTrace) :=
  ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

theorem circleLoopRule_neg (n : ℤ) :
    circleLoopRule
      (GeometricTrace.symm
        (GeometricTrace.single n : CircleTrace))
      (GeometricTrace.single (-n) : CircleTrace) :=
  ⟨rfl, rfl, Or.inr (Or.inr ⟨n, rfl, rfl⟩)⟩

theorem circleLoopRule_sound
    {a b : TopologicalCircle}
    {p q : GeometricTrace circleLoopStepSystem.toGeometricStepSystem a b}
    (h : circleLoopRule p q) :
    _root_.Path.Homotopic
      (GeometricTrace.realize p) (GeometricTrace.realize q) := by
  rcases h with ⟨ha, hb, h⟩
  cases ha
  cases hb
  rcases h with h | h | h
  · rcases h with ⟨n, m, hp, hq⟩
    cases hp
    cases hq
    have hstd := (standardLoop_homotopic
      ((standardLoop n).trans (standardLoop m))).symm
    rw [windingPath_trans, windingPath_standardLoop,
      windingPath_standardLoop] at hstd
    simpa [GeometricTrace.realize, circleLoopStepSystem] using hstd
  · rcases h with ⟨hp, hq⟩
    cases hp
    cases hq
    have hstd := (standardLoop_homotopic
      (_root_.Path.refl (0 : TopologicalCircle))).symm
    rw [windingPath_refl] at hstd
    simpa [GeometricTrace.realize, circleLoopStepSystem] using hstd
  · rcases h with ⟨n, hp, hq⟩
    cases hp
    cases hq
    have hstd := (standardLoop_homotopic ((standardLoop n).symm)).symm
    rw [windingPath_symm, windingPath_standardLoop] at hstd
    simpa [GeometricTrace.realize, circleLoopStepSystem] using hstd

noncomputable def circleLoopPresentation :
    ScopedGeometricRewritePresentation circleLoopStepSystem where
  rule := fun {a b} p q => circleLoopRule p q
  sound_rule := by
    intro a b p q h
    exact circleLoopRule_sound h

noncomputable def circleFinalTopologicalGroupoidCertificate :
    ScopedFinalTopologicalGroupoidCertificate circleLoopPresentation :=
  scopedFinalTopologicalGroupoidCertificate circleLoopPresentation

theorem circleOrdinaryFinalCompatibility_iff :
    ProductQuotientCompatibility circleLoopPresentation ↔
      Continuous (scopedOrdinaryToFinal circleLoopPresentation :
        ScopedComposablePair circleLoopPresentation →
          ScopedComposableClass circleLoopPresentation) :=
  scopedProductCompatibility_iff_ordinary_to_final_continuous
    circleLoopPresentation

theorem circleTraceWinding_realize_aux
    {a b : TopologicalCircle}
    (p : GeometricTrace circleLoopStepSystem.toGeometricStepSystem a b)
    (ha : a = (0 : TopologicalCircle))
    (hb : b = (0 : TopologicalCircle)) :
    windingPath (GeometricTrace.realize (circleTraceCast ha hb p)) =
      circleTraceWinding p := by
  induction p with
  | refl a =>
      cases ha
      cases hb
      change windingPath (_root_.Path.refl (0 : TopologicalCircle)) = 0
      exact windingPath_refl
  | single n =>
      cases ha
      cases hb
      change windingPath (standardLoop n) = n
      exact windingPath_standardLoop n
  | trans p q ihp ihq =>
      have hmid : _ = (0 : TopologicalCircle) :=
        (circleTraceEndpoints_eq p).symm.trans ha
      cases ha
      cases hmid
      cases hb
      simp only [circleTraceCast, GeometricTrace.realize, circleTraceWinding]
      have hp' : windingPath p.realize = circleTraceWinding p := by
        simpa [circleTraceCast] using ihp rfl rfl
      have hq' : windingPath q.realize = circleTraceWinding q := by
        simpa [circleTraceCast] using ihq rfl rfl
      rw [windingPath_trans, hp', hq']
  | symm p ih =>
      cases ha
      cases hb
      simp only [circleTraceCast, GeometricTrace.realize, circleTraceWinding]
      have hp' : windingPath p.realize = circleTraceWinding p := by
        simpa [circleTraceCast] using ih rfl rfl
      rw [windingPath_symm, hp']

theorem circleTraceWinding_realize (p : CircleTrace) :
    windingPath (GeometricTrace.realize p) = circleTraceWinding p :=
  circleTraceWinding_realize_aux p rfl rfl

theorem circleTrace_normalizes_aux
    {a b : TopologicalCircle}
    (p : GeometricTrace circleLoopStepSystem.toGeometricStepSystem a b)
    (ha : a = (0 : TopologicalCircle))
    (hb : b = (0 : TopologicalCircle)) :
    ScopedRwEq circleLoopPresentation (circleTraceCast ha hb p)
      (GeometricTrace.single (circleTraceWinding p) : CircleTrace) := by
  induction p with
  | refl a =>
      cases ha
      cases hb
      simpa [circleTraceCast, circleTraceWinding] using
        (ScopedRwEq.generator
          (P := circleLoopPresentation) circleLoopRule_zero)
  | single n =>
      cases ha
      cases hb
      exact ScopedRwEq.refl _
  | trans p q ihp ihq =>
      have hmid : _ = (0 : TopologicalCircle) :=
        (circleTraceEndpoints_eq p).symm.trans ha
      cases ha
      cases hmid
      cases hb
      simpa [circleTraceCast, circleTraceWinding] using
        (ScopedRwEq.trans (ScopedRwEq.trans_congr (ihp rfl rfl) (ihq rfl rfl))
          (ScopedRwEq.generator
            (P := circleLoopPresentation)
            (circleLoopRule_add (circleTraceWinding p)
              (circleTraceWinding q))))
  | symm p ih =>
      cases ha
      cases hb
      simpa [circleTraceCast, circleTraceWinding] using
        (ScopedRwEq.trans (ScopedRwEq.symm_congr (ih rfl rfl))
          (ScopedRwEq.generator
            (P := circleLoopPresentation)
            (circleLoopRule_neg (circleTraceWinding p))))

theorem circleTrace_normalizes (p : CircleTrace) :
    ScopedRwEq circleLoopPresentation p
      (GeometricTrace.single (circleTraceWinding p) : CircleTrace) :=
  circleTrace_normalizes_aux p rfl rfl

abbrev CircleOpenLoop :=
  OpenGeometricCompPath
    circleLoopStepSystem.toGeometricStepSystem
    (0 : TopologicalCircle) (0 : TopologicalCircle)

noncomputable def circleStandardOpenLoop (n : ℤ) : CircleOpenLoop :=
  { trace := GeometricTrace.single n
    geometric := standardLoop n
    coherent := _root_.Path.Homotopic.refl _ }

noncomputable def circleRawLoop (p : CircleOpenLoop) :
    ScopedRawPath (S := circleLoopStepSystem) :=
  ⟨0, 0, p⟩

def circleLoopEquivalent (p q : CircleOpenLoop) : Prop :=
  _root_.Path.Homotopic p.geometric q.geometric

/-! ## An effective based normal-form certificate -/

noncomputable def circleBasedNormalForm (p : CircleOpenLoop) : CircleOpenLoop :=
  circleStandardOpenLoop (circleTraceWinding p.trace)

def circleBasedNormalCode (p : CircleOpenLoop) : ℤ :=
  circleTraceWinding p.trace

noncomputable def circleBasedNormalRepresentative (n : ℤ) : CircleOpenLoop :=
  circleStandardOpenLoop n

theorem circleBasedNormalForm_scoped (p : CircleOpenLoop) :
    scopedEquivalent circleLoopPresentation
      (circleRawLoop p)
      (circleRawLoop (circleBasedNormalForm p)) := by
  refine ⟨rfl, rfl, ?_⟩
  change ScopedRwEq circleLoopPresentation p.trace
    (GeometricTrace.single (circleTraceWinding p.trace))
  exact circleTrace_normalizes p.trace

theorem circleBasedNormalCode_scoped (p : CircleOpenLoop) :
    scopedEquivalent circleLoopPresentation
      (circleRawLoop p)
      (circleRawLoop
        (circleBasedNormalRepresentative (circleBasedNormalCode p))) := by
  simpa [circleBasedNormalCode, circleBasedNormalRepresentative,
    circleBasedNormalForm] using circleBasedNormalForm_scoped p

theorem circleBasedNormalCode_eq_of_homotopic
    {p q : CircleOpenLoop}
    (h : circleLoopEquivalent p q) :
    circleBasedNormalCode p = circleBasedNormalCode q := by
  have hp : windingPath p.geometric = circleTraceWinding p.trace :=
    (windingPath_eq_of_homotopic p.coherent).trans
      (circleTraceWinding_realize p.trace)
  have hq : windingPath q.geometric = circleTraceWinding q.trace :=
    (windingPath_eq_of_homotopic q.coherent).trans
      (circleTraceWinding_realize q.trace)
  exact hp.symm.trans ((windingPath_eq_of_homotopic h).trans hq)

theorem circleBasedNormalForm_eq_of_homotopic
    {p q : CircleOpenLoop}
    (h : circleLoopEquivalent p q) :
    circleBasedNormalForm p = circleBasedNormalForm q := by
  simpa [circleBasedNormalForm, circleBasedNormalCode] using
    (_root_.congrArg circleStandardOpenLoop
      (circleBasedNormalCode_eq_of_homotopic h))

structure CircleBasedNormalFormCertificate where
  normalCode : CircleOpenLoop → ℤ
  representative : ℤ → CircleOpenLoop
  normal_scoped : ∀ p,
    scopedEquivalent circleLoopPresentation
      (circleRawLoop p)
      (circleRawLoop (representative (normalCode p)))
  semantic_separation : ∀ {p q},
    circleLoopEquivalent p q → normalCode p = normalCode q

noncomputable def circleBasedNormalFormCertificate :
    CircleBasedNormalFormCertificate where
  normalCode := circleBasedNormalCode
  representative := circleBasedNormalRepresentative
  normal_scoped := circleBasedNormalCode_scoped
  semantic_separation := circleBasedNormalCode_eq_of_homotopic

/-! ## The loop quotient seen by the scoped carrier -/

noncomputable def circleLoopSetoid : Setoid CircleOpenLoop where
  r := circleLoopEquivalent
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact _root_.Path.Homotopic.refl p.geometric
    · intro p q h
      exact _root_.Path.Homotopic.symm h
    · intro p q r hpq hqr
      exact _root_.Path.Homotopic.trans hpq hqr

abbrev CircleLoopClass := Quotient (circleLoopSetoid)

noncomputable def circleLoopClassMk (p : CircleOpenLoop) : CircleLoopClass :=
  Quotient.mk (circleLoopSetoid) p

noncomputable instance circleLoopClassTopologicalSpace :
    TopologicalSpace CircleLoopClass :=
  TopologicalSpace.coinduced circleLoopClassMk inferInstance

theorem circleLoopClassMk_surjective :
    Function.Surjective (circleLoopClassMk : CircleOpenLoop → CircleLoopClass) := by
  intro x
  refine Quot.inductionOn x ?_
  intro p
  exact ⟨p, rfl⟩

theorem circleLoopClassMk_isQuotient :
    Topology.IsQuotientMap (circleLoopClassMk : CircleOpenLoop → CircleLoopClass) :=
  ⟨⟨rfl⟩, circleLoopClassMk_surjective⟩

theorem continuous_circleRawLoop :
    Continuous (circleRawLoop : CircleOpenLoop →
      ScopedRawPath (S := circleLoopStepSystem)) := by
  change Continuous (fun p : CircleOpenLoop =>
    TotalOpenGeometricCompPath.ofFiber circleLoopStepSystem p)
  exact TotalOpenGeometricCompPath.continuous_fiberInclusion
    (S := circleLoopStepSystem) (a := (0 : TopologicalCircle))
    (b := (0 : TopologicalCircle))

theorem circleLoopToScoped_respects
    {p q : CircleOpenLoop} (h : circleLoopEquivalent p q) :
    scopedEquivalent circleLoopPresentation
      (circleRawLoop p) (circleRawLoop q) := by
  refine ⟨rfl, rfl, ?_⟩
  have hp : windingPath p.geometric = circleTraceWinding p.trace := by
    exact (windingPath_eq_of_homotopic p.coherent).trans
      (circleTraceWinding_realize p.trace)
  have hq : windingPath q.geometric = circleTraceWinding q.trace := by
    exact (windingPath_eq_of_homotopic q.coherent).trans
      (circleTraceWinding_realize q.trace)
  have hwind : circleTraceWinding p.trace = circleTraceWinding q.trace := by
    exact hp.symm.trans ((windingPath_eq_of_homotopic h).trans hq)
  have hsingle :
      (GeometricTrace.single (circleTraceWinding p.trace) : CircleTrace) =
        GeometricTrace.single (circleTraceWinding q.trace) := by
    exact _root_.congrArg circleSingle hwind
  have hmiddle :
      ScopedRwEq circleLoopPresentation
        (GeometricTrace.single (circleTraceWinding p.trace) : CircleTrace)
        (GeometricTrace.single (circleTraceWinding q.trace) : CircleTrace) := by
    rw [hsingle]
    exact ScopedRwEq.refl _
  change ScopedRwEq circleLoopPresentation p.trace q.trace
  exact (circleTrace_normalizes p.trace).trans
    (hmiddle.trans (circleTrace_normalizes q.trace).symm)

noncomputable def circleLoopToScoped :
    CircleLoopClass → ScopedClass circleLoopPresentation :=
  Quotient.lift
    (fun p => scopedQuotientMk circleLoopPresentation (circleRawLoop p))
    (by
      intro p q h
      apply Quotient.sound
      exact circleLoopToScoped_respects h)

@[simp] theorem circleLoopToScoped_mk (p : CircleOpenLoop) :
    circleLoopToScoped (circleLoopClassMk p) =
      scopedQuotientMk circleLoopPresentation (circleRawLoop p) :=
  rfl

theorem continuous_circleLoopToScoped :
    Continuous (circleLoopToScoped : CircleLoopClass →
      ScopedClass circleLoopPresentation) := by
  apply circleLoopClassMk_isQuotient.continuous_iff.2
  exact continuous_scopedQuotientMk circleLoopPresentation |>.comp
    continuous_circleRawLoop

theorem circleLoopToScoped_injective :
    Function.Injective circleLoopToScoped := by
  intro x y hxy
  revert y
  refine Quotient.inductionOn x ?_
  intro p y hxy
  revert hxy
  refine Quotient.inductionOn y ?_
  intro q hxy
  apply Quotient.sound
  have hxy' : scopedQuotientMk circleLoopPresentation (circleRawLoop p) =
      scopedQuotientMk circleLoopPresentation (circleRawLoop q) := by
    exact hxy
  have hscoped : scopedEquivalent circleLoopPresentation
      (circleRawLoop p) (circleRawLoop q) := Quotient.exact hxy'
  rcases hscoped with ⟨hs, ht, hrewrite⟩
  cases hs
  cases ht
  rcases p.coherent with ⟨hp⟩
  rcases q.coherent with ⟨hq⟩
  rcases ScopedRwEq.sound circleLoopPresentation hrewrite with ⟨hrealize⟩
  exact ⟨hp.trans (hrealize.trans hq.symm)⟩

theorem circleLoopToScoped_range_iff (x : ScopedClass circleLoopPresentation) :
    x ∈ Set.range circleLoopToScoped ↔
      scopedSrc circleLoopPresentation x = 0 ∧
        scopedTgt circleLoopPresentation x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨?_, ?_⟩
    · refine Quotient.inductionOn y ?_
      intro p
      rfl
    · refine Quotient.inductionOn y ?_
      intro p
      rfl
  · intro hx
    revert hx
    refine Quotient.inductionOn x ?_
    intro p hx
    rcases p with ⟨p_src, p_tgt, p_path⟩
    rcases hx with ⟨hs, ht⟩
    cases hs
    cases ht
    exact ⟨circleLoopClassMk p_path, rfl⟩

/-! ## Winding normal form -/

noncomputable def circleLoopEncode : CircleLoopClass → ℤ :=
  Quotient.lift
    (fun p => topologicalWinding (Quotient.mk' p.geometric))
    (by
      intro p q h
      exact _root_.congrArg topologicalWinding (Quotient.sound h))

noncomputable def circleLoopDecode (n : ℤ) : CircleLoopClass :=
  circleLoopClassMk (circleStandardOpenLoop n)

@[simp] theorem circleLoopEncode_decode (n : ℤ) :
    circleLoopEncode (circleLoopDecode n) = n := by
  change topologicalWinding (decodeTopologicalWinding n) = n
  exact topologicalWinding_decode n

theorem circleLoopDecode_encode (x : CircleLoopClass) :
    circleLoopDecode (circleLoopEncode x) = x := by
  refine Quotient.inductionOn x ?_
  intro p
  apply Quotient.sound
  exact standardLoop_homotopic p.geometric

noncomputable def circleLoopEquivInt : CircleLoopClass ≃ Int where
  toFun := circleLoopEncode
  invFun := circleLoopDecode
  left_inv := circleLoopDecode_encode
  right_inv := circleLoopEncode_decode

theorem continuous_circleLoopEncode :
    Continuous (circleLoopEncode : CircleLoopClass → ℤ) := by
  apply circleLoopClassMk_isQuotient.continuous_iff.2
  change Continuous (fun p : CircleOpenLoop =>
    topologicalWinding (Quotient.mk' p.geometric))
  exact continuous_topologicalWinding.comp
    ((continuous_quotient_mk').comp
      (continuous_open_geometric circleLoopStepSystem.toGeometricStepSystem))

noncomputable def circleLoopHomeomorphInt : CircleLoopClass ≃ₜ ℤ where
  toEquiv := circleLoopEquivInt
  continuous_toFun := continuous_circleLoopEncode
  continuous_invFun := continuous_of_discreteTopology

theorem circleScoped_nontrivial :
    circleLoopToScoped (circleLoopDecode 0) ≠
      circleLoopToScoped (circleLoopDecode 1) := by
  intro h
  have hdecode : circleLoopDecode 0 = circleLoopDecode 1 :=
    circleLoopToScoped_injective h
  have hencode := _root_.congrArg circleLoopEncode hdecode
  simp at hencode

structure CircleScopedNondegeneracyCertificate where
  distinct_zero_one :
    circleLoopToScoped (circleLoopDecode 0) ≠
      circleLoopToScoped (circleLoopDecode 1)
  loop_carrier_equiv_int : CircleLoopClass ≃ Int

noncomputable def circleScopedNondegeneracyCertificate :
    CircleScopedNondegeneracyCertificate where
  distinct_zero_one := circleScoped_nontrivial
  loop_carrier_equiv_int := circleLoopEquivInt

/-! ## Explicit nontrivial path certificates -/

noncomputable def circleStandardTraceLengthPath (n : ℤ) :
    ComputationalPaths.Path
      (GeometricTrace.traceLength (circleStandardOpenLoop n).trace) 1 := by
  change ComputationalPaths.Path 1 1
  exact ComputationalPaths.Path.refl 1

noncomputable def circleUnitTraceRewrite :
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl (0 : ℕ))
        (ComputationalPaths.Path.refl 0))
      (ComputationalPaths.Path.refl 0) :=
  ComputationalPaths.Path.RwEq.step
    (ComputationalPaths.Path.Step.trans_refl_right
      (ComputationalPaths.Path.refl 0))

end ScopedGeometricRewrite
end GeometricTopology
end Path
end ComputationalPaths
