import ComputationalPaths.Path.Topology.TraceSensitiveTopologicalCompPath
import ComputationalPaths.Path.Topology.ConcreteCircleWinding
import ComputationalPaths.Path.Topology.ScopedGeometricRewrite
import ComputationalPaths.Path.Topology.ScopedGeometricRewriteQuotient

/-!
# A finite trace-sensitive separation certificate

The finite code model isolates the two-label separation mechanism. The module
also proves the corresponding result for a scoped presentation whose two
primitive steps realize the same nonconstant circle loop. Signed count
separates their scoped classes and descends continuously to the trace-sensitive
quotient. The observable codes agree, so the reverse quotient comparison is
not continuous.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology
namespace TraceSensitiveSeparation

open Set
open scoped Topology

inductive Generator
  | e
  | f
  deriving DecidableEq

instance : Fintype Generator where
  elems := {Generator.e, Generator.f}
  complete := by
    intro g
    cases g <;> simp

/-- The one-letter signed word for a generator. -/
def oneLetter (g : Generator) : FlatWord Generator :=
  ⟨1, fun _ => Sum.inl g⟩

theorem oneLetter_e_ne_f : oneLetter Generator.e ≠ oneLetter Generator.f := by
  intro h
  have hfun : (fun _ : Fin 1 =>
      (Sum.inl Generator.e : SignedStep Generator)) =
      (fun _ : Fin 1 => (Sum.inl Generator.f : SignedStep Generator)) := by
    simpa [oneLetter] using h
  have hvalue := congrFun hfun (0 : Fin 1)
  cases hvalue

/-- The observable code keeps only the common one-letter length. -/
abbrev ObservableCode : Type := Nat × PUnit

def observableCode (_ : Generator) : ObservableCode :=
  (1, PUnit.unit)

theorem observableCode_e_eq_f :
    observableCode Generator.e = observableCode Generator.f := by
  rfl

@[reducible] def traceTopology : TopologicalSpace Generator := ⊥

@[reducible] def observableTopology : TopologicalSpace Generator := ⊤

instance : TopologicalSpace Generator := traceTopology

instance : DiscreteTopology Generator := discreteTopology_bot Generator

/-- Both labels execute the same nonconstant circle loop. -/
noncomputable def duplicateCircleSystem :
    ContinuousGeometricStepSystem
      ConcreteCircleWinding.TopologicalCircle Generator where
  src := fun _ => 0
  tgt := fun _ => 0
  realize := fun _ => ConcreteCircleWinding.standardLoop 1
  continuous_src := continuous_const
  continuous_tgt := continuous_const
  continuous_realize := continuous_of_discreteTopology

theorem duplicateCircle_realize_eq :
    GeometricTrace.realize
      (GeometricTrace.single (S := duplicateCircleSystem.toGeometricStepSystem)
        Generator.e) =
    GeometricTrace.realize
      (GeometricTrace.single (S := duplicateCircleSystem.toGeometricStepSystem)
        Generator.f) := rfl

theorem duplicateCircle_realize_nonconstant :
    ConcreteCircleWinding.standardLoop 1 ≠
      _root_.Path.refl (0 : ConcreteCircleWinding.TopologicalCircle) := by
  intro h
  have hw := _root_.congrArg ConcreteCircleWinding.windingPath h
  rw [ConcreteCircleWinding.windingPath_standardLoop,
    ConcreteCircleWinding.windingPath_refl] at hw
  omega

/-- The scoped presentation has two primitive loops and no named rewrites. -/
noncomputable def duplicateCirclePresentation :
    ScopedGeometricRewritePresentation duplicateCircleSystem where
  rule := fun {_ _} _ _ => False
  sound_rule := by
    intro _ _ _ _ h
    exact False.elim h

/-- Signed counts distinguish the two labels even though their realizations
are the same circle loop. -/
def duplicateSignedCount :
    {a b : ConcreteCircleWinding.TopologicalCircle} →
      GeometricTrace duplicateCircleSystem.toGeometricStepSystem a b → ℤ × ℤ
  | _, _, .refl _ => 0
  | _, _, .single Generator.e => (1, 0)
  | _, _, .single Generator.f => (0, 1)
  | _, _, .trans p q => duplicateSignedCount p + duplicateSignedCount q
  | _, _, .symm p => -duplicateSignedCount p

def signedLetterCount : SignedStep Generator → ℤ × ℤ
  | .inl Generator.e => (1, 0)
  | .inl Generator.f => (0, 1)
  | .inr Generator.e => (-1, 0)
  | .inr Generator.f => (0, -1)

def flatSignedCount (w : FlatWord Generator) : ℤ × ℤ :=
  ∑ i : Fin w.1, signedLetterCount (w.2 i)

theorem flatSignedCount_trans (u v : FlatWord Generator) :
    flatSignedCount (flatWordTrans u v) =
      flatSignedCount u + flatSignedCount v := by
  change (∑ i : Fin (u.1 + v.1),
      signedLetterCount (Fin.append u.2 v.2 i)) =
    (∑ i : Fin u.1, signedLetterCount (u.2 i)) +
      (∑ i : Fin v.1, signedLetterCount (v.2 i))
  rw [Fin.sum_univ_add]
  simp

theorem signedLetterCount_symm (s : SignedStep Generator) :
    signedLetterCount (signedStepSymm s) = -signedLetterCount s := by
  cases s with
  | inl g => cases g <;> simp [signedLetterCount, signedStepSymm]
  | inr g => cases g <;> simp [signedLetterCount, signedStepSymm]

theorem flatSignedCount_symm (u : FlatWord Generator) :
    flatSignedCount (flatWordSymm u) = -flatSignedCount u := by
  simp only [flatSignedCount, flatWordSymm, signedLetterCount_symm]
  rw [← Finset.sum_neg_distrib]
  exact (Equiv.sum_comp (Fin.revPerm)
    (fun i => -signedLetterCount (u.2 i)))

theorem duplicateSignedCount_eq_flat
    {a b : ConcreteCircleWinding.TopologicalCircle}
    (p : GeometricTrace duplicateCircleSystem.toGeometricStepSystem a b) :
    duplicateSignedCount p = flatSignedCount (GeometricTrace.flatWord p) := by
  induction p with
  | refl a => simp [duplicateSignedCount, flatSignedCount]
  | single g => cases g <;> simp [duplicateSignedCount, flatSignedCount,
      signedLetterCount]
  | trans p q ihp ihq =>
      simp [duplicateSignedCount, GeometricTrace.flatWord_trans,
        flatSignedCount_trans, ihp, ihq]
  | symm p ih =>
      simp [duplicateSignedCount, GeometricTrace.flatWord_symm,
        flatSignedCount_symm, ih]

theorem continuous_flatSignedCount : Continuous flatSignedCount := by
  exact continuous_of_discreteTopology

theorem continuous_duplicateSignedCount_traceSensitive :
    @Continuous (ScopedRawPath (S := duplicateCircleSystem)) (ℤ × ℤ)
      (TotalOpenGeometricCompPath.traceSensitiveTopologicalSpace
        duplicateCircleSystem) inferInstance
      (fun p => duplicateSignedCount p.trace) := by
  letI : TopologicalSpace (ScopedRawPath (S := duplicateCircleSystem)) :=
    TotalOpenGeometricCompPath.traceSensitiveTopologicalSpace
      duplicateCircleSystem
  have hword : Continuous
      (fun p : ScopedRawPath (S := duplicateCircleSystem) =>
        GeometricTrace.flatWord p.trace) := by
    exact (TotalOpenGeometricCompPath.continuous_traceSensitiveObservation
      duplicateCircleSystem).fst
  have h := continuous_flatSignedCount.comp hword
  simpa only [Function.comp_def, duplicateSignedCount_eq_flat] using h

theorem duplicateSignedCount_invariant
    {a b : ConcreteCircleWinding.TopologicalCircle}
    {p q : GeometricTrace duplicateCircleSystem.toGeometricStepSystem a b}
    (h : ScopedRwEq duplicateCirclePresentation p q) :
    duplicateSignedCount p = duplicateSignedCount q := by
  induction h with
  | refl p => rfl
  | generator h => exact False.elim h
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | trans_congr h₁ h₂ ih₁ ih₂ => simp [duplicateSignedCount, ih₁, ih₂]
  | symm_congr h ih => simp [duplicateSignedCount, ih]
  | refl_trans p => simp [duplicateSignedCount]
  | trans_refl p => simp [duplicateSignedCount]
  | trans_assoc p q r => simp [duplicateSignedCount, add_assoc]
  | symm_trans p => simp [duplicateSignedCount]
  | trans_symm p => simp [duplicateSignedCount]
  | symm_symm p => simp [duplicateSignedCount]
  | symm_refl a => simp [duplicateSignedCount]
  | symm_comp p q => simp [duplicateSignedCount]

theorem duplicateSignedCount_cast
    {a b a' b' : ConcreteCircleWinding.TopologicalCircle}
    (ha : a' = a) (hb : b' = b)
    (p : GeometricTrace duplicateCircleSystem.toGeometricStepSystem a b) :
    duplicateSignedCount
      (ContinuousGeometricStepSystemMap.castTrace
        (S := duplicateCircleSystem) ha hb p) =
      duplicateSignedCount p := by
  cases ha
  cases hb
  rfl

noncomputable def duplicateClassCount :
    ScopedClass duplicateCirclePresentation → ℤ × ℤ :=
  Quotient.lift (fun p => duplicateSignedCount p.trace) (by
    intro p q h
    rcases h with ⟨hs, ht, htrace⟩
    exact (duplicateSignedCount_cast hs ht p.trace).symm.trans
      (duplicateSignedCount_invariant htrace))

theorem duplicateClassCount_mk
    (p : ScopedRawPath (S := duplicateCircleSystem)) :
    duplicateClassCount
      (scopedQuotientMk duplicateCirclePresentation p) =
      duplicateSignedCount p.trace := rfl

theorem continuous_duplicateClassCount_traceSensitive :
    @Continuous (ScopedClass duplicateCirclePresentation) (ℤ × ℤ)
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (scopedSetoid duplicateCirclePresentation)
        (TotalOpenGeometricCompPath.traceSensitiveTopologicalSpace
          duplicateCircleSystem)) inferInstance
      duplicateClassCount := by
  letI : TopologicalSpace (ScopedRawPath (S := duplicateCircleSystem)) :=
    TotalOpenGeometricCompPath.traceSensitiveTopologicalSpace
      duplicateCircleSystem
  letI : TopologicalSpace (ScopedClass duplicateCirclePresentation) :=
    TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
      (scopedSetoid duplicateCirclePresentation) inferInstance
  apply Continuous.quotient_lift
  exact continuous_duplicateSignedCount_traceSensitive

noncomputable def duplicateOpenLoop (g : Generator) :
    OpenGeometricCompPath duplicateCircleSystem.toGeometricStepSystem 0 0 :=
  { trace := .single g
    geometric := ConcreteCircleWinding.standardLoop 1
    coherent := _root_.Path.Homotopic.refl _ }

noncomputable def duplicateRawLoop (g : Generator) :
    ScopedRawPath (S := duplicateCircleSystem) :=
  ⟨0, 0, duplicateOpenLoop g⟩

theorem duplicateRawLoop_not_scopedEquivalent :
    ¬ scopedEquivalent duplicateCirclePresentation
      (duplicateRawLoop Generator.e) (duplicateRawLoop Generator.f) := by
  intro h
  rcases h with ⟨hs, ht, htrace⟩
  cases hs
  cases ht
  have hcode := duplicateSignedCount_invariant htrace
  have hcast : castScopedTrace
      (p := duplicateRawLoop Generator.e)
      (q := duplicateRawLoop Generator.f) rfl rfl =
        (duplicateRawLoop Generator.e).trace := by
    rfl
  rw [hcast] at hcode
  change ((1 : ℤ), 0) = (0, 1) at hcode
  norm_num at hcode

theorem duplicateScopedClasses_ne :
    scopedQuotientMk duplicateCirclePresentation
        (duplicateRawLoop Generator.e) ≠
      scopedQuotientMk duplicateCirclePresentation
        (duplicateRawLoop Generator.f) := by
  intro h
  exact duplicateRawLoop_not_scopedEquivalent (Quotient.exact h)

theorem duplicateObservation_eq :
    TotalOpenGeometricCompPath.observation duplicateCircleSystem
        (duplicateRawLoop Generator.e) =
      TotalOpenGeometricCompPath.observation duplicateCircleSystem
        (duplicateRawLoop Generator.f) := by
  rfl

theorem duplicateObservable_mem_iff
    {s : Set (ScopedRawPath (S := duplicateCircleSystem))}
    (hs : @IsOpen _
      (TotalOpenGeometricCompPath.instTopologicalSpace
        duplicateCircleSystem) s) :
    duplicateRawLoop Generator.e ∈ s ↔
      duplicateRawLoop Generator.f ∈ s := by
  rcases isOpen_induced_iff.mp hs with ⟨U, hU, hpre⟩
  rw [← hpre]
  change TotalOpenGeometricCompPath.observation duplicateCircleSystem
      (duplicateRawLoop Generator.e) ∈ U ↔
    TotalOpenGeometricCompPath.observation duplicateCircleSystem
      (duplicateRawLoop Generator.f) ∈ U
  rw [duplicateObservation_eq]

@[reducible] noncomputable def duplicateTraceQuotientTopology :
    TopologicalSpace (ScopedClass duplicateCirclePresentation) :=
  TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (scopedSetoid duplicateCirclePresentation)
    (TotalOpenGeometricCompPath.traceSensitiveTopologicalSpace
      duplicateCircleSystem)

@[reducible] noncomputable def duplicateObservableQuotientTopology :
    TopologicalSpace (ScopedClass duplicateCirclePresentation) :=
  TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (scopedSetoid duplicateCirclePresentation)
    (TotalOpenGeometricCompPath.instTopologicalSpace
      duplicateCircleSystem)

theorem duplicateQuotientComparison_continuous :
    @Continuous (ScopedClass duplicateCirclePresentation)
      (ScopedClass duplicateCirclePresentation)
      duplicateTraceQuotientTopology duplicateObservableQuotientTopology
      id := by
  exact TotalOpenGeometricCompPath.TraceSensitiveQuotient.continuous_quotientComparison
    (scopedSetoid duplicateCirclePresentation)
    (TotalOpenGeometricCompPath.continuous_traceSensitive_to_observable
      duplicateCircleSystem)

theorem duplicateQuotientComparison_not_continuous :
    ¬ @Continuous (ScopedClass duplicateCirclePresentation)
      (ScopedClass duplicateCirclePresentation)
      duplicateObservableQuotientTopology duplicateTraceQuotientTopology
      id := by
  intro hreverse
  have hcount : @Continuous (ScopedClass duplicateCirclePresentation)
      (ℤ × ℤ) duplicateObservableQuotientTopology inferInstance
      duplicateClassCount := by
    exact @Continuous.comp (ScopedClass duplicateCirclePresentation)
      (ScopedClass duplicateCirclePresentation) (ℤ × ℤ)
      duplicateObservableQuotientTopology duplicateTraceQuotientTopology
      inferInstance id duplicateClassCount
      continuous_duplicateClassCount_traceSensitive hreverse
  have hmk : @Continuous (ScopedRawPath (S := duplicateCircleSystem))
      (ScopedClass duplicateCirclePresentation)
      (TotalOpenGeometricCompPath.instTopologicalSpace
        duplicateCircleSystem) duplicateObservableQuotientTopology
      (scopedQuotientMk duplicateCirclePresentation) := by
    exact continuous_coinduced_rng
  have hraw : @Continuous (ScopedRawPath (S := duplicateCircleSystem))
      (ℤ × ℤ) (TotalOpenGeometricCompPath.instTopologicalSpace
        duplicateCircleSystem) inferInstance
      (fun p => duplicateSignedCount p.trace) := by
    simpa only [Function.comp_def, duplicateClassCount_mk] using
      hcount.comp hmk
  let U : Set (ScopedRawPath (S := duplicateCircleSystem)) :=
    {p | duplicateSignedCount p.trace = ((1 : ℤ), 0)}
  have hU : @IsOpen _
      (TotalOpenGeometricCompPath.instTopologicalSpace
        duplicateCircleSystem) U := by
    exact hraw.isOpen_preimage {((1 : ℤ), 0)} (isOpen_discrete _)
  have he : duplicateRawLoop Generator.e ∈ U := by
    rfl
  have hf := (duplicateObservable_mem_iff hU).mp he
  change ((0 : ℤ), 1) = (1, 0) at hf
  norm_num at hf

theorem continuous_trace_to_observable :
    @Continuous Generator Generator traceTopology observableTopology id := by
  change @Continuous Generator Generator ⊥ ⊤ id
  exact continuous_bot

theorem not_continuous_observable_to_trace :
    ¬ @Continuous Generator Generator observableTopology traceTopology id := by
  intro h
  letI : TopologicalSpace Generator := traceTopology
  letI : DiscreteTopology Generator := ⟨by rfl⟩
  let U : Set Generator := {Generator.e}
  have hopen : IsOpen[traceTopology] U := by
    exact isOpen_discrete U
  have hpre : IsOpen[observableTopology]
      ((id : Generator → Generator) ⁻¹' U) := by
    exact @IsOpen.preimage Generator Generator observableTopology traceTopology
      id h U hopen
  have hcases :
      ((id : Generator → Generator) ⁻¹' U) = ∅ ∨
        ((id : Generator → Generator) ⁻¹' U) = univ := by
    letI : TopologicalSpace Generator := observableTopology
    apply (TopologicalSpace.isOpen_top_iff _).mp
    exact hpre
  rcases hcases with hempty | huniv
  · have : Generator.e ∈ ((id : Generator → Generator) ⁻¹' U) := by
      simp [U]
    rw [hempty] at this
    exact this
  · have hf : Generator.f ∈ U := by
      have : Generator.f ∈ ((id : Generator → Generator) ⁻¹' U) := by
        rw [huniv]
        exact mem_univ _
      simpa using this
    simp [U] at hf

noncomputable def unitRewrite (n : Nat) :
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl n)
        (ComputationalPaths.Path.refl n))
      (ComputationalPaths.Path.refl n) :=
  ComputationalPaths.Path.RwEq.step
    (ComputationalPaths.Path.Step.trans_refl_right
      (ComputationalPaths.Path.refl n))

structure Certificate where
  trace_separates : oneLetter Generator.e ≠ oneLetter Generator.f
  observable_forgets : observableCode Generator.e = observableCode Generator.f
  forward_continuous :
    @Continuous Generator Generator traceTopology observableTopology id
  reverse_not_continuous :
    ¬ @Continuous Generator Generator observableTopology traceTopology id
  unit_coherence : ∀ n : Nat,
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl n)
        (ComputationalPaths.Path.refl n))
      (ComputationalPaths.Path.refl n)

noncomputable def certificate : Certificate where
  trace_separates := oneLetter_e_ne_f
  observable_forgets := observableCode_e_eq_f
  forward_continuous := continuous_trace_to_observable
  reverse_not_continuous := not_continuous_observable_to_trace
  unit_coherence := unitRewrite

end TraceSensitiveSeparation
end GeometricTopology
end Path
end ComputationalPaths
