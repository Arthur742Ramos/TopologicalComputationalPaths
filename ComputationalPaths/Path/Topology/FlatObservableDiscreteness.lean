import ComputationalPaths.Path.Topology.LiteralWordQuotient
import ComputationalPaths.Path.Topology.BinaryTimingCollision
import ComputationalPaths.Path.Topology.ConcreteCircleWinding
import Mathlib.Topology.Separation.Basic
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sum

/-!
# Discreteness recovered from exact equal-slot observations

For a finite primitive alphabet whose oriented primitive paths are distinct,
the exact equal-slot path and length recover the whole literal word. Each
length fiber is finite. In a T1 geometric space it is a finite open
neighborhood in the observable word topology, so every word is isolated.
This concerns the observable topology, not merely its full-word refinement.
-/

namespace ComputationalPaths.Path.GeometricTopology.FlatObservableDiscreteness

open scoped Topology
open unitInterval LiteralWord
universe u v

variable {A : Type u} [TopologicalSpace A] {Step : Type v}
  {S : GeometricStepSystem A Step}

/-- The actual oriented primitive functions on the unit interval. -/
noncomputable def signedPrimitive (S : GeometricStepSystem A Step)
    (s : SignedStep Step) (t : I) : A := GeometricTrace.signedRealization (S := S) s t

private theorem tuple_eq {n m : Nat} {f : Fin n → SignedStep Step}
    {g : Fin m → SignedStep Step} (h : n = m)
    (hf : ∀ i, f i = g (Fin.cast h i)) :
    (⟨n, f⟩ : FlatWord Step) = ⟨m, g⟩ := by
  subst m
  congr
  funext i
  exact hf i

/-- Restriction to each exact slot recovers its signed primitive letter. -/
theorem flatWord_eq_of_observation
    (hsign : Function.Injective (signedPrimitive S)) {a b : A}
    (p q : GeometricTrace S a b)
    (hlen : GeometricTrace.traceLength p = GeometricTrace.traceLength q)
    (hpath : GeometricTrace.flatRealize p = GeometricTrace.flatRealize q) :
    GeometricTrace.flatWord p = GeometricTrace.flatWord q := by
  rw [GeometricTrace.flatWord_eq_letters, GeometricTrace.flatWord_eq_letters]
  apply tuple_eq hlen
  intro i
  apply hsign
  funext t
  have he := _root_.congrArg (fun path : _root_.Path a b => path.extend
    (((i.val : ℝ) + (t : ℝ)) / (GeometricTrace.traceLength p : ℝ))) hpath
  rw [GeometricTrace.flatRealize_slot p i t] at he
  have hq := GeometricTrace.flatRealize_slot q (Fin.cast hlen i) t
  have hq' : (GeometricTrace.flatRealize q).extend
      (((i.val : ℝ) + (t : ℝ)) / (GeometricTrace.traceLength p : ℝ)) =
      GeometricTrace.signedRealization (S := S)
        (GeometricTrace.letters q (Fin.cast hlen i)) t := by
    simpa only [Fin.val_cast, ← hlen] using hq
  exact he.trans hq'

theorem coordinates_injective (hsign : Function.Injective (signedPrimitive S))
    (a b : A) : Function.Injective (Word.coordinates : Word S a b → _) := by
  intro p q h
  apply Word.toFlatWord_injective a b
  rw [← Word.flatWord_toTrace p, ← Word.flatWord_toTrace q]
  apply flatWord_eq_of_observation hsign
  · simpa only [Word.toTrace_length, Word.coordinates] using _root_.congrArg Prod.fst h
  · exact _root_.congrArg Prod.snd h

/-- Finiteness is needed only at each fixed length, not for all words. -/
theorem finite_length_fiber [Finite Step] (a b : A) (n : Nat) :
    (setOf (fun w : Word S a b => w.length = n)).Finite := by
  let encode (p : {w : Word S a b // w.length = n}) : Fin n → SignedStep Step :=
    fun i => p.1.letters (Fin.cast p.2.symm i)
  have hi : Function.Injective encode := by
    intro p q h
    apply Subtype.ext
    apply Word.toFlatWord_injective a b
    apply tuple_eq (p.2.trans q.2.symm)
    intro i
    simpa only [encode, Fin.cast_cast, Fin.cast_refl, id_eq] using
      _root_.congrFun h (Fin.cast p.2 i)
  have hf : Finite {w : Word S a b // w.length = n} := Finite.of_injective encode hi
  exact Set.finite_coe_iff.mp hf

/-- Finite distinct oriented primitives make the flat observable word carrier
discrete. A T1 space suffices; no discrete primitive-label topology is needed. -/
theorem discrete_observable_words [Finite Step] [T1Space A]
    (hsign : Function.Injective (signedPrimitive S)) (a b : A) :
    @DiscreteTopology (Word S a b) (Word.observableTopology (S := S) a b) := by
  letI := Word.observableTopology (S := S) a b
  letI : T1Space (_root_.Path a b) := t1Space_of_injective_of_continuous
    (DFunLike.coe_injective : Function.Injective
      (fun p : _root_.Path a b => (p : I → A))) continuous_coeFun
  have hc : Continuous (Word.coordinates : Word S a b → _) := continuous_induced_dom
  letI : T1Space (Word S a b) :=
    t1Space_of_injective_of_continuous (coordinates_injective hsign a b) hc
  have hl : Continuous (Word.length : Word S a b → Nat) := continuous_fst.comp hc
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro w
  exact isOpen_singleton_of_finite_mem_nhds w
    ((isOpen_discrete ({w.length} : Set Nat)).preimage hl |>.mem_nhds rfl)
    (finite_length_fiber a b w.length)

variable [TopologicalSpace Step] [Finite Step] [T1Space A]
  {C : ContinuousGeometricStepSystem A Step}

theorem discrete_observable_wordQuotient (P : ScopedGeometricRewritePresentation C)
    (hsign : Function.Injective (signedPrimitive C.toGeometricStepSystem)) (a b : A) :
    @DiscreteTopology (Quotient (WordRwEq.setoid P a b))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (WordRwEq.setoid P a b) (Word.observableTopology (S := C.toGeometricStepSystem) a b)) := by
  letI := Word.observableTopology (S := C.toGeometricStepSystem) a b
  letI := discrete_observable_words hsign a b
  letI := TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (WordRwEq.setoid P a b) (Word.observableTopology (S := C.toGeometricStepSystem) a b)
  apply discreteTopology_iff_forall_isOpen.mpr
  intro U
  exact isOpen_coinduced.mpr (isOpen_discrete _)

theorem discrete_observable_traceQuotient (P : ScopedGeometricRewritePresentation C)
    (hsign : Function.Injective (signedPrimitive C.toGeometricStepSystem)) (a b : A) :
    @DiscreteTopology (Quotient (CoherentRepresentativeElimination.traceSetoid P a b))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (CoherentRepresentativeElimination.traceSetoid P a b)
        (EqualSlotTopology.traceObservableTopology (S := C.toGeometricStepSystem) a b)) := by
  letI := TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (CoherentRepresentativeElimination.traceSetoid P a b)
    (EqualSlotTopology.traceObservableTopology (S := C.toGeometricStepSystem) a b)
  letI := TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (WordRwEq.setoid P a b) (Word.observableTopology (S := C.toGeometricStepSystem) a b)
  letI := discrete_observable_wordQuotient P hsign a b
  exact DiscreteTopology.of_continuous_injective
    (WordRwEq.observableQuotientHomeomorph P a b).continuous_toFun
    (WordRwEq.observableQuotientHomeomorph P a b).injective

end ComputationalPaths.Path.GeometricTopology.FlatObservableDiscreteness

namespace ComputationalPaths.Path.GeometricTopology.FlatObservableDiscreteness.BinaryCircle

open ConcreteCircleWinding BinaryTimingCollision
open unitInterval

local instance : Fintype Label where
  elems := {.a, .b, .c}
  complete := by intro s; cases s <;> simp

private theorem winding_symm (p : _root_.Path (0 : TopologicalCircle) 0) :
    windingPath p.symm = -windingPath p := by
  have h := windingPath_eq_of_homotopic (_root_.Path.Homotopic.trans_symm p)
  rw [windingPath_trans, windingPath_refl] at h
  omega

noncomputable def signedLoop (s : SignedStep Label) :
    _root_.Path (0 : TopologicalCircle) 0 :=
  Sum.elim (system (standardLoop 1)).realize
    (fun s => ((system (standardLoop 1)).realize s).symm) s

theorem signedPrimitive_eq_signedLoop (s : SignedStep Label) (t : I) :
    signedPrimitive (system (standardLoop 1)).toGeometricStepSystem s t = signedLoop s t := by
  cases s <;> exact _root_.Path.extend_extends' _ _

private def windingCode : SignedStep Label → ℤ
  | .inl .a => 1
  | .inl .b => 2
  | .inl .c => 3
  | .inr .a => -1
  | .inr .b => -2
  | .inr .c => -3

theorem winding_signedLoop (s : SignedStep Label) :
    windingPath (signedLoop s) = windingCode s := by
  rcases s with s | s
  · cases s with
    | a =>
        change windingPath (standardLoop 1) = 1
        exact windingPath_standardLoop 1
    | b =>
        change windingPath ((standardLoop 1).trans (standardLoop 1)) = 2
        rw [windingPath_trans]
        norm_num [windingPath_standardLoop]
    | c =>
        change windingPath ((standardLoop 1).trans ((standardLoop 1).trans (standardLoop 1))) = 3
        rw [windingPath_trans, windingPath_trans]
        norm_num [windingPath_standardLoop]
  · cases s with
    | a =>
        change windingPath (standardLoop 1).symm = -1
        rw [winding_symm]
        norm_num [windingPath_standardLoop]
    | b =>
        change windingPath ((standardLoop 1).trans (standardLoop 1)).symm = -2
        rw [winding_symm, windingPath_trans]
        norm_num [windingPath_standardLoop]
    | c =>
        change windingPath ((standardLoop 1).trans ((standardLoop 1).trans (standardLoop 1))).symm = -3
        rw [winding_symm, windingPath_trans, windingPath_trans]
        norm_num [windingPath_standardLoop]

/-- The six actual oriented primitive paths have distinct windings
1, 2, 3, -1, -2, -3, hence they are distinct parametrized functions. -/
theorem signedPrimitive_injective :
    Function.Injective (signedPrimitive (system (standardLoop 1)).toGeometricStepSystem) := by
  intro s t h
  have hp : signedLoop s = signedLoop t := by
    apply _root_.Path.ext
    funext u
    simpa only [signedPrimitive_eq_signedLoop] using _root_.congrFun h u
  have hw : windingCode s = windingCode t := by
    simpa only [winding_signedLoop] using _root_.congrArg windingPath hp
  rcases s with s | s <;> rcases t with t | t <;> cases s <;> cases t
  all_goals first | rfl | (exfalso; norm_num [windingCode] at hw)

/-- The concrete circle collision presentation has a discrete flat observable
fixed-endpoint quotient. The existing binary quotient is not T0. -/
theorem flat_traceQuotient_discrete :
    @DiscreteTopology (Quotient (CoherentRepresentativeElimination.traceSetoid
      (presentation (standardLoop 1)) (0 : TopologicalCircle) 0))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (CoherentRepresentativeElimination.traceSetoid (presentation (standardLoop 1)) 0 0)
        (EqualSlotTopology.traceObservableTopology
          (S := (system (standardLoop 1)).toGeometricStepSystem) 0 0)) :=
  discrete_observable_traceQuotient (presentation (standardLoop 1)) signedPrimitive_injective 0 0

/-- No homeomorphism, including any alternative bijection, identifies the
binary and equal-slot observable quotient topologies in this presentation. -/
theorem binary_flat_not_homeomorphic :
    ¬ Nonempty (@Homeomorph
      (Quotient (CoherentRepresentativeElimination.traceSetoid
        (presentation (standardLoop 1)) (0 : TopologicalCircle) 0))
      (Quotient (CoherentRepresentativeElimination.traceSetoid
        (presentation (standardLoop 1)) (0 : TopologicalCircle) 0))
      (fixedTraceQuotientTopology (standardLoop 1))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (CoherentRepresentativeElimination.traceSetoid (presentation (standardLoop 1)) 0 0)
        (EqualSlotTopology.traceObservableTopology
          (S := (system (standardLoop 1)).toGeometricStepSystem) 0 0))) := by
  rintro ⟨h⟩
  let τ := TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (CoherentRepresentativeElimination.traceSetoid (presentation (standardLoop 1)) 0 0)
    (EqualSlotTopology.traceObservableTopology
      (S := (system (standardLoop 1)).toGeometricStepSystem) 0 0)
  have ht : @T0Space _ τ := by
    letI := τ
    letI := flat_traceQuotient_discrete
    infer_instance
  have hrev := @Homeomorph.symm _ _
    (fixedTraceQuotientTopology (standardLoop 1)) τ h
  exact fixed_not_t0 (standardLoop 1) (@Homeomorph.t0Space _ _ τ
    (fixedTraceQuotientTopology (standardLoop 1)) ht hrev)

end ComputationalPaths.Path.GeometricTopology.FlatObservableDiscreteness.BinaryCircle
