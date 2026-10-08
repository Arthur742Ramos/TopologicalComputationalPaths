import ComputationalPaths.Path.Topology.FlatObservableTopology
import ComputationalPaths.Path.Topology.ScopedWordInterpretation

/-!
# A conservative abbreviation can erase an observable separation

The old based presentation has generators `e,f`, realizing `α,α.trans α`,
and no named rules. Length parity is a continuous scoped invariant for its
equal-slot observable quotient. The expanded presentation adds `a` with the
same geometric realization as `f` and only the defining rule `a ≃ e;e`.
Inclusion and elimination of the abbreviation are inverse up to scoped
rewriting. Nevertheless `a` and `f` have identical observable codes and
distinct scoped classes. The algebraic equivalence therefore has no
continuous inverse for these fixed-endpoint observable topologies.

No geometric completeness of either presentation is claimed. This example
does not assume nontriviality of the geometric loop or any geometric fact
about a circle: its separation is between primitive computational labels.
-/

namespace ComputationalPaths.Path.GeometricTopology.RedundantGeneratorObservable

open scoped Topology

inductive OldLabel | e | f deriving DecidableEq
inductive NewLabel | e | f | a deriving DecidableEq
instance : TopologicalSpace OldLabel := ⊥
instance : DiscreteTopology OldLabel := discreteTopology_bot _
instance : TopologicalSpace NewLabel := ⊥
instance : DiscreteTopology NewLabel := discreteTopology_bot _

variable {X : Type*} [TopologicalSpace X] {x : X}

noncomputable def oldSystem (α : _root_.Path x x) :
    ContinuousGeometricStepSystem X OldLabel where
  src := fun _ => x
  tgt := fun _ => x
  realize | .e => α | .f => α.trans α
  continuous_src := continuous_const
  continuous_tgt := continuous_const
  continuous_realize := continuous_of_discreteTopology

noncomputable def newSystem (α : _root_.Path x x) :
    ContinuousGeometricStepSystem X NewLabel where
  src := fun _ => x
  tgt := fun _ => x
  realize | .e => α | .f => α.trans α | .a => α.trans α
  continuous_src := continuous_const
  continuous_tgt := continuous_const
  continuous_realize := continuous_of_discreteTopology

noncomputable def oldPresentation (α : _root_.Path x x) :
    ScopedGeometricRewritePresentation (oldSystem α) where
  rule := fun {_ _} _ _ => False
  sound_rule := by intro _ _ _ _ h; exact False.elim h

inductive Abbreviation (α : _root_.Path x x) : {a b : X} →
    GeometricTrace (newSystem α).toGeometricStepSystem a b →
    GeometricTrace (newSystem α).toGeometricStepSystem a b → Prop
  | define : Abbreviation α (.single .a) (.trans (.single .e) (.single .e))

noncomputable def newPresentation (α : _root_.Path x x) :
    ScopedGeometricRewritePresentation (newSystem α) where
  rule := Abbreviation α
  sound_rule := by
    intro _ _ _ _ h
    cases h
    exact _root_.Path.Homotopic.refl _

noncomputable def includeOld (α : _root_.Path x x) :
    ScopedWordInterpretation (oldPresentation α) (newPresentation α) where
  substitution.step | .e => .single .e | .f => .single .f
  named_rule := by intro _ _ _ _ h; exact False.elim h

noncomputable def eliminateNew (α : _root_.Path x x) :
    ScopedWordInterpretation (newPresentation α) (oldPresentation α) where
  substitution.step
    | .e => .single .e
    | .f => .single .f
    | .a => .trans (.single .e) (.single .e)
  named_rule := by intro _ _ _ _ h; cases h; exact ScopedRwEq.refl _

/-- The conservative presentation change is proved from its actual substitutions. -/
noncomputable def quotientEquiv (α : _root_.Path x x) (a b : X) :=
  ScopedWordInterpretation.quotientEquiv (includeOld α) (eliminateNew α)
    (by intro s; cases s <;> exact ScopedRwEq.refl _)
    (by
      intro s
      cases s
      · exact ScopedRwEq.refl _
      · exact ScopedRwEq.refl _
      · exact (ScopedRwEq.generator (Abbreviation.define (α := α))).symm)
    a b

/-- Structural rewrites preserve old length parity, despite removing letters. -/
theorem old_parity_invariant (α : _root_.Path x x) {a b : X}
    {p q : GeometricTrace (oldSystem α).toGeometricStepSystem a b}
    (h : ScopedRwEq (oldPresentation α) p q) : p.traceLength % 2 = q.traceLength % 2 := by
  induction h with
  | refl p => rfl
  | generator h => exact False.elim h
  | symm h ih => exact ih.symm
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2
  | trans_congr h1 h2 ih1 ih2 => simp [GeometricTrace.traceLength, Nat.add_mod, ih1, ih2]
  | symm_congr h ih => simpa [GeometricTrace.traceLength] using ih
  | refl_trans p => simp [GeometricTrace.traceLength]
  | trans_refl p => simp [GeometricTrace.traceLength]
  | trans_assoc p q r => simp [GeometricTrace.traceLength, Nat.add_assoc]
  | symm_trans p => simp only [GeometricTrace.traceLength]; omega
  | trans_symm p => simp only [GeometricTrace.traceLength]; omega
  | symm_symm p => rfl
  | symm_refl a => rfl
  | symm_comp p q => simp [GeometricTrace.traceLength, Nat.add_comm]

noncomputable def oldParity (α : _root_.Path x x) (a b : X) :
    Quotient (CoherentRepresentativeElimination.traceSetoid (oldPresentation α) a b) → ℕ :=
  Quotient.lift (fun p => p.traceLength % 2) (fun _ _ h => old_parity_invariant α h)

@[reducible] noncomputable def oldQuotientTopology (α : _root_.Path x x) (a b : X) :
    TopologicalSpace (Quotient
      (CoherentRepresentativeElimination.traceSetoid (oldPresentation α) a b)) :=
  @TopologicalSpace.coinduced _ _
    (Quotient.mk (CoherentRepresentativeElimination.traceSetoid (oldPresentation α) a b))
    (EqualSlotTopology.traceObservableTopology a b)

theorem continuous_oldParity (α : _root_.Path x x) (a b : X) :
    @Continuous _ _ (oldQuotientTopology α a b) inferInstance (oldParity α a b) := by
  letI := EqualSlotTopology.traceObservableTopology (S := (oldSystem α).toGeometricStepSystem) a b
  letI := oldQuotientTopology α a b
  apply (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientMk_isQuotient
    (CoherentRepresentativeElimination.traceSetoid (oldPresentation α) a b)
    inferInstance).continuous_iff.2
  exact (continuous_of_discreteTopology (f := fun n : ℕ => n % 2)).comp
    (continuous_fst.comp (EqualSlotTopology.continuous_traceCoordinates a b))

/-- The old classes of `f` and `e;e` have different values of a continuous invariant. -/
theorem old_parity_values (α : _root_.Path x x) :
    oldParity α x x (Quotient.mk _ (.single .f)) = 1 ∧
    oldParity α x x (Quotient.mk _ (.trans (.single .e) (.single .e))) = 0 := by
  constructor <;> norm_num [oldParity, GeometricTrace.traceLength]

def countF (α : _root_.Path x x) : {a b : X} →
    GeometricTrace (newSystem α).toGeometricStepSystem a b → ℤ
  | _, _, .refl _ => 0
  | _, _, .single .e => 0
  | _, _, .single .f => 1
  | _, _, .single .a => 0
  | _, _, .trans p q => countF α p + countF α q
  | _, _, .symm p => -countF α p

theorem countF_invariant (α : _root_.Path x x) {a b : X}
    {p q : GeometricTrace (newSystem α).toGeometricStepSystem a b}
    (h : ScopedRwEq (newPresentation α) p q) : countF α p = countF α q := by
  induction h with
  | refl p => rfl
  | generator h => cases h; rfl
  | symm h ih => exact ih.symm
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2
  | trans_congr h1 h2 ih1 ih2 => simp [countF, ih1, ih2]
  | symm_congr h ih => simp [countF, ih]
  | refl_trans p => simp [countF]
  | trans_refl p => simp [countF]
  | trans_assoc p q r => simp [countF, add_assoc]
  | symm_trans p => simp [countF]
  | trans_symm p => simp [countF]
  | symm_symm p => simp [countF]
  | symm_refl a => simp [countF]
  | symm_comp p q => simp [countF]

@[reducible] noncomputable def newQuotientTopology (α : _root_.Path x x) (a b : X) :
    TopologicalSpace (Quotient
      (CoherentRepresentativeElimination.traceSetoid (newPresentation α) a b)) :=
  @TopologicalSpace.coinduced _ _
    (Quotient.mk (CoherentRepresentativeElimination.traceSetoid (newPresentation α) a b))
    (EqualSlotTopology.traceObservableTopology a b)

theorem new_classes_ne (α : _root_.Path x x) :
    Quotient.mk (CoherentRepresentativeElimination.traceSetoid (newPresentation α) x x)
      (.single .a) ≠ Quotient.mk _ (.single .f) := by
  intro h
  have hc := countF_invariant α (Quotient.exact h)
  change (0 : ℤ) = 1 at hc
  norm_num at hc

theorem new_inseparable (α : _root_.Path x x) :
    @Inseparable _ (newQuotientTopology α x x)
      (Quotient.mk _ (.single .a)) (Quotient.mk _ (.single .f)) := by
  letI := EqualSlotTopology.traceObservableTopology (S := (newSystem α).toGeometricStepSystem) x x
  letI := newQuotientTopology α x x
  have hcode : Topology.IsInducing
      (EqualSlotTopology.traceCoordinates :
        GeometricTrace (newSystem α).toGeometricStepSystem x x → ℕ × _root_.Path x x) := ⟨rfl⟩
  have ht : @Inseparable (GeometricTrace (newSystem α).toGeometricStepSystem x x)
      (EqualSlotTopology.traceObservableTopology x x)
      (.single .a : GeometricTrace (newSystem α).toGeometricStepSystem x x) (.single .f) :=
    hcode.inseparable_iff.mp (Inseparable.of_eq
      (show EqualSlotTopology.traceCoordinates
          (.single .a : GeometricTrace (newSystem α).toGeometricStepSystem x x) =
        EqualSlotTopology.traceCoordinates
          (.single .f : GeometricTrace (newSystem α).toGeometricStepSystem x x) from rfl))
  have hq : Continuous
      (Quotient.mk (CoherentRepresentativeElimination.traceSetoid (newPresentation α) x x)) :=
    continuous_coinduced_rng
  apply inseparable_iff_forall_isOpen.mpr
  intro U hU
  exact (inseparable_iff_forall_isOpen.mp ht) _ (hU.preimage hq)

/-- The algebraic conservative equivalence cannot have a continuous inverse:
the old parity distinction is erased by the expanded observable topology. -/
theorem not_continuous_inverse (α : _root_.Path x x) :
    ¬ @Continuous _ _ (newQuotientTopology α x x) (oldQuotientTopology α x x)
      (quotientEquiv α x x).symm := by
  letI := newQuotientTopology α x x
  letI := oldQuotientTopology α x x
  intro hc
  have hp := (continuous_oldParity α x x).comp hc
  have hi := new_inseparable α
  have heq := (hi.map hp).eq
  change (2 : ℕ) % 2 = 1 at heq
  norm_num at heq

end ComputationalPaths.Path.GeometricTopology.RedundantGeneratorObservable
