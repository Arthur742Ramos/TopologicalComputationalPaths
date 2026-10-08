import ComputationalPaths.Path.Topology.ScopedGeometricRewriteQuotient
import ComputationalPaths.Path.Topology.CoherentRepresentativeElimination

/-!
# An exact binary-timing collision

Given any based path `α`, three primitive labels realize `α`, `α.trans α`,
and `α.trans (α.trans α)`. Without named rewrites, the traces `(a;b);b`
and `c;(a;a)` have distinct scoped classes but identical observable codes.
This is a result about the implemented binary model. A comparison with the
equal-slot flat model additionally needs a flat realization and separation
of its oriented primitive paths; neither is assumed or asserted here.
-/

namespace ComputationalPaths.Path.GeometricTopology.BinaryTimingCollision

open scoped Topology

inductive Label
  | a | b | c
  deriving DecidableEq

instance : TopologicalSpace Label := ⊥
instance : DiscreteTopology Label := discreteTopology_bot Label

variable {X : Type*} [TopologicalSpace X] {x : X}

noncomputable def system (α : _root_.Path x x) :
    ContinuousGeometricStepSystem X Label where
  src := fun _ => x
  tgt := fun _ => x
  realize
    | .a => α
    | .b => α.trans α
    | .c => α.trans (α.trans α)
  continuous_src := continuous_const
  continuous_tgt := continuous_const
  continuous_realize := continuous_of_discreteTopology

noncomputable def presentation (α : _root_.Path x x) :
    ScopedGeometricRewritePresentation (system α) where
  rule := fun {_ _} _ _ => False
  sound_rule := by
    intro _ _ _ _ h
    exact False.elim h

noncomputable def leftTrace (α : _root_.Path x x) :
    GeometricTrace (system α).toGeometricStepSystem x x :=
  .trans (.trans (.single .a) (.single .b)) (.single .b)

noncomputable def rightTrace (α : _root_.Path x x) :
    GeometricTrace (system α).toGeometricStepSystem x x :=
  .trans (.single .c) (.trans (.single .a) (.single .a))

theorem realize_eq (α : _root_.Path x x) :
    GeometricTrace.realize (leftTrace α) =
      GeometricTrace.realize (rightTrace α) := rfl

/-- Signed occurrence count of the primitive label `c`. -/
def countC (α : _root_.Path x x) : {a b : X} →
    GeometricTrace (system α).toGeometricStepSystem a b → ℤ
  | _, _, .refl _ => 0
  | _, _, .single .a => 0
  | _, _, .single .b => 0
  | _, _, .single .c => 1
  | _, _, .trans p q => countC α p + countC α q
  | _, _, .symm p => -countC α p

theorem countC_invariant (α : _root_.Path x x)
    {a b : X} {p q : GeometricTrace (system α).toGeometricStepSystem a b}
    (h : ScopedRwEq (presentation α) p q) : countC α p = countC α q := by
  induction h with
  | refl p => rfl
  | generator h => exact False.elim h
  | symm h ih => exact ih.symm
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2
  | trans_congr h1 h2 ih1 ih2 => simp [countC, ih1, ih2]
  | symm_congr h ih => simp [countC, ih]
  | refl_trans p => simp [countC]
  | trans_refl p => simp [countC]
  | trans_assoc p q r => simp [countC, add_assoc]
  | symm_trans p => simp [countC]
  | trans_symm p => simp [countC]
  | symm_symm p => simp [countC]
  | symm_refl a => simp [countC]
  | symm_comp p q => simp [countC]

noncomputable def leftRaw (α : _root_.Path x x) : ScopedRawPath (S := system α) :=
  ⟨x, x, ⟨leftTrace α, GeometricTrace.realize (leftTrace α),
    _root_.Path.Homotopic.refl _⟩⟩

noncomputable def rightRaw (α : _root_.Path x x) : ScopedRawPath (S := system α) :=
  ⟨x, x, ⟨rightTrace α, GeometricTrace.realize (leftTrace α),
    by rw [realize_eq]⟩⟩

theorem observation_eq (α : _root_.Path x x) :
    TotalOpenGeometricCompPath.observation (system α) (leftRaw α) =
      TotalOpenGeometricCompPath.observation (system α) (rightRaw α) := rfl

theorem classes_ne (α : _root_.Path x x) :
    scopedQuotientMk (presentation α) (leftRaw α) ≠
      scopedQuotientMk (presentation α) (rightRaw α) := by
  intro h
  rcases Quotient.exact h with ⟨hs, ht, htrace⟩
  have hc := countC_invariant α htrace
  have hcast : castScopedTrace (S := system α) hs ht = (leftRaw α).trace := by
    rfl
  rw [hcast] at hc
  change (0 : ℤ) = 1 at hc
  norm_num at hc

/-- The collision survives quotienting: every open set contains both classes
or neither. This property and `classes_ne` exhibit the failure of T₀. -/
theorem quotient_open_mem_iff (α : _root_.Path x x)
    {U : Set (ScopedClass (presentation α))} (hU : IsOpen U) :
    scopedQuotientMk (presentation α) (leftRaw α) ∈ U ↔
      scopedQuotientMk (presentation α) (rightRaw α) ∈ U := by
  have hpre := hU.preimage (ScopedGeometricRewrite.continuous_scopedQuotientMk
    (presentation α))
  rcases isOpen_induced_iff.mp hpre with ⟨V, hV, heq⟩
  change leftRaw α ∈ scopedQuotientMk (presentation α) ⁻¹' U ↔
    rightRaw α ∈ scopedQuotientMk (presentation α) ⁻¹' U
  rw [← heq]
  change TotalOpenGeometricCompPath.observation (system α) (leftRaw α) ∈ V ↔
    TotalOpenGeometricCompPath.observation (system α) (rightRaw α) ∈ V
  rw [observation_eq]

theorem not_t0 (α : _root_.Path x x) :
    ¬ T0Space (ScopedClass (presentation α)) := by
  intro h
  letI := h
  have hi : Inseparable
      (scopedQuotientMk (presentation α) (leftRaw α))
      (scopedQuotientMk (presentation α) (rightRaw α)) := by
    apply inseparable_iff_forall_isOpen.mpr
    intro U hU
    exact quotient_open_mem_iff α hU
  exact classes_ne α hi.eq

/-- The binary quotient of traces at the fixed basepoint, with its quotient
topology. Coherent enrichment yields a homeomorphic quotient by elimination. -/
@[reducible] noncomputable def fixedTraceQuotientTopology (α : _root_.Path x x) :
    TopologicalSpace (Quotient
      (CoherentRepresentativeElimination.traceSetoid (presentation α) x x)) :=
  TopologicalSpace.coinduced
    (Quotient.mk (CoherentRepresentativeElimination.traceSetoid (presentation α) x x))
    inferInstance

theorem fixed_not_t0 (α : _root_.Path x x) :
    ¬ @T0Space (Quotient
      (CoherentRepresentativeElimination.traceSetoid (presentation α) x x))
      (fixedTraceQuotientTopology α) := by
  letI := fixedTraceQuotientTopology α
  intro h
  letI := h
  let r := CoherentRepresentativeElimination.traceSetoid (presentation α) x x
  have hcode : Topology.IsInducing
      (GeometricTrace.coordinates :
        GeometricTrace (system α).toGeometricStepSystem x x →
          ℕ × _root_.Path x x) := ⟨rfl⟩
  have ht : Inseparable (leftTrace α) (rightTrace α) :=
    hcode.inseparable_iff.mp (Inseparable.of_eq rfl)
  have hq : Continuous (Quotient.mk r) := continuous_coinduced_rng
  have hi : Inseparable (Quotient.mk r (leftTrace α))
      (Quotient.mk r (rightTrace α)) := by
    apply inseparable_iff_forall_isOpen.mpr
    intro U hU
    exact (inseparable_iff_forall_isOpen.mp ht) _ (hU.preimage hq)
  have hc := countC_invariant α (Quotient.exact hi.eq)
  change (0 : ℤ) = 1 at hc
  norm_num at hc

end ComputationalPaths.Path.GeometricTopology.BinaryTimingCollision
