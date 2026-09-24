import ComputationalPaths.Path.Topology.ScopedGeometricRewrite

/-!
# The group of based scoped traces

Structural scoped rewrites make based traces into a group after quotienting.
This algebraic carrier is useful for proving finite-generator normal forms
without adding normalization as a named rewrite rule.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped Topology

namespace BasedScopedTraceGroup

variable {A : Type*} [TopologicalSpace A]
  {Step : Type*} [TopologicalSpace Step]
  {S : ContinuousGeometricStepSystem A Step}

noncomputable def traceSetoid
    (P : ScopedGeometricRewritePresentation S) (x : A) :
    Setoid (GeometricTrace S.toGeometricStepSystem x x) where
  r := ScopedRwEq P
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact ScopedRwEq.refl p
    · intro p q h
      exact ScopedRwEq.symm h
    · intro p q r hpq hqr
      exact ScopedRwEq.trans hpq hqr

abbrev Carrier (P : ScopedGeometricRewritePresentation S) (x : A) :=
  Quotient (traceSetoid P x)

noncomputable def mk (P : ScopedGeometricRewritePresentation S) (x : A)
    (p : GeometricTrace S.toGeometricStepSystem x x) : Carrier P x :=
  Quotient.mk (traceSetoid P x) p

noncomputable instance instGroup (P : ScopedGeometricRewritePresentation S) (x : A) :
    Group (Carrier P x) where
  one := mk P x (.refl x)
  mul := Quotient.map₂ GeometricTrace.trans
    (fun _ _ hp _ _ hq => ScopedRwEq.trans_congr hp hq)
  inv := Quotient.map GeometricTrace.symm
    (fun _ _ h => ScopedRwEq.symm_congr h)
  mul_assoc := by
    intro p q r
    refine Quotient.inductionOn₃ p q r ?_
    intro p q r
    exact Quotient.sound (ScopedRwEq.trans_assoc p q r)
  one_mul := by
    intro p
    refine Quotient.inductionOn p ?_
    intro p
    exact Quotient.sound (ScopedRwEq.refl_trans p)
  mul_one := by
    intro p
    refine Quotient.inductionOn p ?_
    intro p
    exact Quotient.sound (ScopedRwEq.trans_refl p)
  inv_mul_cancel := by
    intro p
    refine Quotient.inductionOn p ?_
    intro p
    exact Quotient.sound (ScopedRwEq.symm_trans p)

@[simp] theorem mk_refl (P : ScopedGeometricRewritePresentation S) (x : A) :
    mk P x (.refl x) = 1 := rfl

@[simp] theorem mk_trans (P : ScopedGeometricRewritePresentation S) (x : A)
    (p q : GeometricTrace S.toGeometricStepSystem x x) :
    mk P x (.trans p q) = mk P x p * mk P x q := rfl

@[simp] theorem mk_symm (P : ScopedGeometricRewritePresentation S) (x : A)
    (p : GeometricTrace S.toGeometricStepSystem x x) :
    mk P x (.symm p) = (mk P x p)⁻¹ := rfl

theorem eq_iff (P : ScopedGeometricRewritePresentation S) (x : A)
    (p q : GeometricTrace S.toGeometricStepSystem x x) :
    mk P x p = mk P x q ↔ ScopedRwEq P p q := by
  exact Quotient.eq

end BasedScopedTraceGroup
end GeometricTopology
end Path
end ComputationalPaths
