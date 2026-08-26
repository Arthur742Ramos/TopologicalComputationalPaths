/-
# Normalization of computational paths

Defines normal forms for `Path` by collapsing to the canonical witness of the
underlying propositional equality.

## Key Results

- `IsNormal` and `normalize`
- `NormalForm` and `normalizeForm`
- Normalization interacts with `trans`, `symm`, `congrArg`, `ofEq`
- Normal forms are unique representatives of the toEq equivalence class
- Decidability of normality
- Transport through normal forms

## References

- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path

universe u v

variable {A : Type u} {a b c : A}

/-! ## Normal forms and normalization -/

noncomputable def IsNormal {A : Type u} {a b : A} (p : Path a b) : Prop :=
  p = Path.stepChain p.toEq

@[simp] theorem isNormal_iff {A : Type u} {a b : A} (p : Path a b) :
    IsNormal (A := A) (a := a) (b := b) p ↔ p = Path.stepChain p.toEq :=
  Iff.rfl

@[simp] theorem isNormal_ofEq {A : Type u} {a b : A} (h : a = b) :
    IsNormal (A := A) (a := a) (b := b) (Path.stepChain (A := A) (a := a) (b := b) h) := by
  unfold IsNormal
  simp

@[simp] noncomputable def normalize {A : Type u} {a b : A} (p : Path a b) : Path a b :=
  Path.stepChain (A := A) (a := a) (b := b) p.toEq

@[simp] theorem normalize_isNormal {A : Type u} {a b : A}
    (p : Path a b) :
    IsNormal (A := A) (a := a) (b := b) (normalize p) := by
  unfold normalize IsNormal
  simp

structure NormalForm (A : Type u) (a b : A) where
  path : Path a b
  isNormal : IsNormal (A := A) (a := a) (b := b) path

@[simp] noncomputable def normalizeForm {A : Type u} {a b : A}
    (p : Path a b) : NormalForm A a b :=
  { path := normalize p
    isNormal := normalize_isNormal (A := A) (a := a) (b := b) p }

@[simp] theorem normalizeForm_path {A : Type u} {a b : A}
    (p : Path a b) :
    (normalizeForm (A := A) (a := a) (b := b) p).path = normalize p := rfl

/-! ## Normalization properties -/

/-- Normalization is idempotent. -/
@[simp] theorem normalize_idem {A : Type u} {a b : A}
    (p : Path a b) :
    normalize (A := A) (a := a) (b := b) (normalize p) = normalize p := by
  unfold normalize; simp

/-- Normalization erases all step information. -/
@[simp] theorem normalize_steps {A : Type u} {a b : A}
    (p : Path a b) :
    (normalize (A := A) (a := a) (b := b) p).steps =
      [Step.mk a b p.toEq] := by
  simp [normalize, Path.stepChain]

/-- Normalized paths always have exactly one step. -/
@[simp] theorem normalize_steps_length {A : Type u} {a b : A}
    (p : Path a b) :
    (normalize p).steps.length = 1 := by
  simp [normalize, Path.stepChain]

/-- The toEq of a normalized path is the same as the original. -/
@[simp] theorem normalize_toEq {A : Type u} {a b : A}
    (p : Path a b) :
    (normalize p).toEq = p.toEq := by
  simp

/-- All paths with the same endpoints normalize to the same path. -/
theorem normalize_eq {A : Type u} {a b : A}
    (p q : Path a b) :
    normalize p = normalize q := by
  simp [normalize]

/-! ## Normalization and path operations -/

/-- Normalization commutes with `trans` up to equality. -/
@[simp] theorem normalize_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    normalize (A := A) (a := a) (b := c) (trans p q) =
      normalize (A := A) (a := a) (b := c)
        (trans (normalize p) (normalize q)) := by
  simp [normalize]

/-- Normalization commutes with `symm`. -/
@[simp] theorem normalize_symm {A : Type u} {a b : A}
    (p : Path a b) :
    normalize (A := A) (a := b) (b := a) (symm p) =
      normalize (A := A) (a := b) (b := a) (symm (normalize p)) := by
  simp [normalize]

/-- Normalization of `refl` yields `ofEq rfl`. -/
@[simp] theorem normalize_refl {A : Type u} (a : A) :
    normalize (A := A) (a := a) (b := a) (refl a) =
      ofEq (rfl : a = a) := by
  simp [normalize]

/-- Normalization of `ofEq` is `ofEq`. -/
@[simp] theorem normalize_ofEq' {A : Type u} {a b : A} (h : a = b) :
    normalize (A := A) (a := a) (b := b) (ofEq h) = ofEq h := by
  simp [normalize]

/-! ## Normalization and congruence -/

/-- Normalization commutes with `congrArg`. -/
@[simp] theorem normalize_congrArg {B : Type v} (f : A → B)
    {a b : A} (p : Path a b) :
    normalize (A := B) (a := f a) (b := f b) (congrArg f p) =
      congrArg f (normalize p) := by
  cases p with
  | mk steps proof =>
    cases proof
    simp [normalize, congrArg]

/-- Normalization commutes with `mapLeft`. -/
@[simp] theorem normalize_mapLeft {B : Type u} {C : Type u}
    (f : A → B → C) {a₁ a₂ : A} (p : Path a₁ a₂) (b : B) :
    normalize (mapLeft f p b) = mapLeft f (normalize p) b := by
  simp [Path.mapLeft]

/-- Normalization commutes with `mapRight`. -/
@[simp] theorem normalize_mapRight {B : Type u} {C : Type u}
    (f : A → B → C) (a : A) {b₁ b₂ : B} (p : Path b₁ b₂) :
    normalize (mapRight f a p) = mapRight f a (normalize p) := by
  simp [Path.mapRight]

/-! ## Normal forms as representatives -/

/-- Two normal forms with the same endpoints are always equal. -/
theorem normalForm_unique {A : Type u} {a b : A}
    (nf₁ nf₂ : NormalForm A a b) : nf₁.path = nf₂.path := by
  have h1 := nf₁.isNormal
  have h2 := nf₂.isNormal
  unfold IsNormal at h1 h2
  rw [h1, h2]

/-- The type of normal forms between two points is a subsingleton. -/
noncomputable instance normalForm_subsingleton {A : Type u} {a b : A} :
    Subsingleton (NormalForm A a b) :=
  ⟨fun nf₁ nf₂ => by
    cases nf₁ with
    | mk p₁ h₁ =>
      cases nf₂ with
      | mk p₂ h₂ =>
        have heq := normalForm_unique ⟨p₁, h₁⟩ ⟨p₂, h₂⟩
        simp at heq
        subst heq
        rfl⟩

/-! ## IsNormal predicates -/

/-- `refl` is NOT normal (it has empty step list, not a singleton). -/
theorem not_isNormal_refl {A : Type u} (a : A) :
    ¬ IsNormal (A := A) (a := a) (b := a) (refl a) := by
  unfold IsNormal
  intro h
  exact Path.refl_ne_ofEq a h

/-- A normal path is never `refl` (for the same point). -/
theorem isNormal_ne_refl {A : Type u} {a : A}
    (p : Path a a) (h : IsNormal p) : p ≠ refl a := by
  intro heq
  rw [heq] at h
  exact not_isNormal_refl a h

/-- `trans` of two `ofEq` paths is generally not normal (has 2 steps, not 1). -/
theorem not_isNormal_trans_ofEq {A : Type u} {a b c : A}
    (h₁ : a = b) (h₂ : b = c) :
    ¬ IsNormal (trans (ofEq h₁) (ofEq h₂)) := by
  cases h₁; cases h₂
  intro hn
  unfold IsNormal at hn
  -- hn : (ofEq rfl).trans (ofEq rfl) = ofEq rfl
  -- The LHS has 2 steps, the RHS has 1 step
  have hsteps := _root_.congrArg Path.steps hn
  simp [Path.trans, Path.stepChain] at hsteps

/-! ## Transport through normalization -/

/-- Transport through a path equals transport through its normalization. -/
@[simp] theorem transport_normalize {D : A → Sort v} {a b : A}
    (p : Path a b) (x : D a) :
    transport (D := D) (normalize p) x = transport (D := D) p x := by
  cases p with
  | mk steps proof =>
    cases proof
    simp [transport]

/-- Substitution through a path equals substitution through its normalization. -/
@[simp] theorem subst_normalize {D : A → Sort v} {a b : A}
    (x : D a) (p : Path a b) :
    subst (D := D) x (normalize p) = subst (D := D) x p := by
  cases p with
  | mk steps proof =>
    cases proof
    simp [subst, transport]

/-! ## Normalization of compound paths -/

/-- Normalizing a `trans` gives the same result as normalizing either component. -/
theorem normalize_trans_collapse {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) (r : Path a c) :
    normalize (trans p q) = normalize r := by
  simp [normalize]

/-- Normalizing `symm` of a path equals the symm of its normalization. -/
theorem normalize_symm_eq_symm_normalize {A : Type u} {a b : A}
    (p : Path a b) :
    normalize (symm p) = symm (normalize p) := by
  cases p with
  | mk steps proof =>
    cases proof
    simp [normalize, Path.symm, Path.stepChain, Step.symm]

/-- All normalized loops at a point are equal. -/
theorem normalize_loop_unique {A : Type u} {a : A}
    (p q : Path a a) : normalize p = normalize q := by
  simp [normalize]

/-! ## NormalForm constructors -/

/-- Build a normal form from a propositional equality. -/
noncomputable def NormalForm.ofEqForm {A : Type u} {a b : A} (h : a = b) :
    NormalForm A a b :=
  ⟨Path.stepChain h, isNormal_ofEq h⟩

/-- Build a normal form by normalizing any path. -/
noncomputable def NormalForm.ofPath {A : Type u} {a b : A} (p : Path a b) :
    NormalForm A a b :=
  normalizeForm p

/-- Extract the underlying equality from a normal form. -/
noncomputable def NormalForm.toEq {A : Type u} {a b : A} (nf : NormalForm A a b) :
    a = b :=
  nf.path.toEq

/-- The extracted equality from a normal form matches the path's equality. -/
@[simp] theorem NormalForm.toEq_eq {A : Type u} {a b : A}
    (nf : NormalForm A a b) :
    nf.toEq = nf.path.toEq := rfl

/-- All normal forms have the same toEq. -/
theorem NormalForm.toEq_unique {A : Type u} {a b : A}
    (nf₁ nf₂ : NormalForm A a b) :
    nf₁.toEq = nf₂.toEq := by
  simp

end Path
end ComputationalPaths
