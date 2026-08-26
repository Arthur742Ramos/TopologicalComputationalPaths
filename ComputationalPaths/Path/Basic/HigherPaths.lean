/-
# Higher Paths — paths between paths, 2-groupoid structure, Eckmann–Hilton

We study the space of paths between paths (`p = q` where `p q : Path a b`),
whiskering, vertical and horizontal composition of 2-paths, and derive the
Eckmann–Hilton argument showing that 2-path loops commute.

Because the `proof` field of `Path` lives in `Prop` (and is therefore
proof-irrelevant), 2-paths are determined entirely by their step-list metadata.
This makes many coherence results automatic via `Subsingleton.elim` on the
propositional equalities, while the step-level structure remains
combinatorially rich.

## Main results

- `Path2` type alias for paths between paths
- Vertical and horizontal composition
- Whiskering operations and their laws
- Eckmann–Hilton commutativity
- 2-groupoid laws (associativity, unit, inverse at the 2-level)
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

namespace Path

universe u v

variable {A : Type u} {a b c d : A}

/-! ## 2-paths: paths between paths -/

/-- A 2-path is simply an equality between paths. -/
abbrev Path2 (p q : Path a b) := p = q

/-- Reflexive 2-path. -/
noncomputable def refl2 (p : Path a b) : Path2 p p := rfl

/-- Inverse 2-path. -/
noncomputable def symm2 {p q : Path a b} (α : Path2 p q) : Path2 q p :=
  α.symm

/-- Vertical composition of 2-paths. -/
noncomputable def vcomp {p q r : Path a b} (α : Path2 p q) (β : Path2 q r) :
    Path2 p r :=
  α.trans β

/-- Computation: `vcomp` with `refl2` on the left is identity. -/
@[simp] theorem vcomp_refl_left {p q : Path a b} (α : Path2 p q) :
    vcomp (refl2 p) α = α := rfl

/-- Computation: `vcomp` with `refl2` on the right is identity. -/
@[simp] theorem vcomp_refl_right {p q : Path a b} (α : Path2 p q) :
    vcomp α (refl2 q) = α := by
  cases α; rfl

/-- Vertical composition is associative. -/
theorem vcomp_assoc {p q r s : Path a b}
    (α : Path2 p q) (β : Path2 q r) (γ : Path2 r s) :
    vcomp (vcomp α β) γ = vcomp α (vcomp β γ) := by
  cases α; cases β; rfl

/-- Left inverse law for `symm2`. -/
@[simp] theorem vcomp_symm_left {p q : Path a b} (α : Path2 p q) :
    vcomp (symm2 α) α = refl2 q := by
  cases α; rfl

/-- Right inverse law for `symm2`. -/
@[simp] theorem vcomp_symm_right {p q : Path a b} (α : Path2 p q) :
    vcomp α (symm2 α) = refl2 p := by
  cases α; rfl

/-- Double inverse of a 2-path. -/
@[simp] theorem symm2_symm2 {p q : Path a b} (α : Path2 p q) :
    symm2 (symm2 α) = α := by
  cases α; rfl

/-- `symm2` distributes over `vcomp` (reversing order). -/
theorem symm2_vcomp {p q r : Path a b}
    (α : Path2 p q) (β : Path2 q r) :
    symm2 (vcomp α β) = vcomp (symm2 β) (symm2 α) := by
  cases α; cases β; rfl

/-! ## Horizontal composition via congruence -/

/-- Horizontal composition of 2-paths: given `α : p₁ = p₂` and `β : q₁ = q₂`,
produce `trans p₁ q₁ = trans p₂ q₂`. -/
noncomputable def hcomp {p₁ p₂ : Path a b} {q₁ q₂ : Path b c}
    (α : Path2 p₁ p₂) (β : Path2 q₁ q₂) :
    Path2 (trans p₁ q₁) (trans p₂ q₂) := by
  cases α; cases β; rfl

/-- `hcomp` with `refl2` on both sides is `refl2`. -/
@[simp] theorem hcomp_refl {p : Path a b} {q : Path b c} :
    hcomp (refl2 p) (refl2 q) = refl2 (trans p q) := rfl

/-- Left whiskering as a special case of `hcomp`. -/
theorem whiskerLeft_eq_hcomp (p : Path a b) {q q' : Path b c}
    (β : Path2 q q') :
    hcomp (refl2 p) β = _root_.congrArg (trans p) β := by
  cases β; rfl

/-- Right whiskering as a special case of `hcomp`. -/
theorem whiskerRight_eq_hcomp {p p' : Path a b} (q : Path b c)
    (α : Path2 p p') :
    hcomp α (refl2 q) = _root_.congrArg (fun x => trans x q) α := by
  cases α; rfl

/-! ## Interchange law -/

/-- The interchange law: horizontal composition distributes over vertical. -/
theorem interchange {p₁ p₂ p₃ : Path a b} {q₁ q₂ q₃ : Path b c}
    (α₁ : Path2 p₁ p₂) (α₂ : Path2 p₂ p₃)
    (β₁ : Path2 q₁ q₂) (β₂ : Path2 q₂ q₃) :
    hcomp (vcomp α₁ α₂) (vcomp β₁ β₂) =
      vcomp (hcomp α₁ β₁) (hcomp α₂ β₂) := by
  cases α₁; cases α₂; cases β₁; cases β₂; rfl

/-! ## Eckmann–Hilton -/

/-- When both 2-paths are loops on `refl`, horizontal and vertical
composition agree. -/
theorem hcomp_eq_vcomp_on_refl
    (α β : Path2 (refl a) (refl a)) :
    hcomp α β = vcomp α β := by
  -- hcomp α β = congrArg₂ trans α β, which on refl loops simplifies
  -- Both live in `refl a = refl a`, which is a subsingleton
  -- Structural: this is equality between proofs in `Prop`.
  exact Subsingleton.elim _ _

/-- Eckmann–Hilton: 2-path loops on `refl` commute under vertical composition. -/
theorem eckmann_hilton
    (α β : Path2 (refl a) (refl a)) :
    vcomp α β = vcomp β α := by
  -- The type `refl a = refl a` is a subsingleton (Eq in a Lean 4 type)
  -- Wait — `Path a a` is NOT a Prop, so `refl a = refl a` is not a priori
  -- subsingleton. But both sides of our goal are in `refl a = refl a`,
  -- and we can use the interchange law.
  -- Actually, `Eq` at any type is a subsingleton in Lean 4's Prop.
  -- No: `refl a = refl a` is `Prop`, so it IS a subsingleton.
  -- Structural: this compares proofs in `Prop`.
  exact Subsingleton.elim _ _

/-- Alternative statement using `Eq.trans` directly. -/
theorem eckmann_hilton' (α β : @refl A a = @refl A a) :
    α.trans β = β.trans α :=
  -- Structural: direct Eq-proof commutativity in `Prop`.
  Subsingleton.elim _ _

/-! ## 2-groupoid structure -/

/-- `hcomp` respects the associator: the two ways of composing three
2-paths around the associator agree. -/
theorem hcomp_assoc_coherence {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} {r₁ r₂ : Path c d}
    (α : Path2 p₁ p₂) (β : Path2 q₁ q₂) (γ : Path2 r₁ r₂) :
    hcomp α (hcomp β γ) =
      (trans_assoc p₁ q₁ r₁) ▸ (trans_assoc p₂ q₂ r₂) ▸ hcomp (hcomp α β) γ := by
  cases α; cases β; cases γ; rfl

/-- `hcomp` with left unitor: whiskering by `refl2 (refl a)` on the left
acts as the identity (after accounting for the left identity law). -/
theorem hcomp_left_refl_eq {p₁ p₂ : Path a b}
    (α : Path2 p₁ p₂) :
    hcomp (refl2 (refl a)) α = _root_.congrArg (trans (refl a)) α := by
  cases α; rfl

/-- `hcomp` with right unitor: whiskering by `refl2 (refl b)` on the right. -/
theorem hcomp_right_refl_eq {p₁ p₂ : Path a b}
    (α : Path2 p₁ p₂) :
    hcomp α (refl2 (refl b)) = _root_.congrArg (fun x => trans x (refl b)) α := by
  cases α; rfl

/-- `symm2` of `hcomp`. -/
@[simp] theorem symm2_hcomp {p₁ p₂ : Path a b} {q₁ q₂ : Path b c}
    (α : Path2 p₁ p₂) (β : Path2 q₁ q₂) :
    symm2 (hcomp α β) = hcomp (symm2 α) (symm2 β) := by
  cases α; cases β; rfl

/-- Any two 2-paths between the same pair of paths are equal. -/
theorem path2_eq {p q : Path a b}
    (α β : Path2 p q) : α = β :=
  -- Structural: `Path2 p q` is itself `Prop`.
  Subsingleton.elim α β

/-- The space of 2-paths is a set. -/
theorem path2_is_set {p q : Path a b} :
    ∀ (α β : Path2 p q), α = β :=
  -- Structural: proof irrelevance for `Eq`.
  fun α β => Subsingleton.elim α β

/-- All 3-paths (equalities between 2-paths) are equal. -/
theorem path3_trivial {p q : Path a b}
    {α β : Path2 p q} (u v : α = β) : u = v :=
  -- Structural: all 3-paths are proof-equal in `Prop`.
  Subsingleton.elim u v

/-- Step-trace companion: a 2-path identifies the underlying step traces. -/
theorem path2_steps_eq {p q : Path a b} (α : Path2 p q) :
    p.steps = q.steps := by
  cases α
  rfl

/-- Step-trace companion: vertical composition preserves endpoint traces. -/
theorem vcomp_steps_eq {p q r : Path a b}
    (α : Path2 p q) (β : Path2 q r) :
    p.steps = r.steps := by
  cases α
  cases β
  rfl

/-- Step-trace companion: horizontal composition preserves concatenated traces. -/
theorem hcomp_steps_eq {p₁ p₂ : Path a b} {q₁ q₂ : Path b c}
    (α : Path2 p₁ p₂) (β : Path2 q₁ q₂) :
    (trans p₁ q₁).steps = (trans p₂ q₂).steps := by
  cases α
  cases β
  rfl

/-! ## Naturality of whiskering -/

/-- Whiskering is natural: composing whiskers in different orders yields
the same result. -/
theorem whisker_natural {p p' : Path a b} {q q' : Path b c}
    (α : Path2 p p') (β : Path2 q q') :
    vcomp (hcomp α (refl2 q)) (hcomp (refl2 p') β) =
      vcomp (hcomp (refl2 p) β) (hcomp α (refl2 q')) := by
  cases α; cases β; rfl

/-- `hcomp` is functorial in the first argument. -/
theorem hcomp_vcomp_left {p₁ p₂ p₃ : Path a b} {q : Path b c}
    (α : Path2 p₁ p₂) (β : Path2 p₂ p₃) :
    hcomp (vcomp α β) (refl2 q) = vcomp (hcomp α (refl2 q)) (hcomp β (refl2 q)) := by
  cases α; cases β; rfl

/-- `hcomp` is functorial in the second argument. -/
theorem hcomp_vcomp_right {p : Path a b} {q₁ q₂ q₃ : Path b c}
    (α : Path2 q₁ q₂) (β : Path2 q₂ q₃) :
    hcomp (refl2 p) (vcomp α β) = vcomp (hcomp (refl2 p) α) (hcomp (refl2 p) β) := by
  cases α; cases β; rfl

end Path

end ComputationalPaths
