/-
# Simple equivalences for rewrite theory

This module contains the `SimpleEquiv` structure plus elementary lemmas used by
rewrite quotients.  It is intentionally standalone so other rewrite files can
import it without pulling in the full rewrite closure machinery.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path

open scoped Quot

universe u v w x

/-- Lightweight equivalence structure used to package mutually inverse maps
without pulling in additional dependencies. -/
structure SimpleEquiv (α : Sort u) (β : Sort v) where
  /-- Forward map. -/
  toFun : α → β
  /-- Inverse map. -/
  invFun : β → α
  /-- Inverse applied after the forward map is the identity. -/
  left_inv : ∀ x : α, invFun (toFun x) = x
  /-- Forward map applied after the inverse is the identity. -/
  right_inv : ∀ y : β, toFun (invFun y) = y

namespace SimpleEquiv

variable {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x}

noncomputable instance : CoeFun (SimpleEquiv α β) (fun _ => α → β) :=
  ⟨SimpleEquiv.toFun⟩

@[simp] theorem coe_apply (e : SimpleEquiv α β) (x : α) :
    e x = e.toFun x := rfl

/-- Equivalence in the opposite direction. -/
@[simp] noncomputable def symm (e : SimpleEquiv α β) : SimpleEquiv β α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

@[simp] theorem symm_apply (e : SimpleEquiv α β) (y : β) :
    e.symm y = e.invFun y := rfl

@[simp] theorem symm_inv_apply (e : SimpleEquiv α β) (x : α) :
    e.symm.invFun x = e x := rfl

/-- Identity equivalence. -/
@[simp] noncomputable def refl (α : Sort u) : SimpleEquiv α α where
  toFun := id
  invFun := id
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- Composition of equivalences. -/
@[simp] noncomputable def comp (e : SimpleEquiv α β) (f : SimpleEquiv β γ) :
    SimpleEquiv α γ where
  toFun := fun x => f.toFun (e.toFun x)
  invFun := fun z => e.invFun (f.invFun z)
  left_inv := by
    intro x
    have hf := f.left_inv (e.toFun x)
    have he := e.left_inv x
    simpa [hf]
  right_inv := by
    intro z
    have he := e.right_inv (f.invFun z)
    have hf := f.right_inv z
    simpa [he]

@[simp] theorem symm_symm (e : SimpleEquiv α β) :
    e.symm.symm = e := rfl

@[simp] theorem comp_apply (e : SimpleEquiv α β)
    (f : SimpleEquiv β γ) (x : α) :
    comp e f x = f (e x) := rfl

@[simp] theorem comp_inv_apply (e : SimpleEquiv α β)
    (f : SimpleEquiv β γ) (z : γ) :
    (comp e f).invFun z = e.invFun (f.invFun z) := rfl

@[simp] theorem comp_refl (e : SimpleEquiv α β) :
    comp e (refl β) = e := by
  cases e
  rfl

@[simp] theorem refl_comp (e : SimpleEquiv α β) :
    comp (refl α) e = e := by
  cases e
  rfl

@[simp] theorem comp_assoc (e : SimpleEquiv α β)
    (f : SimpleEquiv β γ) (g : SimpleEquiv γ δ) :
    comp (comp e f) g = comp e (comp f g) := by
  cases e
  cases f
  cases g
  rfl

@[simp] theorem apply_symm_apply (e : SimpleEquiv α β) (y : β) :
    e (e.symm y) = y := by
  change e.toFun (e.invFun y) = y
  exact e.right_inv y

@[simp] theorem symm_apply_apply (e : SimpleEquiv α β) (x : α) :
    e.symm (e x) = x := by
  change e.invFun (e.toFun x) = x
  exact e.left_inv x

@[ext] theorem ext {e₁ e₂ : SimpleEquiv α β}
    (h₁ : ∀ x : α, e₁ x = e₂ x)
    (h₂ : ∀ y : β, e₁.invFun y = e₂.invFun y) :
    e₁ = e₂ := by
  classical
  cases e₁ with
  | mk toFun₁ invFun₁ left_inv₁ right_inv₁ =>
      cases e₂ with
      | mk toFun₂ invFun₂ left_inv₂ right_inv₂ =>
          have h_toFun : toFun₁ = toFun₂ := funext h₁
          have h_invFun : invFun₁ = invFun₂ := funext h₂
          subst h_toFun
          subst h_invFun
          simp

@[simp] theorem symm_comp (e : SimpleEquiv α β) :
    comp (symm e) e = refl β := by
  apply SimpleEquiv.ext
  · intro y
    simpa [SimpleEquiv.comp, SimpleEquiv.symm, SimpleEquiv.refl]
      using e.right_inv y
  · intro x
    simpa [SimpleEquiv.comp, SimpleEquiv.symm, SimpleEquiv.refl]
      using e.right_inv x

@[simp] theorem comp_symm (e : SimpleEquiv α β) :
    comp e (symm e) = refl α := by
  apply SimpleEquiv.ext
  · intro x
    simpa [SimpleEquiv.comp, SimpleEquiv.symm, SimpleEquiv.refl]
      using e.left_inv x
  · intro y
    simpa [SimpleEquiv.comp, SimpleEquiv.symm, SimpleEquiv.refl]
      using e.left_inv y

/-- Transitivity of equivalences (alias for comp). -/
@[simp] noncomputable def trans (e : SimpleEquiv α β) (f : SimpleEquiv β γ) :
    SimpleEquiv α γ := comp e f

/-- Product of two equivalences. -/
@[simp] noncomputable def prodBoth' {α' β' γ' δ' : Type u}
    (e : SimpleEquiv α' β') (f : SimpleEquiv γ' δ') :
    SimpleEquiv (α' × γ') (β' × δ') where
  toFun := fun (a, c) => (e a, f c)
  invFun := fun (b, d) => (e.invFun b, f.invFun d)
  left_inv := by
    intro (a, c)
    simp [e.left_inv a, f.left_inv c]
  right_inv := by
    intro (b, d)
    simp [e.right_inv b, f.right_inv d]

/-- Equivalence on the left component of a product. -/
@[simp] noncomputable def prodLeft' {α' γ' : Type u} (β' : Type u) (e : SimpleEquiv α' γ') :
    SimpleEquiv (α' × β') (γ' × β') where
  toFun := fun (a, b) => (e a, b)
  invFun := fun (c, b) => (e.invFun c, b)
  left_inv := by intro (a, b); simp [e.left_inv a]
  right_inv := by intro (c, b); simp [e.right_inv c]

/-- Equivalence on the right component of a product. -/
@[simp] noncomputable def prodRight' {β' δ' : Type u} (α' : Type u) (e : SimpleEquiv β' δ') :
    SimpleEquiv (α' × β') (α' × δ') where
  toFun := fun (a, b) => (a, e b)
  invFun := fun (a, d) => (a, e.invFun d)
  left_inv := by intro (a, b); simp [e.left_inv b]
  right_inv := by intro (a, d); simp [e.right_inv d]

/-- Cast an element along an equality of types. -/
noncomputable def cast {α β : Sort u} (h : α = β) (e : SimpleEquiv α γ) : SimpleEquiv β γ :=
  h ▸ e


end SimpleEquiv

end Path
end ComputationalPaths
