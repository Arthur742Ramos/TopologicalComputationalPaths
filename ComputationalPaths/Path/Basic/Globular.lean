/-
# Globular towers of computational paths

This module formalises the "iteration" paragraph from the paper: starting
from a base type `A`, we can iterate the identity type construction to obtain a
globular set where each level stores explicit computational-path witnesses
between elements from the previous level.  The resulting tower exposes reflexive,
symmetric, and transitive operations at every dimension.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path

universe u v

/-- A single higher-dimensional cell whose endpoints live in `β`.  It records
its source, target, and the computational path witnessing the connection. -/
structure GlobularCell (β : Type u) where
  src : β
  tgt : β
  path : Path src tgt

namespace GlobularCell

variable {β : Type u}

/-- Reflexive cell at a given point. -/
@[simp] noncomputable def refl (x : β) : GlobularCell β :=
  { src := x, tgt := x, path := Path.refl x }

/-- Symmetry flips the endpoints and applies `Path.symm`. -/
@[simp] noncomputable def symm (c : GlobularCell β) : GlobularCell β :=
  { src := c.tgt, tgt := c.src, path := Path.symm c.path }

/-- Composition of cells; the path argument aligns the midpoint. -/
@[simp] noncomputable def trans (p : GlobularCell β) (q : GlobularCell β)
    (h : Path p.tgt q.src) : GlobularCell β :=
  { src := p.src
    tgt := q.tgt
    path := Path.trans (Path.trans p.path h) q.path }

@[simp] theorem symm_symm (c : GlobularCell β) : symm (symm c) = c := by
  cases c with
  | mk src tgt path =>
      have h := _root_.congrArg (fun p => GlobularCell.mk src tgt p)
        (Path.symm_symm path)
      simpa [symm, GlobularCell.symm] using h

@[simp] theorem symm_refl (x : β) : symm (refl x) = refl x := by
  simp [refl, symm]

@[simp] theorem trans_refl_left (c : GlobularCell β) :
    trans (refl c.src) c (Path.refl c.src) = c := by
  cases c
  simp [refl, trans]

@[simp] theorem trans_refl_right (c : GlobularCell β) :
    trans c (refl c.tgt) (Path.refl c.tgt) = c := by
  cases c
  simp [refl, trans]

@[simp] theorem symm_src (c : GlobularCell β) :
    (symm c).src = c.tgt := rfl

@[simp] theorem symm_tgt (c : GlobularCell β) :
    (symm c).tgt = c.src := rfl

@[simp] theorem trans_src (p q : GlobularCell β) (h : Path p.tgt q.src) :
    (trans p q h).src = p.src := by
  cases q
  cases h
  rfl

@[simp] theorem trans_tgt (p q : GlobularCell β) (h : Path p.tgt q.src) :
    (trans p q h).tgt = q.tgt := by
  cases q
  cases h
  rfl

private noncomputable def trans_assoc_left_eq (p q r : GlobularCell β)
    (h₁ : Path p.tgt q.src) (h₂ : Path q.tgt r.src) :
    Path (trans p q h₁).tgt r.src := by
  simpa [trans] using h₂

private noncomputable def trans_assoc_right_eq (p q r : GlobularCell β)
    (h₁ : Path p.tgt q.src) (h₂ : Path q.tgt r.src) :
    Path p.tgt (trans q r h₂).src := by
  simpa [trans] using h₁

@[simp] theorem trans_assoc (p q r : GlobularCell β)
    (h₁ : Path p.tgt q.src) (h₂ : Path q.tgt r.src) :
    trans (trans p q h₁) r (trans_assoc_left_eq p q r h₁ h₂) =
      trans p (trans q r h₂) (trans_assoc_right_eq p q r h₁ h₂) := by
  cases p
  cases q
  cases r
  simp [trans, trans_assoc_left_eq, trans_assoc_right_eq]


end GlobularCell

/-- Iterated globular levels over a base type `A`.  Level `0` is `A` itself,
while `level (n+1)` stores explicit cells between level-`n` elements. -/
noncomputable def GlobularLevel (A : Type u) : Nat → Type u
  | 0 => A
  | Nat.succ n => GlobularCell (GlobularLevel A n)

namespace GlobularLevel

variable {A : Type u}

@[simp] theorem zero (A : Type u) : GlobularLevel A 0 = A := rfl
@[simp] theorem succ (n : Nat) :
    GlobularLevel A (Nat.succ n) =
      GlobularCell (GlobularLevel A n) := rfl

/-- Reflexive cell living one dimension higher. -/
@[simp] noncomputable def refl {n : Nat} (x : GlobularLevel A n) :
    GlobularLevel A (n + 1) :=
  GlobularCell.refl x

/-- Symmetry at level `n+1`. -/
@[simp] noncomputable def symm {n : Nat} (c : GlobularLevel A (n + 1)) :
    GlobularLevel A (n + 1) :=
  GlobularCell.symm c

/-- Composition at level `n+1`.  The middle path aligns the endpoints. -/
@[simp] noncomputable def trans {n : Nat}
    (p : GlobularLevel A (n + 1)) (q : GlobularLevel A (n + 1))
    (h : Path p.tgt q.src) :
    GlobularLevel A (n + 1) :=
  GlobularCell.trans p q (β := GlobularLevel A n) h

@[simp] theorem symm_symm {n : Nat}
    (c : GlobularLevel A (n + 1)) : symm (A := A) (symm c) = c := by
  cases c with
  | mk src tgt path =>
    have h := GlobularCell.symm_symm (c := GlobularCell.mk src tgt path)
    simpa [symm, GlobularCell.symm] using h

@[simp] theorem symm_refl {n : Nat}
    (x : GlobularLevel A n) : symm (A := A) (refl x) = refl x := by
  simp [refl, symm]

@[simp] theorem trans_refl_left {n : Nat}
    (c : GlobularLevel A (n + 1)) :
    trans (A := A) (refl c.src) c (Path.refl c.src) = c := by
  cases c
  simp [refl, trans]

@[simp] theorem trans_refl_right {n : Nat}
    (c : GlobularLevel A (n + 1)) :
    trans (A := A) c (refl c.tgt) (Path.refl c.tgt) = c := by
  cases c
  simp [refl, trans]

@[simp] theorem symm_src {n : Nat}
    (c : GlobularLevel A (n + 1)) :
    (symm (A := A) c).src = c.tgt := by
  simp [symm]

@[simp] theorem symm_tgt {n : Nat}
    (c : GlobularLevel A (n + 1)) :
    (symm (A := A) c).tgt = c.src := by
  simp [symm]

@[simp] theorem trans_src {n : Nat}
    (p q : GlobularLevel A (n + 1)) (h : Path p.tgt q.src) :
    (trans (A := A) p q h).src = p.src := by
  cases p
  cases q
  cases h
  rfl

@[simp] theorem trans_tgt {n : Nat}
    (p q : GlobularLevel A (n + 1)) (h : Path p.tgt q.src) :
    (trans (A := A) p q h).tgt = q.tgt := by
  cases p
  cases q
  cases h
  rfl

private noncomputable def globular_trans_assoc_left_eq {n : Nat}
    (p q r : GlobularLevel A (n + 1))
    (h₁ : Path p.tgt q.src) (h₂ : Path q.tgt r.src) :
    Path (trans (A := A) p q h₁).tgt r.src := by
  simpa [trans] using
    (GlobularCell.trans_assoc_left_eq (β := GlobularLevel A n) p q r h₁ h₂)

private noncomputable def globular_trans_assoc_right_eq {n : Nat}
    (p q r : GlobularLevel A (n + 1))
    (h₁ : Path p.tgt q.src) (h₂ : Path q.tgt r.src) :
    Path p.tgt (trans (A := A) q r h₂).src := by
  simpa [trans] using
    (GlobularCell.trans_assoc_right_eq (β := GlobularLevel A n) p q r h₁ h₂)

@[simp] theorem trans_assoc {n : Nat}
    (p q r : GlobularLevel A (n + 1))
    (h₁ : Path p.tgt q.src) (h₂ : Path q.tgt r.src) :
    trans (A := A) (trans (A := A) p q h₁) r
        (globular_trans_assoc_left_eq p q r h₁ h₂) =
      trans (A := A) p (trans (A := A) q r h₂)
        (globular_trans_assoc_right_eq p q r h₁ h₂) := by
  simpa [trans, globular_trans_assoc_left_eq, globular_trans_assoc_right_eq] using
    (GlobularCell.trans_assoc (β := GlobularLevel A n) p q r h₁ h₂)

section Functoriality

variable {B : Type v}

/-- Level-wise action of a function on globular cells.  At the base level this
is just function application, while higher cells are mapped by applying the
function to the endpoints and functorially transporting the underlying
computational path. -/
@[simp] noncomputable def map : {n : Nat} → (A → B) → GlobularLevel A n → GlobularLevel B n
  | 0, f, a => f a
  | Nat.succ n, f, c =>
      { src := map (n := n) f c.src
        tgt := map (n := n) f c.tgt
        path := Path.congrArg (map (n := n) f) c.path }

@[simp] theorem map_src {n : Nat} (f : A → B)
    (c : GlobularLevel A (n + 1)) :
    (map (n := n + 1) f c).src = map (n := n) f c.src := rfl

@[simp] theorem map_tgt {n : Nat} (f : A → B)
    (c : GlobularLevel A (n + 1)) :
    (map (n := n + 1) f c).tgt = map (n := n) f c.tgt := rfl

@[simp] theorem map_refl {n : Nat} (f : A → B)
    (x : GlobularLevel A n) :
    map (n := n + 1) f (refl x) =
      refl (map (n := n) f x) := by
  simp [refl, map]

@[simp] theorem map_symm {n : Nat} (f : A → B)
    (c : GlobularLevel A (n + 1)) :
    map (n := n + 1) f (symm c) =
      symm (map (n := n + 1) f c) := by
  cases c
  simp [symm, map]

@[simp] theorem map_trans {n : Nat} (f : A → B)
    (p q : GlobularLevel A (n + 1)) (h : Path p.tgt q.src) :
    map (n := n + 1) f (trans (A := A) p q h) =
      trans (map (n := n + 1) f p) (map (n := n + 1) f q)
        (Path.congrArg (map (n := n) f) h) := by
  cases q
  cases h
  cases p
  simp [map, trans]

end Functoriality

/-- Underlying computational path of a higher cell. -/
@[simp] noncomputable def toPath {n : Nat} (c : GlobularLevel A (n + 1)) :
    Path c.src c.tgt :=
  c.path

@[simp] theorem toPath_refl {n : Nat} (x : GlobularLevel A n) :
    toPath (A := A) (refl x) = Path.refl x := by
  simp [toPath, refl]

@[simp] theorem toPath_symm {n : Nat}
    (c : GlobularLevel A (n + 1)) :
    toPath (A := A) (symm c) = Path.symm (toPath (A := A) c) := by
  simp [toPath, symm, GlobularCell.symm]

@[simp] theorem toPath_trans {n : Nat}
    (p q : GlobularLevel A (n + 1)) (h : Path p.tgt q.src) :
    toPath (A := A) (trans (A := A) p q h) =
      Path.trans (Path.trans (toPath (A := A) p) h) (toPath (A := A) q) := by
  simp [toPath, trans]

section Functoriality

variable {B : Type v}

@[simp] theorem map_toPath {n : Nat} (f : A → B)
    (c : GlobularLevel A (n + 1)) :
    toPath (map (n := n + 1) f c) =
      Path.congrArg (map (n := n) f) (toPath c) := by
  cases c
  simp [GlobularLevel.map, toPath]

end Functoriality

end GlobularLevel

end Path
end ComputationalPaths
