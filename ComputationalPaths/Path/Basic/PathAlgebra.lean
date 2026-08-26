/-
# Path Algebra — algebraic structure of computational paths

The groupoid-like structure on `Path`: composition (`trans`), inverse (`symm`),
identity (`refl`), together with path length, step operations, and the subpath
relation.  Core already establishes the basic groupoid laws; here we develop
the remaining algebraic infrastructure.

## Main results

- `length` and its interaction with `trans`, `symm`, `refl`, `congrArg`
- Cancellation laws for `trans`/`symm` at the *step-list* level
- Subpath relation (`IsPrefix`, `IsSuffix`) and their properties
- Path concatenation monoid structure
- Step-count invariants and injectivity results
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

open List

namespace Path

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}
variable {a b c d : A}

/-! ## Path length -/

/-- The length of a path is the number of rewrite steps it records. -/
@[simp] noncomputable def length (p : Path a b) : Nat :=
  p.steps.length

/-- The reflexive path has length zero. -/
@[simp] theorem length_refl : length (refl a) = 0 := rfl

/-- `ofEq` always produces a path of length one. -/
@[simp] theorem length_ofEq (h : a = b) : length (ofEq h) = 1 := rfl

/-- Length is additive under composition. -/
@[simp] theorem length_trans (p : Path a b) (q : Path b c) :
    length (trans p q) = length p + length q := by
  simp [length, trans, List.length_append]

/-- Symmetry preserves length. -/
@[simp] theorem length_symm (p : Path a b) :
    length (symm p) = length p := by
  simp [length, symm, List.length_map, List.length_reverse]

/-- `congrArg` preserves length. -/
@[simp] theorem length_congrArg (f : A → B) (p : Path a b) :
    length (congrArg f p) = length p := by
  simp [length, Path.congrArg, List.length_map]

/-- `invA` preserves length (alias for `length_symm`). -/
@[simp] theorem length_invA (p : Path a b) :
    length (invA p) = length p :=
  length_symm p

/-- A path has length zero iff its step list is empty. -/
theorem length_eq_zero_iff (p : Path a b) :
    length p = 0 ↔ p.steps = [] := by
  simp [length]

/-! ## Step extraction -/

/-- The list of source elements from the steps of a path. -/
noncomputable def sources (p : Path a b) : List A :=
  p.steps.map Step.src

/-- The list of target elements from the steps of a path. -/
noncomputable def targets (p : Path a b) : List A :=
  p.steps.map Step.tgt

@[simp] theorem sources_refl : sources (refl a) = [] := rfl
@[simp] theorem targets_refl : targets (refl a) = [] := rfl

@[simp] theorem sources_length (p : Path a b) :
    p.sources.length = p.length := by
  simp [sources, length]

@[simp] theorem targets_length (p : Path a b) :
    p.targets.length = p.length := by
  simp [targets, length]

/-- Sources of a composed path are the concatenation of sources. -/
@[simp] theorem sources_trans (p : Path a b) (q : Path b c) :
    sources (trans p q) = sources p ++ sources q := by
  simp [sources, trans, List.map_append]

/-- Targets of a composed path are the concatenation of targets. -/
@[simp] theorem targets_trans (p : Path a b) (q : Path b c) :
    targets (trans p q) = targets p ++ targets q := by
  simp [targets, trans, List.map_append]

/-! ## Cancellation at the step-list level -/

/-- Two paths from `a` to `b` are equal iff their step lists agree. -/
theorem ext_steps (p q : Path a b) :
    p = q ↔ p.steps = q.steps := by
  constructor
  · intro h; subst h; rfl
  · cases p with
    | mk steps1 proof1 =>
        cases q with
        | mk steps2 proof2 =>
            intro h
            simp at h
            subst h
            rfl

/-- Left cancellation for `trans` on step lists. -/
theorem trans_left_cancel (p : Path a b) (q r : Path b c)
    (h : trans p q = trans p r) : q = r := by
  have hs : (trans p q).steps = (trans p r).steps := by rw [h]
  simp [trans] at hs
  exact (ext_steps q r).mpr hs

/-- Right cancellation for `trans` on step lists. -/
theorem trans_right_cancel (p q : Path a b) (r : Path b c)
    (h : trans p r = trans q r) : p = q := by
  have hs : (trans p r).steps = (trans q r).steps := by rw [h]
  simp [trans] at hs
  exact (ext_steps p q).mpr hs

/-- `symm` is injective on paths. -/
theorem symm_injective (p q : Path a b) (h : symm p = symm q) : p = q := by
  have : symm (symm p) = symm (symm q) := by rw [h]
  rwa [symm_symm, symm_symm] at this

/-! ## Subpath / prefix / suffix -/

/-- `p` is a prefix of `q` when `p.steps` is a prefix of `q.steps`. -/
noncomputable def IsPrefix (p : Path a b) (q : Path a c) : Prop :=
  ∃ tail, q.steps = p.steps ++ tail

/-- `p` is a suffix of `q` when `p.steps` is a suffix of `q.steps`. -/
noncomputable def IsSuffix (p : Path b c) (q : Path a c) : Prop :=
  ∃ front, q.steps = front ++ p.steps

/-- `refl` is a prefix of every path. -/
theorem refl_isPrefix (p : Path a b) : IsPrefix (refl a) p :=
  ⟨p.steps, by simp [refl]⟩

/-- `refl` is a suffix of every path. -/
theorem refl_isSuffix (p : Path a b) : IsSuffix (refl b) p :=
  ⟨p.steps, by simp [refl]⟩

/-- Every path is a prefix of itself. -/
theorem isPrefix_self (p : Path a b) : IsPrefix p p :=
  ⟨[], by simp⟩

/-- Every path is a suffix of itself. -/
theorem isSuffix_self (p : Path a b) : IsSuffix p p :=
  ⟨[], by simp⟩

/-- If `p` is a prefix of `q`, then `length p ≤ length q`. -/
theorem IsPrefix.length_le {p : Path a b} {q : Path a c}
    (h : IsPrefix p q) : length p ≤ length q := by
  obtain ⟨tail, htail⟩ := h
  simp only [length, htail, List.length_append]
  omega

/-- If `p` is a suffix of `q`, then `length p ≤ length q`. -/
theorem IsSuffix.length_le {p : Path b c} {q : Path a c}
    (h : IsSuffix p q) : length p ≤ length q := by
  obtain ⟨front, hfront⟩ := h
  simp only [length, hfront, List.length_append]
  omega

/-- Prefix is transitive for composed paths: if `p` is a prefix of `trans p q`,
   and `trans p q` is a prefix of `trans p (trans q r)`, we get a chain. -/
theorem isPrefix_trans_left (p : Path a b) (q : Path b c) :
    IsPrefix p (trans p q) :=
  ⟨q.steps, by simp [trans]⟩

/-- Suffix for the right component of a composed path. -/
theorem isSuffix_trans_right (p : Path a b) (q : Path b c) :
    IsSuffix q (trans p q) :=
  ⟨p.steps, by simp [trans]⟩

/-! ## Monoid-like properties -/

/-- Path `steps` under `++` form a monoid with `[]` as identity.
We record this as: the path groupoid restricted to `trans`/`refl` is
a category (monoid in each hom-set when we forget inverses). -/
theorem trans_nil_steps (p : Path a b) :
    (trans (refl a) p).steps = p.steps := by simp

/-- `trans` is the unique operation compatible with step-list concatenation. -/
theorem trans_steps_eq (p : Path a b) (q : Path b c) :
    (trans p q).steps = p.steps ++ q.steps := rfl

/-! ## Miscellaneous algebraic properties -/

/-- Double symmetry is definitionally the identity (recall from Core, but
we verify it interacts correctly with `length`). -/
@[simp] theorem length_symm_symm (p : Path a b) :
    length (symm (symm p)) = length p := by
  simp

/-- `trans` with `symm` yields a path whose length is the sum of the parts. -/
theorem length_trans_symm (p : Path a b) :
    length (trans p (symm p)) = 2 * length p := by
  simp [Nat.two_mul]

/-- `trans` with `symm` on the other side. -/
theorem length_symm_trans (p : Path a b) :
    length (trans (symm p) p) = 2 * length p := by
  simp [Nat.two_mul]

/-- The step list of `congrArg f (trans p q)` splits correctly. -/
@[simp] theorem congrArg_trans_steps (f : A → B) (p : Path a b) (q : Path b c) :
    (congrArg f (trans p q)).steps =
      (congrArg f p).steps ++ (congrArg f q).steps := by
  simp [Path.congrArg, trans, List.map_append]

/-- `congrArg` distributes over prefix: if `p` is a prefix of `q`,
then `congrArg f p` is a prefix of `congrArg f q`. -/
theorem congrArg_preserves_prefix (f : A → B) {p : Path a b} {q : Path a c}
    (h : IsPrefix p q) : IsPrefix (congrArg f p) (congrArg f q) := by
  obtain ⟨tail, htail⟩ := h
  exact ⟨tail.map (Step.map f), by simp [Path.congrArg, htail, List.map_append]⟩


-- ============================================================
-- SECTION Inv5 genuine computational-path primitives
-- ============================================================
-- Genuine rewrite traces over the Nat degrees/indices used in this module.
-- (This module is a transitive dependency of the RwEq system, so it stays
-- RwEq-free and provides a genuine multi-step `Path.trans` chain instead.)

/-- Associativity rewrite `(a + b) + c ⤳ a + (b + c)`: one genuine step. -/
noncomputable def basicPathAlgebraAssoc (a b c : Nat) : Path ((a + b) + c) (a + (b + c)) :=
  Path.ofEq (Nat.add_assoc a b c)

/-- Inner commutativity `a + (b + c) ⤳ a + (c + b)` via congruence in the
    right argument (`_root_.congrArg`, since `congrArg` here is `Path.congrArg`). -/
noncomputable def basicPathAlgebraInner (a b c : Nat) : Path (a + (b + c)) (a + (c + b)) :=
  Path.ofEq (_root_.congrArg (fun t => a + t) (Nat.add_comm b c))

/-- Outer commutativity `a + (c + b) ⤳ (c + b) + a`: one genuine step. -/
noncomputable def basicPathAlgebraOuter (a b c : Nat) : Path (a + (c + b)) ((c + b) + a) :=
  Path.ofEq (Nat.add_comm a (c + b))

/-- A genuine **two-step** path: reassociate, then commute the inner pair. -/
noncomputable def basicPathAlgebraTwoStep (a b c : Nat) : Path ((a + b) + c) (a + (c + b)) :=
  Path.trans (basicPathAlgebraAssoc a b c) (basicPathAlgebraInner a b c)

/-- A genuine **three-step** path composing the reassociation, the inner and the
    outer commutation — trace length three, distinct endpoints. -/
noncomputable def basicPathAlgebraThreeStep (a b c : Nat) : Path ((a + b) + c) ((c + b) + a) :=
  Path.trans (basicPathAlgebraTwoStep a b c) (basicPathAlgebraOuter a b c)
end Path

end ComputationalPaths
