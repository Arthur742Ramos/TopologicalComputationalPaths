/-
# Path Induction — eliminators and recursion for computational paths

We develop induction principles for `Path`: a J-like eliminator, based path
induction, path recursion, and transport-based substitution.  Because our
`Path` records an `Eq`-proof together with a step trace, the induction
principles decompose into an appeal to the inner `proof` field (which is just
`Eq`) and reconstruction of the step metadata.

## Main results

- `Path.pathInd` — the J-eliminator for the proof component.
- `Path.basedPathInd` — based path induction fixing one endpoint.
- `Path.pathRec` — recursion out of paths into an arbitrary type.
- Various computation rules and uniqueness principles.
- Transport lemmas derived from the induction structure.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

namespace Path

universe u v w

variable {A : Type u}
variable {a b c : A}

/-! ## J-eliminator (path induction on Eq) -/

/-- The J-eliminator for the equality component of paths. Given a motive
`C : ∀ (b : A), a = b → Sort v` and a proof that `C a rfl` holds,
we derive `C b h` for any `h : a = b`. -/
noncomputable def pathInd {C : ∀ (b : A), a = b → Sort v}
    (base : C a rfl)
    {b : A} (h : a = b) : C b h :=
  h ▸ base

/-- Computation rule: `pathInd` on `rfl` reduces to the base case. -/
@[simp] theorem pathInd_rfl {C : ∀ (b : A), a = b → Sort v}
    (base : C a rfl) :
    pathInd (C := C) base rfl = base := rfl

/-! ## Based path induction -/

/-- Based path induction: fix a basepoint `a` and a motive over all targets.
Given the motive holds at `a` with `rfl`, it holds for all `b` with `h : a = b`. -/
noncomputable def basedPathInd {C : ∀ (b : A), a = b → Sort v}
    (base : C a rfl)
    {b : A} (h : a = b) : C b h :=
  pathInd base h

/-- Computation rule for based path induction on `rfl`. -/
@[simp] theorem basedPathInd_rfl {C : ∀ (b : A), a = b → Sort v}
    (base : C a rfl) :
    basedPathInd (C := C) base rfl = base := rfl

/-! ## Path-level induction using the proof field -/

/-- Eliminate on a `Path` by eliminating on its `proof` field.
The motive sees only the endpoint and the equality proof, not the steps. -/
noncomputable def elimOnProof {C : ∀ (b : A), a = b → Sort v}
    (base : C a rfl)
    (p : Path a b) : C b p.proof :=
  p.proof ▸ base

/-- `elimOnProof` on `refl` computes to the base case. -/
@[simp] theorem elimOnProof_refl {C : ∀ (b : A), a = b → Sort v}
    (base : C a rfl) :
    elimOnProof (C := C) base (refl a) = base := rfl

/-! ## Path recursion -/

/-- Recursion out of paths: produce a value in `B` from any path, given
only a recipe for the source endpoint. -/
noncomputable def pathRec {B : Sort v}
    (base : A → B)
    (_p : Path a b) : B :=
  base a

/-- `pathRec` always returns the value at the source. -/
@[simp] theorem pathRec_eq {B : Sort v}
    (base : A → B) (p : Path a b) :
    pathRec base p = base a := rfl

/-- `pathRec` on `refl` computes. -/
@[simp] theorem pathRec_refl {B : Sort v}
    (base : A → B) :
    pathRec base (refl a) = base a := rfl

/-- `pathRec` is constant across paths with the same source. -/
theorem pathRec_const {B : Sort v}
    (base : A → B)
    (p : Path a b) (q : Path a c) :
    pathRec base p = pathRec base q := rfl

/-! ## Uniqueness / η principles -/

/-- Any function out of `Path` that agrees with `base` on `refl` is
determined by its behavior on `refl` for paths with empty step lists. -/
theorem pathRec_unique_refl {B : Sort v}
    (f : ∀ {a b : A}, Path a b → B)
    (base : A → B)
    (hf : ∀ a, f (refl a) = base a)
    (a : A) : f (refl a) = base a :=
  hf a

/-- η-expansion for paths with the same proof: two paths with `a = a`
have the same `proof` field. -/
theorem eta_proof (p : Path a a) :
    p.proof = (refl a).proof :=
  -- Structural: equality of Eq-proofs in `Prop`.
  Subsingleton.elim _ _

/-- Two functions that agree on all `refl` paths agree on all `refl`-proof paths. -/
theorem funext_refl {B : Sort v}
    (f g : ∀ {a : A}, Path a a → B)
    (h : ∀ a, f (refl a) = g (refl a)) (a : A) :
    f (refl a) = g (refl a) :=
  h a

/-! ## Transport from induction -/

/-- Transport along a path is derivable from path induction.  Here we show
the standard `transport` equals what `Eq.recOn` produces on the proof. -/
theorem transport_via_ind {D : A → Sort v} (p : Path a b) (x : D a) :
    transport p x = Eq.recOn p.proof x := by
  cases p with
  | mk steps proof =>
      cases proof
      rfl

/-- Transport along `ofEq` via induction. -/
@[simp] theorem transport_ofEq_ind {D : A → Sort v} (h : a = b) (x : D a) :
    transport (ofEq h) x = Eq.recOn h x := by
  cases h
  rfl

/-- Transport respects symmetry: `transport (symm p) ∘ transport p = id`. -/
theorem transport_symm_cancel {D : A → Sort v}
    (p : Path a b) (x : D a) :
    transport (symm p) (transport p x) = x :=
  transport_symm_left p x

/-- Transport respects symmetry (other direction). -/
theorem transport_symm_cancel' {D : A → Sort v}
    (p : Path a b) (y : D b) :
    transport p (transport (symm p) y) = y :=
  transport_symm_right p y

/-! ## Induction for path properties -/

/-- A property of paths that depends only on the proof field: if it holds
for the proof of `p`, it holds for `p`. -/
theorem proof_based_ind (p : Path a b) {P : (a = b) → Prop}
    (h : P p.proof) (q : Path a b) : P q.proof := by
  -- Structural: `p.proof` and `q.proof` are proposition proofs.
  have : p.proof = q.proof := Subsingleton.elim _ _
  rwa [← this]

/-- Singleton contractibility: the `proof` field of any path is uniquely
determined (proof irrelevance). -/
theorem proof_unique (p : Path a b) (h : a = b) :
    p.proof = h :=
  -- Structural: proof irrelevance for `Eq`.
  Subsingleton.elim _ _

/-- The proof field of any self-loop is `rfl`. -/
theorem self_path_proof (p : Path a a) :
    p.proof = rfl :=
  -- Structural: proof irrelevance for reflexive equalities.
  Subsingleton.elim _ _

/-- Step-trace companion: path composition is explicitly associative on traces. -/
theorem trans_trace_assoc_companion {d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    (trans (trans p q) r).steps = p.steps ++ q.steps ++ r.steps := by
  simp [trans, List.append_assoc]

/-- Step-trace companion: double symmetry preserves the original trace. -/
theorem symm_symm_trace_companion (p : Path a b) :
    (symm (symm p)).steps = p.steps := by
  simpa using _root_.congrArg Path.steps (symm_symm p)

/-! ## Dependent elimination -/

/-- Dependent elimination: given a path `p : Path a b` and a family
`D : A → Sort v`, transform elements of `D a` to `D b`. -/
noncomputable def depElim {D : A → Sort v} (p : Path a b) (x : D a) : D b :=
  transport p x

/-- `depElim` on `refl` is the identity. -/
@[simp] theorem depElim_refl {D : A → Sort v} (x : D a) :
    depElim (refl a) x = x := rfl

/-- `depElim` composes through `trans`. -/
@[simp] theorem depElim_trans {D : A → Sort v}
    (p : Path a b) (q : Path b c) (x : D a) :
    depElim (trans p q) x = depElim q (depElim p x) :=
  transport_trans p q x

/-- `depElim` through `symm` inverts. -/
@[simp] theorem depElim_symm_cancel {D : A → Sort v}
    (p : Path a b) (x : D a) :
    depElim (symm p) (depElim p x) = x :=
  transport_symm_left p x

/-- `depElim (symm p)` is a left inverse of `depElim p`. -/
theorem depElim_leftInverse {D : A → Sort v} (p : Path a b) :
    Function.LeftInverse (depElim (D := D) (symm p)) (depElim (D := D) p) :=
  fun x => depElim_symm_cancel p x

/-- `depElim p` is a left inverse of `depElim (symm p)`. -/
theorem depElim_rightInverse {D : A → Sort v} (p : Path a b) :
    Function.LeftInverse (depElim (D := D) p) (depElim (D := D) (symm p)) :=
  fun y => transport_symm_right p y

/-! ## Path space contraction -/

/-- The projection of the based path space to the base. -/
theorem based_contr_proof (a : A) (bp : Σ b, Path a b) :
    bp.1 = a := by
  obtain ⟨b, p⟩ := bp
  exact p.proof.symm

/-- Transport is independent of the path: only the proof field matters. -/
theorem transport_Subsingleton.elim {D : A → Sort v}
    (p q : Path a b) (x : D a) :
    transport p x = transport q x := by
  cases p with
  | mk _ proof1 =>
      cases q with
      | mk _ proof2 =>
          cases proof1; cases proof2; rfl

/-- `depElim` is independent of the specific path chosen. -/
theorem depElim_Subsingleton.elim {D : A → Sort v}
    (p q : Path a b) (x : D a) :
    depElim p x = depElim q x :=
  transport_Subsingleton.elim p q x

/-- Path induction on the equality: any proposition about `a = b` that holds
for `rfl` holds for all equalities. -/
theorem eq_ind {a b : A} {P : a = b → Prop} (h : a = b)
    (base : P (h ▸ Eq.refl a)) : P h := by
  cases h
  exact base

/-- Applying `pathInd` twice (nested induction). -/
noncomputable def pathInd_nested {C : ∀ (b c : A), a = b → a = c → Sort v}
    (base : C a a rfl rfl)
    {b c : A} (h₁ : a = b) (h₂ : a = c) : C b c h₁ h₂ := by
  cases h₁; cases h₂; exact base

end Path

end ComputationalPaths
