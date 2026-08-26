/-
# Reflexive/transitive rewrite closure on computational paths

Defines the `Rw` relation (the reflexive/transitive closure of `Step`) together
with its algebraic properties, higher-order transport lemmas, and normalization
infrastructure.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.Step
import ComputationalPaths.Path.Rewrite.Normalization

namespace ComputationalPaths
namespace Path

universe u v w x

/-- Reflexive/transitive closure of rewrite steps (`rw`-reduction). -/
inductive Rw {A : Type u} {a b : A} : Path a b → Path a b → Prop
  | refl (p : Path a b) : Rw p p
  | tail {p q r : Path a b} : Rw p q → Step (A := A) q r → Rw p r

variable {A : Type u} {a b c : A}

@[simp] theorem rw_toEq {p q : Path a b} (h : Rw p q) :
    p.toEq = q.toEq := by
  induction h with
  | refl => rfl
  | tail h step ih =>
      exact ih.trans (step_toEq step)

@[simp] theorem rw_refl (p : Path a b) : Rw p p :=
  Rw.refl p

@[simp] theorem rw_trans {p q r : Path a b}
    (h1 : Rw p q) (h2 : Rw q r) : Rw p r :=
  match h2 with
  | Rw.refl _ => h1
  | Rw.tail h2 step => Rw.tail (rw_trans h1 h2) step

@[simp] theorem rw_of_eq {p q : Path a b} (h : p = q) : Rw p q := by
  cases h
  exact rw_refl _

@[simp] theorem rw_of_step {p q : Path a b} (h : Step p q) : Rw p q :=
  Rw.tail (Rw.refl p) h

@[simp] theorem rw_symm_trans_congr {p : Path a b} {q : Path b c} :
    Rw (symm (trans p q)) (trans (symm q) (symm p)) :=
  rw_of_step (Step.symm_trans_congr p q)

@[simp] theorem rw_congrArg_trans {B : Type v}
    {a b c : A} (f : A → B) (p : Path a b) (q : Path b c) :
    Rw (Path.congrArg f (Path.trans p q))
      (Path.trans (Path.congrArg f p) (Path.congrArg f q)) :=
  rw_of_eq (Path.congrArg_trans (f := f) (p := p) (q := q))

@[simp] theorem rw_congrArg_symm {B : Type v}
    {a b : A} (f : A → B) (p : Path a b) :
    Rw (Path.congrArg f (Path.symm p))
      (Path.symm (Path.congrArg f p)) :=
  rw_of_eq (Path.congrArg_symm (f := f) (p := p))

@[simp] theorem rw_mapLeft_trans {B : Type v} {C : Type w}
    {a1 a2 a3 : A} (f : A → B → C)
    (p : Path a1 a2) (q : Path a2 a3) (b : B) :
    Rw (Path.mapLeft f (Path.trans p q) b)
      (Path.trans (Path.mapLeft f p b) (Path.mapLeft f q b)) :=
  rw_of_eq (Path.mapLeft_trans (f := f) (p := p) (q := q) (b := b))

@[simp] theorem rw_mapLeft_symm {B : Type v} {C : Type w}
    {a1 a2 : A} (f : A → B → C)
    (p : Path a1 a2) (b : B) :
    Rw (Path.mapLeft f (Path.symm p) b)
      (Path.symm (Path.mapLeft f p b)) :=
  rw_of_eq (Path.mapLeft_symm (f := f) (p := p) (b := b))

@[simp] theorem rw_mapLeft_refl {B : Type v} {C : Type w}
    (f : A → B → C) (a : A) (b : B) :
    Rw (Path.mapLeft f (Path.refl a) b) (Path.refl (f a b)) :=
  rw_of_eq (Path.mapLeft_refl (f := f) (a := a) (b := b))

@[simp] theorem rw_mapLeft_ofEq {B : Type v} {C : Type w}
    (f : A → B → C) {a₁ a₂ : A} (h : a₁ = a₂) (b : B) :
    Rw (Path.mapLeft (A := A) (B := B) (C := C) f
          (Path.stepChain (A := A) (a := a₁) (b := a₂) h) b)
      (Path.stepChain (A := C) (a := f a₁ b) (b := f a₂ b)
        (_root_.congrArg (fun x => f x b) h)) :=
  rw_of_eq (by
    simp [Path.mapLeft, Path.stepChain, Path.congrArg, List.map])

@[simp] theorem rw_mapRight_trans {B : Type v} {C : Type w}
    {b1 b2 b3 : B} (f : A → B → C)
    (a : A) (p : Path b1 b2) (q : Path b2 b3) :
    Rw (Path.mapRight f a (Path.trans p q))
      (Path.trans (Path.mapRight f a p) (Path.mapRight f a q)) :=
  rw_of_eq (Path.mapRight_trans (f := f) (a := a) (p := p) (q := q))

@[simp] theorem rw_mapRight_refl {B : Type v} {C : Type w}
    (f : A → B → C) (a : A) (b : B) :
    Rw (Path.mapRight f a (Path.refl b)) (Path.refl (f a b)) :=
  rw_of_eq (Path.mapRight_refl (f := f) (a := a) (b := b))

@[simp] theorem rw_mapRight_ofEq {B : Type v} {C : Type w}
    (f : A → B → C) (a : A) {b₁ b₂ : B} (h : b₁ = b₂) :
    Rw (Path.mapRight (A := A) (B := B) (C := C) f a
          (Path.stepChain (A := B) (a := b₁) (b := b₂) h))
      (Path.stepChain (A := C) (a := f a b₁) (b := f a b₂)
        (_root_.congrArg (f a) h)) :=
  rw_of_eq (by
    simp [Path.mapRight, Path.stepChain, Path.congrArg, List.map])

@[simp] theorem rw_map2_trans
    {A₁ : Type u} {B : Type u}
    {a1 a2 a3 : A₁} {b1 b2 b3 : B}
    (f : A₁ → B → A)
    (p1 : Path (A := A₁) a1 a2) (p2 : Path (A := A₁) a2 a3)
    (q1 : Path (A := B) b1 b2) (q2 : Path (A := B) b2 b3) :
    Rw
      (Path.map2 (A := A₁) (B := B) (C := A) f
        (Path.trans p1 p2) (Path.trans q1 q2))
      (Path.trans
        (Path.mapLeft (A := A₁) (B := B) (C := A) f p1 b1)
        (Path.trans
          (Path.mapLeft (A := A₁) (B := B) (C := A) f p2 b1)
          (Path.trans
            (Path.mapRight (A := A₁) (B := B) (C := A) f a3 q1)
            (Path.mapRight (A := A₁) (B := B) (C := A) f a3 q2)))) :=
  rw_of_eq
    (Path.map2_trans (A := A₁) (B := B) (C := A) (f := f)
      (p1 := p1) (p2 := p2) (q1 := q1) (q2 := q2))

@[simp] theorem rw_map2_refl
    {A₁ : Type u} {B : Type u} (f : A₁ → B → A) (a : A₁) (b : B) :
    Rw (Path.map2 (A := A₁) (B := B) (C := A) f (Path.refl a) (Path.refl b))
      (Path.refl (f a b)) :=
  rw_of_eq (Path.map2_refl (A := A₁) (B := B) (C := A) (f := f) (a := a) (b := b))

@[simp] theorem rw_mapRight_symm {B : Type v} {C : Type w}
    {b1 b2 : B} (f : A → B → C)
    (a : A) (p : Path b1 b2) :
    Rw (Path.mapRight f a (Path.symm p))
      (Path.symm (Path.mapRight f a p)) :=
  rw_of_eq (Path.mapRight_symm (f := f) (a := a) (p := p))

/-- Subterm substitution for `map2`. -/
@[simp] theorem rw_map2_subst
    {A₁ : Type u} {B : Type u}
    {a1 a2 : A₁} {b1 b2 : B}
    (f : A₁ → B → A)
    (p : Path (A := A₁) a1 a2)
    (q : Path (A := B) b1 b2) :
    Rw
      (Path.map2 (A := A₁) (B := B) (C := A) f p q)
      (Path.trans
        (Path.mapRight (A := A₁) (B := B) (C := A) f a1 q)
        (Path.mapLeft (A := A₁) (B := B) (C := A) f p b2)) :=
  rw_of_step (Step.map2_subst (A₁ := A₁) (B := B) (f := f) p q)

@[simp] theorem rw_transport_refl_beta
    {A : Type u} {B : A → Type u}
    {a : A} (x : B a) :
    Rw
      (Path.stepChain (A := B a)
        (a := transport (A := A) (D := fun t => B t)
                (Path.refl a) x)
        (b := x)
        (transport_refl (A := A) (D := fun t => B t)
          (a := a) (x := x)))
      (Path.refl x) :=
  rw_of_step (Step.transport_refl_beta (A := A) (B := B) (a := a) x)

@[simp] theorem rw_context_subst_left_beta
    {A : Type u} {B : Type u}
    (C : Context A B) {x : B} {a₁ a₂ : A}
    (r : Path x (C.fill a₁)) (p : Path a₁ a₂) :
    Rw (Path.trans r (Context.map (A := A) (B := B) C p))
      (Context.substLeft (A := A) (B := B) C r p) :=
  rw_of_step
    (Step.context_subst_left_beta (A := A) (B := B) C r p)

@[simp] theorem rw_context_subst_left_of_right
    {A : Type u} {B : Type u}
    (C : Context A B) {x : B} {a₁ a₂ : A}
    (r : Path x (C.fill a₁)) (p : Path a₁ a₂) :
    Rw (Path.trans r
        (Context.substRight (A := A) (B := B) C p
          (Path.refl (C.fill a₂))))
      (Context.substLeft (A := A) (B := B) C r p) :=
  rw_of_step
    (Step.context_subst_left_of_right (A := A) (B := B) C r p)

@[simp] theorem rw_context_subst_left_assoc
    {A : Type u} {B : Type u}
    (C : Context A B) {x : B} {a₁ a₂ : A} {y : B}
    (r : Path x (C.fill a₁)) (p : Path a₁ a₂)
    (t : Path (C.fill a₂) y) :
    Rw (Path.trans
        (Context.substLeft (A := A) (B := B) C r p) t)
      (Path.trans r
        (Context.substRight (A := A) (B := B) C p t)) :=
  rw_of_step
    (Step.context_subst_left_assoc (A := A) (B := B) C r p t)

@[simp] theorem rw_context_subst_right_assoc
    {A : Type u} {B : Type u}
    (C : Context A B) {a₁ a₂ : A} {y z : B}
    (p : Path a₁ a₂) (t : Path (C.fill a₂) y)
    (u : Path y z) :
    Rw (Path.trans
        (Context.substRight (A := A) (B := B) C p t) u)
      (Context.substRight (A := A) (B := B) C p (Path.trans t u)) :=
  rw_of_step
    (Step.context_subst_right_assoc (A := A) (B := B) C p t u)

@[simp] theorem rw_depContext_map_of_rw {A : Type u} {B : A → Type u}
  (C : DepContext A B) {a₁ a₂ : A}
  {p q : Path a₁ a₂} (h : Rw (A := A) p q) :
  Rw (DepContext.map (A := A) (B := B) C p)
    (DepContext.map (A := A) (B := B) C q) := by
  induction h with
  | refl =>
      exact Rw.refl _
  | tail _ step ih =>
      exact Rw.tail ih
        (Step.depContext_congr (A := A) (B := B) (C := C) step)

@[simp] theorem rw_depContext_subst_left_beta
  {A : Type u} {B : A → Type u}
    (C : DepContext A B) {a₁ a₂ : A} {x : B a₁}
    (r : Path (A := B a₁) x (C.fill a₁)) (p : Path a₁ a₂) :
    Rw (Path.trans
          (Context.map (A := B a₁) (B := B a₂)
            (DepContext.transportContext (A := A) (B := B) p) r)
          (DepContext.map (A := A) (B := B) C p))
      (DepContext.substLeft (A := A) (B := B) C r p) :=
  rw_of_step
    (Step.depContext_subst_left_beta (A := A) (B := B) C r p)

@[simp] theorem rw_depContext_subst_left_assoc
  {A : Type u} {B : A → Type u}
    (C : DepContext A B) {a₁ a₂ : A} {x : B a₁} {y : B a₂}
    (r : Path (A := B a₁) x (C.fill a₁)) (p : Path a₁ a₂)
    (t : Path (A := B a₂) (C.fill a₂) y) :
    Rw (Path.trans
        (DepContext.substLeft (A := A) (B := B) C r p) t)
      (Path.trans
        (Context.map (A := B a₁) (B := B a₂)
          (DepContext.transportContext (A := A) (B := B) p) r)
        (DepContext.substRight (A := A) (B := B) C p t)) :=
  rw_of_step
    (Step.depContext_subst_left_assoc (A := A) (B := B) C r p t)

@[simp] theorem rw_depContext_subst_right_beta
  {A : Type u} {B : A → Type u}
    (C : DepContext A B) {a₁ a₂ : A} {y : B a₂}
    (p : Path a₁ a₂)
    (t : Path (A := B a₂) (C.fill a₂) y) :
    Rw (Path.trans
        (DepContext.map (A := A) (B := B) C p) t)
      (DepContext.substRight (A := A) (B := B) C p t) :=
  rw_of_step
    (Step.depContext_subst_right_beta (A := A) (B := B) C p t)

@[simp] theorem rw_depContext_subst_right_assoc
    {A : Type u} {B : A → Type u}
    (C : DepContext A B) {a₁ a₂ : A} {y z : B a₂}
    (p : Path a₁ a₂)
    (t : Path (A := B a₂) (C.fill a₂) y)
    (u : Path (A := B a₂) y z) :
    Rw (Path.trans
        (DepContext.substRight (A := A) (B := B) C p t) u)
      (DepContext.substRight (A := A) (B := B) C p
        (Path.trans t u)) :=
  rw_of_step
    (Step.depContext_subst_right_assoc (A := A) (B := B) C p t u)

@[simp] theorem rw_depContext_subst_left_refl_right
    {A : Type u} {B : A → Type u}
    (C : DepContext A B) {a : A} {x : B a}
    (r : Path (A := B a) x (C.fill a)) :
    Rw (DepContext.substLeft (A := A) (B := B) C r (Path.refl a))
      r :=
  rw_of_step
    (Step.depContext_subst_left_refl_right (A := A) (B := B) C r)

@[simp] theorem rw_depContext_subst_left_refl_left
    {A : Type u} {B : A → Type u}
    (C : DepContext A B) {a₁ a₂ : A}
    (p : Path a₁ a₂) :
    Rw (DepContext.substLeft (A := A) (B := B) C
        (Path.refl (C.fill a₁)) p)
      (DepContext.map (A := A) (B := B) C p) :=
  rw_of_step
    (Step.depContext_subst_left_refl_left (A := A) (B := B) C p)

@[simp] theorem rw_depContext_subst_right_refl_left
    {A : Type u} {B : A → Type u}
    (C : DepContext A B) {a : A} {y : B a}
    (r : Path (A := B a) (C.fill a) y) :
    Rw (DepContext.substRight (A := A) (B := B) C
        (Path.refl a) r) r :=
  rw_of_step
    (Step.depContext_subst_right_refl_left (A := A) (B := B) C r)

@[simp] theorem rw_depContext_subst_right_refl_right
    {A : Type u} {B : A → Type u}
    (C : DepContext A B) {a₁ a₂ : A}
    (p : Path a₁ a₂) :
    Rw (DepContext.substRight (A := A) (B := B) C p
        (Path.refl (C.fill a₂)))
      (DepContext.map (A := A) (B := B) C p) :=
  rw_of_step
    (Step.depContext_subst_right_refl_right (A := A) (B := B) C p)

@[simp] theorem rw_depContext_subst_left_idempotent
    {A : Type u} {B : A → Type u}
    (C : DepContext A B) {a₁ a₂ : A} {x : B a₁}
    (r : Path (A := B a₁) x (C.fill a₁)) (p : Path a₁ a₂) :
    Rw (DepContext.substLeft (A := A) (B := B) C
        (DepContext.substLeft (A := A) (B := B) C r (Path.refl a₁)) p)
      (DepContext.substLeft (A := A) (B := B) C r p) :=
  rw_of_step
    (Step.depContext_subst_left_idempotent (A := A) (B := B) C r p)

@[simp] theorem rw_depContext_subst_right_cancel_inner
    {A : Type u} {B : A → Type u}
    (C : DepContext A B) {a₁ a₂ : A} {y : B a₂}
    (p : Path a₁ a₂) (t : Path (A := B a₂) (C.fill a₂) y) :
    Rw (DepContext.substRight (A := A) (B := B) C p
        (DepContext.substRight (A := A) (B := B) C (Path.refl a₂) t))
      (DepContext.substRight (A := A) (B := B) C p t) :=
  rw_of_step
    (Step.depContext_subst_right_cancel_inner (A := A) (B := B) C p t)

@[simp] theorem rw_trans_congr_left {a b c : A}
  {p q : Path a b} (r : Path b c) (h : Rw p q) :
  Rw (Path.trans p r) (Path.trans q r) := by
  induction h with
  | refl =>
    exact Rw.refl (Path.trans p r)
  | tail _ step ih =>
    exact Rw.tail ih (Step.trans_congr_left r step)

@[simp] theorem rw_trans_congr_right {a b c : A}
  (p : Path a b) {q r : Path b c} (h : Rw q r) :
  Rw (Path.trans p q) (Path.trans p r) := by
  induction h with
  | refl =>
    exact Rw.refl (Path.trans p q)
  | tail _ step ih =>
    exact Rw.tail ih (Step.trans_congr_right p step)

@[simp] theorem rw_symm_congr {a b : A} {p q : Path a b} (h : Rw p q) :
  Rw (Path.symm p) (Path.symm q) := by
  induction h with
  | refl =>
    exact Rw.refl (Path.symm p)
  | tail _ step ih =>
    exact Rw.tail ih (Step.symm_congr step)

/-- A unary action on paths that is compatible with rewrite steps. -/
structure RewriteLift (A : Type u) (B : Type u) where
  /-- Object function describing how endpoints are transported. -/
  obj : A → B
  /-- Map a path in `A` to a path in `B`. -/
  map :
    ∀ {a b : A},
      Path (A := A) a b → Path (A := B) (obj a) (obj b)
  /-- Transport of rewrite steps along the action. -/
  step_congr :
    ∀ {a b : A} {p q : Path (A := A) a b},
      Step (A := A) p q →
        Step (A := B) (map p) (map q)

namespace RewriteLift

variable {A : Type u} {B : Type u}

@[simp] theorem rw_of_rw (F : RewriteLift A B)
    {a b : A} {p q : Path (A := A) a b}
    (h : Rw (A := A) p q) :
    Rw (A := B) (F.map p) (F.map q) := by
  induction h with
  | refl =>
      exact Rw.refl (F.map p)
  | tail _ step ih =>
      exact Rw.tail ih (F.step_congr step)

@[simp] noncomputable def ofContext (C : Context A B) : RewriteLift A B where
  obj := C.fill
  map := fun {_ _} p => Context.map (A := A) (B := B) C p
  step_congr := fun {_ _ _ _} step =>
    Step.context_congr (A := A) (B := B) C step

@[simp] noncomputable def ofBiContextLeft (K : BiContext A B C) (b₀ : B) :
  RewriteLift A C where
  obj := fun a => K.fill a b₀
  map := fun {_ _} p =>
    BiContext.mapLeft (A := A) (B := B) (C := C) K p b₀
  step_congr := fun {_ _ _ _} step =>
    Step.biContext_mapLeft_congr (A := A) (B := B) (C := C)
      (K := K) (b := b₀) step

@[simp] noncomputable def ofBiContextRight (K : BiContext A B C) (a : A) :
  RewriteLift B C where
  obj := fun b => K.fill a b
  map := fun {_ _} p =>
    BiContext.mapRight (A := A) (B := B) (C := C) K a p
  step_congr := fun {_ _ _ _} step =>
    Step.biContext_mapRight_congr (A := A) (B := B) (C := C)
      (K := K) (a := a) step

end RewriteLift

@[simp] theorem rw_context_map_of_rw {A : Type u} {B : Type u}
  (Ctx : Context A B) {a₁ a₂ : A}
  {p q : Path a₁ a₂} (h : Rw (A := A) p q) :
  Rw (Context.map (A := A) (B := B) Ctx p)
    (Context.map (A := A) (B := B) Ctx q) := by
  simpa using
    (RewriteLift.ofContext (A := A) (B := B) Ctx).rw_of_rw h

@[simp] theorem rw_biContext_mapLeft_of_rw {A : Type u} {B : Type u} {C : Type u}
  (K : BiContext A B C) {a₁ a₂ : A} (b : B)
  {p q : Path a₁ a₂} (h : Rw (A := A) p q) :
  Rw (BiContext.mapLeft (A := A) (B := B) (C := C) K p b)
    (BiContext.mapLeft (A := A) (B := B) (C := C) K q b) := by
  simpa using
    (RewriteLift.ofBiContextLeft (A := A) (B := B) (C := C)
      (K := K) (b₀ := b)).rw_of_rw h

@[simp] theorem rw_biContext_mapRight_of_rw {A : Type u} {B : Type u} {C : Type u}
  (K : BiContext A B C) (a : A) {b₁ b₂ : B}
  {p q : Path b₁ b₂} (h : Rw (A := B) p q) :
  Rw (BiContext.mapRight (A := A) (B := B) (C := C) K a p)
    (BiContext.mapRight (A := A) (B := B) (C := C) K a q) := by
  simpa using
    (RewriteLift.ofBiContextRight (A := A) (B := B) (C := C)
      (K := K) (a := a)).rw_of_rw h

@[simp] theorem rw_biContext_map2_left_of_rw {A : Type u} {B : Type u} {C : Type u}
  (K : BiContext A B C) {a₁ a₂ : A} {b₁ b₂ : B}
  {p q : Path a₁ a₂} (r : Path b₁ b₂) (h : Rw (A := A) p q) :
  Rw (BiContext.map2 (A := A) (B := B) (C := C) K p r)
    (BiContext.map2 (A := A) (B := B) (C := C) K q r) := by
  induction h with
  | refl =>
      exact Rw.refl (BiContext.map2 (A := A) (B := B) (C := C) K p r)
  | tail _ step ih =>
      exact Rw.tail ih
        (Step.biContext_map2_congr_left (A := A) (B := B) (C := C)
          (K := K) (r := r) step)

@[simp] theorem rw_biContext_map2_right_of_rw {A : Type u} {B : Type u} {C : Type u}
  (K : BiContext A B C) {a₁ a₂ : A} {b₁ b₂ : B}
  (p : Path a₁ a₂) {q r : Path b₁ b₂} (h : Rw (A := B) q r) :
  Rw (BiContext.map2 (A := A) (B := B) (C := C) K p q)
    (BiContext.map2 (A := A) (B := B) (C := C) K p r) := by
  induction h with
  | refl =>
      exact Rw.refl (BiContext.map2 (A := A) (B := B) (C := C) K p q)
  | tail _ step ih =>
      exact Rw.tail ih
        (Step.biContext_map2_congr_right (A := A) (B := B) (C := C)
          (K := K) (p := p) step)

@[simp] theorem rw_biContext_map2_of_rw {A : Type u} {B : Type u} {C : Type u}
  (K : BiContext A B C) {a₁ a₂ : A} {b₁ b₂ : B}
  {p q : Path a₁ a₂} {r s : Path b₁ b₂}
  (hp : Rw (A := A) p q) (hq : Rw (A := B) r s) :
  Rw (BiContext.map2 (A := A) (B := B) (C := C) K p r)
    (BiContext.map2 (A := A) (B := B) (C := C) K q s) := by
  refine (rw_trans (A := C)
    (a := K.fill a₁ b₁)
    (b := K.fill a₂ b₂)
    (p := BiContext.map2 (A := A) (B := B) (C := C) K p r)
    (q := BiContext.map2 (A := A) (B := B) (C := C) K q r)
    (r := BiContext.map2 (A := A) (B := B) (C := C) K q s) ?_ ?_)
  · exact
      (rw_biContext_map2_left_of_rw (A := A) (B := B) (C := C)
        (K := K) (r := r) hp)
  · exact
      (rw_biContext_map2_right_of_rw (A := A) (B := B) (C := C)
        (K := K) (p := q) hq)

@[simp] theorem rw_mapLeft_of_rw {B : Type u}
  (f : A → B → A) {a₁ a₂ : A} (b : B)
  {p q : Path a₁ a₂} (h : Rw p q) :
  Rw (Path.mapLeft f p b) (Path.mapLeft f q b) := by
  classical
  let Ctx : Context A A := ⟨fun a => f a b⟩
  simpa [Ctx, Context.map, Path.mapLeft] using
    (rw_context_map_of_rw (A := A) (B := A) (Ctx := Ctx) h)

@[simp] theorem rw_mapRight_of_rw
  (f : A → A → A) (a : A) {b₁ b₂ : A}
  {p q : Path b₁ b₂} (h : Rw p q) :
  Rw (Path.mapRight f a p) (Path.mapRight f a q) := by
  classical
  let Ctx : Context A A := ⟨fun b => f a b⟩
  simpa [Ctx, Context.map, Path.mapRight] using
    (rw_context_map_of_rw (A := A) (B := A) (Ctx := Ctx) h)

@[simp] theorem rw_map2_of_rw {A : Type u} {B : Type u} {C : Type u}
  (f : A → B → C) {a₁ a₂ : A} {b₁ b₂ : B}
  {p q : Path a₁ a₂} {r s : Path b₁ b₂}
  (hp : Rw (A := A) p q) (hq : Rw (A := B) r s) :
  Rw (Path.map2 (A := A) (B := B) (C := C) f p r)
    (Path.map2 (A := A) (B := B) (C := C) f q s) := by
  simpa using
    (rw_biContext_map2_of_rw
      (A := A) (B := B) (C := C) (K := ⟨f⟩)
      (p := p) (q := q) (r := r) (s := s) hp hq)

@[simp] theorem rw_map2_symm
    {A₁ : Type u} {B : Type u}
    {a1 a2 : A₁} {b1 b2 : B}
    (f : A₁ → B → A)
    (p : Path (A := A₁) a1 a2)
    (q : Path (A := B) b1 b2) :
    Rw
      (Path.map2 (A := A₁) (B := B) (C := A) f (Path.symm p) (Path.symm q))
      (Path.symm (Path.map2 (A := A₁) (B := B) (C := A) f p q)) := by
  have h :=
    rw_of_step
      (Step.map2_subst (A₁ := A₁) (B := B) (f := f)
        (p := Path.symm p) (q := Path.symm q))
  have h2 :=
    Path.map2_symm (A := A₁) (B := B) (C := A) f p q
  exact rw_trans h (rw_of_eq h2.symm)

@[simp] theorem rw_sr {A : Type u} (a : A) :
    Rw (Path.symm (Path.refl a)) (Path.refl a) :=
  rw_of_step (Step.symm_refl (A := A) a)

@[simp] theorem rw_ss {A : Type u} {a b : A} (p : Path a b) :
    Rw (Path.symm (Path.symm p)) p :=
  rw_of_step (Step.symm_symm (A := A) (p := p))

@[simp] theorem rw_tt {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Rw (Path.trans (Path.trans p q) r)
      (Path.trans p (Path.trans q r)) :=
  rw_of_step (Step.trans_assoc (A := A) (a := a) (b := b)
    (c := c) (d := d) p q r)

@[simp] theorem rw_cmpA_refl_left {A : Type u} {a b : A}
    (p : Path a b) :
    Rw (Path.trans (Path.refl a) p) p :=
  rw_of_step (Step.trans_refl_left (A := A) (a := a) (b := b) p)

@[simp] theorem rw_cmpA_refl_right {A : Type u} {a b : A}
    (p : Path a b) :
    Rw (Path.trans p (Path.refl b)) p :=
  rw_of_step (Step.trans_refl_right (A := A) (a := a) (b := b) p)

@[simp] theorem rw_cmpA_inv_right {A : Type u} {a b : A}
    (p : Path a b) :
    Rw (Path.trans p (Path.symm p)) (Path.refl a) :=
  rw_of_step (Step.trans_symm (A := A) (a := a) (b := b) p)

@[simp] theorem rw_cmpA_inv_left {A : Type u} {a b : A}
    (p : Path a b) :
    Rw (Path.trans (Path.symm p) p) (Path.refl b) :=
  rw_of_step (Step.symm_trans (A := A) (a := a) (b := b) p)

@[simp] theorem rw_prod_fst_beta {A : Type u} {B : Type u}
    {a1 a2 : A} {b1 b2 : B}
    (p : Path a1 a2) (q : Path b1 b2) :
    Rw (Path.congrArg Prod.fst
        (Path.map2 (A := A) (B := B) (C := Prod A B) Prod.mk p q)) p :=
  rw_of_step (Step.prod_fst_beta (B := B) p q)

@[simp] theorem rw_prod_snd_beta {B : Type u} {A : Type u}
    {a1 a2 : B} {b1 b2 : A}
    (p : Path a1 a2) (q : Path b1 b2) :
    Rw (Path.congrArg Prod.snd
        (Path.map2 (A := B) (B := A) (C := Prod B A) Prod.mk p q)) q :=
  rw_of_step (Step.prod_snd_beta (B := B) p q)

@[simp] theorem rw_prod_rec_beta {α β : Type u} {A : Type u}
    (f : α → β → A)
    {a1 a2 : α} {b1 b2 : β}
    (p : Path a1 a2) (q : Path b1 b2) :
    Rw
      (Path.congrArg (Prod.rec f)
        (Path.map2 (A := α) (B := β) (C := Prod α β) Prod.mk p q))
      (Path.map2 (A := α) (B := β) (C := A) f p q) :=
  rw_of_step (Step.prod_rec_beta (α := α) (β := β) (f := f) p q)

@[simp] theorem rw_prod_eta {α β : Type u}
    {a₁ a₂ : α} {b₁ b₂ : β}
    (p : Path (A := Prod α β) (a₁, b₁) (a₂, b₂)) :
    Rw (Path.prodMk (Path.fst p) (Path.snd p)) p :=
  rw_of_step (Step.prod_eta (α := α) (β := β) p)

@[simp] theorem rw_sigma_fst_beta {A : Type u} {B : A → Type u}
    {a1 a2 : A} {b1 : B a1} {b2 : B a2}
    (p : Path a1 a2)
    (q : Path (transport (A := A) (D := fun a => B a) p b1) b2) :
    Rw
      (Path.congrArg Sigma.fst
        (Path.sigmaMk (B := B) p q))
      (Path.stepChain (A := A) p.toEq) :=
  rw_of_step (Step.sigma_fst_beta (A := A) (B := B) p q)

@[simp] theorem rw_sigma_snd_beta {A : Type u} {B : A → Type u}
    {a1 a2 : A} {b1 : B a1} {b2 : B a2}
    (p : Path a1 a2)
    (q : Path (transport (A := A) (D := fun a => B a) p b1) b2) :
    Rw
      (Path.sigmaSnd (B := B) (Path.sigmaMk (B := B) p q))
      (Path.stepChain
        (A := B a2)
        (a := transport (A := A) (D := fun a => B a)
              (Path.sigmaFst (B := B) (Path.sigmaMk (B := B) p q)) b1)
        (b := b2) q.toEq) :=
  rw_of_step (Step.sigma_snd_beta (A₀ := A) (B := B) p q)

@[simp] theorem rw_sigma_eta {A : Type u} {B : A → Type u}
    {a1 a2 : A} {b1 : B a1} {b2 : B a2}
    (p : Path (A := Sigma B) ⟨a1, b1⟩ ⟨a2, b2⟩) :
    Rw (Path.sigmaMk (Path.sigmaFst p) (Path.sigmaSnd p)) p :=
  rw_of_step (Step.sigma_eta (A := A) (B := B) p)

@[simp] theorem rw_apd_refl {A : Type u} {B : A → Type u}
    (f : ∀ x : A, B x) (a : A) :
    Rw
      (Path.apd (A := A) (B := B) f (Path.refl a))
      (Path.refl (f a)) :=
  rw_of_step (Step.apd_refl (A := A) (B := B) f a)

@[simp] theorem rw_sum_rec_inl_beta {α β : Type u} {A : Type u}
    {a1 a2 : α} (f : α → A) (g : β → A) (p : Path a1 a2) :
    Rw
      (Path.congrArg (Sum.rec f g)
        (Path.congrArg Sum.inl p))
      (Path.congrArg f p) :=
  rw_of_step (Step.sum_rec_inl_beta (α := α) (β := β) (f := f) (g := g) p)

@[simp] theorem rw_sum_rec_inr_beta {α β : Type u} {A : Type u}
    {b1 b2 : β} (f : α → A) (g : β → A) (p : Path b1 b2) :
    Rw
      (Path.congrArg (Sum.rec f g)
        (Path.congrArg Sum.inr p))
      (Path.congrArg g p) :=
  rw_of_step (Step.sum_rec_inr_beta (α := α) (β := β) (f := f) (g := g) p)

@[simp] theorem rw_fun_app_beta {α : Type u}
    {f g : α → A} (p : ∀ x : α, Path (f x) (g x)) (a : α) :
    Rw
      (Path.congrArg (fun h : α → A => h a)
        (Path.lamCongr (f := f) (g := g) p))
      (p a) :=
  rw_of_step (Step.fun_app_beta (A := A) (α := α) p a)

@[simp] theorem rw_fun_eta {α β : Type u}
    {f g : α → β} (p : Path f g) :
    Rw
      (Path.lamCongr (fun x => Path.app p x))
      p :=
  rw_of_step (Step.fun_eta (α := α) (β := β) (p := p))

@[simp] theorem rw_lamCongr_of_rw {A : Type u} {B : Type v}
    {f g : A → B}
    {p q : ∀ x : A, Path (f x) (g x)}
    (h : ∀ x : A, Rw (p x) (q x)) :
    Rw (Path.lamCongr p) (Path.lamCongr q) := by
  classical
  have hxProof :
      ∀ x, (p x).proof = (q x).proof := fun x => by
        have hx := rw_toEq (h x)
        cases hx
        simp
  have hx : Path.lamCongr p = Path.lamCongr q := by
    have hxFun := funext hxProof
    cases hxFun
    simp [Path.lamCongr]
  exact rw_of_eq hx

end Path
end ComputationalPaths
