/-
# Primitive rewrite steps on computational paths

This module defines the `Step` relation capturing single `rw`-style reductions
between computational paths. These are the atomic rewrites that form the basis
of the computational paths rewriting system.

## Overview

The `Step` relation implements the rewrite rules from the computational paths
theory. Each constructor corresponds to a specific algebraic law for path
operations (symmetry, transitivity, congruence, etc.).

## Rule Categories

The constructors are organized into several categories:

### Basic Path Algebra (Rules 1-8)
- `symm_refl`, `symm_symm`: Symmetry simplifications
- `trans_refl_left`, `trans_refl_right`: Identity laws for composition
- `trans_symm`, `symm_trans`: Inverse laws
- `symm_trans_congr`: Contravariance of symmetry over composition
- `trans_assoc`: Associativity of path composition

### Product Types (Rules 9-16)
- `prod_fst_beta`, `prod_snd_beta`: Projection β-rules
- `prod_rec_beta`: Recursor β-rule
- `prod_eta`: η-expansion for products
- `prod_mk_symm`, `prod_map_congrArg`: Structural rules

### Dependent Pairs / Sigma Types (Rules 17-22)
- `sigma_fst_beta`, `sigma_snd_beta`: Projection β-rules
- `sigma_eta`: η-expansion for sigma types
- `sigma_mk_symm`: Symmetry for sigma constructor

### Sum Types (Rules 23-24)
- `sum_rec_inl_beta`, `sum_rec_inr_beta`: Recursor β-rules for coproducts

### Function Types (Rules 25-28)
- `fun_app_beta`: Application β-rule
- `fun_eta`: η-expansion for functions
- `lam_congr_symm`: Symmetry for function congruence

### Dependent Application (Rule 29)
- `apd_refl`: Dependent application on reflexivity

### Transport (Rules 30-36)
- `transport_refl_beta`: Transport along reflexivity
- `transport_trans_beta`: Transport along composition
- `transport_symm_left_beta`, `transport_symm_right_beta`: Transport with symmetry
- `transport_sigmaMk_*`: Transport through sigma constructors

### Context Rules (Rules 37-52)
- `context_congr`, `context_map_symm`: Basic context operations
- `context_subst_*`: Substitution rules for contexts
- `depContext_*`: Dependent context variants
- `biContext_*`, `depBiContext_*`: Binary context rules

### Structural Rules (Rules 53-56)
- `symm_congr`, `trans_congr_left`, `trans_congr_right`: Congruence closure
- `trans_cancel_left`, `trans_cancel_right`: Completion rules for confluence

## Usage

The `Step` relation is typically used through its closures:
- `Rw`: Reflexive-transitive closure (multi-step rewriting)
- `RwEq`: Equivalence closure (bidirectional rewriting)

All rules are registered as `[simp]` lemmas via `step_toEq`.

## References

- de Queiroz, de Oliveira & Ramos, "Propositional equality, identity types,
  and direct computational paths", SAJL 2016
- Ramos et al., "Explicit Computational Paths", SAJL 2018
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Basic.Context
import ComputationalPaths.Path.Basic.Congruence
import ComputationalPaths.Path.Basic.Congruence

namespace ComputationalPaths
namespace Path

open scoped Quot

universe u v w

/-- A single rewrite step between computational paths.

Each constructor represents an atomic rewrite rule. The relation captures
the computational content of path equality: two paths are related by `Step`
if one can be obtained from the other by applying a single rewrite rule.

See the module documentation for a complete list of rule categories. -/
inductive Step :
  {A : Type u} → {a b : A} → Path a b → Path a b → Type (u + 1)
  /-- Rule 1: Symmetry of reflexivity is reflexivity. `symm(refl) ▷ refl` -/
  | symm_refl {A : Type u} (a : A) :
      Step (A := A) (symm (Path.refl a)) (Path.refl a)
  /-- Rule 2: Double symmetry cancels. `symm(symm(p)) ▷ p` -/
  | symm_symm {A : Type u} {a b : A} (p : Path a b) :
      Step (A := A) (symm (symm p)) p
  /-- Rule 3: Left identity for composition. `refl ∘ p ▷ p` -/
  | trans_refl_left {A : Type u} {a b : A} (p : Path a b) :
      Step (A := A) (trans (Path.refl a) p) p
  /-- Rule 4: Right identity for composition. `p ∘ refl ▷ p` -/
  | trans_refl_right {A : Type u} {a b : A} (p : Path a b) :
      Step (A := A) (trans p (Path.refl b)) p
  /-- Rule 5: Right inverse law. `p ∘ symm(p) ▷ refl` -/
  | trans_symm {A : Type u} {a b : A} (p : Path a b) :
      Step (A := A) (trans p (symm p)) (Path.refl a)
  /-- Rule 6: Left inverse law. `symm(p) ∘ p ▷ refl` -/
  | symm_trans {A : Type u} {a b : A} (p : Path a b) :
      Step (A := A) (trans (symm p) p) (Path.refl b)
  /-- Rule 7: Contravariance of symmetry. `symm(p ∘ q) ▷ symm(q) ∘ symm(p)` -/
  | symm_trans_congr {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
      Step (A := A) (symm (trans p q)) (trans (symm q) (symm p))
  /-- Rule 8: Associativity of composition. `(p ∘ q) ∘ r ▷ p ∘ (q ∘ r)` -/
  | trans_assoc {A : Type u} {a b c d : A}
      (p : Path a b) (q : Path b c) (r : Path c d) :
      Step (A := A) (trans (trans p q) r) (trans p (trans q r))
  /-- Rule 9: Decomposition of binary map. `map2 f p q ▷ mapRight f a₁ q ∘ mapLeft f p b₂` -/
  | map2_subst
    {A : Type u} {A₁ : Type u} {B : Type u}
      {a1 a2 : A₁} {b1 b2 : B}
      (f : A₁ → B → A)
      (p : Path (A := A₁) a1 a2)
      (q : Path (A := B) b1 b2) :
      Step (A := A)
        (Path.map2 (A := A₁) (B := B) (C := A) f p q)
        (Path.trans
          (Path.mapRight (A := A₁) (B := B) (C := A) f a1 q)
          (Path.mapLeft (A := A₁) (B := B) (C := A) f p b2))
  /-- Rule 10: First projection β-rule. `fst(mk(p, q)) ▷ p` -/
  | prod_fst_beta
    {A : Type u} {B : Type u}
      {a1 a2 : A} {b1 b2 : B}
      (p : Path a1 a2) (q : Path b1 b2) :
      Step (A := A)
        (Path.congrArg Prod.fst
          (Path.map2 (A := A) (B := B) (C := Prod A B) Prod.mk p q))
        p
  /-- Rule 11: Second projection β-rule. `snd(mk(p, q)) ▷ q` -/
  | prod_snd_beta
    {A : Type u} {B : Type u}
      {a1 a2 : B} {b1 b2 : A}
      (p : Path a1 a2) (q : Path b1 b2) :
      Step (A := A)
        (Path.congrArg Prod.snd
          (Path.map2 (A := B) (B := A) (C := Prod B A) Prod.mk p q))
        q
  /-- Rule 12: Product recursor β-rule. `rec f (mk(p, q)) ▷ map2 f p q` -/
  | prod_rec_beta
    {A : Type u} {α β : Type u}
      {a1 a2 : α} {b1 b2 : β}
      (f : α → β → A)
      (p : Path a1 a2) (q : Path b1 b2) :
      Step (A := A)
        (Path.congrArg (Prod.rec f)
          (Path.map2 (A := α) (B := β) (C := Prod α β) Prod.mk p q))
        (Path.map2 (A := α) (B := β) (C := A) f p q)
  /-- Rule 13: Product η-expansion. `mk(fst(p), snd(p)) ▷ p` -/
  | prod_eta
    {α β : Type u}
      {a₁ a₂ : α} {b₁ b₂ : β}
      (p : Path (A := Prod α β) (a₁, b₁) (a₂, b₂)) :
      Step (A := Prod α β)
        (Path.prodMk (Path.fst p) (Path.snd p)) p
  /-- Rule 14: Symmetry distributes over product constructor. `symm(mk(p, q)) ▷ mk(symm(p), symm(q))` -/
  | prod_mk_symm
    {A : Type u} {B : Type u}
      {a₁ a₂ : A} {b₁ b₂ : B}
      (p : Path a₁ a₂) (q : Path b₁ b₂) :
      Step (A := Prod A B)
        (Path.symm (Path.prodMk (p := p) (q := q)))
        (Path.prodMk (Path.symm p) (Path.symm q))
  /-- Rule 15: Componentwise map through products.
      For f(x) = (g(fst x), h(snd x)), congrArg f (mk(p,q)) ▷ mk(congrArg g p, congrArg h q) -/
  | prod_map_congrArg
    {A : Type u} {B : Type u} {A' : Type u} {B' : Type u}
      {a₁ a₂ : A} {b₁ b₂ : B}
      (g : A → A') (h : B → B')
      (p : Path a₁ a₂) (q : Path b₁ b₂) :
      Step (A := Prod A' B')
        (Path.congrArg (fun x : Prod A B => (g x.fst, h x.snd))
          (Path.prodMk p q))
        (Path.prodMk (Path.congrArg g p) (Path.congrArg h q))
  /-- Rule 16: Sigma first projection β-rule. `fst(sigmaMk(p, q)) ▷ ofEq(p.toEq)` -/
  | sigma_fst_beta
    {A : Type u} {B : A → Type u}
      {a1 a2 : A} {b1 : B a1} {b2 : B a2}
      (p : Path a1 a2)
      (q : Path (transport (A := A) (D := fun a => B a) p b1) b2) :
      Step (A := A)
        (Path.congrArg Sigma.fst
        (Path.sigmaMk (B := B) p q))
        (Path.stepChain (A := A) p.toEq)
  /-- Rule 17: Sigma second projection β-rule. Extracts the second component path. -/
  | sigma_snd_beta
    {A₀ : Type u} {B : A₀ → Type u}
      {a1 a2 : A₀} {b1 : B a1} {b2 : B a2}
      (p : Path a1 a2)
      (q :
        Path (transport (A := A₀) (D := fun a => B a) p b1) b2) :
      Step (A := B a2)
        (Path.sigmaSnd (B := B) (Path.sigmaMk (B := B) p q))
        (Path.stepChain
          (A := B a2)
          (a := transport (A := A₀) (D := fun a => B a)
                (Path.sigmaFst (B := B) (Path.sigmaMk (B := B) p q)) b1)
          (b := b2) q.toEq)
  /-- Rule 18: Sigma η-expansion. `sigmaMk(sigmaFst(p), sigmaSnd(p)) ▷ p` -/
  | sigma_eta
    {A : Type u} {B : A → Type u}
      {a1 a2 : A} {b1 : B a1} {b2 : B a2}
      (p : Path (A := Sigma B) ⟨a1, b1⟩ ⟨a2, b2⟩) :
      Step (A := Sigma B)
        (Path.sigmaMk (Path.sigmaFst p) (Path.sigmaSnd p)) p
  /-- Rule 19: Symmetry distributes over sigma constructor. -/
  | sigma_mk_symm
    {A : Type u} {B : A → Type u}
      {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
      (p : Path a₁ a₂)
      (q : Path (Path.transport (A := A) (D := fun a => B a) p b₁) b₂) :
      Step (A := Sigma B)
        (Path.symm (Path.sigmaMk (B := B) p q))
        (Path.sigmaMk (Path.symm p)
          (sigmaSymmSnd (B := B) (p := p) (q := q)))
  /-- Rule 20: Sum recursor β-rule for left injection. `rec f g (inl p) ▷ f p` -/
  | sum_rec_inl_beta
    {A : Type u} {α β : Type u}
      {a1 a2 : α}
      (f : α → A) (g : β → A)
      (p : Path a1 a2) :
      Step (A := A)
        (Path.congrArg (Sum.rec f g)
          (Path.congrArg Sum.inl p))
        (Path.congrArg f p)
  /-- Rule 21: Sum recursor β-rule for right injection. `rec f g (inr p) ▷ g p` -/
  | sum_rec_inr_beta
    {A : Type u} {α β : Type u}
      {b1 b2 : β}
      (f : α → A) (g : β → A)
      (p : Path b1 b2) :
      Step (A := A)
        (Path.congrArg (Sum.rec f g)
          (Path.congrArg Sum.inr p))
        (Path.congrArg g p)
  /-- Rule 22: Function application β-rule. `(λx.p x) a ▷ p a` -/
  | fun_app_beta
    {A : Type u} {α : Type u}
      {f g : α → A}
      (p : ∀ x : α, Path (f x) (g x)) (a : α) :
      Step (A := A)
        (Path.congrArg (fun h : α → A => h a)
          (Path.lamCongr (f := f) (g := g) p))
        (p a)
  /-- Rule 23: Function η-expansion. `λx.(app p x) ▷ p` -/
  | fun_eta
    {α β : Type u}
      {f g : α → β} (p : Path f g) :
      Step (A := α → β)
        (Path.lamCongr (fun x => Path.app p x)) p
  /-- Rule 24: Symmetry distributes into lambda. `symm(λx.p x) ▷ λx.symm(p x)` -/
  | lam_congr_symm
    {α β : Type u}
      {f g : α → β}
      (p : ∀ x : α, Path (f x) (g x)) :
      Step (A := α → β)
        (Path.symm (Path.lamCongr (f := f) (g := g) p))
        (Path.lamCongr (f := g) (g := f) (fun x => Path.symm (p x)))
  /-- Rule 25: Dependent application on reflexivity. `apd f refl ▷ refl` -/
  | apd_refl
    {A : Type u} {B : A → Type u}
      (f : ∀ x : A, B x) (a : A) :
      Step (A := B a)
        (Path.apd (A := A) (B := B) f (Path.refl a))
        (Path.refl (f a))
  /-- Rule 26: Transport along reflexivity is identity. `transport refl x ▷ x` -/
  | transport_refl_beta
    {A : Type u} {B : A → Type u}
      {a : A} (x : B a) :
      Step (A := B a)
        (Path.stepChain (A := B a)
          (a := transport (A := A) (D := fun t => B t)
                  (Path.refl a) x)
          (b := x)
          (transport_refl (A := A) (D := fun t => B t)
            (a := a) (x := x)))
        (Path.refl x)
  /-- Rule 27: Transport along composition. `transport (p∘q) x ▷ transport q (transport p x)` -/
  | transport_trans_beta
      {A : Type u} {B : A → Type u}
        {a₁ a₂ a₃ : A}
        (p : Path a₁ a₂) (q : Path a₂ a₃) (x : B a₁) :
        Step (A := B a₃)
          (Path.stepChain (A := B a₃)
            (a := Path.transport (A := A) (D := fun t => B t)
                    (Path.trans p q) x)
            (b := Path.transport (A := A) (D := fun t => B t) q
                    (Path.transport (A := A) (D := fun t => B t) p x))
            (Path.transport_trans (A := A) (D := fun t => B t)
              (p := p) (q := q) (x := x)))
          (Eq.ndrec
            (motive := fun y =>
              Path (A := B a₃)
                (Path.transport (A := A) (D := fun t => B t)
                  (Path.trans p q) x) y)
            (Path.refl
              (Path.transport (A := A) (D := fun t => B t)
                (Path.trans p q) x))
            (Path.transport_trans (A := A) (D := fun t => B t)
              (p := p) (q := q) (x := x)))
  /-- Rule 28: Left inverse for transport. `transport (symm p) (transport p x) ▷ x` -/
  | transport_symm_left_beta
      {A : Type u} {B : A → Type u}
        {a₁ a₂ : A} (p : Path a₁ a₂) (x : B a₁) :
        Step (A := B a₁)
          (Path.stepChain (A := B a₁)
            (a := Path.transport (A := A) (D := fun t => B t)
                    (Path.symm p)
                    (Path.transport (A := A) (D := fun t => B t) p x))
            (b := x)
            (Path.transport_symm_left (A := A) (D := fun t => B t)
              (p := p) (x := x)))
          (Eq.ndrec
            (motive := fun y =>
              Path (A := B a₁)
                (Path.transport (A := A) (D := fun t => B t)
                  (Path.symm p)
                  (Path.transport (A := A) (D := fun t => B t) p x)) y)
            (Path.refl
              (Path.transport (A := A) (D := fun t => B t)
                (Path.symm p)
                (Path.transport (A := A) (D := fun t => B t) p x)))
            (Path.transport_symm_left (A := A) (D := fun t => B t)
              (p := p) (x := x)))
  /-- Rule 29: Right inverse for transport. `transport p (transport (symm p) y) ▷ y` -/
  | transport_symm_right_beta
      {A : Type u} {B : A → Type u}
        {a₁ a₂ : A} (p : Path a₁ a₂) (y : B a₂) :
        Step (A := B a₂)
          (Path.stepChain (A := B a₂)
            (a := Path.transport (A := A) (D := fun t => B t) p
                    (Path.transport (A := A) (D := fun t => B t)
                      (Path.symm p) y))
            (b := y)
            (Path.transport_symm_right (A := A) (D := fun t => B t)
              (p := p) (y := y)))
          (Eq.ndrec
            (motive := fun y' =>
              Path (A := B a₂)
                (Path.transport (A := A) (D := fun t => B t) p
                  (Path.transport (A := A) (D := fun t => B t)
                    (Path.symm p) y)) y')
            (Path.refl
              (Path.transport (A := A) (D := fun t => B t) p
                (Path.transport (A := A) (D := fun t => B t)
                  (Path.symm p) y)))
            (Path.transport_symm_right (A := A) (D := fun t => B t)
              (p := p) (y := y)))
  /-- Rule 30: Transport through sigma along first projection. -/
  | transport_sigmaMk_fst_beta
      {A : Type u} {B : A → Type u}
        {D : A → Type u}
        {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
        (p : Path a₁ a₂)
        (q : Path (transport (A := A) (D := fun a => B a) p b₁) b₂)
        (x : D a₁) :
        Step (A := D a₂)
          (Path.stepChain (A := D a₂)
            (a := transport (A := Sigma B)
                    (D := fun z => D z.fst) (Path.sigmaMk (B := B) p q) x)
            (b := transport (A := A) (D := D) p x)
            (transport_sigmaMk_fst (A := A) (B := B)
              (D := D) (p := p) (q := q) (x := x)))
          (Eq.ndrec
            (motive := fun y =>
              Path (A := D a₂)
                (transport (A := Sigma B)
                  (D := fun z => D z.fst)
                  (Path.sigmaMk (B := B) p q) x) y)
            (Path.refl
              (transport (A := Sigma B)
                (D := fun z => D z.fst)
                (Path.sigmaMk (B := B) p q) x))
            (transport_sigmaMk_fst (A := A) (B := B)
              (D := D) (p := p) (q := q) (x := x)))
    | transport_sigmaMk_dep_beta
      {A : Type u} {B : A → Type u}
        {D : ∀ a, B a → Type u}
        {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
        (p : Path a₁ a₂)
        (q : Path (transport (A := A) (D := fun a => B a) p b₁) b₂)
        (x : D a₁ b₁) :
        Step (A := D a₂ b₂)
          (Path.stepChain (A := D a₂ b₂)
            (a := transport (A := Sigma B)
                    (D := fun z => D z.fst z.snd)
                    (Path.sigmaMk (B := B) p q) x)
            (b := transportSigma (A := A) (B := B) (D := D) p q x)
            (transport_sigmaMk_dep (A := A) (B := B) (D := D)
              (p := p) (q := q) (x := x)))
          (Eq.ndrec
            (motive := fun y =>
              Path (A := D a₂ b₂)
                (transport (A := Sigma B)
                  (D := fun z => D z.fst z.snd)
                  (Path.sigmaMk (B := B) p q) x) y)
            (Path.refl
              (transport (A := Sigma B)
                (D := fun z => D z.fst z.snd)
                (Path.sigmaMk (B := B) p q) x))
            (transport_sigmaMk_dep (A := A) (B := B) (D := D)
              (p := p) (q := q) (x := x)))
    | subst_sigmaMk_dep_beta
      {A : Type u} {B : A → Type u}
        {D : ∀ a, B a → Type u}
        {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
        (p : Path a₁ a₂)
        (q : Path (transport (A := A) (D := fun a => B a) p b₁) b₂)
        (x : D a₁ b₁) :
        Step (A := D a₂ b₂)
          (Path.stepChain (A := D a₂ b₂)
            (a := transport (A := Sigma B)
                    (D := fun z => D z.fst z.snd)
                    (Path.sigmaMk (B := B) p q) x)
            (b := substSigma (A := A) (B := B) (D := D) x p q)
            (subst_sigmaMk_dep (A := A) (B := B) (D := D)
              (p := p) (q := q) (x := x)))
          (Eq.ndrec
            (motive := fun y =>
              Path (A := D a₂ b₂)
                (transport (A := Sigma B)
                  (D := fun z => D z.fst z.snd)
                  (Path.sigmaMk (B := B) p q) x) y)
            (Path.refl
              (transport (A := Sigma B)
                (D := fun z => D z.fst z.snd)
                (Path.sigmaMk (B := B) p q) x))
            (subst_sigmaMk_dep (A := A) (B := B) (D := D)
              (p := p) (q := q) (x := x)))
  /-- Rule 33: Context congruence. If `p ▷ q` then `C[p] ▷ C[q]` for any context C. -/
  | context_congr
    {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A}
      {p q : Path a₁ a₂} :
      Step (A := A) p q →
        Step (A := B)
          (Context.map (A := A) (B := B) C p)
          (Context.map (A := A) (B := B) C q)
  /-- Rule 34: Symmetry commutes with context. `symm(C[p]) ▷ C[symm(p)]` -/
  | context_map_symm
    {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A}
      (p : Path a₁ a₂) :
      Step (A := B)
        (Path.symm (Context.map (A := A) (B := B) C p))
        (Context.map (A := A) (B := B) C (Path.symm p))
  /-- Rule 35: Left cancellation in context. -/
  | context_tt_cancel_left
    {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A} {y : B}
      (p : Path a₁ a₂) (v : Path (C.fill a₁) y) :
      Step (A := B)
        (Path.trans
          (Context.map (A := A) (B := B) C p)
          (Path.trans
            (Context.map (A := A) (B := B) C (Path.symm p)) v))
        (Path.trans
          (Context.map (A := A) (B := B) C
            (Path.trans p (Path.symm p)))
          v)
  /-- Rule 36: Right cancellation in context. -/
  | context_tt_cancel_right
    {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A} {x : B}
      (p : Path a₁ a₂) (v : Path x (C.fill a₁)) :
      Step (A := B)
        (Path.trans
          (Path.trans v (Context.map (A := A) (B := B) C p))
          (Context.map (A := A) (B := B) C (Path.symm p)))
        (Path.trans
          v
          (Context.map (A := A) (B := B) C
            (Path.trans p (Path.symm p))))
  /-- Rule 37: Left substitution β-rule. `r ∘ C[p] ▷ substLeft C r p` -/
  | context_subst_left_beta
    {A : Type u} {B : Type u}
      (C : Context A B) {x : B} {a₁ a₂ : A}
      (r : Path x (C.fill a₁)) (p : Path a₁ a₂) :
      Step (A := B)
        (Path.trans r (Context.map (A := A) (B := B) C p))
        (Context.substLeft (A := A) (B := B) C r p)
  /-- Rule 38: Relating left and right substitution. -/
  | context_subst_left_of_right
    {A : Type u} {B : Type u}
      (C : Context A B) {x : B} {a₁ a₂ : A}
      (r : Path x (C.fill a₁)) (p : Path a₁ a₂) :
      Step (A := B)
        (Path.trans r
          (Context.substRight (A := A) (B := B) C p
            (Path.refl (C.fill a₂))))
        (Context.substLeft (A := A) (B := B) C r p)
  /-- Rule 39: Associativity for left substitution. -/
  | context_subst_left_assoc
    {A : Type u} {B : Type u}
      (C : Context A B) {x : B} {a₁ a₂ : A} {y : B}
      (r : Path x (C.fill a₁)) (p : Path a₁ a₂)
      (t : Path (C.fill a₂) y) :
      Step (A := B)
        (Path.trans (Context.substLeft (A := A) (B := B) C r p) t)
        (Path.trans r
          (Context.substRight (A := A) (B := B) C p t))
  /-- Rule 40: Right substitution β-rule. `C[p] ∘ t ▷ substRight C p t` -/
  | context_subst_right_beta
    {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A} {y : B}
      (p : Path a₁ a₂) (t : Path (C.fill a₂) y) :
      Step (A := B)
        (Path.trans (Context.map (A := A) (B := B) C p) t)
        (Context.substRight (A := A) (B := B) C p t)
  /-- Rule 41: Associativity for right substitution. -/
  | context_subst_right_assoc
    {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A} {y z : B}
      (p : Path a₁ a₂) (t : Path (C.fill a₂) y)
      (u : Path y z) :
      Step (A := B)
        (Path.trans
          (Context.substRight (A := A) (B := B) C p t) u)
        (Context.substRight (A := A) (B := B) C p
          (Path.trans t u))
  /-- Rule 42: Left substitution with refl on right simplifies. `substLeft C r refl ▷ r` -/
  | context_subst_left_refl_right
    {A : Type u} {B : Type u}
      (C : Context A B) {x : B} {a : A}
      (r : Path x (C.fill a)) :
      Step (A := B)
        (Context.substLeft C r (Path.refl a)) r
  /-- Rule 43: Left substitution with refl on left simplifies. `substLeft C refl p ▷ C[p]` -/
  | context_subst_left_refl_left
    {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A}
      (p : Path a₁ a₂) :
      Step (A := B)
        (Context.substLeft C (Path.refl (C.fill a₁)) p)
        (Context.map C p)
  /-- Rule 44: Right substitution with refl on left simplifies. `substRight C refl r ▷ r` -/
  | context_subst_right_refl_left
    {A : Type u} {B : Type u}
      (C : Context A B) {a : A} {y : B}
      (r : Path (C.fill a) y) :
      Step (A := B)
        (Context.substRight C (Path.refl a) r) r
  /-- Rule 45: Right substitution with refl on right simplifies. `substRight C p refl ▷ C[p]` -/
  | context_subst_right_refl_right
    {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A}
      (p : Path a₁ a₂) :
      Step (A := B)
        (Context.substRight C p (Path.refl (C.fill a₂)))
        (Context.map C p)
  /-- Rule 46: Idempotence for nested left substitutions. -/
  | context_subst_left_idempotent
    {A : Type u} {B : Type u}
      (C : Context A B) {x : B} {a₁ a₂ : A}
      (r : Path x (C.fill a₁)) (p : Path a₁ a₂) :
      Step (A := B)
        (Context.substLeft C
          (Context.substLeft C r (Path.refl a₁)) p)
        (Context.substLeft C r p)
  /-- Rule 47: Inner cancellation for nested right substitutions. -/
  | context_subst_right_cancel_inner
    {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A} {y : B}
      (p : Path a₁ a₂) (t : Path (C.fill a₂) y) :
      Step (A := B)
        (Context.substRight C p
          (Context.substRight C (Path.refl a₂) t))
        (Context.substRight C p t)
  /-- Rule 48: Outer cancellation for nested right substitutions. -/
  | context_subst_right_cancel_outer
    {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A} {y : B}
      (p : Path a₁ a₂) (t : Path (C.fill a₂) y) :
      Step (A := B)
        (Context.substRight C (Path.refl a₁)
          (Context.substRight C p t))
        (Context.substRight C p t)
  /-- Rule 49: Dependent context congruence. If `p ▷ q` then `C[p] ▷ C[q]` for dependent context C. -/
  | depContext_congr
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a₁ a₂ : A}
      {p q : Path a₁ a₂} :
      Step (A := A) p q →
        Step (A := B a₂)
          (DepContext.map (A := A) (B := B) C p)
          (DepContext.map (A := A) (B := B) C q)
  /-- Rule 50: Symmetry with dependent context. `symm(C[p]) ▷ C.symmMap(p)` -/
  | depContext_map_symm
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a₁ a₂ : A}
      (p : Path a₁ a₂) :
      Step (A := B a₂)
        (Path.symm (DepContext.map (A := A) (B := B) C p))
        (DepContext.symmMap (A := A) (B := B) C p)
  /-- Rule 51: Dependent context left substitution β-rule. -/
  | depContext_subst_left_beta
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a₁ a₂ : A} {x : B a₁}
      (r : Path (A := B a₁) x (C.fill a₁)) (p : Path a₁ a₂) :
      Step (A := B a₂)
        (Path.trans
          (Context.map (A := B a₁) (B := B a₂)
            (DepContext.transportContext (A := A) (B := B) p) r)
          (DepContext.map (A := A) (B := B) C p))
        (DepContext.substLeft (A := A) (B := B) C r p)
  /-- Rule 52: Dependent context left substitution associativity. -/
  | depContext_subst_left_assoc
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a₁ a₂ : A} {x : B a₁} {y : B a₂}
      (r : Path (A := B a₁) x (C.fill a₁)) (p : Path a₁ a₂)
      (t : Path (A := B a₂) (C.fill a₂) y) :
      Step (A := B a₂)
        (Path.trans
          (DepContext.substLeft (A := A) (B := B) C r p) t)
        (Path.trans
          (Context.map (A := B a₁) (B := B a₂)
            (DepContext.transportContext (A := A) (B := B) p) r)
          (DepContext.substRight (A := A) (B := B) C p t))
  /-- Rule 53: Dependent context right substitution β-rule. -/
  | depContext_subst_right_beta
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a₁ a₂ : A} {y : B a₂}
      (p : Path a₁ a₂)
      (t : Path (A := B a₂) (C.fill a₂) y) :
      Step (A := B a₂)
        (Path.trans
          (DepContext.map (A := A) (B := B) C p) t)
        (DepContext.substRight (A := A) (B := B) C p t)
  /-- Rule 54: Dependent context right substitution associativity. -/
  | depContext_subst_right_assoc
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a₁ a₂ : A} {y z : B a₂}
      (p : Path a₁ a₂)
      (t : Path (A := B a₂) (C.fill a₂) y)
      (u : Path (A := B a₂) y z) :
      Step (A := B a₂)
        (Path.trans
          (DepContext.substRight (A := A) (B := B) C p t) u)
        (DepContext.substRight (A := A) (B := B) C p
          (Path.trans t u))
  /-- Rule 55: Dependent left substitution with refl simplifies. -/
  | depContext_subst_left_refl_right
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a : A} {x : B a}
      (r : Path (A := B a) x (C.fill a)) :
      Step (A := B a)
        (DepContext.substLeft (A := A) (B := B) C r (Path.refl a)) r
  /-- Rule 56: Dependent left substitution with refl on left simplifies. -/
  | depContext_subst_left_refl_left
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a₁ a₂ : A}
      (p : Path a₁ a₂) :
      Step (A := B a₂)
        (DepContext.substLeft (A := A) (B := B) C
          (Path.refl (C.fill a₁)) p)
        (DepContext.map (A := A) (B := B) C p)
  /-- Rule 57: Dependent right substitution with refl simplifies. -/
  | depContext_subst_right_refl_left
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a : A} {y : B a}
      (r : Path (A := B a) (C.fill a) y) :
      Step (A := B a)
        (DepContext.substRight (A := A) (B := B) C
          (Path.refl a) r) r
  /-- Rule 58: Dependent right substitution with refl on right simplifies. -/
  | depContext_subst_right_refl_right
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a₁ a₂ : A}
      (p : Path a₁ a₂) :
      Step (A := B a₂)
        (DepContext.substRight (A := A) (B := B) C p
          (Path.refl (C.fill a₂)))
        (DepContext.map (A := A) (B := B) C p)
  /-- Rule 59: Idempotence for nested dependent left substitutions. -/
  | depContext_subst_left_idempotent
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a₁ a₂ : A} {x : B a₁}
      (r : Path (A := B a₁) x (C.fill a₁))
      (p : Path a₁ a₂) :
      Step (A := B a₂)
        (DepContext.substLeft (A := A) (B := B) C
          (DepContext.substLeft (A := A) (B := B) C r (Path.refl a₁)) p)
        (DepContext.substLeft (A := A) (B := B) C r p)
  /-- Rule 60: Inner cancellation for nested dependent right substitutions. -/
  | depContext_subst_right_cancel_inner
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a₁ a₂ : A} {y : B a₂}
      (p : Path a₁ a₂)
      (t : Path (A := B a₂) (C.fill a₂) y) :
      Step (A := B a₂)
        (DepContext.substRight (A := A) (B := B) C p
          (DepContext.substRight (A := A) (B := B) C (Path.refl a₂) t))
        (DepContext.substRight (A := A) (B := B) C p t)
  /-- Rule 61: Dependent bicontext left map congruence. -/
  | depBiContext_mapLeft_congr
    {A : Type u} {B : Type u} {C : A → B → Type u}
      (K : _root_.ComputationalPaths.Path.DepBiContext A B C)
      {a₁ a₂ : A} (b : B)
      {p q : Path a₁ a₂} :
      Step (A := A) p q →
        Step (A := C a₂ b)
          (_root_.ComputationalPaths.Path.DepBiContext.mapLeft
            (A := A) (B := B) (C := C) K p b)
          (_root_.ComputationalPaths.Path.DepBiContext.mapLeft
            (A := A) (B := B) (C := C) K q b)
  /-- Rule 62: Dependent bicontext right map congruence. -/
  | depBiContext_mapRight_congr
    {A : Type u} {B : Type u} {C : A → B → Type u}
      (K : _root_.ComputationalPaths.Path.DepBiContext A B C)
      (a : A) {b₁ b₂ : B}
      {p q : Path b₁ b₂} :
      Step (A := B) p q →
        Step (A := C a b₂)
          (_root_.ComputationalPaths.Path.DepBiContext.mapRight
            (A := A) (B := B) (C := C) K a p)
          (_root_.ComputationalPaths.Path.DepBiContext.mapRight
            (A := A) (B := B) (C := C) K a q)
  /-- Rule 63: Dependent bicontext map2 left congruence. -/
  | depBiContext_map2_congr_left
    {A : Type u} {B : Type u} {C : A → B → Type u}
      (K : _root_.ComputationalPaths.Path.DepBiContext A B C)
      {a₁ a₂ : A} {b₁ b₂ : B}
      {p q : Path a₁ a₂} (r : Path b₁ b₂) :
      Step (A := A) p q →
        Step (A := C a₂ b₂)
          (_root_.ComputationalPaths.Path.DepBiContext.map2
            (A := A) (B := B) (C := C) K p r)
          (_root_.ComputationalPaths.Path.DepBiContext.map2
            (A := A) (B := B) (C := C) K q r)
  /-- Rule 64: Dependent bicontext map2 right congruence. -/
  | depBiContext_map2_congr_right
    {A : Type u} {B : Type u} {C : A → B → Type u}
      (K : _root_.ComputationalPaths.Path.DepBiContext A B C)
      {a₁ a₂ : A} {b₁ b₂ : B}
      (p : Path a₁ a₂) {q r : Path b₁ b₂} :
      Step (A := B) q r →
        Step (A := C a₂ b₂)
          (_root_.ComputationalPaths.Path.DepBiContext.map2
            (A := A) (B := B) (C := C) K p q)
          (_root_.ComputationalPaths.Path.DepBiContext.map2
            (A := A) (B := B) (C := C) K p r)
  /-- Rule 65: Bicontext left map congruence. -/
  | biContext_mapLeft_congr
    {A : Type u} {B : Type u} {C : Type u}
      (K : BiContext A B C) {a₁ a₂ : A} (b : B)
      {p q : Path a₁ a₂} :
      Step (A := A) p q →
        Step (A := C)
          (BiContext.mapLeft (A := A) (B := B) (C := C) K p b)
          (BiContext.mapLeft (A := A) (B := B) (C := C) K q b)
  /-- Rule 66: Bicontext right map congruence. -/
  | biContext_mapRight_congr
    {A : Type u} {B : Type u} {C : Type u}
      (K : BiContext A B C) (a : A) {b₁ b₂ : B}
      {p q : Path b₁ b₂} :
      Step (A := B) p q →
        Step (A := C)
          (BiContext.mapRight (A := A) (B := B) (C := C) K a p)
          (BiContext.mapRight (A := A) (B := B) (C := C) K a q)
  /-- Rule 67: Bicontext map2 left congruence. -/
  | biContext_map2_congr_left
    {A : Type u} {B : Type u} {C : Type u}
      (K : BiContext A B C) {a₁ a₂ : A} {b₁ b₂ : B}
      {p q : Path a₁ a₂} (r : Path b₁ b₂) :
      Step (A := A) p q →
        Step (A := C)
          (BiContext.map2 (A := A) (B := B) (C := C) K p r)
          (BiContext.map2 (A := A) (B := B) (C := C) K q r)
  /-- Rule 68: Bicontext map2 right congruence. -/
  | biContext_map2_congr_right
    {A : Type u} {B : Type u} {C : Type u}
      (K : BiContext A B C) {a₁ a₂ : A} {b₁ b₂ : B}
      (p : Path a₁ a₂) {q r : Path b₁ b₂} :
      Step (A := B) q r →
        Step (A := C)
          (BiContext.map2 (A := A) (B := B) (C := C) K p q)
          (BiContext.map2 (A := A) (B := B) (C := C) K p r)
  /-- Rule 69: Left map congruence for binary operations. -/
  | mapLeft_congr
    {A : Type u} {B : Type u}
      (f : A → B → A) {a₁ a₂ : A} (b : B)
      {p q : Path a₁ a₂} :
      Step (A := A) p q →
        Step (A := A) (Path.mapLeft (A := A) (B := B) (C := A) f p b)
          (Path.mapLeft (A := A) (B := B) (C := A) f q b)
  /-- Rule 70: Right map congruence for binary operations. -/
  | mapRight_congr
    {A : Type u} (f : A → A → A) (a : A) {b₁ b₂ : A}
      {p q : Path b₁ b₂} :
      Step (A := A) p q →
        Step (A := A) (Path.mapRight (A := A) (B := A) (C := A) f a p)
          (Path.mapRight (A := A) (B := A) (C := A) f a q)
  /-- Rule 71: Left map with propositional equality. -/
  | mapLeft_ofEq
    {A : Type u} {B : Type u}
      (f : A → B → A) {a₁ a₂ : A} (h : a₁ = a₂) (b : B) :
      Step (A := A)
        (Path.mapLeft (A := A) (B := B) (C := A) f
          (Path.stepChain (A := A) (a := a₁) (b := a₂) h) b)
        (Path.stepChain (A := A) (a := f a₁ b) (b := f a₂ b)
          (_root_.congrArg (fun x => f x b) h))
  /-- Rule 72: Right map with propositional equality. -/
  | mapRight_ofEq
    {A : Type u} (f : A → A → A) (a : A) {b₁ b₂ : A} (h : b₁ = b₂) :
      Step (A := A)
        (Path.mapRight (A := A) (B := A) (C := A) f a
          (Path.stepChain (A := A) (a := b₁) (b := b₂) h))
        (Path.stepChain (A := A) (a := f a b₁) (b := f a b₂)
          (_root_.congrArg (f a) h))
  /-- Rule 73: Symmetry congruence (structural). If `p ▷ q` then `symm(p) ▷ symm(q)`. -/
  | symm_congr {A : Type u} {a b : A} {p q : Path a b} :
      Step (A := A) p q → Step (A := A) (Path.symm p) (Path.symm q)
  /-- Rule 75: Left transitivity congruence (structural). If `p ▷ q` then `p ∘ r ▷ q ∘ r`. -/
  | trans_congr_left {A : Type u} {a b c : A}
      {p q : Path a b} (r : Path b c) :
      Step (A := A) p q → Step (A := A) (Path.trans p r) (Path.trans q r)
  /-- Rule 76: Right transitivity congruence (structural). If `q ▷ r` then `p ∘ q ▷ p ∘ r`. -/
  | trans_congr_right {A : Type u} {a b c : A}
      (p : Path a b) {q r : Path b c} :
      Step (A := A) q r → Step (A := A) (Path.trans p q) (Path.trans p r)
  /-- Rule 77: Left cancellation. `p ∘ (σ(p) ∘ q) ▷ q`.
      This is the completion rule that closes the critical pair between
      `trans_assoc` and `trans_symm`. Together with `trans_cancel_right`,
      it makes the groupoid fragment confluent without UIP/Step.canon.
      See `GroupoidConfluence.lean` for the free group confluence proof. -/
  | trans_cancel_left {A : Type u} {a b c : A}
      (p : Path a b) (q : Path a c) :
      Step (A := A) (Path.trans p (Path.trans (Path.symm p) q)) q
  /-- Rule 78: Right cancellation. `σ(p) ∘ (p ∘ q) ▷ q`.
      Dual of `trans_cancel_left`. Closes the critical pair between
      `trans_assoc` and `symm_trans`. -/
  | trans_cancel_right {A : Type u} {a b c : A}
      (p : Path a b) (q : Path b c) :
      Step (A := A) (Path.trans (Path.symm p) (Path.trans p q)) q
/-- Step-oriented path constructor for reflexivity. -/
@[simp] noncomputable def Step.refl {A : Type u} (a : A) : Path a a :=
  Path.refl a

/-- Step-oriented path constructor for symmetry. -/
@[simp] noncomputable def Step.symm {A : Type u} {a b : A} (p : Path a b) : Path b a :=
  Path.symm p

/-- Step-oriented path constructor for composition. -/
@[simp] noncomputable def Step.trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

/-- Step-oriented congruence for composition of functions. -/
@[simp] noncomputable def Step.congr_comp {A : Type u} {B : Type v} {C : Type w}
    (f : A → B) (g : B → C) {a b : A} (p : Path a b) :
    Path (g (f a)) (g (f b)) :=
  Path.congrArg g (Path.congrArg f p)

/-- Step-oriented right-associated composition. -/
@[simp] noncomputable def Step.assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) : Path a d :=
  Step.trans p (Step.trans q r)

/-- Step-oriented left unit insertion. -/
@[simp] noncomputable def Step.unit_left {A : Type u} {a b : A} (p : Path a b) : Path a b :=
  Step.trans (Step.refl a) p

/-- Step-oriented right unit insertion. -/
@[simp] noncomputable def Step.unit_right {A : Type u} {a b : A} (p : Path a b) : Path a b :=
  Step.trans p (Step.refl b)

@[simp] theorem step_toEq {A : Type u} {a b : A}
    {p q : Path a b} (h : Step p q) :
    p.toEq = q.toEq := by
  induction h with
  | symm_refl _ => simp
  | symm_symm _ => simp
  | trans_refl_left _ => simp
  | trans_refl_right _ => simp
  | trans_symm _ => simp
  | symm_trans _ => simp
  | symm_trans_congr _ _ => simp
  | trans_assoc _ _ _ => simp
  | map2_subst _ _ _ => simp
  | prod_fst_beta _ _ => simp
  | prod_snd_beta _ _ => simp
  | prod_eta _ => simp
  | prod_mk_symm _ _ => simp
  | prod_map_congrArg _ _ _ _ => simp
  | prod_rec_beta _ _ _ => simp
  | sigma_fst_beta _ _ => simp
  | sigma_snd_beta _ _ => simp
  | sigma_eta _ => simp
  | sigma_mk_symm _ _ => simp
  | sum_rec_inl_beta _ _ _ => simp
  | sum_rec_inr_beta _ _ _ => simp
  | fun_app_beta _ _ => simp
  | fun_eta _ => simp
  | lam_congr_symm _ => simp
  | apd_refl _ _ => simp
  | transport_refl_beta _ =>
    simp
  | transport_trans_beta _ _ _ =>
    simp
  | transport_symm_left_beta _ _ =>
    simp
  | transport_symm_right_beta _ _ =>
    simp
  | transport_sigmaMk_fst_beta _ _ _ =>
    simp
  | transport_sigmaMk_dep_beta _ _ _ =>
    simp
  | subst_sigmaMk_dep_beta _ _ _ =>
    simp
  | context_congr _ _ ih =>
    cases ih
    rfl
  | context_map_symm _ _ =>
    simp
  | context_tt_cancel_left _ _ _ =>
    simp
  | context_tt_cancel_right _ _ _ =>
    simp
  | context_subst_left_beta _ _ _ =>
    simp
  | context_subst_left_of_right _ _ _ =>
    simp
  | context_subst_left_assoc _ _ _ _ =>
    simp
  | context_subst_right_beta _ _ _ =>
    simp
  | context_subst_right_assoc _ _ _ _ =>
    simp
  | context_subst_left_refl_right _ _ =>
    simp
  | context_subst_left_refl_left _ _ =>
    simp
  | context_subst_right_refl_left _ _ =>
    simp
  | context_subst_right_refl_right _ _ =>
    simp
  | context_subst_left_idempotent _ _ _ =>
    simp
  | context_subst_right_cancel_inner _ _ _ =>
    simp
  | context_subst_right_cancel_outer _ _ _ =>
    simp
  | depContext_congr _ _ ih =>
    cases ih
    rfl
  | depContext_map_symm _ _ =>
    simp
  | depContext_subst_left_beta _ _ _ =>
    simp
  | depContext_subst_left_assoc _ _ _ _ =>
    simp
  | depContext_subst_right_beta _ _ _ =>
    simp
  | depContext_subst_right_assoc _ _ _ _ =>
    simp
  | depContext_subst_left_refl_right _ _ =>
    simp
  | depContext_subst_left_refl_left _ _ =>
    simp
  | depContext_subst_right_refl_left _ _ =>
    simp
  | depContext_subst_right_refl_right _ _ =>
    simp
  | depContext_subst_left_idempotent _ _ _ =>
    simp
  | depContext_subst_right_cancel_inner _ _ _ =>
    simp
  | depBiContext_mapLeft_congr _ _ _ ih =>
    cases ih
    rfl
  | depBiContext_mapRight_congr _ _ _ ih =>
    cases ih
    rfl
  | depBiContext_map2_congr_left _ _ _ ih =>
    cases ih
    rfl
  | depBiContext_map2_congr_right _ _ _ ih =>
    cases ih
    rfl
  | biContext_mapLeft_congr _ _ _ ih =>
    cases ih
    rfl
  | biContext_mapRight_congr _ _ _ ih =>
    cases ih
    rfl
  | biContext_map2_congr_left _ _ _ ih =>
    cases ih
    rfl
  | biContext_map2_congr_right _ _ _ ih =>
    cases ih
    rfl
  | mapLeft_congr _ _ _ ih =>
    cases ih
    simp
  | mapRight_congr _ _ _ ih =>
    cases ih
    simp
  | mapLeft_ofEq _ _ _ =>
    simp
  | mapRight_ofEq _ _ _ =>
    simp
  | symm_congr _ ih =>
    cases ih
    simp
  | trans_congr_left _ _ ih =>
    cases ih
    simp
  | trans_congr_right _ _ ih =>
    cases ih
    simp
  | trans_cancel_left _ _ => simp
  | trans_cancel_right _ _ => simp

/-! ## Local joinability for critical overlaps -/

/-- Compatibility helper used by deep modules: append `refl` and contract. -/
def Step.exact_compose {A : Type u} {a b : A} (p : Path a b) :
    Step (Path.trans p (Path.refl b)) p :=
  Step.trans_refl_right (A := A) p

/-- Reflexive-transitive closure of `Step`, used for critical-pair joins. -/
inductive StepStar :
  {A : Type u} → {a b : A} → Path a b → Path a b → Type (u + 1)
  | refl {A : Type u} {a b : A} (p : Path a b) :
      StepStar p p
  | tail {A : Type u} {a b : A} {p q r : Path a b} :
      StepStar p q → Step q r → StepStar p r

namespace StepStar

/-- Embed a single rewrite step in `StepStar`. -/
noncomputable def single {A : Type u} {a b : A} {p q : Path a b}
    (h : Step p q) : StepStar p q :=
  StepStar.tail (StepStar.refl p) h

/-- Compose two single steps in `StepStar`. -/
noncomputable def two {A : Type u} {a b : A} {p q r : Path a b}
    (h₁ : Step p q) (h₂ : Step q r) : StepStar p r :=
  StepStar.tail (single h₁) h₂

end StepStar

/-- Two reducts are joinable when they have a common `StepStar` descendant. -/
inductive Step.Joinable {A : Type u} {a b : A} (p q : Path a b) : Type (u + 1) where
  | intro (r : Path a b) (hp : StepStar p r) (hq : StepStar q r) : Step.Joinable p q

/-- Joinability is symmetric. -/
def Step.Joinable.symm {A : Type u} {a b : A} {p q : Path a b} :
    Step.Joinable p q → Step.Joinable q p := by
  intro h
  rcases h with ⟨r, hp, hq⟩
  exact ⟨r, hq, hp⟩

/-- Type-level local-confluence payload carrying explicit `StepStar` witnesses. -/
structure Step.JoinableData {A : Type u} {a b : A} (p q : Path a b) : Type (u + 1) where
  meet : Path a b
  left : StepStar p meet
  right : StepStar q meet

/-- Extract the explicit `StepStar` witnesses already carried by `Joinable`. -/
def Step.Joinable.toData {A : Type u} {a b : A} {p q : Path a b} :
    Step.Joinable p q → Step.JoinableData p q
  | .intro r hp hq => ⟨r, hp, hq⟩

/-- Forget type-level join data to recover Prop-level joinability. -/
def Step.Joinable.ofData {A : Type u} {a b : A} {p q : Path a b} :
    Step.JoinableData p q → Step.Joinable p q := by
  intro h
  exact ⟨h.meet, h.left, h.right⟩

/-- Local-confluence oracle with explicit witness payload, given a joinability proof. -/
def Step.local_confluence_data
    {A : Type u} {a b : A} {p q r : Path a b}
    (_s₁ : Step p q) (_s₂ : Step p r)
    (h : Step.Joinable q r) : Step.JoinableData q r :=
  Step.Joinable.toData h

/-- Determinism up to `toEq`: any two one-step reducts have equal semantic proof. -/
theorem Step.deterministic {A : Type u} {a b : A} {p q r : Path a b}
    (hq : Step p q) (hr : Step p r) :
    q.toEq = r.toEq := by
  exact (step_toEq hq).symm.trans (step_toEq hr)

/-- Non-overlapping base case: `symm(refl)` has a unique semantic reduct. -/
theorem Step.deterministic_symm_refl {A : Type u} (a : A) {q : Path a a}
    (hq : Step (Path.symm (Path.refl a)) q) :
    q.toEq = (Path.refl a).toEq := by
  exact Step.deterministic (hq := hq) (hr := Step.symm_refl a)

/-- Non-overlapping base case: `symm(symm(p))` has a unique semantic reduct. -/
theorem Step.deterministic_symm_symm {A : Type u} {a b : A}
    (p : Path a b) {q : Path a b}
    (hq : Step (Path.symm (Path.symm p)) q) :
    q.toEq = p.toEq := by
  exact Step.deterministic (hq := hq) (hr := Step.symm_symm p)

/-- Non-overlapping base case: `refl ∘ p` has a unique semantic reduct. -/
theorem Step.deterministic_trans_refl_left {A : Type u} {a b : A}
    (p : Path a b) {q : Path a b}
    (hq : Step (Path.trans (Path.refl a) p) q) :
    q.toEq = p.toEq := by
  exact Step.deterministic (hq := hq) (hr := Step.trans_refl_left p)

/-- Non-overlapping base case: `p ∘ refl` has a unique semantic reduct. -/
theorem Step.deterministic_trans_refl_right {A : Type u} {a b : A}
    (p : Path a b) {q : Path a b}
    (hq : Step (Path.trans p (Path.refl b)) q) :
    q.toEq = p.toEq := by
  exact Step.deterministic (hq := hq) (hr := Step.trans_refl_right p)

/-- Non-overlapping base case: `p ∘ symm(p)` has a unique semantic reduct. -/
theorem Step.deterministic_trans_symm {A : Type u} {a b : A}
    (p : Path a b) {q : Path a a}
    (hq : Step (Path.trans p (Path.symm p)) q) :
    q.toEq = (Path.refl a).toEq := by
  exact Step.deterministic (hq := hq) (hr := Step.trans_symm p)

/-- Non-overlapping base case: `symm(p) ∘ p` has a unique semantic reduct. -/
theorem Step.deterministic_symm_trans {A : Type u} {a b : A}
    (p : Path a b) {q : Path b b}
    (hq : Step (Path.trans (Path.symm p) p) q) :
    q.toEq = (Path.refl b).toEq := by
  exact Step.deterministic (hq := hq) (hr := Step.symm_trans p)

/-- Non-overlapping base case: left cancellation has a unique semantic reduct. -/
theorem Step.deterministic_trans_cancel_left {A : Type u} {a b c : A}
    (p : Path a b) (q : Path a c) {r : Path a c}
    (hr : Step (Path.trans p (Path.trans (Path.symm p) q)) r) :
    r.toEq = q.toEq := by
  exact Step.deterministic (hq := hr) (hr := Step.trans_cancel_left p q)

/-- Non-overlapping base case: right cancellation has a unique semantic reduct. -/
theorem Step.deterministic_trans_cancel_right {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) {r : Path b c}
    (hr : Step (Path.trans (Path.symm p) (Path.trans p q)) r) :
    r.toEq = q.toEq := by
  exact Step.deterministic (hq := hr) (hr := Step.trans_cancel_right p q)

/-- Non-overlapping base case: symmetry over composition has a unique semantic reduct. -/
theorem Step.deterministic_symm_trans_congr {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) {r : Path c a}
    (hr : Step (Path.symm (Path.trans p q)) r) :
    r.toEq = (Path.trans (Path.symm q) (Path.symm p)).toEq := by
  exact Step.deterministic (hq := hr) (hr := Step.symm_trans_congr p q)

/-- Non-overlapping base case: associativity has a unique semantic reduct. -/
theorem Step.deterministic_trans_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) {s : Path a d}
    (hs : Step (Path.trans (Path.trans p q) r) s) :
    s.toEq = (Path.trans p (Path.trans q r)).toEq := by
  exact Step.deterministic (hq := hs) (hr := Step.trans_assoc p q r)

/-- Non-overlapping base case: symmetry congruence has a unique semantic reduct. -/
theorem Step.deterministic_symm_congr {A : Type u} {a b : A}
    {p p' : Path a b} (hp : Step p p') {r : Path b a}
    (hr : Step (Path.symm p) r) :
    r.toEq = (Path.symm p').toEq := by
  exact Step.deterministic (hq := hr) (hr := Step.symm_congr hp)

/-- Non-overlapping base case: left transitivity congruence has a unique semantic reduct. -/
theorem Step.deterministic_trans_congr_left {A : Type u} {a b c : A}
    {p p' : Path a b} (r : Path b c) (hp : Step p p') {s : Path a c}
    (hs : Step (Path.trans p r) s) :
    s.toEq = (Path.trans p' r).toEq := by
  exact Step.deterministic (hq := hs) (hr := Step.trans_congr_left r hp)

/-- Non-overlapping base case: right transitivity congruence has a unique semantic reduct. -/
theorem Step.deterministic_trans_congr_right {A : Type u} {a b c : A}
    (p : Path a b) {q q' : Path b c} (hq : Step q q') {s : Path a c}
    (hs : Step (Path.trans p q) s) :
    s.toEq = (Path.trans p q').toEq := by
  exact Step.deterministic (hq := hs) (hr := Step.trans_congr_right p hq)

/-- Non-overlapping base case: map2 substitution has a unique semantic reduct. -/
theorem Step.deterministic_map2_subst
    {A A₁ B : Type u} {a1 a2 : A₁} {b1 b2 : B}
    (f : A₁ → B → A)
    (p : Path (A := A₁) a1 a2) (q : Path (A := B) b1 b2)
    {r : Path (A := A) (f a1 b1) (f a2 b2)}
    (hr : Step (A := A) (Path.map2 (A := A₁) (B := B) (C := A) f p q) r) :
    r.toEq =
      (Path.trans
        (Path.mapRight (A := A₁) (B := B) (C := A) f a1 q)
        (Path.mapLeft (A := A₁) (B := B) (C := A) f p b2)).toEq := by
  exact Step.deterministic (hq := hr) (hr := Step.map2_subst f p q)

/-- Non-overlapping base case: product η has a unique semantic reduct. -/
theorem Step.deterministic_prod_eta
    {α β : Type u} {a1 a2 : α} {b1 b2 : β}
    (p : Path (A := Prod α β) (a1, b1) (a2, b2))
    {r : Path (A := Prod α β) (a1, b1) (a2, b2)}
    (hr : Step (A := Prod α β) (Path.prodMk (Path.fst p) (Path.snd p)) r) :
    r.toEq = p.toEq := by
  exact Step.deterministic (hq := hr) (hr := Step.prod_eta p)

/-- Non-overlapping base case: function η has a unique semantic reduct. -/
def Step.deterministic_fun_eta
    {α β : Type u} {f g : α → β}
    (p : Path f g) {r : Path f g}
    (hr : Step (A := α → β) (Path.lamCongr (fun x => Path.app p x)) r) :
    r.toEq = p.toEq := by
  exact Step.deterministic (hq := hr) (hr := Step.fun_eta p)

/-- Non-overlapping base case: left map over propositional equality is deterministic. -/
theorem Step.deterministic_mapLeft_ofEq
    {A B : Type u} (f : A → B → A) {a1 a2 : A}
    (h : a1 = a2) (b : B)
    {r : Path (A := A) (f a1 b) (f a2 b)}
    (hr : Step (A := A)
      (Path.mapLeft (A := A) (B := B) (C := A) f
        (Path.stepChain (A := A) (a := a1) (b := a2) h) b) r) :
    r.toEq =
      (Path.stepChain (A := A) (a := f a1 b) (b := f a2 b)
        (_root_.congrArg (fun x => f x b) h)).toEq := by
  exact Step.deterministic (hq := hr) (hr := Step.mapLeft_ofEq f h b)

/-- Non-overlapping base case: right map over propositional equality is deterministic. -/
theorem Step.deterministic_mapRight_ofEq
    {A : Type u} (f : A → A → A) (a : A) {b1 b2 : A}
    (h : b1 = b2)
    {r : Path (A := A) (f a b1) (f a b2)}
    (hr : Step (A := A)
      (Path.mapRight (A := A) (B := A) (C := A) f a
        (Path.stepChain (A := A) (a := b1) (b := b2) h)) r) :
    r.toEq =
      (Path.stepChain (A := A) (a := f a b1) (b := f a b2)
        (_root_.congrArg (f a) h)).toEq := by
  exact Step.deterministic (hq := hr) (hr := Step.mapRight_ofEq f a h)

noncomputable section

noncomputable section

def critical_pair_trans_assoc_trans_refl_left_joinable
    {A : Type u} {a b c : A} (p : Path a b) (r : Path b c) :
    Step.Joinable
      (Path.trans (Path.refl a) (Path.trans p r))
      (Path.trans p r) := by
  refine ⟨Path.trans p r, ?_, ?_⟩
  · exact StepStar.single (Step.trans_refl_left (Path.trans p r))
  · exact StepStar.refl (Path.trans p r)

def critical_pair_trans_assoc_trans_refl_right_joinable
    {A : Type u} {a b c : A} (p : Path a b) (r : Path b c) :
    Step.Joinable
      (Path.trans p (Path.trans (Path.refl b) r))
      (Path.trans p r) := by
  refine ⟨Path.trans p r, ?_, ?_⟩
  · exact StepStar.single
      (Step.trans_congr_right p (Step.trans_refl_left r))
  · exact StepStar.refl (Path.trans p r)

def critical_pair_trans_assoc_trans_symm_joinable
    {A : Type u} {a b c : A} (p : Path a b) (q : Path a c) :
    Step.Joinable
      (Path.trans p (Path.trans (Path.symm p) q))
      (Path.trans (Path.refl a) q) := by
  refine ⟨q, ?_, ?_⟩
  · exact StepStar.single (Step.trans_cancel_left p q)
  · exact StepStar.single (Step.trans_refl_left q)

def critical_pair_trans_assoc_symm_trans_joinable
    {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
    Step.Joinable
      (Path.trans (Path.symm p) (Path.trans p q))
      (Path.trans (Path.refl b) q) := by
  refine ⟨q, ?_, ?_⟩
  · exact StepStar.single (Step.trans_cancel_right p q)
  · exact StepStar.single (Step.trans_refl_left q)

def critical_pair_trans_assoc_trans_assoc_joinable
    {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Step.Joinable
      (Path.trans (Path.trans p (Path.trans q r)) s)
      (Path.trans (Path.trans p q) (Path.trans r s)) := by
  refine ⟨Path.trans p (Path.trans q (Path.trans r s)), ?_, ?_⟩
  · exact StepStar.two
      (Step.trans_assoc p (Path.trans q r) s)
      (Step.trans_congr_right p (Step.trans_assoc q r s))
  · exact StepStar.single (Step.trans_assoc p q (Path.trans r s))

def critical_pair_symm_congr_symm_symm_joinable
    {A : Type u} {a b : A} {p p' : Path a b}
    (hp : Step p p') :
    Step.Joinable
      (Path.symm (Path.symm p'))
      p := by
  refine ⟨p', ?_, ?_⟩
  · exact StepStar.single (Step.symm_symm p')
  · exact StepStar.single hp

def critical_pair_symm_congr_symm_trans_congr_left_joinable
    {A : Type u} {a b c : A}
    {p p' : Path a b} {q : Path b c}
    (hp : Step p p') :
    Step.Joinable
      (Path.symm (Path.trans p' q))
      (Path.trans (Path.symm q) (Path.symm p)) := by
  refine ⟨Path.trans (Path.symm q) (Path.symm p'), ?_, ?_⟩
  · exact StepStar.single (Step.symm_trans_congr p' q)
  · exact StepStar.single
      (Step.trans_congr_right (Path.symm q) (Step.symm_congr hp))

def critical_pair_symm_congr_symm_trans_congr_right_joinable
    {A : Type u} {a b c : A}
    {p : Path a b} {q q' : Path b c}
    (hq : Step q q') :
    Step.Joinable
      (Path.symm (Path.trans p q'))
      (Path.trans (Path.symm q) (Path.symm p)) := by
  refine ⟨Path.trans (Path.symm q') (Path.symm p), ?_, ?_⟩
  · exact StepStar.single (Step.symm_trans_congr p q')
  · exact StepStar.single
      (Step.trans_congr_left (Path.symm p) (Step.symm_congr hq))

def critical_pair_trans_congr_left_right_joinable
    {A : Type u} {a b c : A}
    {p p' : Path a b} {q q' : Path b c}
    (hp : Step p p') (hq : Step q q') :
    Step.Joinable
      (Path.trans p' q)
      (Path.trans p q') := by
  refine ⟨Path.trans p' q', ?_, ?_⟩
  · exact StepStar.single (Step.trans_congr_right p' hq)
  · exact StepStar.single (Step.trans_congr_left q' hp)

def critical_pair_trans_congr_left_trans_assoc_joinable
    {A : Type u} {a b c d : A}
    {p p' : Path a b} {q : Path b c} {r : Path c d}
    (hp : Step p p') :
    Step.Joinable
      (Path.trans (Path.trans p' q) r)
      (Path.trans p (Path.trans q r)) := by
  refine ⟨Path.trans p' (Path.trans q r), ?_, ?_⟩
  · exact StepStar.single (Step.trans_assoc p' q r)
  · exact StepStar.single (Step.trans_congr_left (Path.trans q r) hp)

def critical_pair_trans_congr_right_trans_assoc_joinable
    {A : Type u} {a b c d : A}
    {p : Path a b} {q q' : Path b c} {r : Path c d}
    (hq : Step q q') :
    Step.Joinable
      (Path.trans (Path.trans p q') r)
      (Path.trans p (Path.trans q r)) := by
  refine ⟨Path.trans p (Path.trans q' r), ?_, ?_⟩
  · exact StepStar.single (Step.trans_assoc p q' r)
  · exact StepStar.single
      (Step.trans_congr_right p (Step.trans_congr_left r hq))

def critical_pair_trans_assoc_trans_refl_inner_right_joinable
    {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
    Step.Joinable
      (Path.trans p (Path.trans q (Path.refl c)))
      (Path.trans p q) := by
  refine ⟨Path.trans p q, ?_, ?_⟩
  · exact StepStar.single
      (Step.trans_congr_right p (Step.trans_refl_right q))
  · exact StepStar.refl (Path.trans p q)

def critical_pair_symm_symm_symm_refl_joinable
    {A : Type u} (a : A) :
    Step.Joinable (Path.refl a) (Path.symm (Path.refl a)) := by
  refine ⟨Path.refl a, ?_, ?_⟩
  · exact StepStar.refl (Path.refl a)
  · exact StepStar.single (Step.symm_refl a)

def critical_pair_symm_symm_symm_trans_congr_joinable
    {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Step.Joinable
      (Path.trans p q)
      (Path.symm (Path.trans (Path.symm q) (Path.symm p))) := by
  refine ⟨Path.trans p q, ?_, ?_⟩
  · exact StepStar.refl (Path.trans p q)
  · exact StepStar.tail
      (StepStar.two
        (Step.symm_trans_congr (Path.symm q) (Path.symm p))
        (Step.trans_congr_left (Path.symm (Path.symm q))
          (Step.symm_symm p)))
      (Step.trans_congr_right p (Step.symm_symm q))

def critical_pair_symm_trans_congr_trans_refl_left_joinable
    {A : Type u} {a b : A} (p : Path a b) :
    Step.Joinable
      (Path.symm p)
      (Path.trans (Path.symm p) (Path.symm (Path.refl a))) := by
  refine ⟨Path.symm p, ?_, ?_⟩
  · exact StepStar.refl (Path.symm p)
  · exact StepStar.two
      (Step.trans_congr_right (Path.symm p) (Step.symm_refl a))
      (Step.trans_refl_right (Path.symm p))

def critical_pair_symm_trans_congr_trans_refl_right_joinable
    {A : Type u} {a b : A} (p : Path a b) :
    Step.Joinable
      (Path.symm p)
      (Path.trans (Path.symm (Path.refl b)) (Path.symm p)) := by
  refine ⟨Path.symm p, ?_, ?_⟩
  · exact StepStar.refl (Path.symm p)
  · exact StepStar.two
      (Step.trans_congr_left (Path.symm p) (Step.symm_refl b))
      (Step.trans_refl_left (Path.symm p))

def critical_pair_trans_cancel_left_trans_refl_left_inner_joinable
    {A : Type u} {a c : A} (q : Path a c) :
    Step.Joinable
      q
      (Path.trans (Path.symm (Path.refl a)) q) := by
  refine ⟨q, ?_, ?_⟩
  · exact StepStar.refl q
  · exact StepStar.two
      (Step.trans_congr_left q (Step.symm_refl a))
      (Step.trans_refl_left q)

def critical_pair_trans_cancel_right_symm_refl_joinable
    {A : Type u} {a c : A} (q : Path a c) :
    Step.Joinable
      q
      (Path.trans (Path.refl a) (Path.trans (Path.refl a) q)) := by
  refine ⟨q, ?_, ?_⟩
  · exact StepStar.refl q
  · exact StepStar.tail
      (StepStar.single (Step.trans_refl_left (Path.trans (Path.refl a) q)))
      (Step.trans_refl_left q)

def critical_pair_trans_assoc_trans_cancel_left_joinable
    {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path a c) (r : Path c d) :
    Step.Joinable
      (Path.trans q r)
      (Path.trans p (Path.trans (Path.trans (Path.symm p) q) r)) := by
  refine ⟨Path.trans q r, ?_, ?_⟩
  · exact StepStar.refl (Path.trans q r)
  · exact StepStar.tail
      (StepStar.single
        (Step.trans_congr_right p (Step.trans_assoc (Path.symm p) q r)))
      (Step.trans_cancel_left p (Path.trans q r))

def critical_pair_trans_assoc_trans_cancel_right_joinable
    {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Step.Joinable
      (Path.trans q r)
      (Path.trans (Path.symm p) (Path.trans (Path.trans p q) r)) := by
  refine ⟨Path.trans q r, ?_, ?_⟩
  · exact StepStar.refl (Path.trans q r)
  · exact StepStar.tail
      (StepStar.single
        (Step.trans_congr_right (Path.symm p) (Step.trans_assoc p q r)))
      (Step.trans_cancel_right p (Path.trans q r))

def critical_pair_symm_trans_congr_symm_symm_left_joinable
    {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Step.Joinable
      (Path.symm (Path.trans p q))
      (Path.trans (Path.symm q) (Path.symm (Path.symm (Path.symm p)))) := by
  refine ⟨Path.trans (Path.symm q) (Path.symm p), ?_, ?_⟩
  · exact StepStar.single (Step.symm_trans_congr p q)
  · exact StepStar.single
      (Step.trans_congr_right (Path.symm q) (Step.symm_symm (Path.symm p)))

def critical_pair_symm_trans_congr_symm_symm_right_joinable
    {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Step.Joinable
      (Path.symm (Path.trans p q))
      (Path.trans (Path.symm (Path.symm (Path.symm q))) (Path.symm p)) := by
  refine ⟨Path.trans (Path.symm q) (Path.symm p), ?_, ?_⟩
  · exact StepStar.single (Step.symm_trans_congr p q)
  · exact StepStar.single
      (Step.trans_congr_left (Path.symm p) (Step.symm_symm (Path.symm q)))

def critical_pair_trans_cancel_left_trans_refl_right_joinable
    {A : Type u} {a b c : A}
    (p : Path a b) (q : Path a c) :
    Step.Joinable
      (Path.trans q (Path.refl c))
      (Path.trans p (Path.trans (Path.symm p) q)) := by
  refine ⟨q, ?_, ?_⟩
  · exact StepStar.single (Step.trans_refl_right q)
  · exact StepStar.single (Step.trans_cancel_left p q)

def critical_pair_trans_cancel_right_trans_refl_right_joinable
    {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Step.Joinable
      (Path.trans q (Path.refl c))
      (Path.trans (Path.symm p) (Path.trans p q)) := by
  refine ⟨q, ?_, ?_⟩
  · exact StepStar.single (Step.trans_refl_right q)
  · exact StepStar.single (Step.trans_cancel_right p q)

def critical_pair_trans_cancel_left_trans_refl_left_joinable
    {A : Type u} {a b c : A}
    (p : Path a b) (q : Path a c) :
    Step.Joinable
      (Path.trans (Path.refl a) q)
      (Path.trans p (Path.trans (Path.symm p) q)) := by
  refine ⟨q, ?_, ?_⟩
  · exact StepStar.single (Step.trans_refl_left q)
  · exact StepStar.single (Step.trans_cancel_left p q)

def critical_pair_trans_cancel_right_trans_refl_left_joinable
    {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Step.Joinable
      (Path.trans (Path.refl b) q)
      (Path.trans (Path.symm p) (Path.trans p q)) := by
  refine ⟨q, ?_, ?_⟩
  · exact StepStar.single (Step.trans_refl_left q)
  · exact StepStar.single (Step.trans_cancel_right p q)

def critical_pair_trans_refl_left_trans_assoc_joinable
    {A : Type u} {a b c : A} (p : Path a b) (r : Path b c) :
    Step.Joinable
      (Path.trans p r)
      (Path.trans (Path.refl a) (Path.trans p r)) := by
  exact Step.Joinable.symm
    (critical_pair_trans_assoc_trans_refl_left_joinable p r)

def critical_pair_trans_refl_right_trans_assoc_joinable
    {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
    Step.Joinable
      (Path.trans p q)
      (Path.trans p (Path.trans q (Path.refl c))) := by
  exact Step.Joinable.symm
    (critical_pair_trans_assoc_trans_refl_inner_right_joinable p q)

def critical_pair_trans_symm_trans_assoc_joinable
    {A : Type u} {a b c : A} (p : Path a b) (q : Path a c) :
    Step.Joinable
      (Path.trans (Path.refl a) q)
      (Path.trans p (Path.trans (Path.symm p) q)) := by
  exact Step.Joinable.symm
    (critical_pair_trans_assoc_trans_symm_joinable p q)

def critical_pair_symm_trans_trans_assoc_joinable
    {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
    Step.Joinable
      (Path.trans (Path.refl b) q)
      (Path.trans (Path.symm p) (Path.trans p q)) := by
  exact Step.Joinable.symm
    (critical_pair_trans_assoc_symm_trans_joinable p q)

def critical_pair_symm_congr_trans_assoc_joinable
    {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Step.Joinable
      (Path.trans (Path.symm r) (Path.symm (Path.trans p q)))
      (Path.symm (Path.trans p (Path.trans q r))) := by
  refine ⟨Path.trans (Path.symm r) (Path.trans (Path.symm q) (Path.symm p)), ?_, ?_⟩
  · exact StepStar.single
      (Step.trans_congr_right (Path.symm r) (Step.symm_trans_congr p q))
  · exact StepStar.tail
      (StepStar.two
        (Step.symm_trans_congr p (Path.trans q r))
        (Step.trans_congr_left (Path.symm p) (Step.symm_trans_congr q r)))
      (Step.trans_assoc (Path.symm r) (Path.symm q) (Path.symm p))

def critical_pair_symm_congr_trans_symm_joinable
    {A : Type u} {a b : A}
    (p : Path a b) :
    Step.Joinable
      (Path.symm (Path.refl a))
      (Path.trans (Path.symm (Path.symm p)) (Path.symm p)) := by
  refine ⟨Path.refl a, ?_, ?_⟩
  · exact StepStar.single (Step.symm_refl a)
  · exact StepStar.two
      (Step.trans_congr_left (Path.symm p) (Step.symm_symm p))
      (Step.trans_symm p)

def critical_pair_symm_congr_symm_trans_joinable
    {A : Type u} {a b : A}
    (p : Path a b) :
    Step.Joinable
      (Path.symm (Path.refl b))
      (Path.trans (Path.symm p) (Path.symm (Path.symm p))) := by
  refine ⟨Path.refl b, ?_, ?_⟩
  · exact StepStar.single (Step.symm_refl b)
  · exact StepStar.single (Step.trans_symm (Path.symm p))


end

end

/-! ## Lexicographic termination measure scaffold -/

/-- Size companion for path-weight calculations (analogous to `Expr.size`). -/
@[simp] noncomputable def size {A : Type u} {a b : A} (p : Path a b) : Nat :=
  p.steps.length + 1

/-- Primary weight component (analogous to `Expr.weight`). -/
@[simp] noncomputable def weight {A : Type u} {a b : A} (p : Path a b) : Nat :=
  2 * p.steps.length + 4

/-- Secondary weight component (analogous to `Expr.leftWeight`). -/
@[simp] noncomputable def leftWeight {A : Type u} {a b : A} (p : Path a b) : Nat :=
  p.steps.length

/-- Lexicographic termination helper `(weight, leftWeight)` for `Path`. -/
@[simp] noncomputable def termMeasure {A : Type u} {a b : A} (p : Path a b) : Nat × Nat :=
  (p.weight, p.leftWeight)

/-- Weight lower bound matching the groupoid-trs baseline constant. -/
theorem weight_ge_four {A : Type u} {a b : A} (p : Path a b) : 4 ≤ p.weight := by
  simp [weight]

theorem size_pos {A : Type u} {a b : A} (p : Path a b) : 0 < p.size := by
  simp [size]

private noncomputable def NatLex : Nat × Nat → Nat × Nat → Prop :=
  fun x y => x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)

private theorem natLex_irrefl (x : Nat × Nat) : ¬ NatLex x x := by
  intro h
  rcases h with hlt | ⟨heq, hlt⟩
  · exact Nat.lt_irrefl _ hlt
  · exact Nat.lt_irrefl _ hlt

private theorem natLex_trans {x y z : Nat × Nat}
    (hxy : NatLex x y) (hyz : NatLex y z) : NatLex x z := by
  rcases hxy with hxy | ⟨hxyEq, hxyLt⟩
  · rcases hyz with hyz | ⟨hyzEq, _⟩
    · exact Or.inl (Nat.lt_trans hxy hyz)
    · exact Or.inl (hyzEq ▸ hxy)
  · rcases hyz with hyz | ⟨hyzEq, hyzLt⟩
    · exact Or.inl (hxyEq ▸ hyz)
    · exact Or.inr ⟨hxyEq.trans hyzEq, Nat.lt_trans hxyLt hyzLt⟩

private theorem natLex_asymm {x y : Nat × Nat}
    (hxy : NatLex x y) (hyx : NatLex y x) : False :=
  natLex_irrefl x (natLex_trans hxy hyx)

private theorem termMeasure_lt_of_weight_lt
    {A : Type u} {a b : A} {p q : Path a b}
    (h : q.weight < p.weight) : NatLex q.termMeasure p.termMeasure :=
  Or.inl h

private theorem termMeasure_lt_of_leftWeight_lt
    {A : Type u} {a b : A} {p q : Path a b}
    (hw : q.weight = p.weight)
    (hl : q.leftWeight < p.leftWeight) :
    NatLex q.termMeasure p.termMeasure :=
  Or.inr ⟨hw, hl⟩

@[simp] theorem weight_symm {A : Type u} {a b : A} (p : Path a b) :
    (Path.symm p).weight = p.weight := by
  simp [weight]

@[simp] theorem leftWeight_symm {A : Type u} {a b : A} (p : Path a b) :
    (Path.symm p).leftWeight = p.leftWeight := by
  simp [leftWeight]

@[simp] theorem weight_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    (Path.trans p q).weight = 2 * (p.steps.length + q.steps.length) + 4 := by
  simp [weight]

@[simp] theorem leftWeight_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    (Path.trans p q).leftWeight = p.leftWeight + q.leftWeight := by
  simp [leftWeight]

theorem weight_lt_under_symm
    {A : Type u} {a b : A} {p q : Path a b}
    (h : q.weight < p.weight) :
    (Path.symm q).weight < (Path.symm p).weight := by
  simpa [weight] using h

theorem leftWeight_lt_under_symm
    {A : Type u} {a b : A} {p q : Path a b}
    (h : q.leftWeight < p.leftWeight) :
    (Path.symm q).leftWeight < (Path.symm p).leftWeight := by
  simpa [leftWeight] using h

theorem weight_lt_under_trans_left
    {A : Type u} {a b c : A} {p q : Path a b} (r : Path b c)
    (h : q.weight < p.weight) :
    (Path.trans q r).weight < (Path.trans p r).weight := by
  simp [weight] at h ⊢
  omega

theorem weight_lt_under_trans_right
    {A : Type u} {a b c : A} (p : Path a b) {q r : Path b c}
    (h : r.weight < q.weight) :
    (Path.trans p r).weight < (Path.trans p q).weight := by
  simp [weight] at h ⊢
  omega

theorem leftWeight_lt_under_trans_left
    {A : Type u} {a b c : A} {p q : Path a b} (r : Path b c)
    (h : q.leftWeight < p.leftWeight) :
    (Path.trans q r).leftWeight < (Path.trans p r).leftWeight := by
  simp [leftWeight] at h ⊢
  omega

theorem leftWeight_lt_under_trans_right
    {A : Type u} {a b c : A} (p : Path a b) {q r : Path b c}
    (h : r.leftWeight < q.leftWeight) :
    (Path.trans p r).leftWeight < (Path.trans p q).leftWeight := by
  simp [leftWeight] at h ⊢
  omega

/-! ## Lightweight complexity measure -/

/-- Complexity of a path expression, measured by trace length. -/
@[simp] noncomputable def Step.complexity {A : Type u} {a b : A} (p : Path a b) : Nat :=
  p.steps.length

@[simp] theorem Step.complexity_symm {A : Type u} {a b : A} (p : Path a b) :
    Step.complexity (Path.symm p) = Step.complexity p := by
  simp [Step.complexity]

@[simp] theorem Step.complexity_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Step.complexity (Path.trans p q) = Step.complexity p + Step.complexity q := by
  simp [Step.complexity]

def Step.complexity_trans_refl_left_decreases
    {A : Type u} {a b : A} (p : Path a b) :
    Step.complexity p ≤ Step.complexity (Path.trans (Path.refl a) p) := by
  simp [Step.complexity]

def Step.complexity_trans_refl_right_decreases
    {A : Type u} {a b : A} (p : Path a b) :
    Step.complexity p ≤ Step.complexity (Path.trans p (Path.refl b)) := by
  simp [Step.complexity]

def Step.complexity_trans_assoc_preserved
    {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Step.complexity (Path.trans (Path.trans p q) r) =
      Step.complexity (Path.trans p (Path.trans q r)) := by
  simp [Step.complexity]

def Step.complexity_trans_cancel_left_decreases
    {A : Type u} {a b c : A} (p : Path a b) (q : Path a c) :
    Step.complexity q ≤
      Step.complexity (Path.trans p (Path.trans (Path.symm p) q)) := by
  simpa [Step.complexity, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (Nat.le_add_right q.steps.length (p.steps.length + p.steps.length))

def Step.complexity_trans_cancel_right_decreases
    {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
    Step.complexity q ≤
      Step.complexity (Path.trans (Path.symm p) (Path.trans p q)) := by
  simpa [Step.complexity, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (Nat.le_add_right q.steps.length (p.steps.length + p.steps.length))

def Step.complexity_trans_symm_gap
    {A : Type u} {a b : A} (p : Path a b) :
    Step.complexity (Path.trans p (Path.symm p)) =
      Step.complexity p + Step.complexity p := by
  simp [Step.complexity]

def Step.complexity_symm_trans_gap
    {A : Type u} {a b : A} (p : Path a b) :
    Step.complexity (Path.trans (Path.symm p) p) =
      Step.complexity p + Step.complexity p := by
  simp [Step.complexity]

def Step.complexity_trans_cancel_left_gap
    {A : Type u} {a b c : A} (p : Path a b) (q : Path a c) :
    Step.complexity (Path.trans p (Path.trans (Path.symm p) q)) =
      Step.complexity q + (Step.complexity p + Step.complexity p) := by
  simp [Step.complexity, Nat.add_assoc, Nat.add_comm]

def Step.complexity_trans_cancel_right_gap
    {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
    Step.complexity (Path.trans (Path.symm p) (Path.trans p q)) =
      Step.complexity q + (Step.complexity p + Step.complexity p) := by
  simp [Step.complexity, Nat.add_assoc, Nat.add_comm]

def Step.complexity_trans_symm_decreases
    {A : Type u} {a b : A} (p : Path a b) :
    Step.complexity (Path.refl a) ≤
      Step.complexity (Path.trans p (Path.symm p)) := by
  simp [Step.complexity]

def Step.complexity_symm_trans_decreases
    {A : Type u} {a b : A} (p : Path a b) :
    Step.complexity (Path.refl b) ≤
      Step.complexity (Path.trans (Path.symm p) p) := by
  simp [Step.complexity]

def Step.complexity_trans_symm_strict
    {A : Type u} {a b : A} (p : Path a b)
    (hp : 0 < Step.complexity p) :
    Step.complexity (Path.refl a) <
      Step.complexity (Path.trans p (Path.symm p)) := by
  have hpp : 0 < Step.complexity p + Step.complexity p := by
    exact Nat.lt_of_lt_of_le hp (Nat.le_add_right (Step.complexity p) (Step.complexity p))
  simpa [Step.complexity] using hpp

def Step.complexity_symm_trans_strict
    {A : Type u} {a b : A} (p : Path a b)
    (hp : 0 < Step.complexity p) :
    Step.complexity (Path.refl b) <
      Step.complexity (Path.trans (Path.symm p) p) := by
  have hpp : 0 < Step.complexity p + Step.complexity p := by
    exact Nat.lt_of_lt_of_le hp (Nat.le_add_right (Step.complexity p) (Step.complexity p))
  simpa [Step.complexity] using hpp

def Step.complexity_trans_cancel_left_strict
    {A : Type u} {a b c : A} (p : Path a b) (q : Path a c)
    (hp : 0 < Step.complexity p) :
    Step.complexity q <
      Step.complexity (Path.trans p (Path.trans (Path.symm p) q)) := by
  have hpp : 0 < Step.complexity p + Step.complexity p := by
    exact Nat.lt_of_lt_of_le hp (Nat.le_add_right (Step.complexity p) (Step.complexity p))
  have hlt : Step.complexity q <
      Step.complexity q + (Step.complexity p + Step.complexity p) :=
    Nat.lt_add_of_pos_right hpp
  simpa [Step.complexity, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlt

def Step.complexity_trans_cancel_right_strict
    {A : Type u} {a b c : A} (p : Path a b) (q : Path b c)
    (hp : 0 < Step.complexity p) :
    Step.complexity q <
      Step.complexity (Path.trans (Path.symm p) (Path.trans p q)) := by
  have hpp : 0 < Step.complexity p + Step.complexity p := by
    exact Nat.lt_of_lt_of_le hp (Nat.le_add_right (Step.complexity p) (Step.complexity p))
  have hlt : Step.complexity q <
      Step.complexity q + (Step.complexity p + Step.complexity p) :=
    Nat.lt_add_of_pos_right hpp
  simpa [Step.complexity, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlt

def Step.complexity_symm_trans_symm_decreases
    {A : Type u} {a b : A} (p : Path a b) :
    Step.complexity (Path.symm (Path.refl a)) ≤
      Step.complexity (Path.symm (Path.trans p (Path.symm p))) := by
  calc
    Step.complexity (Path.symm (Path.refl a))
        = Step.complexity (Path.refl a) := Step.complexity_symm (Path.refl a)
    _ ≤ Step.complexity (Path.trans p (Path.symm p)) := Step.complexity_trans_symm_decreases p
    _ = Step.complexity (Path.symm (Path.trans p (Path.symm p))) :=
      (Step.complexity_symm (Path.trans p (Path.symm p))).symm

def Step.complexity_symm_symm_trans_decreases
    {A : Type u} {a b : A} (p : Path a b) :
    Step.complexity (Path.symm (Path.refl b)) ≤
      Step.complexity (Path.symm (Path.trans (Path.symm p) p)) := by
  calc
    Step.complexity (Path.symm (Path.refl b))
        = Step.complexity (Path.refl b) := Step.complexity_symm (Path.refl b)
    _ ≤ Step.complexity (Path.trans (Path.symm p) p) := Step.complexity_symm_trans_decreases p
    _ = Step.complexity (Path.symm (Path.trans (Path.symm p) p)) :=
      (Step.complexity_symm (Path.trans (Path.symm p) p)).symm

def Step.complexity_symm_trans_symm_strict_decreases
    {A : Type u} {a b : A} (p : Path a b)
    (hp : 0 < Step.complexity p) :
    Step.complexity (Path.symm (Path.refl a)) <
      Step.complexity (Path.symm (Path.trans p (Path.symm p))) := by
  simpa using Step.complexity_trans_symm_strict p hp

def Step.complexity_symm_symm_trans_strict_decreases
    {A : Type u} {a b : A} (p : Path a b)
    (hp : 0 < Step.complexity p) :
    Step.complexity (Path.symm (Path.refl b)) <
      Step.complexity (Path.symm (Path.trans (Path.symm p) p)) := by
  simpa using Step.complexity_symm_trans_strict p hp

def Step.complexity_symm_trans_cancel_left_strict
    {A : Type u} {a b c : A} (p : Path a b) (q : Path a c)
    (hp : 0 < Step.complexity p) :
    Step.complexity (Path.symm q) <
      Step.complexity (Path.symm (Path.trans p (Path.trans (Path.symm p) q))) := by
  simp only [Step.complexity_symm]
  exact Step.complexity_trans_cancel_left_strict p q hp

def Step.complexity_symm_trans_cancel_right_strict
    {A : Type u} {a b c : A} (p : Path a b) (q : Path b c)
    (hp : 0 < Step.complexity p) :
    Step.complexity (Path.symm q) <
      Step.complexity (Path.symm (Path.trans (Path.symm p) (Path.trans p q))) := by
  simp only [Step.complexity_symm]
  exact Step.complexity_trans_cancel_right_strict p q hp

end Path
end ComputationalPaths
