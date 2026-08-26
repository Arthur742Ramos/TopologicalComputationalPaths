/-
# Basic combinators for computational paths (congruence)

Additional machinery that builds on the core path operations: congruence for
unary and binary functions together with product, sum, sigma, and dependent
function constructions.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

open Function

universe u v w

namespace Path

variable {A : Type u} {B : Type v} {C : Type w}
variable {a1 a2 a3 : A} {b1 b2 b3 : B}

/-- Congruence in the first argument of a binary function. -/
@[simp] noncomputable def mapLeft (f : A → B → C) {a1 a2 : A}
    (p : Path a1 a2) (b : B) :
    Path (f a1 b) (f a2 b) :=
  congrArg (fun x => f x b) p

/-- `mapLeft` preserves concatenation of paths. -/
@[simp] theorem mapLeft_trans (f : A → B → C)
    {a1 a2 a3 : A} (p : Path a1 a2) (q : Path a2 a3) (b : B) :
    mapLeft f (trans p q) b =
      trans (mapLeft f p b) (mapLeft f q b) := by
  classical
  calc
    mapLeft f (trans p q) b
        = congrArg (fun x => f x b) (trans p q) := rfl
    _ = trans (congrArg (fun x => f x b) p)
          (congrArg (fun x => f x b) q) :=
        congrArg_trans (f := fun x => f x b) p q
    _ = trans (mapLeft f p b) (mapLeft f q b) := by rfl

/-- `mapLeft` commutes with symmetry. -/
@[simp] theorem mapLeft_symm (f : A → B → C)
    {a1 a2 : A} (p : Path a1 a2) (b : B) :
    mapLeft f (symm p) b =
      symm (mapLeft f p b) := by
  classical
  calc
    mapLeft f (symm p) b
        = congrArg (fun x => f x b) (symm p) := rfl
    _ = symm (congrArg (fun x => f x b) p) :=
        congrArg_symm (f := fun x => f x b) p
    _ = symm (mapLeft f p b) := by rfl

/-- Congruence in the second argument of a binary function. -/
@[simp] noncomputable def mapRight (f : A → B → C) (a : A)
    {b1 b2 : B} (p : Path b1 b2) :
    Path (f a b1) (f a b2) :=
  congrArg (f a) p

/-- `mapRight` preserves concatenation of paths. -/
@[simp] theorem mapRight_trans (f : A → B → C)
    (a : A) {b1 b2 b3 : B} (p : Path b1 b2) (q : Path b2 b3) :
    mapRight f a (trans p q) =
      trans (mapRight f a p) (mapRight f a q) := by
  classical
  calc
    mapRight f a (trans p q)
        = congrArg (f a) (trans p q) := rfl
    _ = trans (congrArg (f a) p) (congrArg (f a) q) :=
        congrArg_trans (f := f a) p q
    _ = trans (mapRight f a p) (mapRight f a q) := by rfl

/-- `mapRight` commutes with symmetry. -/
@[simp] theorem mapRight_symm (f : A → B → C)
    (a : A) {b1 b2 : B} (p : Path b1 b2) :
    mapRight f a (symm p) =
      symm (mapRight f a p) := by
  classical
  calc
    mapRight f a (symm p)
        = congrArg (f a) (symm p) := rfl
    _ = symm (congrArg (f a) p) := congrArg_symm (f := f a) p
    _ = symm (mapRight f a p) := by rfl

/-- Congruence in both arguments of a binary function. -/
@[simp] noncomputable def map2 (f : A → B → C)
    {a1 a2 : A} {b1 b2 : B}
    (p : Path a1 a2) (q : Path b1 b2) :
    Path (f a1 b1) (f a2 b2) :=
  trans (mapLeft f p b1) (mapRight f a2 q)

/-- Concatenating both arguments before applying `map2` factors through
the left component followed by the right component. -/
@[simp] theorem map2_trans (f : A → B → C)
    {a1 a2 a3 : A} {b1 b2 b3 : B}
    (p1 : Path a1 a2) (p2 : Path a2 a3)
    (q1 : Path b1 b2) (q2 : Path b2 b3) :
    map2 f (trans p1 p2) (trans q1 q2) =
      trans
        (mapLeft f p1 b1)
        (trans
          (mapLeft f p2 b1)
          (trans
            (mapRight f a3 q1)
            (mapRight f a3 q2))) := by
  classical
  simp [map2, mapLeft, mapRight]

/-- Symmetry of `map2` first reverses the right component, then the left one. -/
@[simp] theorem map2_symm (f : A → B → C)
    {a1 a2 : A} {b1 b2 : B}
    (p : Path a1 a2) (q : Path b1 b2) :
    symm (map2 f p q) =
      trans
        (mapRight f a2 (symm q))
        (mapLeft f (symm p) b1) := by
  classical
  have hRight :
      symm (mapRight f a2 q) = mapRight f a2 (symm q) :=
    (mapRight_symm (f := f) (a := a2) (p := q)).symm
  have hLeft :
      symm (mapLeft f p b1) = mapLeft f (symm p) b1 :=
    (mapLeft_symm (f := f) (p := p) (b := b1)).symm
  calc
    symm (map2 f p q)
        = trans (symm (mapRight f a2 q)) (symm (mapLeft f p b1)) := by
            simp [map2, mapLeft, mapRight]
    _ = trans (mapRight f a2 (symm q)) (symm (mapLeft f p b1)) := by
            rw [hRight]
    _ = trans (mapRight f a2 (symm q)) (mapLeft f (symm p) b1) := by
            rw [hLeft]

@[simp] theorem mapLeft_refl (f : A → B → C) (a : A) (b : B) :
    mapLeft f (refl a) b = refl (f a b) := by
  simp [mapLeft, refl]

@[simp] theorem mapRight_refl (f : A → B → C) (a : A) (b : B) :
    mapRight f a (refl b) = refl (f a b) := by
  simp [mapRight, refl]

@[simp] theorem map2_refl (f : A → B → C) (a : A) (b : B) :
    map2 f (refl a) (refl b) = refl (f a b) := by
  simp [map2, refl]

@[simp] theorem steps_refl (a : A) : (refl a).steps = [] := rfl

@[simp] theorem steps_ofEq {a b : A} (h : a = b) :
    (ofEq h).steps = [Step.mk a b h] := rfl

/-- The empty, reflexive path is not definitionally equal to the path that
records a single explicit reflexive rewrite. -/
theorem refl_ne_ofEq (a : A) :
    refl a ≠ ofEq (rfl : a = a) := by
  intro h
  have := _root_.congrArg Path.steps h
  simp [refl, ofEq] at this

section Prod

variable {A : Type u} {B : Type v}
variable {a1 a2 : A} {b1 b2 : B}

/-- Path on product values built componentwise. -/
@[simp] noncomputable def prodMk (p : Path a1 a2) (q : Path b1 b2) :
    Path (Prod.mk a1 b1) (Prod.mk a2 b2) :=
  map2 Prod.mk p q

/-- Project a path on pairs to a path on the first component. -/
@[simp] noncomputable def fst (p : Path (a1, b1) (a2, b2)) : Path a1 a2 :=
  congrArg Prod.fst p

/-- Project a path on pairs to a path on the second component. -/
@[simp] noncomputable def snd (p : Path (a1, b1) (a2, b2)) : Path b1 b2 :=
  congrArg Prod.snd p

@[simp] theorem prodMk_refl_refl (a : A) (b : B) :
    prodMk (refl a) (refl b) = refl (a, b) := by
  simp [prodMk]

@[simp] theorem transport_prodMk_fst
    {D : A → Sort w}
    {a1 a2 : A} {b1 b2 : B}
    (p : Path a1 a2) (q : Path b1 b2) (x : D a1) :
    transport (D := fun ab : Prod A B => D ab.fst) (prodMk p q) x =
      transport (D := D) p x := by
  cases p with
  | mk steps₁ proof₁ =>
      cases proof₁
      cases q with
      | mk steps₂ proof₂ =>
          cases proof₂
          simp [transport]

@[simp] theorem subst_prodMk_fst
    {D : A → Sort w}
    {a1 a2 : A} {b1 b2 : B}
    (p : Path a1 a2) (q : Path b1 b2) (x : D a1) :
    subst (D := fun ab : Prod A B => D ab.fst) x (prodMk p q) =
      subst (D := D) x p := by
  simpa [subst] using
    transport_prodMk_fst (A := A) (B := B) (D := D)
      (p := p) (q := q) (x := x)

@[simp] theorem transport_prodMk_snd
    {D : B → Sort w}
    {a1 a2 : A} {b1 b2 : B}
    (p : Path a1 a2) (q : Path b1 b2) (x : D b1) :
    transport (D := fun ab : Prod A B => D ab.snd) (prodMk p q) x =
      transport (D := D) q x := by
  cases p with
  | mk steps₁ proof₁ =>
      cases proof₁
      cases q with
      | mk steps₂ proof₂ =>
          cases proof₂
          simp [transport]

@[simp] theorem subst_prodMk_snd
    {D : B → Sort w}
    {a1 a2 : A} {b1 b2 : B}
    (p : Path a1 a2) (q : Path b1 b2) (x : D b1) :
    subst (D := fun ab : Prod A B => D ab.snd) x (prodMk p q) =
      subst (D := D) x q := by
  simpa [subst] using
    transport_prodMk_snd (A := A) (B := B) (D := D)
      (p := p) (q := q) (x := x)

@[simp] theorem transport_prodMk
    {D : A → B → Sort w}
    {a1 a2 : A} {b1 b2 : B}
    (p : Path a1 a2) (q : Path b1 b2) (x : D a1 b1) :
    transport (D := fun ab : Prod A B => D ab.fst ab.snd)
        (prodMk p q) x =
      transport₂ (D := D) p q x := by
  cases p with
  | mk steps₁ proof₁ =>
      cases proof₁
      cases q with
      | mk steps₂ proof₂ =>
          cases proof₂
          simp [transport, transport₂]

@[simp] theorem subst_prodMk
    {D : A → B → Sort w}
    {a1 a2 : A} {b1 b2 : B}
    (p : Path a1 a2) (q : Path b1 b2) (x : D a1 b1) :
    subst (D := fun ab : Prod A B => D ab.fst ab.snd)
        x (prodMk p q) =
      subst₂ (D := D) x p q := by
  simpa [subst, subst₂] using
    transport_prodMk (A := A) (B := B) (D := D)
      (p := p) (q := q) (x := x)

@[simp] theorem toEq_prodMk
    {p : Path (Prod.mk a1 b1) (Prod.mk a2 b2)} :
    (prodMk (fst p) (snd p)).toEq = p.toEq := by
  cases p
  rfl

@[simp] theorem toEq_fst_prodMk (p : Path a1 a2) (q : Path b1 b2) :
    (fst (prodMk p q)).toEq = p.toEq := by
  cases p
  cases q
  rfl

@[simp] theorem toEq_snd_prodMk (p : Path a1 a2) (q : Path b1 b2) :
    (snd (prodMk p q)).toEq = q.toEq := by
  cases p
  cases q
  rfl

@[simp] theorem transport_prod_fun
    {Z : Type w} {A_fam : Z → Type u} {B_fam : Z → Type v}
    {z1 z2 : Z} (p : Path z1 z2) (x : A_fam z1 × B_fam z1) :
    transport (D := fun z => A_fam z × B_fam z) p x =
      (transport (D := A_fam) p x.1, transport (D := B_fam) p x.2) := by
  cases p with
  | mk steps proof =>
      cases proof
      rfl

@[simp] theorem toEq_congrArg_prod_map
    {A' : Type u} {B' : Type v}
    (g : A → A') (h : B → B')
    (p : Path a1 a2) (q : Path b1 b2) :
    (congrArg (fun x : A × B => (g x.1, h x.2)) (prodMk p q)).toEq =
      (prodMk (congrArg g p) (congrArg h q)).toEq := by
  cases p
  cases q
  rfl

end Prod

section Sum

variable {A : Type u} {B : Type v}
variable {a1 a2 : A} {b1 b2 : B}

/-- Lift a path on the left summand to a path on the coproduct. -/
@[simp] noncomputable def inlCongr (p : Path a1 a2) :
    Path (Sum.inl a1 : Sum A B) (Sum.inl a2) :=
  congrArg Sum.inl p

/-- Lift a path on the right summand to a path on the coproduct. -/
@[simp] noncomputable def inrCongr (p : Path b1 b2) :
    Path (Sum.inr b1 : Sum A B) (Sum.inr b2) :=
  congrArg Sum.inr p

@[simp] theorem transport_inlCongr
    {DL : A → Sort w} {DR : B → Sort w}
    {a1 a2 : A} (p : Path a1 a2) (x : DL a1) :
    transport (D := fun s : Sum A B => Sum.elim DL DR s)
        (inlCongr (A := A) (B := B) p) x =
      transport (D := DL) p x := by
  cases p with
  | mk steps proof =>
      cases proof
      rfl

@[simp] theorem subst_inlCongr
    {DL : A → Sort w} {DR : B → Sort w}
    {a1 a2 : A} (p : Path a1 a2)
    (x : (fun s : Sum A B => Sum.elim DL DR s) (Sum.inl a1)) :
    subst (D := fun s : Sum A B => Sum.elim DL DR s)
        x (inlCongr (A := A) (B := B) p) =
      subst (D := DL) (by simpa using x) p := by
  change
    transport (D := fun s : Sum A B => Sum.elim DL DR s)
        (inlCongr (A := A) (B := B) p) x =
      transport (D := DL) p (by simpa using x)
  simpa [subst] using
    transport_inlCongr (A := A) (B := B)
      (DL := DL) (DR := DR) (p := p) (x := by simpa using x)

@[simp] theorem transport_inrCongr
    {DL : A → Sort w} {DR : B → Sort w}
    {b1 b2 : B} (p : Path b1 b2) (x : DR b1) :
    transport (D := fun s : Sum A B => Sum.elim DL DR s)
        (inrCongr (A := A) (B := B) p) x =
      transport (D := DR) p x := by
  cases p with
  | mk steps proof =>
      cases proof
      rfl

@[simp] theorem subst_inrCongr
    {DL : A → Sort w} {DR : B → Sort w}
    {b1 b2 : B} (p : Path b1 b2)
    (x : (fun s : Sum A B => Sum.elim DL DR s) (Sum.inr b1)) :
    subst (D := fun s : Sum A B => Sum.elim DL DR s)
        x (inrCongr (A := A) (B := B) p) =
      subst (D := DR) (by simpa using x) p := by
  change
    transport (D := fun s : Sum A B => Sum.elim DL DR s)
        (inrCongr (A := A) (B := B) p) x =
      transport (D := DR) p (by simpa using x)
  simpa [subst] using
    transport_inrCongr (A := A) (B := B)
      (DL := DL) (DR := DR) (p := p) (x := by simpa using x)

end Sum

section Sigma

variable {A : Type u} {B : A → Type u}
variable {a1 a2 : A}
variable {b1 : B a1} {b2 : B a2}

/-- Build a path between dependent pairs from a base path and a fibre path. -/
@[simp] noncomputable def sigmaMk (p : Path a1 a2)
    (q : Path (transport (A := A) (D := fun a => B a) p b1) b2) :
    Path (Sigma.mk a1 b1) (Sigma.mk a2 b2) :=
  Path.stepChain <| by
    classical
    cases p with
    | mk steps1 h1 =>
        cases h1
        cases q with
        | mk steps2 h2 =>
            cases h2
            simp [transport]

/-- Project a path on dependent pairs to the path on the first component. -/
@[simp] noncomputable def sigmaFst (p : Path (Sigma.mk a1 b1) (Sigma.mk a2 b2)) :
    Path a1 a2 :=
  congrArg Sigma.fst p

/-- Project a path on dependent pairs to a path in the fibre of the second component. -/
@[simp] noncomputable def sigmaSnd (p : Path (Sigma.mk a1 b1) (Sigma.mk a2 b2)) :
    Path
      (transport (A := A) (D := fun a => B a) (sigmaFst (B := B) p) b1)
      b2 :=
  Path.stepChain <| by
    classical
    cases p with
    | mk steps h =>
        cases h
        simp [transport]

/-- Helper producing the fibre witness that appears when symmetrising
`sigmaMk` paths. -/
@[simp] noncomputable def sigmaSymmSnd
    (p : Path a1 a2)
    (q : Path (transport (A := A) (D := fun a => B a) p b1) b2) :
    Path (A := B a1)
      (Path.transport (A := A) (D := fun a => B a) (Path.symm p) b2)
      b1 :=
  Path.trans
    (Path.symm
      (Path.congrArg
        (fun z : B a2 =>
          Path.transport (A := A) (D := fun a => B a) (Path.symm p) z)
        q))
    (Path.stepChain
      (A := B a1)
      (a :=
        Path.transport (A := A) (D := fun a => B a) (Path.symm p)
          (Path.transport (A := A) (D := fun a => B a) p b1))
      (b := b1)
      (Path.transport_symm_left (A := A) (D := fun a => B a)
        (p := p) (x := b1)))

@[simp] theorem sigmaSnd_sigmaMk_eq_ofEq
    (p : Path a1 a2)
    (q : Path (transport (A := A) (D := fun a => B a) p b1) b2) :
    sigmaSnd (B := B) (sigmaMk (B := B) p q) =
      Path.stepChain
        (A := B a2)
        (a := transport (A := A) (D := fun a => B a)
              (sigmaFst (B := B) (sigmaMk (B := B) p q)) b1)
        (b := b2) q.toEq := by
  classical
  cases p with
  | mk steps1 h1 =>
      cases h1
      cases q with
      | mk steps2 h2 =>
          cases h2
          simp [sigmaSnd, sigmaMk, sigmaFst, Path.stepChain, transport]

@[simp] theorem transport_sigmaMk_fst
    {D : A → Sort w}
    {a1 a2 : A} {b1 : B a1} {b2 : B a2}
    (p : Path a1 a2)
    (q : Path (transport (A := A) (D := fun a => B a) p b1) b2)
    (x : D a1) :
    transport (D := fun z : Sigma B => D z.fst) (sigmaMk p q) x =
      transport (D := D) p x := by
  cases p with
  | mk steps₁ proof₁ =>
      cases proof₁
      cases q with
      | mk steps₂ proof₂ =>
          cases proof₂
          simp [transport]

@[simp] theorem subst_sigmaMk_fst
    {D : A → Sort w}
    {a1 a2 : A} {b1 : B a1} {b2 : B a2}
    (p : Path a1 a2)
    (q : Path (transport (D := fun a => B a) p b1) b2)
    (x : D a1) :
    subst (D := fun z : Sigma B => D z.fst) x (sigmaMk p q) =
      subst (D := D) x p := by
  simpa [subst] using
    transport_sigmaMk_fst (B := B) (D := D)
      (p := p) (q := q) (x := x)

/-- Transport for dependent types (Sigma types). -/
noncomputable def transportSigma {A : Type u} {B : A → Type v}
    {D : ∀ a, B a → Sort w}
    {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
    (p : Path a₁ a₂)
    (q : Path (transport (D := B) p b₁) b₂)
    (x : D a₁ b₁) : D a₂ b₂ :=
  by
    cases p with | mk _ h1 =>
    cases h1
    simp [transport] at q
    cases q with | mk _ h2 =>
    cases h2
    exact x

/-- Substitution for dependent types. -/
noncomputable def substSigma {A : Type u} {B : A → Type v}
    {D : ∀ a, B a → Sort w}
    {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
    (x : D a₁ b₁)
    (p : Path a₁ a₂)
    (q : Path (transport (D := B) p b₁) b₂) : D a₂ b₂ :=
  transportSigma p q x

@[simp] theorem transport_sigmaMk_dep
    {D : ∀ a, B a → Sort w}
    {a1 a2 : A} {b1 : B a1} {b2 : B a2}
    (p : Path a1 a2)
    (q : Path (transport (D := fun a => B a) p b1) b2)
    (x : D a1 b1) :
    transport (D := fun z : Sigma B => D z.fst z.snd)
        (sigmaMk p q) x =
      transportSigma (A := A) (B := B) (D := D) p q x := by
  cases p with
  | mk steps₁ proof₁ =>
    cases proof₁
    cases q with
    | mk steps₂ proof₂ =>
      cases proof₂
      simp [transportSigma, transport]

@[simp] theorem subst_sigmaMk_dep
    {D : ∀ a, B a → Sort w}
    {a1 a2 : A} {b1 : B a1} {b2 : B a2}
    (p : Path a1 a2)
    (q : Path (transport (D := fun a => B a) p b1) b2)
    (x : D a1 b1) :
    subst (D := fun z : Sigma B => D z.fst z.snd)
        x (sigmaMk p q) =
      substSigma (A := A) (B := B) (D := D) x p q := by
  simpa [substSigma, subst]
    using
      transport_sigmaMk_dep (A := A) (B := B) (D := D)
        (p := p) (q := q) (x := x)

end Sigma

section Function

variable {A : Type u} {B : Type v}
variable {f g h : A → B}

/-- Package pointwise paths into a path between functions. -/
@[simp] noncomputable def lamCongr (p : ∀ x : A, Path (f x) (g x)) : Path f g :=
  Path.mk [] (funext fun x => (p x).proof)

@[simp] noncomputable def app (p : Path f g) (a : A) : Path (f a) (g a) :=
  congrArg (fun h => h a) p

@[simp] theorem lamCongr_refl (f : A → B) :
    lamCongr (fun x => refl (f x)) = refl f := rfl

@[simp] theorem transport_arrow {A : Type u}
    {B : A → Sort v} {C : A → Sort w}
    {a b : A} (p : Path a b) (f : B a → C a) (y : B b) :
    Path.transport (A := A) (D := fun t => B t → C t) p f y =
      Path.transport (A := A) (D := C) p
        (f (Path.transport (A := A) (D := B)
          (Path.symm p) y)) := by
  cases p with
  | mk steps proof =>
      cases proof
      simp [transport]

@[simp] theorem lamCongr_trans
    (p : ∀ x : A, Path (f x) (g x))
    (q : ∀ x : A, Path (g x) (h x)) :
    trans (lamCongr (f := f) (g := g) p) (lamCongr (f := g) (g := h) q) =
      lamCongr (f := f) (g := h) (fun x => trans (p x) (q x)) := by
  classical
  simp [lamCongr, trans]

@[simp] theorem lamCongr_symm
    (p : ∀ x : A, Path (f x) (g x)) :
    symm (lamCongr (f := f) (g := g) p) =
      lamCongr (f := g) (g := f) (fun x => symm (p x)) := by
  classical
  simp [lamCongr, symm]

@[simp] theorem app_refl (f : A → B) (a : A) :
    app (refl f) a = refl (f a) := by
  simp [app]

@[simp] theorem app_trans (p : Path f g) (q : Path g h) (a : A) :
    app (trans p q) a =
      trans (app p a) (app q a) := by
  simp [app]

@[simp] theorem app_symm (p : Path f g) (a : A) :
    app (symm p) a = symm (app p a) := by
  simp [app]

@[simp] theorem toEq_lam_app {f g : A → B} (p : Path f g) :
    (lamCongr (fun x => app p x)).toEq = p.toEq := by
  cases p
  rfl

end Function

end Path

end ComputationalPaths
