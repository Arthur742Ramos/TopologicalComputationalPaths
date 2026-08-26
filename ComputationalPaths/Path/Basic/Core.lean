/-
# Basic combinators for computational paths (core)

Core definitions for computational paths: we introduce elementary rewrite
steps, package them into paths, and record the foundational operations
(`refl`, `symm`, `trans`) together with transport/substitution infrastructure.

Important: `Path` is a structure that *records* a propositional equality
(`proof : a = b`) plus a list of rewrite steps as metadata.  The equality
semantics are given entirely by the `proof` field (Lean's `Eq` in `Prop`, hence
UIP/proof-irrelevance), while the `steps` list preserves a trace for the
computational-path rewriting system.  This is *not* the HoTT identity type: we
do not treat `Path` as a higher inductive identity, and we intentionally rely
on UIP to keep coherence proofs proof-irrelevant.
-/

namespace List

@[simp] theorem map_reverse_eq_reverse_map {α β : Type _}
    (f : α → β) (xs : List α) :
    xs.reverse.map f = (xs.map f).reverse := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [List.reverse_cons, ih, List.map_append, List.map_cons]

end List

namespace ComputationalPaths

open List Function

universe u v w

/-- An elementary rewrite step between two elements of `A`. The fields record
the source, the target, and the propositional equality justifying the step.
The equality proof lives in `Prop`, so different proofs are definitionally
irrelevant (UIP). -/
structure Step (A : Type u) where
  src : A
  tgt : A
  proof : src = tgt

namespace Step

variable {A : Type u} {B : Type v}

/-- Reverse the direction of a rewrite step. -/
@[simp] noncomputable def symm (s : Step A) : Step A :=
  Step.mk s.tgt s.src s.proof.symm

/-- Map a rewrite step through a function. -/
@[simp] noncomputable def map (f : A → B) (s : Step A) : Step B :=
  Step.mk (f s.src) (f s.tgt) (_root_.congrArg f s.proof)

@[simp] theorem symm_symm (s : Step A) : symm (symm s) = s := by
  cases s
  rfl

@[simp] theorem map_symm (f : A → B) (s : Step A) :
    map f (symm s) = symm (map f s) := by
  cases s
  rfl

@[simp] theorem map_id (s : Step A) :
    map (fun x : A => x) s = s := by
  cases s
  simp [map]

end Step

/-- A computational path from `a` to `b`. The equality semantics come solely from
`proof : a = b`; the `steps` list is metadata recording a rewrite trace used by
the path-rewrite system (`RwEq`, normalisation, and derived groupoid laws).

This is not the HoTT identity type: `Path` packages a proof-irrelevant equality
with its trace, and different traces can witness the same equality.
Composition concatenates the trace; symmetry reverses it. -/
structure Path {A : Type u} (a b : A) where
  steps : List (Step A)
  proof : a = b

namespace Path

variable {A : Type u} {B : Type v} {C : Type w}
variable {a b c d : A}
variable {a1 a2 a3 : A} {b1 b2 b3 : B}


/-- Helper showing that mapping the identity over step lists is a no-op. -/
@[simp] theorem steps_map_id (steps : List (Step A)) :
    steps.map (Step.map fun x : A => x) = steps := by
  induction steps with
  | nil => simp
  | cons s tail ih =>
      cases s
      simp [Step.map, ih]

/-- Extract the propositional equality witnessed by a path.  This is the
semantic equality; the trace `steps` does not affect `toEq`. -/
@[simp] noncomputable def toEq (p : Path a b) : a = b :=
  p.proof

/-- Reflexive path (empty sequence of rewrites). -/
@[simp] noncomputable def refl (a : A) : Path a a :=
  Path.mk [] rfl

/-- Path consisting of a single rewrite step. -/
@[simp] noncomputable def ofEq (h : a = b) : Path a b :=
  Path.mk [Step.mk a b h] h

/-- Path consisting of a single explicit step-chain witness. -/
@[simp] noncomputable def stepChain (h : a = b) : Path a b :=
  Path.mk [Step.mk a b h] h

@[simp] theorem toEq_ofEq (h : a = b) : toEq (ofEq h) = h := rfl
@[simp] theorem toEq_stepChain (h : a = b) : toEq (stepChain h) = h := rfl

/-- Paths built from two equality witnesses are definitionally equal.
This reflects proof irrelevance (UIP) for Lean's `Eq` in `Prop`. -/
@[simp] theorem ofEq_eq_ofEq (h₁ h₂ : a = b) :
    ofEq h₁ = ofEq h₂ := by
  cases h₁
  cases h₂
  simp [ofEq]

/-- Compose two paths, concatenating their step lists. -/
@[simp] noncomputable def trans (p : Path a b) (q : Path b c) : Path a c :=
  Path.mk (p.steps ++ q.steps) (p.proof.trans q.proof)

/-- Reverse a path by reversing and inverting each step. -/
@[simp] noncomputable def symm (p : Path a b) : Path b a :=
  Path.mk (p.steps.reverse.map Step.symm) p.proof.symm

/-- Paper notation `invA` for symmetry of computational paths. -/
@[simp] noncomputable def invA (p : Path a b) : Path b a :=
  symm p

/-- Paper notation `cmpA` for path composition. -/
@[simp] noncomputable def cmpA (p : Path a b) (q : Path b c) : Path a c :=
  trans p q

/-- Cast an element from `D a` to `D b` given a path `p : Path a b`. -/
noncomputable def cast {D : A → Sort v} (p : Path a b) (x : D a) : D b :=
  Eq.recOn p.proof x

@[simp] theorem cast_refl {D : A → Sort v} (x : D a) :
    cast (refl a) x = x := rfl

@[simp] theorem trans_steps (p : Path a b) (q : Path b c) :
    (trans p q).steps = p.steps ++ q.steps := rfl

@[simp] theorem symm_steps (p : Path a b) :
    (symm p).steps = p.steps.reverse.map Step.symm := rfl

@[simp] theorem symm_trans (p : Path a b) (q : Path b c) :
    symm (trans p q) = trans (symm q) (symm p) := by
  cases p with
  | mk steps1 proof1 =>
      cases q with
      | mk steps2 proof2 =>
          cases proof1
          cases proof2
          simp [symm, trans, List.reverse_append, List.map_append]

@[simp] theorem trans_refl_left (p : Path a b) : trans (refl a) p = p := by
  cases p
  simp [trans, refl]

@[simp] theorem trans_refl_right (p : Path a b) : trans p (refl b) = p := by
  cases p
  simp [trans, refl]

/-- Associativity of path composition. -/
@[simp] theorem trans_assoc (p : Path a b) (q : Path b c) (r : Path c d) :
    trans (trans p q) r = trans p (trans q r) := by
  cases p with
  | mk steps1 proof1 =>
      cases q with
      | mk steps2 proof2 =>
          cases r with
          | mk steps3 proof3 =>
              cases proof1
              cases proof2
              cases proof3
              simp [trans, List.append_assoc]

/-- Fourfold associativity (left-nested to right-nested). -/
theorem trans_assoc_fourfold {e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    trans (trans (trans p q) r) s = trans p (trans q (trans r s)) := by
  calc
    trans (trans (trans p q) r) s
        = trans (trans p q) (trans r s) := trans_assoc (trans p q) r s
    _ = trans p (trans q (trans r s)) := trans_assoc p q (trans r s)

/-- Alternate fourfold reassociation through the inner-associator route. -/
theorem trans_assoc_fourfold_alt {e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    trans (trans (trans p q) r) s = trans p (trans q (trans r s)) := by
  calc
    trans (trans (trans p q) r) s
        = trans (trans p (trans q r)) s := by
            exact _root_.congrArg (fun t => trans t s) (trans_assoc p q r)
    _ = trans p (trans (trans q r) s) := trans_assoc p (trans q r) s
    _ = trans p (trans q (trans r s)) := by
          exact _root_.congrArg (fun t => trans p t) (trans_assoc q r s)

/-- Pentagon identity for the associator `trans_assoc`. -/
theorem trans_assoc_pentagon {e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Eq.trans (trans_assoc (trans p q) r s) (trans_assoc p q (trans r s)) =
      Eq.trans
        (_root_.congrArg (fun t => trans t s) (trans_assoc p q r))
        (Eq.trans
          (trans_assoc p (trans q r) s)
          (_root_.congrArg (fun t => trans p t) (trans_assoc q r s))) := by
  -- Structural: this is equality between proofs in `Prop` (Eq proof irrelevance).
  apply Subsingleton.elim

/-- Mac Lane coherence: any two reassociations with identical endpoints agree. -/
theorem mac_lane_coherence {e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e)
    (h₁ h₂ :
      trans (trans (trans p q) r) s = trans p (trans q (trans r s))) :
    h₁ = h₂ := by
  -- Structural: this compares proofs of the same proposition.
  apply Subsingleton.elim

/-- Specialization of Mac Lane coherence to the two standard fourfold routes. -/
theorem mac_lane_coherence_fourfold {e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Eq.trans (trans_assoc (trans p q) r s) (trans_assoc p q (trans r s)) =
      trans_assoc_fourfold_alt p q r s := by
  -- Structural: both sides are proofs in `Prop`.
  apply Subsingleton.elim

/-- Step-trace companion to fourfold coherence: both reassociation routes yield
the same rewrite trace. -/
theorem mac_lane_coherence_fourfold_steps {e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    (trans (trans (trans p q) r) s).steps =
      (trans p (trans q (trans r s))).steps := by
  simp [trans, List.append_assoc]

/-- Step-trace companion: reversing and symmetrizing a trace twice is identity. -/
def trace_symm_involutive (steps : List (Step A)) :
    (steps.reverse.map Step.symm).reverse.map Step.symm = steps := by
  have hmap : List.map (Step.symm ∘ Step.symm) steps = steps := by
    induction steps with
    | nil => simp
    | cons s tail ih =>
        simp [Function.comp, ih]
  calc
    (steps.reverse.map Step.symm).reverse.map Step.symm
        = List.map (Step.symm ∘ Step.symm) steps := by
            simp [List.map_map]
    _ = steps := hmap

/-- Left whiskering of a 2-path by postcomposition. -/
@[simp] noncomputable def whiskerLeft {p p' : Path a b} (h : p = p') (q : Path b c) :
    trans p q = trans p' q :=
  _root_.congrArg (fun t => trans t q) h

/-- Right whiskering of a 2-path by precomposition. -/
@[simp] noncomputable def whiskerRight (p : Path a b) {q q' : Path b c} (h : q = q') :
    trans p q = trans p q' :=
  _root_.congrArg (fun t => trans p t) h

@[simp] theorem whiskerLeft_refl (p : Path a b) (q : Path b c) :
    whiskerLeft (p := p) (p' := p) rfl q = rfl := rfl

@[simp] theorem whiskerRight_refl (p : Path a b) (q : Path b c) :
    whiskerRight (p := p) (q := q) (q' := q) rfl = rfl := rfl

@[simp] theorem whiskerLeft_trans {p₁ p₂ p₃ : Path a b}
    (h₁ : p₁ = p₂) (h₂ : p₂ = p₃) (q : Path b c) :
    whiskerLeft (Eq.trans h₁ h₂) q =
      Eq.trans (whiskerLeft h₁ q) (whiskerLeft h₂ q) := by
  cases h₁
  cases h₂
  rfl

@[simp] theorem whiskerRight_trans (p : Path a b) {q₁ q₂ q₃ : Path b c}
    (h₁ : q₁ = q₂) (h₂ : q₂ = q₃) :
    whiskerRight (p := p) (Eq.trans h₁ h₂) =
      Eq.trans (whiskerRight (p := p) h₁) (whiskerRight (p := p) h₂) := by
  cases h₁
  cases h₂
  rfl

@[simp] theorem whiskerLeft_symm {p p' : Path a b}
    (h : p = p') (q : Path b c) :
    whiskerLeft (Eq.symm h) q = Eq.symm (whiskerLeft h q) := by
  cases h
  rfl

@[simp] theorem whiskerRight_symm (p : Path a b) {q q' : Path b c}
    (h : q = q') :
    whiskerRight (p := p) (Eq.symm h) = Eq.symm (whiskerRight (p := p) h) := by
  cases h
  rfl

/-- Naturality square for left and right whiskering. -/
theorem whisker_naturality {p p' : Path a b} {q q' : Path b c}
    (h : p = p') (k : q = q') :
    Eq.trans (whiskerRight p k) (whiskerLeft h q') =
      Eq.trans (whiskerLeft h q) (whiskerRight p' k) := by
  cases h
  cases k
  rfl

/-- Interchange law for 2-path loops. -/
theorem two_path_interchange {p : Path a b}
    (α β γ δ : p = p) :
    Eq.trans (Eq.trans α β) (Eq.trans γ δ) =
      Eq.trans (Eq.trans α γ) (Eq.trans β δ) := by
  -- Structural: 2-path loops are proofs in `Prop`.
  apply Subsingleton.elim

/-- Eckmann–Hilton commutativity for 2-path loops. -/
theorem eckmann_hilton_two_paths {p : Path a b}
    (α β : p = p) :
    Eq.trans α β = Eq.trans β α := by
  -- Structural: equality between equality-proofs in `Prop`.
  apply Subsingleton.elim

/-- Step-trace companion to 2-path loop laws: inversion reverses composite
traces in the expected order. -/
theorem symm_trans_steps_concat (p : Path a b) (q : Path b c) :
    (symm (trans p q)).steps = (symm q).steps ++ (symm p).steps := by
  simp [trans, symm, List.reverse_append, List.map_append]

@[simp] theorem symm_refl (a : A) : symm (refl a) = refl a := by
  simp [symm, refl]

/-- Taking symmetry twice yields the original path. -/
@[simp] theorem symm_symm (p : Path a b) : symm (symm p) = p := by
  cases p with
  | mk steps proof =>
      cases proof
      have hmap :
          List.map Step.symm (List.map Step.symm steps) = steps := by
        induction steps with
        | nil => simp
        | cons s tail ih =>
            cases s
            simp [Step.symm, ih]
      calc
        symm (symm (Path.mk steps rfl))
            = Path.mk ((steps.reverse.map Step.symm).reverse.map Step.symm) rfl := rfl
        _ = Path.mk (List.map Step.symm (List.map Step.symm steps)) rfl := by
              simp
        _ = Path.mk steps rfl := by
              simp [hmap]

@[simp] theorem toEq_trans (p : Path a b) (q : Path b c) :
    toEq (trans p q) = (toEq p).trans (toEq q) := rfl

@[simp] theorem toEq_symm (p : Path a b) :
    toEq (symm p) = (toEq p).symm := rfl

@[simp] theorem toEq_trans_symm (p : Path a b) :
    toEq (trans p (symm p)) = rfl := by
  cases p
  simp

@[simp] theorem toEq_symm_trans (p : Path a b) :
    toEq (trans (symm p) p) = rfl := by
  cases p
  simp

@[simp] theorem cmpA_refl_left (p : Path a b) :
    cmpA (refl a) p = p :=
  trans_refl_left p

@[simp] theorem cmpA_refl_right (p : Path a b) :
    cmpA p (refl b) = p :=
  trans_refl_right p

@[simp] theorem cmpA_assoc (p : Path a b) (q : Path b c)
    (r : Path c d) :
    cmpA (cmpA p q) r = cmpA p (cmpA q r) :=
  trans_assoc p q r

@[simp] theorem cmpA_inv_right_toEq (p : Path a b) :
    toEq (cmpA p (invA p)) = rfl := by
  simp

@[simp] theorem cmpA_inv_left_toEq (p : Path a b) :
    toEq (cmpA (invA p) p) = rfl := by
  simp

/-! ## Transport bridge -/

/-- Transport along a path. -/
noncomputable def transport {D : A → Sort v} (p : Path a b) (x : D a) : D b :=
  Eq.recOn p.proof x

@[simp] theorem transport_refl {D : A → Sort v} (x : D a) :
    transport (refl a) x = x := rfl

@[simp] theorem transport_trans {D : A → Sort v}
    (p : Path a b) (q : Path b c) (x : D a) :
    transport (trans p q) x =
      transport q (transport p x) := by
  cases p with
  | mk steps1 proof1 =>
      cases q with
      | mk steps2 proof2 =>
          cases proof1
          cases proof2
          rfl

section Dependent

variable {A : Type u} {B : A → Type v}
variable (f : ∀ x : A, B x)
variable {a b : A}

/-- Apply a dependent function to a path, yielding the transported result. -/
@[simp] noncomputable def apd (p : Path a b) :
    Path (transport (A := A) (D := fun x => B x) p (f a)) (f b) := by
  cases p with
  | mk steps h =>
      cases h
      simpa [transport] using (refl (f a))

@[simp] theorem apd_refl (a : A) :
    apd (f := f) (refl a) = refl (f a) := by
  simp [apd, transport]

end Dependent

@[simp] theorem transport_symm_left {D : A → Sort v}
    (p : Path a b) (x : D a) :
    transport (symm p) (transport p x) = x := by
  cases p with
  | mk steps proof =>
      cases proof
      rfl

@[simp] theorem transport_symm_right {D : A → Sort v}
    (p : Path a b) (y : D b) :
    transport p (transport (symm p) y) = y := by
  cases p with
  | mk steps proof =>
      cases proof
      rfl

/-- Transport along a path built from a propositional equality computes to
`Eq.mp` on that equality. -/
@[simp] theorem transport_ofEq {D : A → Sort v}
    {a b : A} (h : a = b) (x : D a) :
    transport (A := A) (D := D)
      (ofEq (A := A) (a := a) (b := b) h) x =
    Eq.mp (congrArg D h) x := by
  cases h
  rfl

/-- Transport along the symmetric of a path built from a propositional
equality computes to `Eq.mpr`. -/
@[simp] theorem transport_symm_ofEq {D : A → Sort v}
    {a b : A} (h : a = b) (y : D b) :
    transport (A := A) (D := D)
      (symm (ofEq (A := A) (a := a) (b := b) h)) y =
    Eq.mpr (congrArg D h) y := by
  cases h
  rfl

@[simp] theorem transport_of_toEq_eq {D : A → Sort v}
    {p q : Path a b} (h : p.toEq = q.toEq) (x : D a) :
    transport (D := D) p x = transport (D := D) q x := by
  cases p with
  | mk steps₁ proof₁ =>
      cases q with
      | mk steps₂ proof₂ =>
          cases proof₁
          cases proof₂
          cases h
          rfl

@[simp] theorem transport_const {D : Type v} (p : Path a b) (x : D) :
    transport (D := fun _ => D) p x = x := by
  cases p with
  | mk steps proof =>
      cases proof
      rfl

/-- Substitution along a path, following the paper's notation. -/
noncomputable def subst {D : A → Sort v} (x : D a) (p : Path a b) : D b :=
  transport p x

@[simp] theorem subst_refl {D : A → Sort v} (x : D a) :
    subst (D := D) x (refl a) = x := rfl

@[simp] theorem subst_trans {D : A → Sort v}
    (x : D a) (p : Path a b) (q : Path b c) :
    subst (D := D) x (trans p q) =
      subst (D := D) (subst (D := D) x p) q :=
  transport_trans (D := D) p q x

@[simp] theorem subst_symm_left {D : A → Sort v}
    (x : D a) (p : Path a b) :
    subst (D := D) (subst (D := D) x p) (symm p) = x :=
  transport_symm_left (D := D) p x

@[simp] theorem subst_symm_right {D : A → Sort v}
    (y : D b) (p : Path a b) :
    subst (D := D) (subst (D := D) y (symm p)) p = y :=
  transport_symm_right (D := D) p y

@[simp] theorem subst_const {D : Type v} (x : D) (p : Path a b) :
    subst (D := fun _ => D) x p = x :=
  transport_const (p := p) (x := x)

@[simp] theorem subst_ofEq {D : A → Sort v} (x : D a) (h : a = b) :
    subst (D := D) x (ofEq h) = Eq.recOn h x := rfl

@[simp] theorem subst_symm_ofEq {D : A → Sort v}
    (y : D b) (h : a = b) :
    subst (D := D) y (symm (ofEq h)) = Eq.recOn h.symm y := rfl

/-- Transport across two independent path arguments.  The value is first
carried along the `A`-component, and the resulting element is transported
along the `B`-component. -/
@[simp] noncomputable def transport₂ {A : Type u} {B : Type v}
    {D : A → B → Sort w}
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) (x : D a₁ b₁) : D a₂ b₂ :=
  transport (D := fun b => D a₂ b) q
    (transport (D := fun a => D a b₁) p x)

@[simp] theorem transport₂_refl_left {A : Type u} {B : Type v}
    {D : A → B → Sort w} {a : A} {b₁ b₂ : B}
    (q : Path b₁ b₂) (x : D a b₁) :
    transport₂ (D := D) (refl a) q x =
      transport (D := fun b => D a b) q x := by
  cases q with
  | mk steps proof =>
      cases proof
      simp [transport₂, transport]

@[simp] theorem transport₂_refl_right {A : Type u} {B : Type v}
    {D : A → B → Sort w} {a₁ a₂ : A} {b : B}
    (p : Path a₁ a₂) (x : D a₁ b) :
    transport₂ (D := D) p (refl b) x =
      transport (D := fun a => D a b) p x := by
  cases p with
  | mk steps proof =>
      cases proof
      simp [transport₂, transport]

@[simp] theorem transport₂_refl {A : Type u} {B : Type v}
    {D : A → B → Sort w} {a : A} {b : B} (x : D a b) :
    transport₂ (D := D) (refl a) (refl b) x = x := by
  simp [transport₂, transport]

@[simp] theorem transport₂_trans_left {A : Type u} {B : Type v}
    {D : A → B → Sort w}
    {a₁ a₂ a₃ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path a₂ a₃)
    (r : Path b₁ b₂) (x : D a₁ b₁) :
    transport₂ (D := D) (trans p q) r x =
      transport₂ (D := D) q r (transport₂ (D := D) p (refl b₁) x) := by
  cases p with
  | mk steps₁ proof₁ =>
    cases proof₁
    cases q with
    | mk steps₂ proof₂ =>
      cases proof₂
      cases r with
      | mk steps₃ proof₃ =>
        simp [transport₂, transport]

@[simp] theorem transport₂_trans_right {A : Type u} {B : Type v}
    {D : A → B → Sort w}
    {a₁ a₂ : A} {b₁ b₂ b₃ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) (r : Path b₂ b₃)
    (x : D a₁ b₁) :
    transport₂ (D := D) p (trans q r) x =
      transport₂ (D := D) p r (transport₂ (D := D) (refl a₁) q x) := by
  cases p with
  | mk steps₁ proof₁ =>
    cases proof₁
    cases q with
    | mk steps₂ proof₂ =>
      cases proof₂
      cases r with
      | mk steps₃ proof₃ =>
        simp [transport₂, transport]

@[simp] theorem transport₂_symm_left {A : Type u} {B : Type v}
    {D : A → B → Sort w}
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂)
    (x : D a₁ b₁) :
    transport₂ (D := D) (symm p) q (transport₂ (D := D) p (refl b₁) x) =
      transport (D := fun b => D a₁ b) q x := by
  cases p with
  | mk steps₁ proof₁ =>
      cases proof₁
      cases q with
      | mk steps₂ proof₂ =>
          cases proof₂
          simp [transport₂, transport]

@[simp] theorem transport₂_symm_right {A : Type u} {B : Type v}
    {D : A → B → Sort w}
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂)
    (x : D a₁ b₁) :
    transport₂ (D := D) p (symm q) (transport₂ (D := D) (refl a₁) q x) =
      transport (D := fun a => D a b₁) p x := by
  cases p with
  | mk steps₁ proof₁ =>
      cases proof₁
      cases q with
      | mk steps₂ proof₂ =>
          cases proof₂
          simp [transport₂, transport]

@[simp] theorem transport₂_const {A : Type u} {B : Type v}
    {D : Type w} {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) (x : D) :
    transport₂ (D := fun _ _ => D) p q x = x := by
  cases p with
  | mk steps₁ proof₁ =>
      cases proof₁
      cases q with
      | mk steps₂ proof₂ =>
          cases proof₂
          simp [transport₂, transport]

/-- Substitution across two arguments, mirroring the binary transport. -/
@[simp] noncomputable def subst₂ {A : Type u} {B : Type v}
    {D : A → B → Sort w}
    {a₁ a₂ : A} {b₁ b₂ : B}
    (x : D a₁ b₁) (p : Path a₁ a₂) (q : Path b₁ b₂) : D a₂ b₂ :=
  transport₂ (D := D) p q x

@[simp] theorem subst₂_refl_left {A : Type u} {B : Type v}
    {D : A → B → Sort w} {a : A} {b₁ b₂ : B}
    (q : Path b₁ b₂) (x : D a b₁) :
    subst₂ (D := D) x (refl a) q =
      subst (D := fun b => D a b) x q :=
  transport₂_refl_left (D := D) q x

@[simp] theorem subst₂_refl_right {A : Type u} {B : Type v}
    {D : A → B → Sort w} {a₁ a₂ : A} {b : B}
    (p : Path a₁ a₂) (x : D a₁ b) :
    subst₂ (D := D) x p (refl b) =
      subst (D := fun a => D a b) x p :=
  transport₂_refl_right (D := D) p x

@[simp] theorem subst₂_trans_left {A : Type u} {B : Type v}
    {D : A → B → Sort w}
    {a₁ a₂ a₃ : A} {b₁ b₂ : B}
    (x : D a₁ b₁) (p : Path a₁ a₂)
    (q : Path a₂ a₃) (r : Path b₁ b₂) :
    subst₂ (D := D) x (trans p q) r =
      subst₂ (D := D) (subst₂ (D := D) x p (refl b₁)) q r :=
  transport₂_trans_left (D := D) p q r x

@[simp] theorem subst₂_trans_right {A : Type u} {B : Type v}
    {D : A → B → Sort w}
    {a₁ a₂ : A} {b₁ b₂ b₃ : B}
    (x : D a₁ b₁) (p : Path a₁ a₂)
    (q : Path b₁ b₂) (r : Path b₂ b₃) :
    subst₂ (D := D) x p (trans q r) =
      subst₂ (D := D) (subst₂ (D := D) x (refl a₁) q) p r :=
  transport₂_trans_right (D := D) p q r x

@[simp] theorem subst₂_symm_left {A : Type u} {B : Type v}
    {D : A → B → Sort w}
    {a₁ a₂ : A} {b₁ b₂ : B}
    (x : D a₁ b₁) (p : Path a₁ a₂) (q : Path b₁ b₂) :
    subst₂ (D := D) (subst₂ (D := D) x p (refl b₁)) (symm p) q =
      subst (D := fun b => D a₁ b) x q :=
  transport₂_symm_left (D := D) p q x

@[simp] theorem subst₂_symm_right {A : Type u} {B : Type v}
    {D : A → B → Sort w}
    {a₁ a₂ : A} {b₁ b₂ : B}
    (x : D a₁ b₁) (p : Path a₁ a₂) (q : Path b₁ b₂) :
    subst₂ (D := D) (subst₂ (D := D) x (refl a₁) q) p (symm q) =
      subst (D := fun a => D a b₁) x p :=
  transport₂_symm_right (D := D) p q x

@[simp] theorem subst₂_const {A : Type u} {B : Type v}
    {D : Type w} {a₁ a₂ : A} {b₁ b₂ : B}
    (x : D) (p : Path a₁ a₂) (q : Path b₁ b₂) :
    subst₂ (D := fun _ _ => D) x p q = x :=
  transport₂_const (D := D) p q x

/-- Congruence of unary functions along paths. -/
@[simp] noncomputable def congrArg (f : A → B) (p : Path a b) :
    Path (f a) (f b) :=
  Path.mk (p.steps.map (Step.map f)) (_root_.congrArg f p.proof)

theorem transport_congrArg {D : A → Type w}
    {a b : A} (p : Path a b) (x : D a) :
    transport (A := A) (D := D) p x =
      Path.transport (A := Type w) (D := fun X => X)
        (congrArg (fun t => D t) p) x := by
  cases p with
  | mk steps proof =>
      cases proof
      simp [transport]

theorem transport_compose {A B : Type u} {P : B → Type v}
    (f : A → B) {a1 a2 : A} (p : Path a1 a2) (x : P (f a1)) :
    transport (D := P ∘ f) p x = transport (D := P) (Path.congrArg f p) x := by
  cases p with
  | mk steps proof =>
      cases proof
      rfl

theorem transport_app {P Q : A → Type v} (f : ∀ x, P x → Q x)
    {a1 a2 : A} (p : Path a1 a2) (u : P a1) :
    transport (D := Q) p (f a1 u) = f a2 (transport (D := P) p u) := by
  cases p with
  | mk steps proof =>
      cases proof
      rfl

/-- Unary congruence preserves concatenation. -/
@[simp] theorem congrArg_trans (f : A → B)
    (p : Path a b) (q : Path b c) :
    congrArg f (trans p q) =
      trans (congrArg f p) (congrArg f q) := by
  cases p with
  | mk steps1 proof1 =>
      cases q with
      | mk steps2 proof2 =>
          cases proof1
          cases proof2
          simp [congrArg, trans, List.map_append]

/-- Unary congruence commutes with symmetry. -/
@[simp] theorem congrArg_symm (f : A → B)
    (p : Path a b) :
    congrArg f (symm p) =
      symm (congrArg f p) := by
  cases p with
  | mk steps proof =>
      cases proof
      simp [congrArg, symm]

@[simp] theorem congrArg_comp (f : B → C) (g : A → B)
  (p : Path a b) :
  congrArg (fun x => f (g x)) p =
    congrArg f (congrArg g p) := by
  cases p with
  | mk steps proof =>
      cases proof
      simp [congrArg]

@[simp] theorem congrArg_id (p : Path a b) :
    congrArg (fun x : A => x) p = p := by
  cases p with
  | mk steps proof =>
      cases proof
      have h := steps_map_id (A := A) steps
      simp [congrArg, h]

/-! ## Transport–composition naturality -/

/-- Transport along a path composes with `trans` in the expected way:
`transport (trans p q) = transport q ∘ transport p`. This is the definitional
content already shown in `transport_trans`; we record a curried version for
downstream convenience. -/
theorem transport_compose_eq {D : A → Sort v} {a b c : A}
    (p : Path a b) (q : Path b c) :
    (fun x => transport (D := D) (trans p q) x) =
      (fun x => transport (D := D) q (transport (D := D) p x)) := by
  funext x
  exact transport_trans (D := D) p q x

/-- Naturality square for transport: applying `f` after transport along
`p` equals transporting the codomain along `congrArg f p` after `f`. -/
theorem transport_naturality {D E : A → Type v}
    (f : ∀ x, D x → E x) {a b : A} (p : Path a b) (d : D a) :
    transport (D := E) p (f a d) = f b (transport (D := D) p d) :=
  transport_app f p d

/-- `apd` along `refl` yields `refl` at the propositional level. -/
@[simp] theorem apd_refl_toEq {B : A → Type v} (f : ∀ x, B x)
    (a : A) : (apd (B := B) f (refl a)).toEq = rfl := by
  simp [transport]

/-- Transport is an equivalence: the inverse is transport along `symm p`. -/
theorem transport_equiv {D : A → Sort v} {a b : A} (p : Path a b) :
    Function.LeftInverse
      (transport (D := D) (symm p))
      (transport (D := D) p) :=
  fun x => transport_symm_left (D := D) p x

end Path

end ComputationalPaths
