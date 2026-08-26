/-
# Contextual substitution for computational paths

This module packages the "subterm substitution" principle from the paper, making
it possible to treat contexts with one or two holes uniformly.  The constructors
mirror Definition 3.5 (sub L/sub R) and propagate `Path` witnesses through those
contexts.
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Basic.Congruence

namespace ComputationalPaths
namespace Path

universe u v w

/-- A unary context `A ⊢ B` that can contain a single hole of type `A`. -/
structure Context (A : Type u) (B : Type v) where
  fill : A → B

namespace Context

variable {A : Type u} {B : Type v}

/-- Map a path through a unary context (paper's `sub L`). -/
@[simp] noncomputable def map (C : Context A B) {a b : A} (p : Path a b) :
    Path (C.fill a) (C.fill b) :=
  congrArg C.fill p

@[simp] theorem map_toEq (C : Context A B) {a b : A} (p : Path a b) :
  (map C p).toEq = _root_.congrArg C.fill p.toEq := rfl

@[simp] theorem map_refl (C : Context A B) (a : A) :
    map C (Path.refl a) = Path.refl (C.fill a) := by
  simp [map]

@[simp] theorem map_symm (C : Context A B) {a b : A} (p : Path a b) :
    map C (Path.symm p) = Path.symm (map C p) := by
  simp [map]

@[simp] theorem map_trans (C : Context A B)
    {a b c : A} (p : Path a b) (q : Path b c) :
    map C (Path.trans p q) =
      Path.trans (map C p) (map C q) := by
  simp [map]

@[simp] theorem map_ofEq (C : Context A B) {a b : A} (h : a = b) :
    map C (Path.stepChain (A := A) (a := a) (b := b) h) =
      Path.stepChain (A := B)
        (a := C.fill a) (b := C.fill b)
        (_root_.congrArg C.fill h) := by
  cases h
  simp [map]

/-- Compose two unary contexts. -/
@[simp] noncomputable def comp {C' : Type w}
    (g : Context B C') (f : Context A B) : Context A C' :=
  ⟨fun a => g.fill (f.fill a)⟩

@[simp] theorem map_comp {C' : Type w}
    (g : Context B C') (f : Context A B)
    {a b : A} (p : Path a b) :
    map (comp g f) p =
      map g (map f p) := by
  simp [map, comp]

/-- Substitution through a unary context on the "left" rewrite.
This packages the composition described in Definition 3.5 of the paper. -/
@[simp] noncomputable def substLeft (C : Context A B)
    {x : B} {a₁ a₂ : A}
    (h : Path x (C.fill a₁)) (p : Path a₁ a₂) :
    Path x (C.fill a₂) :=
  Path.trans h (map C p)

/-- Substitution through a unary context on the "right" rewrite.
This captures the second rule in Definition 3.5 of the paper. -/
@[simp] noncomputable def substRight (C : Context A B)
    {a₁ a₂ : A} {y : B}
    (p : Path a₁ a₂) (h : Path (C.fill a₂) y) :
    Path (C.fill a₁) y :=
  Path.trans (map C p) h

end Context

/-- A binary context encapsulating Definition 3.5's `sub L` and `sub R`. -/
structure BiContext (A : Type u) (B : Type v) (C : Type w) where
  fill : A → B → C

namespace BiContext

variable {A : Type u} {B : Type v} {C : Type w}

/-- Substitute along the left hole of a binary context (paper's `sub L`). -/
@[simp] noncomputable def mapLeft (K : BiContext A B C)
    {a₁ a₂ : A} (p : Path a₁ a₂) (b : B) :
    Path (K.fill a₁ b) (K.fill a₂ b) :=
  Path.mapLeft (f := K.fill) p b

/-- Substitute along the right hole of a binary context (paper's `sub R`). -/
@[simp] noncomputable def mapRight (K : BiContext A B C)
    (a : A) {b₁ b₂ : B} (p : Path b₁ b₂) :
    Path (K.fill a b₁) (K.fill a b₂) :=
  Path.mapRight (f := K.fill) a p

@[simp] theorem mapLeft_refl (K : BiContext A B C) (a : A) (b : B) :
    mapLeft K (Path.refl a) b = Path.refl (K.fill a b) := by
  simp [mapLeft]

@[simp] theorem mapLeft_symm (K : BiContext A B C)
    {a₁ a₂ : A} (p : Path a₁ a₂) (b : B) :
    mapLeft K (Path.symm p) b =
      Path.symm (mapLeft K p b) := by
  simp [mapLeft]

@[simp] theorem mapLeft_trans (K : BiContext A B C)
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) (b : B) :
    mapLeft K (Path.trans p q) b =
      Path.trans (mapLeft K p b) (mapLeft K q b) := by
  simp [mapLeft]

/-- Freeze the right hole of a binary context to obtain a unary context. -/
@[simp] noncomputable def fixRight (K : BiContext A B C) (b : B) : Context A C :=
  ⟨fun a => K.fill a b⟩

/-- Freeze the left hole of a binary context to obtain a unary context. -/
@[simp] noncomputable def fixLeft (K : BiContext A B C) (a : A) : Context B C :=
  ⟨fun b => K.fill a b⟩

@[simp] theorem map_fixRight (K : BiContext A B C) (b : B)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    Context.map (fixRight (A := A) (B := B) (C := C) K b) p =
      mapLeft K p b := rfl

@[simp] theorem map_fixLeft (K : BiContext A B C) (a : A)
    {b₁ b₂ : B} (p : Path b₁ b₂) :
    Context.map (fixLeft (A := A) (B := B) (C := C) K a) p =
      mapRight K a p := rfl

@[simp] theorem mapRight_refl (K : BiContext A B C) (a : A) (b : B) :
    mapRight K a (Path.refl b) = Path.refl (K.fill a b) := by
  simp [mapRight]

@[simp] theorem mapRight_symm (K : BiContext A B C)
    (a : A) {b₁ b₂ : B} (p : Path b₁ b₂) :
    mapRight K a (Path.symm p) =
      Path.symm (mapRight K a p) := by
  simp [mapRight]

@[simp] theorem mapRight_trans (K : BiContext A B C)
    (a : A) {b₁ b₂ b₃ : B} (p : Path b₁ b₂) (q : Path b₂ b₃) :
    mapRight K a (Path.trans p q) =
      Path.trans (mapRight K a p) (mapRight K a q) := by
  simp [mapRight]

/-- Substitute through both holes of a binary context simultaneously. -/
@[simp] noncomputable def map2 (K : BiContext A B C)
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    Path (K.fill a₁ b₁) (K.fill a₂ b₂) :=
  Path.map2 (f := K.fill) p q

@[simp] theorem map2_refl (K : BiContext A B C) (a : A) (b : B) :
    map2 K (Path.refl a) (Path.refl b) =
      Path.refl (K.fill a b) := by
  simp [map2]

@[simp] theorem map2_symm (K : BiContext A B C)
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    Path.symm (map2 K p q) =
      Path.trans
        (mapRight K a₂ (Path.symm q))
        (mapLeft K (Path.symm p) b₁) := by
  change
    Path.symm (Path.map2 (f := K.fill) p q) =
      Path.trans
        (Path.mapRight (f := K.fill) a₂ (Path.symm q))
        (Path.mapLeft (f := K.fill) (Path.symm p) b₁)
  exact Path.map2_symm (f := K.fill) (p := p) (q := q)

@[simp] theorem map2_trans (K : BiContext A B C)
    {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
    (p₁ : Path a₁ a₂) (p₂ : Path a₂ a₃)
    (q₁ : Path b₁ b₂) (q₂ : Path b₂ b₃) :
    map2 K (Path.trans p₁ p₂) (Path.trans q₁ q₂) =
      Path.trans
        (mapLeft K p₁ b₁)
        (Path.trans
          (mapLeft K p₂ b₁)
          (Path.trans
            (mapRight K a₃ q₁)
            (mapRight K a₃ q₂))) := by
  change
    Path.map2 (f := K.fill) (Path.trans p₁ p₂) (Path.trans q₁ q₂) =
      Path.trans
        (Path.mapLeft (f := K.fill) p₁ b₁)
        (Path.trans
          (Path.mapLeft (f := K.fill) p₂ b₁)
          (Path.trans
            (Path.mapRight (f := K.fill) a₃ q₁)
            (Path.mapRight (f := K.fill) a₃ q₂)))
  exact
    Path.map2_trans (f := K.fill)
      (p1 := p₁) (p2 := p₂) (q1 := q₁) (q2 := q₂)

end BiContext

/-- A unary context whose result type depends on the element inserted in the hole. -/
structure DepContext (A : Type u) (B : A → Type v) where
  fill : (a : A) → B a

namespace DepContext

variable {A : Type u} {B : A → Type v}

/-- View transport along a base path as a unary context between fibres. -/
@[simp] noncomputable def transportContext {a₁ a₂ : A} (p : Path a₁ a₂) :
    Context (B a₁) (B a₂) :=
  ⟨fun y =>
    Path.transport (A := A) (D := fun a => B a) p y⟩

/-- Map a base path through a dependent context, transporting the source witness. -/
@[simp] noncomputable def map (C : DepContext A B)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    Path (A := B a₂)
      (Path.transport (A := A) (D := fun a => B a) p (C.fill a₁))
      (C.fill a₂) :=
  Path.apd (A := A) (B := fun a => B a) (f := C.fill) p

@[simp] theorem map_refl (C : DepContext A B) (a : A) :
    map C (Path.refl a) = Path.refl (C.fill a) :=
  Path.apd_refl (f := C.fill) a

/-- Dependent substitution on the left: transport the proof across the base path
before reapplying the context. -/
@[simp] noncomputable def substLeft (C : DepContext A B)
    {a₁ a₂ : A} {x : B a₁}
    (r : Path (A := B a₁) x (C.fill a₁))
    (p : Path a₁ a₂) :
    Path (A := B a₂)
      (Path.transport (A := A) (D := fun a => B a) p x)
      (C.fill a₂) :=
  Path.trans
    (Context.map (A := B a₁) (B := B a₂)
      (transportContext (A := A) (B := B) p) r)
    (map (A := A) (B := B) C p)

/-- Dependent substitution on the right: apply the context and continue with a
path in the target fibre. -/
@[simp] noncomputable def substRight (C : DepContext A B)
    {a₁ a₂ : A} {y : B a₂}
    (p : Path a₁ a₂) (t : Path (A := B a₂) (C.fill a₂) y) :
    Path (A := B a₂)
      (Path.transport (A := A) (D := fun a => B a) p (C.fill a₁))
      y :=
  Path.trans (map (A := A) (B := B) C p) t

/-- Symmetry through a dependent context: applying `symm` to the mapped path
is equivalent to mapping the symmetric witness and transporting the result. -/
@[simp] noncomputable def symmMap (C : DepContext A B)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    Path (A := B a₂)
      (C.fill a₂)
      (Path.transport (A := A) (D := fun a => B a) p (C.fill a₁)) :=
  Path.trans
    (Path.symm
      (Path.stepChain
        (A := B a₂)
        (a :=
          Path.transport (A := A) (D := fun a => B a) p
            (Path.transport (A := A) (D := fun a => B a)
              (Path.symm p) (C.fill a₂)))
        (b := C.fill a₂)
        (Path.transport_symm_right (A := A) (D := fun a => B a)
          (p := p) (y := C.fill a₂))))
    (Context.map
      (transportContext (A := A) (B := B) p)
      (DepContext.map (A := A) (B := B) C (Path.symm p)))

end DepContext

/-- Dependent congruence for binary functions: left hole. -/
@[simp] noncomputable def mapLeftDep
    {A : Type u} {B : Type v} {C : A → B → Type w}
    (f : (a : A) → (b : B) → C a b)
    {a₁ a₂ : A} (p : Path a₁ a₂) (b : B) :
    Path (A := C a₂ b)
      (Path.transport (A := A) (D := fun a => C a b) p (f a₁ b))
      (f a₂ b) :=
  Path.apd (A := A) (B := fun a => C a b) (f := fun a => f a b) p

@[simp] theorem mapLeftDep_refl
    {A : Type u} {B : Type v} {C : A → B → Type w}
    (f : (a : A) → (b : B) → C a b) (a : A) (b : B) :
    mapLeftDep f (Path.refl a) b = Path.refl (f a b) := by
  simp [mapLeftDep]

/-- Dependent congruence for binary functions: right hole. -/
@[simp] noncomputable def mapRightDep
    {A : Type u} {B : Type v} {C : A → B → Type w}
    (f : (a : A) → (b : B) → C a b)
    (a : A) {b₁ b₂ : B} (q : Path b₁ b₂) :
    Path (A := C a b₂)
      (Path.transport (A := B) (D := fun b => C a b) q (f a b₁))
      (f a b₂) :=
  Path.apd (A := B) (B := fun b => C a b) (f := fun b => f a b) q

@[simp] theorem mapRightDep_refl
    {A : Type u} {B : Type v} {C : A → B → Type w}
    (f : (a : A) → (b : B) → C a b) (a : A) (b : B) :
    mapRightDep f a (Path.refl b) = Path.refl (f a b) := by
  simp [mapRightDep]

/-- Dependent congruence for binary functions on both holes. -/
@[simp] noncomputable def map2Dep
    {A : Type u} {B : Type v} {C : A → B → Type w}
    (f : (a : A) → (b : B) → C a b)
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    Path (A := C a₂ b₂)
      (Path.transport (A := B) (D := fun b => C a₂ b) q
        (Path.transport (A := A) (D := fun a => C a b₁) p (f a₁ b₁)))
      (f a₂ b₂) :=
  Path.trans
    (Context.map
      ⟨fun z => Path.transport (A := B) (D := fun b => C a₂ b) q z⟩
      (mapLeftDep f p b₁))
    (mapRightDep f a₂ q)

@[simp] theorem map2Dep_refl
    {A : Type u} {B : Type v} {C : A → B → Type w}
    (f : (a : A) → (b : B) → C a b) (a : A) (b : B) :
    map2Dep f (Path.refl a) (Path.refl b) = Path.refl (f a b) := by
  simp [map2Dep]

/-- A binary context whose codomain may depend on the left hole. -/
structure DepBiContext (A : Type u) (B : Type v)
    (C : A → B → Type w) where
  fill : (a : A) → (b : B) → C a b

namespace DepBiContext

variable {A : Type u} {B : Type v} {C : A → B → Type w}

/-- Freeze the right hole to obtain a dependent unary context. -/
@[simp] noncomputable def fixRight (K : DepBiContext A B C) (b : B) :
    DepContext A (fun a => C a b) :=
  ⟨fun a => K.fill a b⟩

/-- Freeze the left hole to obtain a dependent unary context on `B`. -/
@[simp] noncomputable def fixLeft (K : DepBiContext A B C) (a : A) :
    DepContext B (fun b => C a b) :=
  ⟨fun b => K.fill a b⟩

/-- Map a path through the left hole of a dependent binary context. -/
@[simp] noncomputable def mapLeft (K : DepBiContext A B C)
    {a₁ a₂ : A} (p : Path a₁ a₂) (b : B) :
    Path (A := C a₂ b)
      (Path.transport (A := A) (D := fun a => C a b) p (K.fill a₁ b))
      (K.fill a₂ b) :=
  mapLeftDep (f := K.fill) p b

/-- Map a path through the right hole of a dependent binary context. -/
@[simp] noncomputable def mapRight (K : DepBiContext A B C)
    (a : A) {b₁ b₂ : B} (q : Path b₁ b₂) :
    Path (A := C a b₂)
      (Path.transport (A := B) (D := fun b => C a b) q (K.fill a b₁))
      (K.fill a b₂) :=
  mapRightDep (f := K.fill) a q

/-- Simultaneously substitute through both holes of a dependent binary context. -/
@[simp] noncomputable def map2 (K : DepBiContext A B C)
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    Path (A := C a₂ b₂)
      (Path.transport (A := B) (D := fun b => C a₂ b) q
        (Path.transport (A := A) (D := fun a => C a b₁) p (K.fill a₁ b₁)))
      (K.fill a₂ b₂) :=
  map2Dep (f := K.fill) p q

end DepBiContext

end Path
end ComputationalPaths
