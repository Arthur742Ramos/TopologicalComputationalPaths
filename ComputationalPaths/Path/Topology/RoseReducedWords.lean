import ComputationalPaths.Path.Topology.BasedScopedTraceGroup
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Reduced words for a two-loop scoped presentation

Two actual based loops supply the primitive realizations. There are no named
rewrite rules. The structural scoped rules alone give the free group on the
two labels, and every trace has an explicitly reconstructed reduced-word
normal form. In particular, the words `ab` and `ba` remain different.

These are algebraic results about scoped rewriting, valid for any two based
loops. They do not assert that geometric homotopy distinguishes the generators,
or that scoped rewriting is complete for geometric homotopy. A genuine rose
space and its geometric completeness bridge are separate obligations.
-/

namespace ComputationalPaths.Path.GeometricTopology.RoseReducedWords

open scoped Topology
universe u

inductive Label
  | a | b
  deriving DecidableEq

instance : TopologicalSpace Label := ⊥
instance : DiscreteTopology Label := discreteTopology_bot Label

instance : Fintype Label where
  elems := {.a, .b}
  complete := by intro s; cases s <;> simp

variable {A : Type u} [TopologicalSpace A] {x : A}

noncomputable def system (α β : _root_.Path x x) :
    ContinuousGeometricStepSystem A Label where
  src := fun _ => x
  tgt := fun _ => x
  realize
    | .a => α
    | .b => β
  continuous_src := continuous_const
  continuous_tgt := continuous_const
  continuous_realize := continuous_of_discreteTopology

noncomputable def presentation (α β : _root_.Path x x) :
    ScopedGeometricRewritePresentation (system α β) where
  rule := fun {_ _} _ _ => False
  sound_rule := by intro _ _ _ _ h; exact False.elim h

abbrev Trace (α β : _root_.Path x x) :=
  GeometricTrace (system α β).toGeometricStepSystem x x

abbrev ScopedGroup (α β : _root_.Path x x) :=
  BasedScopedTraceGroup.Carrier (presentation α β) x

/-- Positive signs are encoded by `true`, as in Mathlib's free-group words. -/
def rawWord (α β : _root_.Path x x) : {a b : A} →
    GeometricTrace (system α β).toGeometricStepSystem a b → List (Label × Bool)
  | _, _, .refl _ => []
  | _, _, .single s => [(s, true)]
  | _, _, .trans p q => rawWord α β p ++ rawWord α β q
  | _, _, .symm p => FreeGroup.invRev (rawWord α β p)

def encode (α β : _root_.Path x x) : {a b : A} →
    GeometricTrace (system α β).toGeometricStepSystem a b → FreeGroup Label
  | _, _, .refl _ => 1
  | _, _, .single s => FreeGroup.of s
  | _, _, .trans p q => encode α β p * encode α β q
  | _, _, .symm p => (encode α β p)⁻¹

theorem encode_eq_mk_rawWord (α β : _root_.Path x x) {a b : A}
    (p : GeometricTrace (system α β).toGeometricStepSystem a b) :
    encode α β p = FreeGroup.mk (rawWord α β p) := by
  induction p with
  | refl a => rfl
  | single s => rfl
  | trans p q ihp ihq =>
      simp only [encode, rawWord, ihp, ihq, FreeGroup.mul_mk]
  | symm p ih => simp only [encode, rawWord, ih, FreeGroup.inv_mk]

theorem encode_invariant (α β : _root_.Path x x) {a b : A}
    {p q : GeometricTrace (system α β).toGeometricStepSystem a b}
    (h : ScopedRwEq (presentation α β) p q) : encode α β p = encode α β q := by
  induction h with
  | refl p => rfl
  | generator h => exact False.elim h
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | trans_congr h₁ h₂ ih₁ ih₂ => simp only [encode, ih₁, ih₂]
  | symm_congr h ih => simp only [encode, ih]
  | refl_trans p => simp [encode]
  | trans_refl p => simp [encode]
  | trans_assoc p q r => simp [encode, mul_assoc]
  | symm_trans p => simp [encode]
  | trans_symm p => simp [encode]
  | symm_symm p => simp [encode]
  | symm_refl a => simp [encode]
  | symm_comp p q => simp [encode]

def decodeLetter (α β : _root_.Path x x) (s : Label × Bool) : Trace α β :=
  if s.2 then .single s.1 else .symm (.single s.1)

def decode (α β : _root_.Path x x) : List (Label × Bool) → Trace α β
  | [] => .refl x
  | s :: l => .trans (decodeLetter α β s) (decode α β l)

/-- The actual reconstructed trace realizes its freely evaluated word. -/
theorem encode_decode (α β : _root_.Path x x) (l : List (Label × Bool)) :
    encode α β (decode α β l) = FreeGroup.mk l := by
  induction l with
  | nil => rfl
  | cons s l ih =>
      rcases s with ⟨s, b⟩
      cases b <;> simp only [decode, decodeLetter, Bool.false_eq_true,
        if_false, if_true, encode, ih] <;> rfl

theorem endpoints_eq (α β : _root_.Path x x) {a b : A}
    (p : GeometricTrace (system α β).toGeometricStepSystem a b) : a = b := by
  induction p with
  | refl a => rfl
  | single s => rfl
  | trans p q ihp ihq => exact ihp.trans ihq
  | symm p ih => exact ih.symm

def castTrace (α β : _root_.Path x x) {a b : A}
    (ha : a = x) (hb : b = x)
    (p : GeometricTrace (system α β).toGeometricStepSystem a b) : Trace α β := by
  cases ha
  cases hb
  exact p

noncomputable def generatorClass (α β : _root_.Path x x) (s : Label) : ScopedGroup α β :=
  BasedScopedTraceGroup.mk (presentation α β) x (.single s)

/-- The free-group interpretation is built from actual primitive scoped
classes; no quotient inverse or completeness statement is assumed. -/
noncomputable def interpret (α β : _root_.Path x x) : FreeGroup Label →* ScopedGroup α β :=
  FreeGroup.lift (generatorClass α β)

theorem class_eq_interpret_encode_aux (α β : _root_.Path x x) {a b : A}
    (p : GeometricTrace (system α β).toGeometricStepSystem a b)
    (ha : a = x) (hb : b = x) :
    BasedScopedTraceGroup.mk (presentation α β) x (castTrace α β ha hb p) =
      interpret α β (encode α β p) := by
  induction p with
  | refl a =>
      cases ha
      cases hb
      simp [castTrace, encode]
  | single s =>
      cases ha
      cases hb
      simp [castTrace, encode, interpret, generatorClass]
  | trans p q ihp ihq =>
      have hmid : _ = x := (endpoints_eq α β p).symm.trans ha
      cases ha
      cases hmid
      cases hb
      simp only [castTrace, encode, BasedScopedTraceGroup.mk_trans, map_mul]
      have hp : BasedScopedTraceGroup.mk (presentation α β) x p =
          interpret α β (encode α β p) := by simpa [castTrace] using ihp rfl rfl
      have hq : BasedScopedTraceGroup.mk (presentation α β) x q =
          interpret α β (encode α β q) := by simpa [castTrace] using ihq rfl rfl
      rw [hp, hq]
  | symm p ih =>
      cases ha
      cases hb
      simp only [castTrace, encode, BasedScopedTraceGroup.mk_symm, map_inv]
      have hp : BasedScopedTraceGroup.mk (presentation α β) x p =
          interpret α β (encode α β p) := by simpa [castTrace] using ih rfl rfl
      rw [hp]

theorem class_eq_interpret_encode (α β : _root_.Path x x) (p : Trace α β) :
    BasedScopedTraceGroup.mk (presentation α β) x p = interpret α β (encode α β p) :=
  class_eq_interpret_encode_aux α β p rfl rfl

def reducedWord (α β : _root_.Path x x) (p : Trace α β) : List (Label × Bool) :=
  FreeGroup.reduce (rawWord α β p)

theorem reducedWord_eq_toWord (α β : _root_.Path x x) (p : Trace α β) :
    reducedWord α β p = (encode α β p).toWord := by
  rw [encode_eq_mk_rawWord]
  rfl

theorem isReduced_reducedWord (α β : _root_.Path x x) (p : Trace α β) :
    FreeGroup.IsReduced (reducedWord α β p) :=
  FreeGroup.IsReduced.of_reduce_eq FreeGroup.reduce.idem

theorem reducedWord_decode_of_isReduced (α β : _root_.Path x x)
    (l : List (Label × Bool)) (hl : FreeGroup.IsReduced l) :
    reducedWord α β (decode α β l) = l := by
  rw [reducedWord_eq_toWord, encode_decode, FreeGroup.toWord_mk]
  exact hl.reduce_eq

/-- An actual scoped derivation to the reconstructed maximal reduction. -/
theorem normalization (α β : _root_.Path x x) (p : Trace α β) :
    ScopedRwEq (presentation α β) p (decode α β (reducedWord α β p)) := by
  apply (BasedScopedTraceGroup.eq_iff (presentation α β) x _ _).mp
  rw [class_eq_interpret_encode, class_eq_interpret_encode, encode_decode]
  unfold reducedWord
  rw [FreeGroup.reduce.self, ← encode_eq_mk_rawWord]

theorem scoped_iff_reducedWord_eq (α β : _root_.Path x x) (p q : Trace α β) :
    ScopedRwEq (presentation α β) p q ↔ reducedWord α β p = reducedWord α β q := by
  constructor
  · intro h
    rw [reducedWord_eq_toWord, reducedWord_eq_toWord, encode_invariant α β h]
  · intro h
    exact (normalization α β p).trans
      (by rw [h]; exact (normalization α β q).symm)

theorem scoped_iff_encode_eq (α β : _root_.Path x x) (p q : Trace α β) :
    ScopedRwEq (presentation α β) p q ↔ encode α β p = encode α β q := by
  rw [scoped_iff_reducedWord_eq, reducedWord_eq_toWord, reducedWord_eq_toWord,
    FreeGroup.toWord_inj]

set_option backward.isDefEq.respectTransparency false in
/-- Generator reconstruction is derived from the structural right unit. -/
theorem primitive_roundtrip (α β : _root_.Path x x) (s : Label) :
    ScopedRwEq (presentation α β) (.single s : Trace α β)
      (decode α β (FreeGroup.of s).toWord) := by
  have h : ScopedRwEq (presentation α β) (.single s : Trace α β)
      ((.single s : Trace α β).trans (.refl x)) :=
    (ScopedRwEq.trans_refl (P := presentation α β) (.single s : Trace α β)).symm
  change ScopedRwEq (presentation α β) (.single s : Trace α β)
    ((.single s : Trace α β).trans (.refl x))
  exact h

noncomputable def quotientEncode (α β : _root_.Path x x) : ScopedGroup α β → FreeGroup Label :=
  Quotient.lift (encode α β) (fun _ _ h => encode_invariant α β h)

noncomputable def quotientDecode (α β : _root_.Path x x) (z : FreeGroup Label) : ScopedGroup α β :=
  BasedScopedTraceGroup.mk (presentation α β) x (decode α β z.toWord)

noncomputable def quotientEquiv (α β : _root_.Path x x) : ScopedGroup α β ≃ FreeGroup Label where
  toFun := quotientEncode α β
  invFun := quotientDecode α β
  left_inv := by
    intro z
    refine Quotient.inductionOn z ?_
    intro p
    apply Quotient.sound
    change ScopedRwEq (presentation α β) (decode α β (encode α β p).toWord) p
    rw [← reducedWord_eq_toWord]
    exact (normalization α β p).symm
  right_inv := by
    intro z
    change encode α β (decode α β z.toWord) = z
    rw [encode_decode, FreeGroup.mk_toWord]

noncomputable def quotientMulEquiv (α β : _root_.Path x x) : ScopedGroup α β ≃* FreeGroup Label where
  toEquiv := quotientEquiv α β
  map_mul' := by
    intro p q
    refine Quotient.inductionOn₂ p q ?_
    intro p q
    change encode α β (p.trans q) = encode α β p * encode α β q
    rfl

noncomputable def abTrace (α β : _root_.Path x x) : Trace α β := .trans (.single .a) (.single .b)
noncomputable def baTrace (α β : _root_.Path x x) : Trace α β := .trans (.single .b) (.single .a)

/-- Word order survives scoped rewriting, even if the actual geometric loops
happen to be homotopic. No geometric noncommutativity is asserted here. -/
theorem ab_not_scoped_ba (α β : _root_.Path x x) :
    ¬ ScopedRwEq (presentation α β) (abTrace α β) (baTrace α β) := by
  intro h
  have hw := (scoped_iff_reducedWord_eq α β _ _).mp h
  change [(Label.a, true), (Label.b, true)] = [(Label.b, true), (Label.a, true)] at hw
  cases hw

theorem ab_classes_ne_ba (α β : _root_.Path x x) :
    BasedScopedTraceGroup.mk (presentation α β) x (abTrace α β) ≠
      BasedScopedTraceGroup.mk (presentation α β) x (baTrace α β) := by
  intro h
  exact ab_not_scoped_ba α β ((BasedScopedTraceGroup.eq_iff (presentation α β) x _ _).mp h)

end ComputationalPaths.Path.GeometricTopology.RoseReducedWords
