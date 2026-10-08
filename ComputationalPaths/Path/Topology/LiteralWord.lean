import ComputationalPaths.Path.Topology.ScopedGeometricRewrite
import ComputationalPaths.Path.Topology.TraceSensitiveTopologicalCompPath
import Mathlib.Data.List.OfFn

/-!
# Endpoint-indexed literal signed words

Words contain composable signed primitive letters rather than trace trees.
The empty word is indexed by its basepoint. Thus passing to a total carrier
does not identify empty words at different points. Reconstruction is canonical
right-associated composition with a final identity trace.

Every trace is scoped equivalent to its reconstructed word, using only the
structural groupoid constructors. No named rule or realization assumption is
used for this normalization. This file supplies algebraic word operations and
the exact finite-letter bridge; it does not choose a word topology or relation.
-/

namespace ComputationalPaths.Path.GeometricTopology.LiteralWord

universe u v

variable {A : Type u} [TopologicalSpace A] {Step : Type v}

def signedSrc (S : GeometricStepSystem A Step) : SignedStep Step → A
  | .inl s => S.src s
  | .inr s => S.tgt s

def signedTgt (S : GeometricStepSystem A Step) : SignedStep Step → A
  | .inl s => S.tgt s
  | .inr s => S.src s

@[simp] theorem signedSrc_symm (S : GeometricStepSystem A Step) (s : SignedStep Step) :
    signedSrc S (signedStepSymm s) = signedTgt S s := by cases s <;> rfl

@[simp] theorem signedTgt_symm (S : GeometricStepSystem A Step) (s : SignedStep Step) :
    signedTgt S (signedStepSymm s) = signedSrc S s := by cases s <;> rfl

def atomTrace (S : GeometricStepSystem A Step) (s : SignedStep Step) :
    GeometricTrace S (signedSrc S s) (signedTgt S s) :=
  match s with
  | .inl s => .single s
  | .inr s => .symm (.single s)

inductive Word (S : GeometricStepSystem A Step) : A → A → Type (max u v)
  | nil (a : A) : Word S a a
  | cons (s : SignedStep Step) {b : A} (tail : Word S (signedTgt S s) b) :
      Word S (signedSrc S s) b

namespace Word

variable {S : GeometricStepSystem A Step}

def atom (s : SignedStep Step) : Word S (signedSrc S s) (signedTgt S s) :=
  .cons s (.nil _)

def toList {a b : A} : Word S a b → List (SignedStep Step)
  | .nil _ => []
  | .cons s tail => s :: tail.toList

@[reducible] def length {a b : A} (w : Word S a b) : Nat := w.toList.length

def letters {a b : A} (w : Word S a b) : Fin w.length → SignedStep Step := w.toList.get

def toFlatWord {a b : A} (w : Word S a b) : FlatWord Step := ⟨w.length, w.letters⟩

@[simp] theorem length_nil (a : A) : (Word.nil (S := S) a).length = 0 := rfl

@[simp] theorem length_cons (s : SignedStep Step) {b : A} (p : Word S (signedTgt S s) b) :
    (Word.cons s p).length = p.length + 1 := rfl

def append {a b c : A} : Word S a b → Word S b c → Word S a c
  | .nil _, q => q
  | .cons s tail, q => .cons s (tail.append q)

/-- The reversed singleton has the original target and source as endpoints. -/
def reverseAtom (s : SignedStep Step) : Word S (signedTgt S s) (signedSrc S s) :=
  match s with
  | .inl s => atom (.inr s)
  | .inr s => atom (.inl s)

def reverse {a b : A} : Word S a b → Word S b a
  | .nil a => .nil a
  | .cons s tail => tail.reverse.append (reverseAtom s)

def toTrace {a b : A} : Word S a b → GeometricTrace S a b
  | .nil a => .refl a
  | .cons s tail => .trans (atomTrace S s) tail.toTrace

def ofTrace {a b : A} : GeometricTrace S a b → Word S a b
  | .refl a => .nil a
  | .single s => atom (.inl s)
  | .trans p q => (ofTrace p).append (ofTrace q)
  | .symm p => (ofTrace p).reverse

/-- The letter list determines a typed word once both endpoints are fixed.
The endpoint assumptions retain the basepoint in the empty-list case. -/
theorem heq_of_toList_eq {a b c d : A} (p : Word S a b) (q : Word S c d)
    (ha : a = c) (hb : b = d) (h : p.toList = q.toList) : HEq p q := by
  induction p generalizing c d with
  | nil a =>
      cases q with
      | nil c => cases ha; rfl
      | cons s q => simp [toList] at h
  | cons s p ih =>
      cases q with
      | nil c => simp [toList] at h
      | cons t q =>
          have hs : s = t := (List.cons.inj h).1
          cases hs
          cases hb
          have hp : p = q := eq_of_heq (ih q rfl rfl (List.cons.inj h).2)
          cases hp
          rfl

theorem toList_injective (a b : A) : Function.Injective (toList : Word S a b → _) := by
  intro p q h
  exact eq_of_heq (heq_of_toList_eq p q rfl rfl h)

theorem toFlatWord_injective (a b : A) : Function.Injective (toFlatWord : Word S a b → _) := by
  intro p q h
  apply toList_injective a b
  have h' := _root_.congrArg (fun w : FlatWord Step => List.ofFn w.2) h
  simpa [toFlatWord, letters] using h'

@[simp] theorem nil_append {a b : A} (q : Word S a b) : (Word.nil a).append q = q := rfl

@[simp] theorem append_nil {a b : A} (p : Word S a b) : p.append (.nil b) = p := by
  induction p with
  | nil a => rfl
  | cons s p ih => simp only [append, ih]

theorem append_assoc {a b c d : A} (p : Word S a b) (q : Word S b c) (r : Word S c d) :
    (p.append q).append r = p.append (q.append r) := by
  induction p with
  | nil a => rfl
  | cons s p ih => simp only [append, ih]

@[simp] theorem reverse_nil (a : A) : (Word.nil (S := S) a).reverse = .nil a := rfl

@[simp] theorem reverse_atom (s : SignedStep Step) : (atom (S := S) s).reverse = reverseAtom s :=
  by cases s <;> rfl

@[simp] theorem reverse_reverseAtom (s : SignedStep Step) :
    (reverseAtom (S := S) s).reverse = atom s := by cases s <;> rfl

theorem reverse_append {a b c : A} (p : Word S a b) (q : Word S b c) :
    (p.append q).reverse = q.reverse.append p.reverse := by
  induction p with
  | nil a => simp only [append, reverse, append_nil]
  | cons s p ih => simp only [append, reverse, ih, append_assoc]

@[simp] theorem reverse_reverse {a b : A} (p : Word S a b) : p.reverse.reverse = p := by
  induction p with
  | nil a => rfl
  | cons s p ih =>
      rw [reverse, reverse_append, reverse_reverseAtom, ih]
      rfl

@[simp] theorem toList_append {a b c : A} (p : Word S a b) (q : Word S b c) :
    (p.append q).toList = p.toList ++ q.toList := by
  induction p with
  | nil a => rfl
  | cons s p ih => simp only [append, toList, ih, List.cons_append]

@[simp] theorem toList_reverseAtom (s : SignedStep Step) :
    (reverseAtom (S := S) s).toList = [signedStepSymm s] := by cases s <;> rfl

@[simp] theorem toList_reverse {a b : A} (p : Word S a b) :
    p.reverse.toList = p.toList.reverse.map signedStepSymm := by
  induction p with
  | nil a => rfl
  | cons s p ih =>
      simp only [reverse, toList_append, ih, toList_reverseAtom, toList,
        List.reverse_cons, List.map_append, List.map_cons, List.map_nil]

@[simp] theorem length_append {a b c : A} (p : Word S a b) (q : Word S b c) :
    (p.append q).length = p.length + q.length := by simp [length]

@[simp] theorem length_reverse {a b : A} (p : Word S a b) : p.reverse.length = p.length := by
  simp [length]

@[simp] theorem ofTrace_trans {a b c : A} (p : GeometricTrace S a b) (q : GeometricTrace S b c) :
    ofTrace (p.trans q) = (ofTrace p).append (ofTrace q) := rfl

@[simp] theorem ofTrace_symm {a b : A} (p : GeometricTrace S a b) :
    ofTrace p.symm = (ofTrace p).reverse := rfl

@[simp] theorem ofTrace_atomTrace (s : SignedStep Step) : ofTrace (atomTrace S s) = atom s :=
  by cases s <;> rfl

@[simp] theorem ofTrace_toTrace {a b : A} (p : Word S a b) : ofTrace p.toTrace = p := by
  induction p with
  | nil a => rfl
  | cons s p ih =>
      simp only [toTrace, ofTrace_trans, ofTrace_atomTrace, ih]
      rfl

/-- Reverse the finite index exactly when reversing the corresponding list. -/
theorem ofFn_rev {α : Type*} {n : Nat} (f : Fin n → α) :
    List.ofFn (fun i => f i.rev) = (List.ofFn f).reverse := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_ofFn, List.getElem_reverse, List.length_ofFn]
  congr 1
  apply Fin.ext
  simp only [Fin.rev]
  omega

theorem ofFn_flatWordSymm (w : FlatWord Step) :
    List.ofFn (flatWordSymm w).2 = (List.ofFn w.2).reverse.map signedStepSymm := by
  change List.ofFn (fun i => signedStepSymm (w.2 i.rev)) = _
  rw [List.ofFn_comp', ofFn_rev]

theorem toList_ofTrace {a b : A} (p : GeometricTrace S a b) :
    (ofTrace p).toList = List.ofFn (GeometricTrace.flatWord p).2 := by
  induction p with
  | refl a => simp [ofTrace, toList, GeometricTrace.flatWord]
  | single s => simp [ofTrace, atom, toList, GeometricTrace.flatWord]
  | trans p q ihp ihq =>
      simp only [ofTrace_trans, toList_append, ihp, ihq, GeometricTrace.flatWord_trans,
        flatWordTrans, List.ofFn_fin_append]
  | symm p ih =>
      rw [ofTrace_symm, toList_reverse, ih, GeometricTrace.flatWord_symm, ofFn_flatWordSymm]

/-- Flattening the typed word of a trace recovers its exact finite signed word. -/
theorem toFlatWord_ofTrace {a b : A} (p : GeometricTrace S a b) :
    (ofTrace p).toFlatWord = GeometricTrace.flatWord p := by
  apply List.equivSigmaTuple.symm.injective
  change List.ofFn (ofTrace p).letters = List.ofFn (GeometricTrace.flatWord p).2
  rw [letters, List.ofFn_get, toList_ofTrace]

@[simp] theorem flatWord_toTrace {a b : A} (p : Word S a b) :
    GeometricTrace.flatWord p.toTrace = p.toFlatWord := by
  simpa only [ofTrace_toTrace] using (toFlatWord_ofTrace p.toTrace).symm

@[simp] theorem toTrace_length {a b : A} (p : Word S a b) :
    GeometricTrace.traceLength p.toTrace = p.length := by
  have h := _root_.congrArg Sigma.fst (flatWord_toTrace p)
  simpa only [GeometricTrace.flatWord_length, toFlatWord] using h

@[simp] theorem ofTrace_length {a b : A} (p : GeometricTrace S a b) :
    (ofTrace p).length = GeometricTrace.traceLength p := by
  have h := _root_.congrArg Sigma.fst (toFlatWord_ofTrace p)
  simpa only [GeometricTrace.flatWord_length, toFlatWord] using h

theorem ofTrace_eq_of_flatWord {a b : A} {p q : GeometricTrace S a b}
    (h : GeometricTrace.flatWord p = GeometricTrace.flatWord q) : ofTrace p = ofTrace q := by
  apply toFlatWord_injective a b
  simpa only [toFlatWord_ofTrace] using h

variable [TopologicalSpace Step] {C : ContinuousGeometricStepSystem A Step}

/-- Reconstructing concatenation differs from trace composition only by
structural units and associativity. -/
theorem toTrace_append (P : ScopedGeometricRewritePresentation C) {a b c : A}
    (p : Word C.toGeometricStepSystem a b) (q : Word C.toGeometricStepSystem b c) :
    ScopedRwEq P (p.append q).toTrace (p.toTrace.trans q.toTrace) := by
  induction p with
  | nil a => exact (ScopedRwEq.refl_trans q.toTrace).symm
  | cons s p ih =>
      exact (ScopedRwEq.trans_congr (ScopedRwEq.refl (atomTrace _ s)) (ih q)).trans
        (ScopedRwEq.trans_assoc _ _ _).symm

theorem toTrace_reverseAtom (P : ScopedGeometricRewritePresentation C) (s : SignedStep Step) :
    ScopedRwEq P (reverseAtom (S := C.toGeometricStepSystem) s).toTrace
      (atomTrace C.toGeometricStepSystem s).symm := by
  cases s with
  | inl s => exact ScopedRwEq.trans_refl _
  | inr s => exact (ScopedRwEq.trans_refl _).trans (ScopedRwEq.symm_symm _).symm

/-- Reconstructing reversal is structurally equivalent to reversing the
reconstructed trace. -/
theorem toTrace_reverse (P : ScopedGeometricRewritePresentation C) {a b : A}
    (p : Word C.toGeometricStepSystem a b) :
    ScopedRwEq P p.reverse.toTrace p.toTrace.symm := by
  induction p with
  | nil a => exact (ScopedRwEq.symm_refl a).symm
  | cons s p ih =>
      exact (toTrace_append P p.reverse (reverseAtom s)).trans
        ((ScopedRwEq.trans_congr ih (toTrace_reverseAtom P s)).trans
          (ScopedRwEq.symm_comp _ _).symm)

/-- Structural normalization, with no use of a named rewrite generator. -/
theorem normalization (P : ScopedGeometricRewritePresentation C) {a b : A}
    (p : GeometricTrace C.toGeometricStepSystem a b) :
    ScopedRwEq P p (ofTrace p).toTrace := by
  induction p with
  | refl a => exact ScopedRwEq.refl _
  | single s => exact (ScopedRwEq.trans_refl _).symm
  | trans p q ihp ihq =>
      exact (ScopedRwEq.trans_congr ihp ihq).trans (toTrace_append P _ _).symm
  | symm p ih => exact (ScopedRwEq.symm_congr ih).trans (toTrace_reverse P _).symm

/-- Equal signed words at fixed endpoints are already equivalent using only
structural rewrites, even when the presentation has no named rules. -/
theorem scopedEq_of_flatWord (P : ScopedGeometricRewritePresentation C) {a b : A}
    {p q : GeometricTrace C.toGeometricStepSystem a b}
    (h : GeometricTrace.flatWord p = GeometricTrace.flatWord q) : ScopedRwEq P p q := by
  have hw : ofTrace p = ofTrace q := ofTrace_eq_of_flatWord h
  have hq : ScopedRwEq P q (ofTrace p).toTrace := by
    simpa only [hw] using normalization P q
  exact (normalization P p).trans hq.symm

end Word

end ComputationalPaths.Path.GeometricTopology.LiteralWord
