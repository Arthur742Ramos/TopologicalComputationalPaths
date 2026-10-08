import ComputationalPaths.Path.Topology.ScopedWordInterpretation
import ComputationalPaths.Path.Topology.LiteralWord

/-!
# Continuous variable-length substitution on finite signed tuples

The domain and codomain are the genuine coproducts of finite products used by
`FlatWord`. A primitive image may have varying length; continuity into that
coproduct is the primitive hypothesis. A recursion over each input stratum
proves continuity of the actual concatenated substitution. Negative letters
reverse their primitive image and toggle all target signs.

The exact flattening law identifies this tuple substitution with the recursive
trace substitution. Lists are used only to prove the algebraic identities;
no discrete list topology or desired quotient continuity is assumed. This file
does not assert trace-realization continuity or presentation homeomorphisms.
-/

namespace ComputationalPaths.Path.GeometricTopology.FlatWordSubstitution

open scoped Topology

universe u v w

variable {Step : Type v} {Step' : Type w}

def emptyWord (Step : Type*) : FlatWord Step := ⟨0, Fin.elim0⟩

def wordList (w : FlatWord Step) : List (SignedStep Step) := List.ofFn w.2

theorem wordList_injective : Function.Injective (wordList : FlatWord Step → _) :=
  List.equivSigmaTuple.symm.injective

@[simp] theorem wordList_empty : wordList (emptyWord Step) = [] := rfl

@[simp] theorem wordList_trans (p q : FlatWord Step) :
    wordList (flatWordTrans p q) = wordList p ++ wordList q := by
  simp [wordList, flatWordTrans]

@[simp] theorem wordList_symm (p : FlatWord Step) :
    wordList (flatWordSymm p) = (wordList p).reverse.map signedStepSymm :=
  LiteralWord.Word.ofFn_flatWordSymm p

@[simp] theorem signedStepSymm_symm (s : SignedStep Step) :
    signedStepSymm (signedStepSymm s) = s := by cases s <;> rfl

@[simp] theorem flatWordTrans_empty (p : FlatWord Step) : flatWordTrans p (emptyWord Step) = p :=
  wordList_injective (by simp)

@[simp] theorem empty_flatWordTrans (p : FlatWord Step) : flatWordTrans (emptyWord Step) p = p :=
  wordList_injective (by simp)

@[simp] theorem flatWordSymm_symm (p : FlatWord Step) : flatWordSymm (flatWordSymm p) = p := by
  apply wordList_injective
  simp only [wordList_symm, List.map_reverse, List.reverse_reverse, List.map_map]
  simp [Function.comp_def]

/-- Concatenate the images of a finite indexed tuple, in its original order. -/
def bindTuple (f : SignedStep Step → FlatWord Step') :
    (n : Nat) → (Fin n → SignedStep Step) → FlatWord Step'
  | 0, _ => emptyWord Step'
  | n + 1, letters => flatWordTrans (f (letters 0))
      (bindTuple f n (fun i => letters i.succ))

def flatWordBind (f : SignedStep Step → FlatWord Step') (p : FlatWord Step) : FlatWord Step' :=
  bindTuple f p.1 p.2

theorem wordList_bindTuple (f : SignedStep Step → FlatWord Step') (n : Nat)
    (letters : Fin n → SignedStep Step) :
    wordList (bindTuple f n letters) =
      (List.ofFn letters).flatMap (fun s => wordList (f s)) := by
  induction n with
  | zero => simp [bindTuple, wordList, emptyWord]
  | succ n ih =>
      simp only [bindTuple, wordList_trans, List.ofFn_succ, List.flatMap_cons, ih]

@[simp] theorem wordList_flatWordBind (f : SignedStep Step → FlatWord Step') (p : FlatWord Step) :
    wordList (flatWordBind f p) = (wordList p).flatMap (fun s => wordList (f s)) :=
  wordList_bindTuple f p.1 p.2

theorem flatWordBind_trans (f : SignedStep Step → FlatWord Step') (p q : FlatWord Step) :
    flatWordBind f (flatWordTrans p q) = flatWordTrans (flatWordBind f p) (flatWordBind f q) :=
  wordList_injective (by simp)

theorem listFlatMap_reverse
    (g : SignedStep Step → List (SignedStep Step'))
    (h : ∀ s, g (signedStepSymm s) = (g s).reverse.map signedStepSymm)
    (l : List (SignedStep Step)) :
    (l.reverse.map signedStepSymm).flatMap g = (l.flatMap g).reverse.map signedStepSymm := by
  induction l with
  | nil => rfl
  | cons s l ih =>
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.reverse_append, ih, h s]

theorem flatWordBind_symm (f : SignedStep Step → FlatWord Step')
    (h : ∀ s, f (signedStepSymm s) = flatWordSymm (f s)) (p : FlatWord Step) :
    flatWordBind f (flatWordSymm p) = flatWordSymm (flatWordBind f p) := by
  apply wordList_injective
  simp only [wordList_flatWordBind, wordList_symm]
  apply listFlatMap_reverse
  intro s
  rw [h s, wordList_symm]

variable [TopologicalSpace Step] [TopologicalSpace Step']

/-- Continuity is proved on each genuine finite-product stratum. -/
theorem continuous_bindTuple (f : SignedStep Step → FlatWord Step') (hf : Continuous f)
    (n : Nat) : Continuous (bindTuple f n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
      have htail : Continuous (fun letters : Fin (n + 1) → SignedStep Step =>
          fun i : Fin n => letters i.succ) := by
        apply continuous_pi
        intro i
        exact continuous_apply i.succ
      exact continuous_flatWordTrans.comp
        ((hf.comp (continuous_apply 0)).prodMk (ih.comp htail))

/-- Primitive-image continuity implies continuity of the actual variable-length
tuple substitution over the entire coproduct. -/
theorem continuous_flatWordBind (f : SignedStep Step → FlatWord Step') (hf : Continuous f) :
    Continuous (flatWordBind f) := by
  apply continuous_sigma
  intro n
  exact continuous_bindTuple f hf n

variable {A : Type u} [TopologicalSpace A]
  {S : GeometricStepSystem A Step} {T : GeometricStepSystem A Step'}

def primitiveWord (M : WordSubstitution S T) (s : Step) : FlatWord Step' :=
  GeometricTrace.flatWord (M.step s)

def signedImage (M : WordSubstitution S T) : SignedStep Step → FlatWord Step'
  | .inl s => primitiveWord M s
  | .inr s => flatWordSymm (primitiveWord M s)

omit [TopologicalSpace Step] [TopologicalSpace Step'] in
@[simp] theorem signedImage_symm (M : WordSubstitution S T) (s : SignedStep Step) :
    signedImage M (signedStepSymm s) = flatWordSymm (signedImage M s) := by
  cases s with
  | inl s => rfl
  | inr s => exact (flatWordSymm_symm _).symm

theorem continuous_signedImage (M : WordSubstitution S T)
    (hprimitive : Continuous (primitiveWord M)) : Continuous (signedImage M) := by
  have hfun : signedImage M = Sum.elim (primitiveWord M)
      (fun s => flatWordSymm (primitiveWord M s)) := by
    funext s
    cases s <;> rfl
  rw [hfun]
  exact continuous_sumElim.2 ⟨hprimitive, continuous_flatWordSymm.comp hprimitive⟩

theorem continuous_substitution (M : WordSubstitution S T)
    (hprimitive : Continuous (primitiveWord M)) : Continuous (flatWordBind (signedImage M)) :=
  continuous_flatWordBind _ (continuous_signedImage M hprimitive)

omit [TopologicalSpace Step] [TopologicalSpace Step'] in
/-- Exact signed-word substitution for the actual recursive trace map. The
statement allows arbitrary primitive image lengths and internal parentheses. -/
theorem mapTrace_flatWord (M : WordSubstitution S T) {a b : A} (p : GeometricTrace S a b) :
    GeometricTrace.flatWord (M.mapTrace p) =
      flatWordBind (signedImage M) (GeometricTrace.flatWord p) := by
  induction p with
  | refl a => rfl
  | single s =>
      change primitiveWord M s = flatWordTrans (primitiveWord M s) (emptyWord Step')
      exact (flatWordTrans_empty _).symm
  | trans p q ihp ihq =>
      simp only [WordSubstitution.mapTrace, GeometricTrace.flatWord_trans, ihp, ihq,
        flatWordBind_trans]
  | symm p ih =>
      simp only [WordSubstitution.mapTrace, GeometricTrace.flatWord_symm, ih,
        flatWordBind_symm _ (signedImage_symm M)]

end ComputationalPaths.Path.GeometricTopology.FlatWordSubstitution
