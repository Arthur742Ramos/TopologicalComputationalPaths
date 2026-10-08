import ComputationalPaths.Path.Topology.LiteralWord
import ComputationalPaths.Path.Topology.CoherentRepresentativeElimination

/-!
# Rewriting on literal composable words

This relation is generated on words themselves. Its cancellation generators
remove an adjacent signed letter and its inverse; its other generators are
the flattened named presentation rules. It is not defined by pulling back
the existing tree relation.
-/

namespace ComputationalPaths.Path.GeometricTopology.LiteralWord

universe u v

variable {A : Type u} [TopologicalSpace A] {Step : Type v} [TopologicalSpace Step]
  {S : ContinuousGeometricStepSystem A Step}

/-- Equivalence and contextual closure of named rules and letter cancellation. -/
inductive WordRwEq (P : ScopedGeometricRewritePresentation S) :
    {a b : A} → Word S.toGeometricStepSystem a b →
      Word S.toGeometricStepSystem a b → Prop
  | refl {a b} (w : Word S.toGeometricStepSystem a b) : WordRwEq P w w
  | symm {a b} {w z : Word S.toGeometricStepSystem a b} :
      WordRwEq P w z → WordRwEq P z w
  | trans {a b} {w z t : Word S.toGeometricStepSystem a b} :
      WordRwEq P w z → WordRwEq P z t → WordRwEq P w t
  | append_congr {a b c} {w w' : Word S.toGeometricStepSystem a b}
      {z z' : Word S.toGeometricStepSystem b c} :
      WordRwEq P w w' → WordRwEq P z z' →
        WordRwEq P (w.append z) (w'.append z')
  | reverse_congr {a b} {w z : Word S.toGeometricStepSystem a b} :
      WordRwEq P w z → WordRwEq P w.reverse z.reverse
  | generator {a b} {p q : GeometricTrace S.toGeometricStepSystem a b} :
      P.rule p q → WordRwEq P (Word.ofTrace p) (Word.ofTrace q)
  | cancel (s : SignedStep Step) :
      WordRwEq P
        ((Word.atom (S := S.toGeometricStepSystem) s).append
          (Word.atom (S := S.toGeometricStepSystem) s).reverse)
        (Word.nil (signedSrc S.toGeometricStepSystem s))

end ComputationalPaths.Path.GeometricTopology.LiteralWord

namespace ComputationalPaths.Path.GeometricTopology.LiteralWord

universe u v
variable {A : Type u} [TopologicalSpace A] {Step : Type v} [TopologicalSpace Step]
  {S : ContinuousGeometricStepSystem A Step}

namespace WordRwEq

variable (P : ScopedGeometricRewritePresentation S)

/-- Cancellation of a whole word is derived from adjacent-letter cancellation. -/
theorem cancel_word {a b : A} (w : Word S.toGeometricStepSystem a b) :
    WordRwEq P (w.append w.reverse) (Word.nil a) := by
  induction w with
  | nil a => exact .refl _
  | cons s w ih =>
      have h := append_congr (refl (Word.atom (S := S.toGeometricStepSystem) s))
        (append_congr ih (refl (Word.reverseAtom (S := S.toGeometricStepSystem) s)))
      have h' : WordRwEq P
          ((Word.cons s w).append (Word.cons s w).reverse)
          ((Word.atom (S := S.toGeometricStepSystem) s).append (Word.reverseAtom s)) := by
        simpa only [Word.append, Word.reverse, Word.atom, Word.append_assoc,
          Word.nil_append] using h
      exact h'.trans (by simpa only [Word.reverse_atom] using WordRwEq.cancel (P := P) s)

/-- The opposite cancellation follows by reversing the derived cancellation. -/
theorem reverse_cancel_word {a b : A} (w : Word S.toGeometricStepSystem a b) :
    WordRwEq P (w.reverse.append w) (Word.nil b) :=
  by simpa only [Word.reverse_reverse] using cancel_word P w.reverse

/-- The independently generated word relation reconstructs to scoped rewriting. -/
theorem toTrace {a b : A} {w z : Word S.toGeometricStepSystem a b}
    (h : WordRwEq P w z) : ScopedRwEq P w.toTrace z.toTrace := by
  induction h with
  | refl w => exact .refl _
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | append_congr h₁ h₂ ih₁ ih₂ =>
      exact (Word.toTrace_append P _ _).trans
        ((ScopedRwEq.trans_congr ih₁ ih₂).trans (Word.toTrace_append P _ _).symm)
  | reverse_congr h ih =>
      exact (Word.toTrace_reverse P _).trans
        ((ScopedRwEq.symm_congr ih).trans (Word.toTrace_reverse P _).symm)
  | generator h =>
      exact (Word.normalization P _).symm.trans
        ((ScopedRwEq.generator h).trans (Word.normalization P _))
  | cancel s =>
      exact (Word.toTrace_append P _ _).trans
        ((ScopedRwEq.trans_congr (.refl _) (Word.toTrace_reverse P _)).trans
          (ScopedRwEq.trans_symm _))

/-- Every scoped tree derivation has a derivation in the literal word relation. -/
theorem ofTrace {a b : A} {p q : GeometricTrace S.toGeometricStepSystem a b}
    (h : ScopedRwEq P p q) : WordRwEq P (Word.ofTrace p) (Word.ofTrace q) := by
  induction h with
  | refl p => exact .refl _
  | generator h => exact .generator h
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | trans_congr h₁ h₂ ih₁ ih₂ => exact .append_congr ih₁ ih₂
  | symm_congr h ih => exact .reverse_congr ih
  | refl_trans p => exact .refl _
  | trans_refl p => simpa only [Word.ofTrace, Word.append_nil] using (refl (P := P) (Word.ofTrace p))
  | trans_assoc p q r =>
      simpa only [Word.ofTrace, Word.append_assoc] using
        (refl (P := P) ((Word.ofTrace p).append ((Word.ofTrace q).append (Word.ofTrace r))))
  | symm_trans p => exact reverse_cancel_word P (Word.ofTrace p)
  | trans_symm p => exact cancel_word P (Word.ofTrace p)
  | symm_symm p =>
      simpa only [Word.ofTrace, Word.reverse_reverse] using (refl (P := P) (Word.ofTrace p))
  | symm_refl a => exact .refl _
  | symm_comp p q =>
      simpa only [Word.ofTrace, Word.reverse_append] using
        (refl (P := P) ((Word.ofTrace q).reverse.append (Word.ofTrace p).reverse))

/-- The word/tree equivalence is proved in both directions, rather than defined. -/
theorem ofTrace_iff {a b : A} (p q : GeometricTrace S.toGeometricStepSystem a b) :
    WordRwEq P (Word.ofTrace p) (Word.ofTrace q) ↔ ScopedRwEq P p q := by
  constructor
  · intro h
    exact (Word.normalization P p).trans ((toTrace P h).trans (Word.normalization P q).symm)
  · exact ofTrace P

def setoid (a b : A) : Setoid (Word S.toGeometricStepSystem a b) where
  r := WordRwEq P
  iseqv := ⟨refl, symm, trans⟩

/-- Canonical reconstruction induces inverse bijections on the presented quotients. -/
def quotientEquiv (a b : A) :
    Quotient (CoherentRepresentativeElimination.traceSetoid P a b) ≃
      Quotient (setoid P a b) where
  toFun := Quotient.map Word.ofTrace (fun _ _ h => ofTrace P h)
  invFun := Quotient.map Word.toTrace (fun _ _ h => toTrace P h)
  left_inv x := by
    refine Quotient.inductionOn x ?_
    intro p
    exact Quotient.sound (Word.normalization P p).symm
  right_inv x := by
    refine Quotient.inductionOn x ?_
    intro w
    simp only [Quotient.map_mk, Word.ofTrace_toTrace]

end WordRwEq
end ComputationalPaths.Path.GeometricTopology.LiteralWord
