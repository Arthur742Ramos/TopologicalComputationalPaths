import ComputationalPaths.Path.Topology.RoseLiftedWords
import ComputationalPaths.Path.Topology.CayleyReducedPrefix
import ComputationalPaths.Path.Topology.LiteralWord

/-!
# Equal-slot walks along actual Cayley edges

Finite signed words determine composable words of actual Cayley edges. Their
realization uses equal slots, including the actual vertex in the empty case.
Exact append, prefix, and final-slot laws provide finite-path infrastructure
for a subsequent contraction. No contraction or simple connectivity is assumed.
-/

namespace ComputationalPaths.Path.GeometricTopology.CayleyFlatWalk

open RoseReducedWords CayleyTreeGeometry
open RoseLiftedWords (letterValue)
open LiteralWord
open unitInterval
open scoped Topology

noncomputable section

abbrev Step := G × Label

def system : ContinuousGeometricStepSystem Tree Step where
  src s := .vertex s.1
  tgt s := .vertex (s.1 * FreeGroup.of s.2)
  realize s := edge s.1 s.2
  continuous_src := continuous_of_discreteTopology
  continuous_tgt := continuous_of_discreteTopology
  continuous_realize := continuous_of_discreteTopology

abbrev WalkWord := LiteralWord.Word system.toGeometricStepSystem
abbrev WalkTrace := GeometricTrace system.toGeometricStepSystem

/-- Endpoint transport changes no signed edge in a literal word. -/
def castWord {a b a' b' : Tree} (p : WalkWord a b)
    (ha : a' = a) (hb : b' = b) : WalkWord a' b' := by
  cases ha
  cases hb
  exact p

@[simp] theorem castWord_toList {a b a' b' : Tree} (p : WalkWord a b)
    (ha : a' = a) (hb : b' = b) : (castWord p ha hb).toList = p.toList := by
  cases ha
  cases hb
  rfl

theorem flatRealize_castWord {a b a' b' : Tree} (p : WalkWord a b)
    (ha : a' = a) (hb : b' = b) :
    GeometricTrace.flatRealize (castWord p ha hb).toTrace =
      (GeometricTrace.flatRealize p.toTrace).cast ha hb := by
  cases ha
  cases hb
  rfl

/-- The negative letter uses the edge immediately preceding the current vertex. -/
def signedEdge (g : G) : Label × Bool → SignedStep Step
  | (i, true) => .inl (g, i)
  | (i, false) => .inr (g * (FreeGroup.of i)⁻¹, i)

theorem signedEdge_src (g : G) (s : Label × Bool) :
    Tree.vertex g = LiteralWord.signedSrc system.toGeometricStepSystem (signedEdge g s) := by
  rcases s with ⟨i, b⟩
  cases b <;> simp [signedEdge, LiteralWord.signedSrc, system, mul_assoc]

theorem signedEdge_tgt (g : G) (s : Label × Bool) :
    Tree.vertex (g * letterValue s) =
      LiteralWord.signedTgt system.toGeometricStepSystem (signedEdge g s) := by
  rcases s with ⟨i, b⟩
  cases b <;> rfl

def atomWord (g : G) (s : Label × Bool) :
    WalkWord (.vertex g) (.vertex (g * letterValue s)) :=
  castWord (LiteralWord.Word.atom (signedEdge g s))
    (signedEdge_src g s) (signedEdge_tgt g s)

@[simp] theorem atomWord_toList (g : G) (s : Label × Bool) :
    (atomWord g s).toList = [signedEdge g s] := by
  simp [atomWord, LiteralWord.Word.atom, LiteralWord.Word.toList]

/-- The exact primitive edge sequence, with the current vertex updated after each letter. -/
def signedEdges (g : G) : List (Label × Bool) → List (SignedStep Step)
  | [] => []
  | s :: l => signedEdge g s :: signedEdges (g * letterValue s) l

@[simp] theorem signedEdges_length (g : G) (l : List (Label × Bool)) :
    (signedEdges g l).length = l.length := by
  induction l generalizing g with
  | nil => rfl
  | cons s l ih => simp only [signedEdges, List.length_cons, ih]

theorem append_endpoint (g : G) (l r : List (Label × Bool)) :
    Tree.vertex (g * FreeGroup.mk (l ++ r)) =
      Tree.vertex ((g * FreeGroup.mk l) * FreeGroup.mk r) := by
  rw [← FreeGroup.mul_mk, mul_assoc]

theorem signedEdges_append (g : G) (l r : List (Label × Bool)) :
    signedEdges g (l ++ r) = signedEdges g l ++ signedEdges (g * FreeGroup.mk l) r := by
  induction l generalizing g with
  | nil => simp [signedEdges, ← FreeGroup.one_eq_mk]
  | cons s l ih =>
      simp only [List.cons_append, signedEdges, ih, RoseLiftedWords.mk_cons, mul_assoc]

/-- A genuinely composable word of signed edges, preserving the empty vertex. -/
def walkWord (g : G) : (l : List (Label × Bool)) →
    WalkWord (.vertex g) (.vertex (g * FreeGroup.mk l))
  | [] => castWord (.nil (.vertex g)) rfl (by simp [← FreeGroup.one_eq_mk])
  | s :: l => castWord ((atomWord g s).append (walkWord (g * letterValue s) l))
      rfl (by simp only [RoseLiftedWords.mk_cons, mul_assoc])

@[simp] theorem walkWord_toList (g : G) (l : List (Label × Bool)) :
    (walkWord g l).toList = signedEdges g l := by
  induction l generalizing g with
  | nil => simp [walkWord, LiteralWord.Word.toList, signedEdges]
  | cons s l ih =>
      simp only [walkWord, castWord_toList, LiteralWord.Word.toList_append,
        atomWord_toList, ih, List.singleton_append, signedEdges]

theorem walkWord_append (g : G) (l r : List (Label × Bool)) :
    walkWord g (l ++ r) =
      castWord ((walkWord g l).append (walkWord (g * FreeGroup.mk l) r))
        rfl (append_endpoint g l r) := by
  apply LiteralWord.Word.toList_injective
  simp only [walkWord_toList, castWord_toList, LiteralWord.Word.toList_append,
    signedEdges_append]

def walkTrace (g : G) (l : List (Label × Bool)) :
    WalkTrace (.vertex g) (.vertex (g * FreeGroup.mk l)) := (walkWord g l).toTrace

@[simp] theorem walkTrace_length (g : G) (l : List (Label × Bool)) :
    GeometricTrace.traceLength (walkTrace g l) = l.length := by
  simp [walkTrace, LiteralWord.Word.length]

def walkPath (g : G) (l : List (Label × Bool)) :
    _root_.Path (Tree.vertex g) (Tree.vertex (g * FreeGroup.mk l)) :=
  GeometricTrace.flatRealize (walkTrace g l)

@[simp] theorem walkPath_nil_apply (g : G) (t : I) :
    walkPath g [] t = Tree.vertex g := by
  unfold walkPath walkTrace walkWord
  rw [flatRealize_castWord]
  rfl

theorem flatRealize_word_append {a b c : Tree} (p : WalkWord a b) (q : WalkWord b c) :
    GeometricTrace.flatRealize (p.append q).toTrace =
      GeometricTrace.flatRealize (p.toTrace.trans q.toTrace) := by
  apply GeometricTrace.flatRealize_eq_of_flatWord
  rw [← LiteralWord.Word.toFlatWord_ofTrace, ← LiteralWord.Word.toFlatWord_ofTrace]
  simp only [LiteralWord.Word.ofTrace_toTrace, LiteralWord.Word.ofTrace_trans]

/-- Exact flat concatenation, derived from equality of the actual signed edge words. -/
theorem walkPath_append (g : G) (l r : List (Label × Bool)) :
    walkPath g (l ++ r) =
      (GeometricTrace.flatRealize
        ((walkTrace g l).trans (walkTrace (g * FreeGroup.mk l) r))).cast
        rfl (append_endpoint g l r) := by
  change GeometricTrace.flatRealize (walkWord g (l ++ r)).toTrace = _
  rw [walkWord_append, flatRealize_castWord, flatRealize_word_append]
  rfl

theorem walkPath_append_extend (g : G) (l r : List (Label × Bool)) (t : ℝ) :
    (walkPath g (l ++ r)).extend t =
      (GeometricTrace.flatRealize
        ((walkTrace g l).trans (walkTrace (g * FreeGroup.mk l) r))).extend t := by
  rw [walkPath_append]
  rfl

theorem singleton_endpoint (g : G) (s : Label × Bool) :
    Tree.vertex (g * FreeGroup.mk [s]) = Tree.vertex (g * letterValue s) := by
  simp [RoseLiftedWords.mk_cons, ← FreeGroup.one_eq_mk]

theorem walkWord_singleton (g : G) (s : Label × Bool) :
    walkWord g [s] = castWord (atomWord g s) rfl (singleton_endpoint g s) := by
  apply LiteralWord.Word.toList_injective
  simp [signedEdges]

theorem flatRealize_atomWord_apply (g : G) (s : Label × Bool) (t : I) :
    GeometricTrace.flatRealize (atomWord g s).toTrace t =
      RoseLiftedWords.liftLetter g s t := by
  unfold atomWord
  rw [flatRealize_castWord]
  rcases s with ⟨i, b⟩
  cases b <;> rfl

@[simp] theorem walkPath_singleton_apply (g : G) (s : Label × Bool) (t : I) :
    walkPath g [s] t = RoseLiftedWords.liftLetter g s t := by
  change GeometricTrace.flatRealize (walkWord g [s]).toTrace t = _
  rw [walkWord_singleton, flatRealize_castWord]
  exact flatRealize_atomWord_apply g s t

/-- The last signed edge occupies the final closed equal slot. -/
theorem walkPath_last_slot (g : G) (l : List (Label × Bool)) (s : Label × Bool) (t : I) :
    (walkPath g (l ++ [s])).extend
        (((l.length : ℝ) + (t : ℝ)) / ((l.length + 1 : ℕ) : ℝ)) =
      RoseLiftedWords.liftLetter (g * FreeGroup.mk l) s t := by
  rw [walkPath_append_extend]
  have h := GeometricTrace.flatRealize_trans_right_slot
    (walkTrace g l) (walkTrace (g * FreeGroup.mk l) [s])
    ⟨0, by simp⟩ t
  have h' : (GeometricTrace.flatRealize
      ((walkTrace g l).trans (walkTrace (g * FreeGroup.mk l) [s]))).extend
        (((l.length : ℝ) + (t : ℝ)) / ((l.length + 1 : ℕ) : ℝ)) =
      walkPath (g * FreeGroup.mk l) [s] t := by
    simpa only [walkTrace_length, List.length_singleton, Fin.val_mk, Nat.cast_one, Nat.cast_zero,
      add_zero, zero_add, div_one, _root_.Path.extend_extends', walkPath] using h
  exact h'.trans (walkPath_singleton_apply _ s t)

/-- Rescale a time into the prefix of a word with one additional final edge. -/
def prefixTime (m : ℕ) (t : I) : I :=
  ⟨(m : ℝ) / ((m + 1 : ℕ) : ℝ) * (t : ℝ), by
    have hd : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hr0 : (0 : ℝ) ≤ (m : ℝ) / ((m + 1 : ℕ) : ℝ) := by positivity
    have hr1 : (m : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ 1 := by
      apply (div_le_iff₀ hd).mpr
      simp
    constructor
    · exact mul_nonneg hr0 t.2.1
    · exact (mul_le_mul_of_nonneg_left t.2.2 hr0).trans (by simpa using hr1)⟩

theorem prefixTime_le (m : ℕ) (t : I) :
    (prefixTime m t : ℝ) ≤ (m : ℝ) / ((m + 1 : ℕ) : ℝ) := by
  change (m : ℝ) / ((m + 1 : ℕ) : ℝ) * (t : ℝ) ≤ _
  simpa only [mul_one] using mul_le_mul_of_nonneg_left t.2.2
    (show (0 : ℝ) ≤ (m : ℝ) / ((m + 1 : ℕ) : ℝ) from by positivity)

/-- The entire initial prefix, including the empty prefix, has exact timing. -/
theorem walkPath_prefix (g : G) (l : List (Label × Bool)) (s : Label × Bool) (t : I) :
    (walkPath g (l ++ [s])).extend
        ((l.length : ℝ) / ((l.length + 1 : ℕ) : ℝ) * (t : ℝ)) = walkPath g l t := by
  by_cases hm : l.length = 0
  · have hl : l = [] := List.length_eq_zero_iff.mp hm
    subst l
    simp only [List.length_nil, Nat.cast_zero, zero_div, zero_mul,
      _root_.Path.extend_zero, walkPath_nil_apply]
  · have hp : 0 < GeometricTrace.traceLength (walkTrace g l) := by
      rw [walkTrace_length]
      exact Nat.pos_of_ne_zero hm
    have hq : 0 < GeometricTrace.traceLength (walkTrace (g * FreeGroup.mk l) [s]) := by simp
    have ht : (prefixTime l.length t : ℝ) ≤
        (GeometricTrace.traceLength (walkTrace g l) : ℝ) /
          ((GeometricTrace.traceLength (walkTrace g l) +
            GeometricTrace.traceLength (walkTrace (g * FreeGroup.mk l) [s]) : ℕ) : ℝ) := by
      simpa only [walkTrace_length, List.length_singleton] using prefixTime_le l.length t
    rw [walkPath_append_extend]
    change (GeometricTrace.flatRealize
      ((walkTrace g l).trans (walkTrace (g * FreeGroup.mk l) [s]))).extend
        (prefixTime l.length t : ℝ) = _
    rw [_root_.Path.extend_apply _ (prefixTime l.length t).2,
      GeometricTrace.flatRealize_trans_left_value _ _ hp hq _ ht]
    simp only [walkTrace_length, List.length_singleton]
    change (walkPath g l).extend
      (((l.length + 1 : ℕ) : ℝ) / (l.length : ℝ) *
        ((l.length : ℝ) / ((l.length + 1 : ℕ) : ℝ) * (t : ℝ))) = _
    have hmR : (l.length : ℝ) ≠ 0 := by exact_mod_cast hm
    have hd : (((l.length + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have he : (((l.length + 1 : ℕ) : ℝ) / (l.length : ℝ)) *
        ((l.length : ℝ) / ((l.length + 1 : ℕ) : ℝ) * (t : ℝ)) = t := by
      field_simp [hmR, hd]
    rw [he, _root_.Path.extend_extends']

/-- The canonical root path follows the actual reduced word from the identity. -/
def rootPath (g : G) : _root_.Path (Tree.vertex (1 : G)) (Tree.vertex g) :=
  (walkPath 1 g.toWord).cast rfl (by simp [FreeGroup.mk_toWord])

@[simp] theorem rootPath_apply (g : G) (t : I) : rootPath g t = walkPath 1 g.toWord t := rfl

theorem rootPath_extend (g : G) (t : ℝ) :
    (rootPath g).extend t = (walkPath 1 g.toWord).extend t := rfl

@[simp] theorem root_walk_length (g : G) :
    GeometricTrace.traceLength (walkTrace 1 g.toWord) = FreeGroup.norm g := by
  rw [walkTrace_length]
  rfl

@[simp] theorem rootPath_one (t : I) : rootPath 1 t = Tree.vertex 1 := by
  rw [rootPath_apply, FreeGroup.toWord_one, walkPath_nil_apply]

theorem outward_prefix (g : G) (i : Label)
    (h : FreeGroup.norm g < FreeGroup.norm (g * FreeGroup.of i)) (t : I) :
    (rootPath (g * FreeGroup.of i)).extend
        ((FreeGroup.norm g : ℝ) / ((FreeGroup.norm g + 1 : ℕ) : ℝ) * (t : ℝ)) =
      rootPath g t := by
  rw [rootPath_extend, CayleyReducedPrefix.toWord_mul_of_eq_append_of_norm_lt g i h,
    rootPath_apply]
  exact walkPath_prefix 1 g.toWord (i, true) t

theorem inward_prefix (g : G) (i : Label)
    (h : FreeGroup.norm (g * FreeGroup.of i) < FreeGroup.norm g) (t : I) :
    (rootPath g).extend
        ((FreeGroup.norm (g * FreeGroup.of i) : ℝ) /
          ((FreeGroup.norm (g * FreeGroup.of i) + 1 : ℕ) : ℝ) * (t : ℝ)) =
      rootPath (g * FreeGroup.of i) t := by
  rw [rootPath_extend, CayleyReducedPrefix.toWord_eq_append_of_norm_lt g i h,
    rootPath_apply]
  exact walkPath_prefix 1 (g * FreeGroup.of i).toWord (i, false) t

theorem outward_last_edge (g : G) (i : Label)
    (h : FreeGroup.norm g < FreeGroup.norm (g * FreeGroup.of i)) (t : I) :
    (rootPath (g * FreeGroup.of i)).extend
        (((FreeGroup.norm g : ℝ) + (t : ℝ)) / ((FreeGroup.norm g + 1 : ℕ) : ℝ)) =
      edge g i t := by
  rw [rootPath_extend, CayleyReducedPrefix.toWord_mul_of_eq_append_of_norm_lt g i h]
  have he := walkPath_last_slot 1 g.toWord (i, true) t
  have hv : (1 : G) * FreeGroup.mk g.toWord = g := by
    rw [FreeGroup.mk_toWord, one_mul]
  rw [hv] at he
  change (walkPath 1 (g.toWord ++ [(i, true)])).extend
      ((((g.toWord).length : ℝ) + (t : ℝ)) / (((g.toWord).length + 1 : ℕ) : ℝ)) =
    edge g i t
  exact he

theorem inward_last_edge (g : G) (i : Label)
    (h : FreeGroup.norm (g * FreeGroup.of i) < FreeGroup.norm g) (t : I) :
    (rootPath g).extend
        (((FreeGroup.norm (g * FreeGroup.of i) : ℝ) + (t : ℝ)) /
          ((FreeGroup.norm (g * FreeGroup.of i) + 1 : ℕ) : ℝ)) =
      edge g i (unitInterval.symm t) := by
  rw [rootPath_extend, CayleyReducedPrefix.toWord_eq_append_of_norm_lt g i h]
  have he := walkPath_last_slot 1 (g * FreeGroup.of i).toWord (i, false) t
  have hv : (1 : G) * FreeGroup.mk (g * FreeGroup.of i).toWord = g * FreeGroup.of i := by
    rw [FreeGroup.mk_toWord, one_mul]
  rw [hv] at he
  change (walkPath 1 ((g * FreeGroup.of i).toWord ++ [(i, false)])).extend
      (((FreeGroup.norm (g * FreeGroup.of i) : ℝ) + (t : ℝ)) /
        ((FreeGroup.norm (g * FreeGroup.of i) + 1 : ℕ) : ℝ)) =
    edge g i (unitInterval.symm t)
  have he' : (walkPath 1 ((g * FreeGroup.of i).toWord ++ [(i, false)])).extend
      (((FreeGroup.norm (g * FreeGroup.of i) : ℝ) + (t : ℝ)) /
        ((FreeGroup.norm (g * FreeGroup.of i) + 1 : ℕ) : ℝ)) =
    edge ((g * FreeGroup.of i) * (FreeGroup.of i)⁻¹) i (unitInterval.symm t) := he
  have hg : (g * FreeGroup.of i) * (FreeGroup.of i)⁻¹ = g := by simp
  rw [hg] at he'
  exact he'

end
end ComputationalPaths.Path.GeometricTopology.CayleyFlatWalk
