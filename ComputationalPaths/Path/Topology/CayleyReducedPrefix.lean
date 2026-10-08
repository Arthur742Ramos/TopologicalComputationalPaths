import ComputationalPaths.Path.Topology.RoseReducedWords

/-!
# Reduced-word prefixes along a Cayley edge

Right multiplication by a positive primitive either appends that primitive
or deletes its negative occurrence at the end of the reduced word. Thus the
shorter endpoint word is an exact prefix of the longer endpoint word and their
lengths differ by one. These are algebraic facts derived from Mathlib's actual
word reduction; no graph, covering, or geometric completeness is assumed.
-/

namespace ComputationalPaths.Path.GeometricTopology.CayleyReducedPrefix

open RoseReducedWords

abbrev G := FreeGroup Label

section GeneralWords

variable {α : Type*} [DecidableEq α]

/-- Prepending one signed letter to a reduced word either keeps it or cancels
the opposite initial letter. -/
theorem reduce_cons_cases (w : List (α × Bool))
    (hw : FreeGroup.reduce w = w) (s : α × Bool) :
    FreeGroup.reduce (s :: w) = s :: w ∨
      w = (s.1, !s.2) :: FreeGroup.reduce (s :: w) := by
  cases w with
  | nil => exact Or.inl rfl
  | cons t w =>
      have hr : FreeGroup.reduce (s :: t :: w) =
          if s.1 = t.1 ∧ s.2 = !t.2 then w else s :: t :: w := by
        rw [FreeGroup.reduce.cons, hw]
      by_cases hc : s.1 = t.1 ∧ s.2 = !t.2
      · right
        have ht : t = (s.1, !s.2) := by
          apply Prod.ext
          · exact hc.1.symm
          · simpa only [Bool.not_not] using (_root_.congrArg Bool.not hc.2).symm
        have hred : FreeGroup.reduce (s :: t :: w) = w := by
          simpa only [if_pos hc] using hr
        rw [hred, ht]
      · left
        simpa only [if_neg hc] using hr

/-- Appending one signed letter to a reduced word either keeps it or cancels
the opposite final letter. This is obtained by reversing and inverting the
checked initial-letter reduction. -/
theorem reduce_append_singleton_cases (w : List (α × Bool))
    (hw : FreeGroup.reduce w = w) (i : α) (b : Bool) :
    FreeGroup.reduce (w ++ [(i, b)]) = w ++ [(i, b)] ∨
      w = FreeGroup.reduce (w ++ [(i, b)]) ++ [(i, !b)] := by
  have hwi : FreeGroup.reduce (FreeGroup.invRev w) = FreeGroup.invRev w := by
    rw [FreeGroup.reduce_invRev, hw]
  have hi : FreeGroup.invRev (w ++ [(i, b)]) =
      (i, !b) :: FreeGroup.invRev w := by
    rw [FreeGroup.invRev_append]
    rfl
  have hr : FreeGroup.reduce ((i, !b) :: FreeGroup.invRev w) =
      FreeGroup.invRev (FreeGroup.reduce (w ++ [(i, b)])) := by
    rw [← hi, FreeGroup.reduce_invRev]
  rcases reduce_cons_cases (FreeGroup.invRev w) hwi (i, !b) with h | h
  · left
    have hh := _root_.congrArg FreeGroup.invRev h
    rw [hr, FreeGroup.invRev_invRev, FreeGroup.invRev_cons,
      FreeGroup.invRev_invRev] at hh
    simpa only [FreeGroup.invRev, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, Bool.not_not] using hh
  · right
    have hh := _root_.congrArg FreeGroup.invRev h
    rw [FreeGroup.invRev_invRev, hr, FreeGroup.invRev_cons,
      FreeGroup.invRev_invRev] at hh
    simpa only [FreeGroup.invRev, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, Bool.not_not] using hh

/-- The exact reduced words at both ends of a signed Cayley edge. -/
theorem toWord_mul_signed_cases (g : FreeGroup α) (i : α) (b : Bool) :
    (g * FreeGroup.mk [(i, b)]).toWord = g.toWord ++ [(i, b)] ∨
      g.toWord = (g * FreeGroup.mk [(i, b)]).toWord ++ [(i, !b)] := by
  have h := reduce_append_singleton_cases g.toWord (FreeGroup.reduce_toWord g) i b
  have hm : (g * FreeGroup.mk [(i, b)]).toWord =
      FreeGroup.reduce (g.toWord ++ [(i, b)]) := by
    rw [FreeGroup.toWord_mul, FreeGroup.toWord_mk, FreeGroup.reduce_singleton]
  rwa [← hm] at h

end GeneralWords

/-- A positive edge either appends its positive label or deletes its negative
label. The words are the actual Mathlib reduced representatives. -/
theorem toWord_mul_of_cases (g : G) (i : Label) :
    (g * FreeGroup.of i).toWord = g.toWord ++ [(i, true)] ∨
      g.toWord = (g * FreeGroup.of i).toWord ++ [(i, false)] := by
  exact toWord_mul_signed_cases g i true

/-- Both outward orientations, with the exact one-letter prefix extension and
the corresponding strict length increase. -/
theorem outward_word_cases (g : G) (i : Label) :
    (FreeGroup.norm (g * FreeGroup.of i) = FreeGroup.norm g + 1 ∧
      (g * FreeGroup.of i).toWord = g.toWord ++ [(i, true)]) ∨
    (FreeGroup.norm g = FreeGroup.norm (g * FreeGroup.of i) + 1 ∧
      g.toWord = (g * FreeGroup.of i).toWord ++ [(i, false)]) := by
  rcases toWord_mul_of_cases g i with h | h
  · left
    refine ⟨?_, h⟩
    simpa only [FreeGroup.norm, List.length_append, List.length_cons,
      List.length_nil, Nat.zero_add] using _root_.congrArg List.length h
  · right
    refine ⟨?_, h⟩
    simpa only [FreeGroup.norm, List.length_append, List.length_cons,
      List.length_nil, Nat.zero_add] using _root_.congrArg List.length h

theorem norm_mul_of_cases (g : G) (i : Label) :
    FreeGroup.norm (g * FreeGroup.of i) = FreeGroup.norm g + 1 ∨
      FreeGroup.norm g = FreeGroup.norm (g * FreeGroup.of i) + 1 := by
  rcases outward_word_cases g i with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

theorem norm_lt_or_lt (g : G) (i : Label) :
    FreeGroup.norm g < FreeGroup.norm (g * FreeGroup.of i) ∨
      FreeGroup.norm (g * FreeGroup.of i) < FreeGroup.norm g := by
  rcases norm_mul_of_cases g i with h | h
  · left; omega
  · right; omega

theorem norm_mul_of_ne (g : G) (i : Label) :
    FreeGroup.norm (g * FreeGroup.of i) ≠ FreeGroup.norm g := by
  rcases norm_mul_of_cases g i with h | h <;> omega

/-- One endpoint word is an actual prefix of the other. -/
theorem toWord_prefix_cases (g : G) (i : Label) :
    List.IsPrefix g.toWord (g * FreeGroup.of i).toWord ∨
      List.IsPrefix (g * FreeGroup.of i).toWord g.toWord := by
  rcases toWord_mul_of_cases g i with h | h
  · exact Or.inl ⟨[(i, true)], h.symm⟩
  · exact Or.inr ⟨[(i, false)], h.symm⟩

/-- When the right endpoint is farther from the root, its reduced word appends
the positive edge label. -/
theorem toWord_mul_of_eq_append_of_norm_lt (g : G) (i : Label)
    (h : FreeGroup.norm g < FreeGroup.norm (g * FreeGroup.of i)) :
    (g * FreeGroup.of i).toWord = g.toWord ++ [(i, true)] := by
  rcases outward_word_cases g i with hp | hn
  · exact hp.2
  · have := hn.1; omega

/-- When the left endpoint is farther from the root, its reduced word appends
the negative edge label to the word of the right endpoint. -/
theorem toWord_eq_append_of_norm_lt (g : G) (i : Label)
    (h : FreeGroup.norm (g * FreeGroup.of i) < FreeGroup.norm g) :
    g.toWord = (g * FreeGroup.of i).toWord ++ [(i, false)] := by
  rcases outward_word_cases g i with hp | hn
  · have := hp.1; omega
  · exact hn.2

theorem toWord_prefix_of_norm_lt (g : G) (i : Label)
    (h : FreeGroup.norm g < FreeGroup.norm (g * FreeGroup.of i)) :
    List.IsPrefix g.toWord (g * FreeGroup.of i).toWord :=
  ⟨[(i, true)], (toWord_mul_of_eq_append_of_norm_lt g i h).symm⟩

theorem toWord_mul_of_prefix_of_norm_lt (g : G) (i : Label)
    (h : FreeGroup.norm (g * FreeGroup.of i) < FreeGroup.norm g) :
    List.IsPrefix (g * FreeGroup.of i).toWord g.toWord :=
  ⟨[(i, false)], (toWord_eq_append_of_norm_lt g i h).symm⟩

end ComputationalPaths.Path.GeometricTopology.CayleyReducedPrefix
