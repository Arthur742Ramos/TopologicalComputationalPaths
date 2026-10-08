import ComputationalPaths.Path.Topology.TraceSensitiveTopologicalCompPath
import ComputationalPaths.Path.Topology.WeightedConcatenation
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Equal-slot realization of geometric traces

The existing `GeometricTrace.realize` assigns half the time to each binary
factor. Here the breakpoint is the ratio of the two primitive-letter counts.
Zero-letter factors are omitted. This is a separate realization and does not
change any topology or theorem about the existing binary model.
-/

namespace ComputationalPaths.Path.GeometricTopology

open unitInterval

universe u v

private theorem weighted_zero_zero {X : Type*} [TopologicalSpace X]
    {a b c : X} {m n : Nat} (w : WeightedSlotReparam m n)
    (hm : m = 0 → a = b) (hn : n = 0 → b = c)
    (p : _root_.Path a b) (q : _root_.Path b c)
    (hm0 : m = 0) (hn0 : n = 0) :
    weightedConcatenation w hm hn p q =
      (_root_.Path.refl a).cast rfl ((hm hm0).trans (hn hn0)).symm := by
  subst m
  subst n
  rfl

private theorem weighted_positive {X : Type*} [TopologicalSpace X]
    {a b c : X} {m n : Nat} (w : WeightedSlotReparam m n)
    (hm : m = 0 → a = b) (hn : n = 0 → b = c)
    (p : _root_.Path a b) (q : _root_.Path b c)
    (hm0 : 0 < m) (hn0 : 0 < n) :
    weightedConcatenation w hm hn p q =
      (p.trans q).reparam w.map w.continuous_map w.map_zero w.map_one := by
  cases m with
  | zero => omega
  | succ m => cases n with
    | zero => omega
    | succ n => rfl

private theorem weighted_left_zero {X : Type*} [TopologicalSpace X]
    {a b c : X} {m n : Nat} (w : WeightedSlotReparam m n)
    (hm : m = 0 → a = b) (hn : n = 0 → b = c)
    (p : _root_.Path a b) (q : _root_.Path b c)
    (hm0 : m = 0) (hn0 : 0 < n) :
    weightedConcatenation w hm hn p q = q.cast (hm hm0) rfl := by
  subst m
  cases n with
  | zero => omega
  | succ n => rfl

private theorem weighted_right_zero {X : Type*} [TopologicalSpace X]
    {a b c : X} {m n : Nat} (w : WeightedSlotReparam m n)
    (hm : m = 0 → a = b) (hn : n = 0 → b = c)
    (p : _root_.Path a b) (q : _root_.Path b c)
    (hm0 : 0 < m) (hn0 : n = 0) :
    weightedConcatenation w hm hn p q = p.cast rfl (hn hn0).symm := by
  subst n
  cases m with
  | zero => omega
  | succ m => rfl

namespace GeometricTrace

variable {A : Type u} [TopologicalSpace A] {Step : Type v}
  {S : GeometricStepSystem A Step}

theorem length_zero_endpoint {a b : A} (p : GeometricTrace S a b)
    (h : traceLength p = 0) : a = b := by
  induction p with
  | refl a => rfl
  | single s => simp [traceLength] at h
  | trans p q ihp ihq =>
      have hp : traceLength p = 0 := by simp only [traceLength] at h; omega
      have hq : traceLength q = 0 := by simp only [traceLength] at h; omega
      exact (ihp hp).trans (ihq hq)
  | symm p ih => exact (ih h).symm

/-- Balanced slot data, with the identity map in the unused zero cases. -/
noncomputable def equalSlotReparam (m n : Nat) : WeightedSlotReparam m n :=
  match m, n with
  | 0, _ => ⟨id, continuous_id, rfl, rfl⟩
  | _ + 1, 0 => ⟨id, continuous_id, rfl, rfl⟩
  | m + 1, n + 1 => balancedSlotReparam (m + 1) (n + 1) (by omega) (by omega)

theorem equalSlotReparam_pos (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    equalSlotReparam m n = balancedSlotReparam m n hm hn := by
  cases m with
  | zero => omega
  | succ m => cases n with
    | zero => omega
    | succ n => rfl

/-- Execute each primitive signed letter for an equal share of the interval. -/
noncomputable def flatRealize {a b : A} : GeometricTrace S a b → _root_.Path a b
  | .refl a => _root_.Path.refl a
  | .single s => S.realize s
  | .trans p q => weightedConcatenation
      (equalSlotReparam (traceLength p) (traceLength q))
      (length_zero_endpoint p) (length_zero_endpoint q)
      (flatRealize p) (flatRealize q)
  | .symm p => (flatRealize p).symm

/-- No-letter traces have constant equal-slot realization, up to endpoint casts. -/
theorem flatRealize_zero {a b : A} (p : GeometricTrace S a b)
    (h : traceLength p = 0) :
    flatRealize p = (_root_.Path.refl a).cast rfl (length_zero_endpoint p h).symm := by
  induction p with
  | refl a => rfl
  | single s => simp [traceLength] at h
  | @trans a b c p q ihp ihq =>
      have hp : traceLength p = 0 := by simp only [traceLength] at h; omega
      have hq : traceLength q = 0 := by simp only [traceLength] at h; omega
      have hab := length_zero_endpoint p hp
      have hbc := length_zero_endpoint q hq
      cases hab
      cases hbc
      exact weighted_zero_zero _ _ _ _ _ hp hq
  | @symm a b p ih =>
      have hab := length_zero_endpoint p h
      cases hab
      simpa [flatRealize] using _root_.congrArg _root_.Path.symm (ih h)

theorem flatRealize_endpointNull {a b : A} (p : GeometricTrace S a b)
    (h : traceLength p = 0) : EndpointNull (flatRealize p) :=
  ⟨length_zero_endpoint p h, by rw [flatRealize_zero p h]⟩

/-- The flat and binary realizations have the same endpoint-fixed homotopy
class. This statement alone does not compare observable topologies. -/
theorem flatRealize_homotopic_binary {a b : A} (p : GeometricTrace S a b) :
    _root_.Path.Homotopic (flatRealize p) (realize p) := by
  induction p with
  | refl a => exact .refl _
  | single s => exact .refl _
  | trans p q ihp ihq =>
      exact (weightedConcatenation_homotopic_to_fixed
        (equalSlotReparam (traceLength p) (traceLength q))
        (length_zero_endpoint p) (length_zero_endpoint q)
        (flatRealize p) (flatRealize q)
        (flatRealize_endpointNull p) (flatRealize_endpointNull q)).trans
        (ihp.hcomp ihq)
  | symm p ih => exact _root_.Path.Homotopic.symm₂ ih

theorem flatRealize_trans_positive {a b c : A}
    (p : GeometricTrace S a b) (q : GeometricTrace S b c)
    (hp : 0 < traceLength p) (hq : 0 < traceLength q) :
    flatRealize (p.trans q) =
      ((flatRealize p).trans (flatRealize q)).reparam
        (balancedSlotMap (traceLength p) (traceLength q) hp hq)
        (continuous_balancedSlotMap _ _ hp hq)
        (balancedSlotMap_zero _ _ hp hq) (balancedSlotMap_one _ _ hp hq) := by
  change weightedConcatenation _ _ _ _ _ = _
  rw [weighted_positive _ _ _ _ _ hp hq, equalSlotReparam_pos _ _ hp hq]
  rfl

theorem flatRealize_trans_left_value {a b c : A}
    (p : GeometricTrace S a b) (q : GeometricTrace S b c)
    (hp : 0 < traceLength p) (hq : 0 < traceLength q) (t : I)
    (ht : (t : ℝ) ≤ (traceLength p : ℝ) / ((traceLength p + traceLength q : Nat) : ℝ)) :
    flatRealize (p.trans q) t = (flatRealize p).extend
      (((traceLength p + traceLength q : Nat) : ℝ) / (traceLength p : ℝ) * (t : ℝ)) := by
  have hpR : (0 : ℝ) < (traceLength p : ℝ) := by exact_mod_cast hp
  have hqR : (0 : ℝ) < (traceLength q : ℝ) := by exact_mod_cast hq
  have hsum : (0 : ℝ) < ((traceLength p + traceLength q : Nat) : ℝ) := by positivity
  have hmap : (balancedSlotMap _ _ hp hq t : ℝ) =
      ((traceLength p + traceLength q : Nat) : ℝ) / (2 * (traceLength p : ℝ)) * (t : ℝ) := by
    simp only [balancedSlotMap, if_pos ht]
  have hhalf : (balancedSlotMap _ _ hp hq t : ℝ) ≤ 1 / 2 := by
    rw [hmap]
    have hb := mul_le_mul_of_nonneg_left ht (by positivity :
      0 ≤ ((traceLength p + traceLength q : Nat) : ℝ) / (2 * (traceLength p : ℝ)))
    have heq : ((traceLength p + traceLength q : Nat) : ℝ) / (2 * (traceLength p : ℝ)) *
        ((traceLength p : ℝ) / ((traceLength p + traceLength q : Nat) : ℝ)) = 1 / 2 := by
      field_simp
    rwa [heq] at hb
  rw [flatRealize_trans_positive p q hp hq]
  change ((flatRealize p).trans (flatRealize q)) (balancedSlotMap _ _ hp hq t) = _
  rw [← _root_.Path.extend_extends', _root_.Path.extend_trans_of_le_half _ _ hhalf]
  congr 1
  rw [hmap]
  field_simp

theorem flatRealize_trans_right_value {a b c : A}
    (p : GeometricTrace S a b) (q : GeometricTrace S b c)
    (hp : 0 < traceLength p) (hq : 0 < traceLength q) (t : I)
    (ht : (traceLength p : ℝ) / ((traceLength p + traceLength q : Nat) : ℝ) ≤ (t : ℝ)) :
    flatRealize (p.trans q) t = (flatRealize q).extend
      (((traceLength p + traceLength q : Nat) : ℝ) / (traceLength q : ℝ) *
        ((t : ℝ) - (traceLength p : ℝ) / ((traceLength p + traceLength q : Nat) : ℝ))) := by
  have hpR : (0 : ℝ) < (traceLength p : ℝ) := by exact_mod_cast hp
  have hqR : (0 : ℝ) < (traceLength q : ℝ) := by exact_mod_cast hq
  have hsum : (0 : ℝ) < ((traceLength p + traceLength q : Nat) : ℝ) := by positivity
  have hmap : (balancedSlotMap _ _ hp hq t : ℝ) =
      1 / 2 + ((traceLength p + traceLength q : Nat) : ℝ) / (2 * (traceLength q : ℝ)) *
        ((t : ℝ) - (traceLength p : ℝ) / ((traceLength p + traceLength q : Nat) : ℝ)) := by
    unfold balancedSlotMap
    dsimp only
    split_ifs with h
    · have heq : (t : ℝ) = (traceLength p : ℝ) /
          ((traceLength p + traceLength q : Nat) : ℝ) := le_antisymm h ht
      rw [heq]
      field_simp
      ring
    · rfl
  have hhalf : 1 / 2 ≤ (balancedSlotMap _ _ hp hq t : ℝ) := by
    rw [hmap]
    have hnonneg : 0 ≤ ((traceLength p + traceLength q : Nat) : ℝ) /
        (2 * (traceLength q : ℝ)) *
        ((t : ℝ) - (traceLength p : ℝ) / ((traceLength p + traceLength q : Nat) : ℝ)) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr ht)
    linarith
  rw [flatRealize_trans_positive p q hp hq]
  change ((flatRealize p).trans (flatRealize q)) (balancedSlotMap _ _ hp hq t) = _
  rw [← _root_.Path.extend_extends', _root_.Path.extend_trans_of_half_le _ _ hhalf]
  congr 1
  rw [hmap]
  field_simp
  ring

theorem flatRealize_trans_left_slot {a b c : A}
    (p : GeometricTrace S a b) (q : GeometricTrace S b c)
    (i : Fin (traceLength p)) (t : I) :
    (flatRealize (p.trans q)).extend
      (((i.val : ℝ) + (t : ℝ)) / ((traceLength p + traceLength q : Nat) : ℝ)) =
      (flatRealize p).extend (((i.val : ℝ) + (t : ℝ)) / (traceLength p : ℝ)) := by
  have hp : 0 < traceLength p := Nat.zero_lt_of_lt i.isLt
  have hpR : (0 : ℝ) < (traceLength p : ℝ) := by exact_mod_cast hp
  by_cases hq0 : traceLength q = 0
  · have hbc := length_zero_endpoint q hq0
    cases hbc
    have heq : flatRealize (p.trans q) = flatRealize p :=
      weighted_right_zero _ _ _ _ _ hp hq0
    rw [heq]
    simp [hq0]
  · have hq : 0 < traceLength q := Nat.pos_of_ne_zero hq0
    have hqR : (0 : ℝ) < (traceLength q : ℝ) := by exact_mod_cast hq
    have hsum : (0 : ℝ) < ((traceLength p + traceLength q : Nat) : ℝ) := by positivity
    have hi : (i.val : ℝ) + 1 ≤ (traceLength p : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt i.isLt
    have ht0 := t.2.1
    have hnum : (i.val : ℝ) + (t : ℝ) ≤ (traceLength p : ℝ) := by linarith [t.2.2]
    have hT : ((i.val : ℝ) + (t : ℝ)) / ((traceLength p + traceLength q : Nat) : ℝ) ∈ I := by
      constructor
      · exact div_nonneg (by positivity) hsum.le
      · apply (div_le_one hsum).2
        simp only [Nat.cast_add]
        linarith
    rw [_root_.Path.extend_apply _ hT]
    rw [flatRealize_trans_left_value p q hp hq _
      ((div_le_div_iff_of_pos_right hsum).2 hnum)]
    congr 1
    dsimp only
    field_simp

theorem flatRealize_trans_right_slot {a b c : A}
    (p : GeometricTrace S a b) (q : GeometricTrace S b c)
    (i : Fin (traceLength q)) (t : I) :
    (flatRealize (p.trans q)).extend
      (((traceLength p : ℝ) + (i.val : ℝ) + (t : ℝ)) /
        ((traceLength p + traceLength q : Nat) : ℝ)) =
      (flatRealize q).extend (((i.val : ℝ) + (t : ℝ)) / (traceLength q : ℝ)) := by
  have hq : 0 < traceLength q := Nat.zero_lt_of_lt i.isLt
  have hqR : (0 : ℝ) < (traceLength q : ℝ) := by exact_mod_cast hq
  by_cases hp0 : traceLength p = 0
  · have hab := length_zero_endpoint p hp0
    cases hab
    have heq : flatRealize (p.trans q) = flatRealize q :=
      weighted_left_zero _ _ _ _ _ hp0 hq
    rw [heq]
    simp [hp0]
  · have hp : 0 < traceLength p := Nat.pos_of_ne_zero hp0
    have hpR : (0 : ℝ) < (traceLength p : ℝ) := by exact_mod_cast hp
    have hsum : (0 : ℝ) < ((traceLength p + traceLength q : Nat) : ℝ) := by positivity
    have hi : (i.val : ℝ) + 1 ≤ (traceLength q : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt i.isLt
    have ht0 := t.2.1
    have hnum : (traceLength p : ℝ) + (i.val : ℝ) + (t : ℝ) ≤
        ((traceLength p + traceLength q : Nat) : ℝ) := by
      simp only [Nat.cast_add]
      linarith [t.2.2]
    have hT : ((traceLength p : ℝ) + (i.val : ℝ) + (t : ℝ)) /
        ((traceLength p + traceLength q : Nat) : ℝ) ∈ I :=
      ⟨div_nonneg (by positivity) hsum.le, (div_le_one hsum).2 hnum⟩
    rw [_root_.Path.extend_apply _ hT]
    have hcut : (traceLength p : ℝ) / ((traceLength p + traceLength q : Nat) : ℝ) ≤
        ((traceLength p : ℝ) + (i.val : ℝ) + (t : ℝ)) /
          ((traceLength p + traceLength q : Nat) : ℝ) := by
      apply (div_le_div_iff_of_pos_right hsum).2
      have hi0 : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
      linarith
    rw [flatRealize_trans_right_value p q hp hq _ hcut]
    congr 1
    dsimp only
    field_simp
    ring

/-- The exact signed-letter sequence, indexed by primitive-letter count. -/
def letters {a b : A} : (p : GeometricTrace S a b) → Fin (traceLength p) → SignedStep Step
  | .refl _, i => Fin.elim0 i
  | .single s, _ => Sum.inl s
  | .trans p q, i => Fin.append (letters p) (letters q) i
  | .symm p, i => signedStepSymm (letters p i.rev)

theorem flatWord_eq_letters {a b : A} (p : GeometricTrace S a b) :
    flatWord p = ⟨traceLength p, letters p⟩ := by
  induction p with
  | refl a => rfl
  | single s => rfl
  | trans p q ihp ihq =>
      change flatWordTrans (flatWord p) (flatWord q) = _
      rw [ihp, ihq]
      rfl
  | symm p ih =>
      change flatWordSymm (flatWord p) = _
      rw [ih]
      rfl

/-- Evaluation of one signed primitive path on the extended real interval. -/
noncomputable def signedRealization : SignedStep Step → ℝ → A
  | Sum.inl s => (S.realize s).extend
  | Sum.inr s => (S.realize s).symm.extend

theorem signedRealization_symm (s : SignedStep Step) (t : ℝ) :
    signedRealization (S := S) (signedStepSymm s) t =
      signedRealization (S := S) s (1 - t) := by
  cases s with
  | inl s => exact _root_.Path.extend_symm_apply _ _
  | inr s =>
      change (S.realize s).extend t = (S.realize s).symm.extend (1 - t)
      rw [_root_.Path.extend_symm_apply]
      congr 1
      ring

/-- Every signed primitive letter occupies exactly its prescribed equal slot.
Both ends of each slot are included; endpoint compatibility handles seams. -/
theorem flatRealize_slot {a b : A} (p : GeometricTrace S a b) :
    ∀ (i : Fin (traceLength p)) (t : I),
      (flatRealize p).extend (((i.val : ℝ) + (t : ℝ)) / (traceLength p : ℝ)) =
        signedRealization (S := S) (letters p i) t := by
  induction p with
  | refl a => intro i; exact Fin.elim0 i
  | single s =>
      intro i t
      simp [flatRealize, letters, traceLength, signedRealization]
  | trans p q ihp ihq =>
      intro i t
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [traceLength, Fin.val_castAdd, letters, Fin.append_left]
        exact (flatRealize_trans_left_slot p q j t).trans (ihp j t)
      · simp only [traceLength, Fin.val_natAdd, Nat.cast_add, letters, Fin.append_right]
        simpa only [Nat.cast_add] using
          (flatRealize_trans_right_slot p q j t).trans (ihq j t)
  | symm p ih =>
      intro i t
      change Fin (traceLength p) at i
      change (flatRealize p).symm.extend
        (((i.val : ℝ) + (t : ℝ)) / (traceLength p : ℝ)) =
          signedRealization (S := S) (signedStepSymm (letters p i.rev)) t
      rw [_root_.Path.extend_symm_apply]
      let tr : I := ⟨1 - (t : ℝ), by constructor <;> linarith [t.2.1, t.2.2]⟩
      have hn : (0 : ℝ) < (traceLength p : ℝ) := by
        exact_mod_cast Nat.zero_lt_of_lt i.isLt
      have hiNat : i.rev.val + 1 + i.val = traceLength p := by
        simp only [Fin.val_rev]
        have := i.isLt
        omega
      have hi : (i.rev.val : ℝ) + 1 + (i.val : ℝ) = (traceLength p : ℝ) := by
        exact_mod_cast hiNat
      have heq : 1 - ((i.val : ℝ) + (t : ℝ)) / (traceLength p : ℝ) =
          ((i.rev.val : ℝ) + (tr : ℝ)) / (traceLength p : ℝ) := by
        change 1 - ((i.val : ℝ) + (t : ℝ)) / (traceLength p : ℝ) =
          ((i.rev.val : ℝ) + (1 - (t : ℝ))) / (traceLength p : ℝ)
        field_simp
        simp only [Fin.val_rev] at hi ⊢
        linarith
      rw [heq, ih i.rev tr, signedRealization_symm]

private theorem exists_slot (n : Nat) (hn : 0 < n) (t : I) :
    ∃ (i : Fin n) (s : I), (t : ℝ) = ((i.val : ℝ) + (s : ℝ)) / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  by_cases ht : (t : ℝ) = 1
  · let i : Fin n := ⟨n - 1, by omega⟩
    refine ⟨i, 1, ?_⟩
    have hiNat : i.val + 1 = n := by dsimp [i]; omega
    have hi : (i.val : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hiNat
    change (t : ℝ) = ((i.val : ℝ) + 1) / (n : ℝ)
    rw [ht, hi, div_self hnR.ne']
  · let k := Nat.floor ((n : ℝ) * (t : ℝ))
    have ha : 0 ≤ (n : ℝ) * (t : ℝ) := mul_nonneg hnR.le t.2.1
    have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 ht
    have hk : k < n := (Nat.floor_lt ha).2 (by nlinarith)
    have hk0 : (k : ℝ) ≤ (n : ℝ) * (t : ℝ) := Nat.floor_le ha
    have hk1 : (n : ℝ) * (t : ℝ) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    let i : Fin n := ⟨k, hk⟩
    let s : I := ⟨(n : ℝ) * (t : ℝ) - (k : ℝ),
      ⟨sub_nonneg.mpr hk0, by linarith⟩⟩
    refine ⟨i, s, ?_⟩
    change (t : ℝ) = ((k : ℝ) + ((n : ℝ) * (t : ℝ) - (k : ℝ))) / (n : ℝ)
    field_simp
    ring

private theorem letters_congr {n m : Nat} {f : Fin n → SignedStep Step}
    {g : Fin m → SignedStep Step} (h : n = m) (hf : HEq f g) (i : Fin n) :
    f i = g (Fin.cast h i) := by
  subst m
  exact _root_.congrFun (eq_of_heq hf) i

theorem flatRealize_eq_of_letters {a b : A} (p q : GeometricTrace S a b)
    (h : traceLength p = traceLength q)
    (hs : ∀ i : Fin (traceLength p), letters p i = letters q (Fin.cast h i)) :
    flatRealize p = flatRealize q := by
  by_cases hp0 : traceLength p = 0
  · have hq0 : traceLength q = 0 := h.symm.trans hp0
    rw [flatRealize_zero p hp0, flatRealize_zero q hq0]
  · apply _root_.Path.ext
    funext t
    obtain ⟨i, s, ht⟩ := exists_slot (traceLength p) (Nat.pos_of_ne_zero hp0) t
    rw [← _root_.Path.extend_extends' (flatRealize p) t,
      ← _root_.Path.extend_extends' (flatRealize q) t, ht]
    have hq := flatRealize_slot q (Fin.cast h i) s
    have hq' : (flatRealize q).extend
        (((i.val : ℝ) + (s : ℝ)) / (traceLength p : ℝ)) =
          signedRealization (S := S) (letters p i) s := by
      simpa only [Fin.val_cast, ← h, ← hs i] using hq
    exact (flatRealize_slot p i s).trans hq'.symm

/-- Parenthesization has no effect on exact equal-slot realization. Unlike
the binary realization, this function factors through the full signed word. -/
theorem flatRealize_eq_of_flatWord {a b : A} (p q : GeometricTrace S a b)
    (h : flatWord p = flatWord q) : flatRealize p = flatRealize q := by
  rw [flatWord_eq_letters p, flatWord_eq_letters q] at h
  obtain ⟨hlen, hletters⟩ := Sigma.mk.inj_iff.mp h
  exact flatRealize_eq_of_letters p q hlen (letters_congr hlen hletters)

end GeometricTrace

end ComputationalPaths.Path.GeometricTopology
