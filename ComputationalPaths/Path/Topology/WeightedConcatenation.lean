import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Topology.Homotopy.Path

/-!
# Weighted concatenation invariance

The paper's flat-word realization changes the breakpoint of a path
concatenation when the two word lengths change.  Mathlib's interval-path
concatenation uses the fixed breakpoint `1 / 2`; the bridge between the two
descriptions is endpoint-preserving reparametrization.

This file formalizes that bridge.  A `WeightedSlotReparam m n` records the
endpoint-preserving reparametrization associated with two slot counts.  The
invariance theorem then proves that changing both the path representatives and
the slot counts preserves endpoint-fixed homotopy.  Concrete piecewise-linear
slot maps can be supplied as instances of this data.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open unitInterval

universe u

/-! ## Slot reparametrizations -/

/-- Endpoint-preserving reparametrization data for an `m`-by-`n` concatenation.

The slot counts are part of the data even though the homotopy argument only
uses the resulting endpoint-preserving map.  This matches the paper's
length-weighted operation: the counts choose the breakpoint, while the map
records the corresponding piecewise-linear reparametrization.
-/
structure WeightedSlotReparam (m n : Nat) where
  map : I → I
  continuous_map : Continuous map
  map_zero : map 0 = 0
  map_one : map 1 = 1

/-- A path which is endpoint-fixed homotopic to the constant path at its
source.  The endpoint equality is recorded explicitly so the statement is
well-typed even before the endpoints are identified. -/
structure EndpointNull
    {X : Type u} [TopologicalSpace X]
    {a b : X} (p : _root_.Path a b) where
  endpoint_eq : a = b
  homotopy : _root_.Path.Homotopic p
    ((_root_.Path.refl a).cast rfl endpoint_eq.symm)

/-! ## The balanced positive-slot map -/

/-- The piecewise-linear map which moves the `m`-by-`n` breakpoint to `1 / 2`.
It is the Lean counterpart of the map used in the paper. -/
noncomputable def balancedSlotMap
    (m n : Nat) (hm : 0 < m) (hn : 0 < n) : I → I :=
  fun t =>
    ⟨if (t : ℝ) ≤ (m : ℝ) / ((m + n : Nat) : ℝ) then
        ((m + n : Nat) : ℝ) / (2 * (m : ℝ)) * (t : ℝ)
      else
        1 / 2 + ((m + n : Nat) : ℝ) / (2 * (n : ℝ)) *
          ((t : ℝ) - (m : ℝ) / ((m + n : Nat) : ℝ)), by
      have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hmn' : (0 : ℝ) < ((m + n : Nat) : ℝ) := by positivity
      split_ifs with h
      · constructor
        · exact mul_nonneg (by positivity) t.2.1
        · have hbound := mul_le_mul_of_nonneg_left h (by positivity :
              0 ≤ ((m + n : Nat) : ℝ) / (2 * (m : ℝ)))
          have hhalf :
              ((m + n : Nat) : ℝ) / (2 * (m : ℝ)) *
                ((m : ℝ) / ((m + n : Nat) : ℝ)) = (1 : ℝ) / 2 := by
            field_simp
          rw [hhalf] at hbound
          linarith
      · constructor
        · have hbound :
              (m : ℝ) / ((m + n : Nat) : ℝ) ≤ (t : ℝ) := le_of_not_ge h
          have hnonneg :
              0 ≤ ((m + n : Nat) : ℝ) / (2 * (n : ℝ)) := by positivity
          have hdiff : 0 ≤
              ((m + n : Nat) : ℝ) / (2 * (n : ℝ)) *
                ((t : ℝ) - (m : ℝ) / ((m + n : Nat) : ℝ)) := by
            exact mul_nonneg hnonneg (sub_nonneg.mpr hbound)
          linarith
        · have hbound := mul_le_mul_of_nonneg_left t.2.2 (by positivity :
              0 ≤ ((m + n : Nat) : ℝ) / (2 * (n : ℝ)))
          have hratio : (m : ℝ) / ((m + n : Nat) : ℝ) ≤ 1 := by
            apply (div_le_iff₀ hmn').2
            norm_num [Nat.cast_add]
          have hbreak := mul_le_mul_of_nonneg_left hratio (by positivity :
              0 ≤ ((m + n : Nat) : ℝ) / (2 * (n : ℝ)))
          have hupper :
              1 / 2 + ((m + n : Nat) : ℝ) / (2 * (n : ℝ)) *
                  (1 - (m : ℝ) / ((m + n : Nat) : ℝ)) = 1 := by
            field_simp
            norm_num [Nat.cast_add]
            ring
          nlinarith⟩

theorem continuous_balancedSlotMap
    (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    Continuous (balancedSlotMap m n hm hn) := by
  apply Continuous.subtype_mk
  · apply Continuous.if_le
    · fun_prop
    · fun_prop
    · fun_prop
    · fun_prop
    · intro t ht
      change
        ((m + n : Nat) : ℝ) / (2 * (m : ℝ)) * (t : ℝ) =
          1 / 2 + ((m + n : Nat) : ℝ) / (2 * (n : ℝ)) *
            ((t : ℝ) - (m : ℝ) / ((m + n : Nat) : ℝ))
      rw [ht]
      field_simp
      norm_num [Nat.cast_add]

theorem balancedSlotMap_zero
    (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    balancedSlotMap m n hm hn 0 = 0 := by
  ext
  have hmn' : (0 : ℝ) < ((m + n : Nat) : ℝ) := by positivity
  have hratio0 : (0 : ℝ) ≤ (m : ℝ) / ((m + n : Nat) : ℝ) := by positivity
  norm_num [Nat.cast_add] at hratio0
  simp only [balancedSlotMap]
  split_ifs with h
  · norm_num
  · norm_num at h
    exact False.elim ((not_lt_of_ge hratio0) h)

theorem balancedSlotMap_one
    (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    balancedSlotMap m n hm hn 1 = 1 := by
  ext
  simp only [balancedSlotMap]
  split_ifs with h
  · exfalso
    have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hmn' : (0 : ℝ) < ((m + n : Nat) : ℝ) := by positivity
    have hlt : (m : ℝ) < ((m + n : Nat) : ℝ) := by
      exact_mod_cast Nat.lt_add_of_pos_right hn
    have hratio : (m : ℝ) / ((m + n : Nat) : ℝ) < 1 :=
      (div_lt_iff₀ hmn').2 (by linarith)
    norm_num [Nat.cast_add] at hratio
    norm_num at h
    exact (not_le_of_gt hratio) h
  · have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hmn' : (0 : ℝ) ≠ ((m + n : Nat) : ℝ) := by positivity
    field_simp
    norm_num [Nat.cast_add]
    ring

/-- The reparametrized concatenation associated with slot data. -/
noncomputable def weightedConcatenation
    {X : Type u} [TopologicalSpace X]
    {a b c : X} (w : WeightedSlotReparam m n)
    (hm : m = 0 → a = b) (hn : n = 0 → b = c)
    (α : _root_.Path a b) (β : _root_.Path b c) : _root_.Path a c :=
  match m, n with
  | 0, 0 => (_root_.Path.refl a).cast rfl ((hm rfl).trans (hn rfl)).symm
  | 0, _ + 1 => β.cast (hm rfl) rfl
  | _ + 1, 0 => α.cast rfl (hn rfl).symm
  | _ + 1, _ + 1 =>
      (_root_.Path.trans α β).reparam w.map w.continuous_map w.map_zero w.map_one

theorem weightedConcatenation_homotopic_to_fixed
    {X : Type u} [TopologicalSpace X]
    {a b c : X} (w : WeightedSlotReparam m n)
    (hm : m = 0 → a = b) (hn : n = 0 → b = c)
    (α : _root_.Path a b) (β : _root_.Path b c)
    (hα₀ : m = 0 → EndpointNull α)
    (hβ₀ : n = 0 → EndpointNull β) :
    _root_.Path.Homotopic
      (weightedConcatenation w hm hn α β)
      (_root_.Path.trans α β) := by
  cases m with
  | zero =>
      cases n with
      | zero =>
          rcases hα₀ rfl with ⟨hab, hα₀⟩
          cases hab
          rcases hβ₀ rfl with ⟨hbc, hβ₀⟩
          cases hbc
          have hα₀' : _root_.Path.Homotopic α (_root_.Path.refl a) := by
            simpa using hα₀
          have hβ₀' : _root_.Path.Homotopic β (_root_.Path.refl a) := by
            simpa using hβ₀
          have hcomp : _root_.Path.Homotopic
              (_root_.Path.trans α β)
              (_root_.Path.trans (_root_.Path.refl a) (_root_.Path.refl a)) :=
            hα₀'.hcomp hβ₀'
          have hunit : _root_.Path.Homotopic
              (_root_.Path.trans (_root_.Path.refl a) (_root_.Path.refl a))
              (_root_.Path.refl a) :=
            ⟨_root_.Path.Homotopy.reflTrans (_root_.Path.refl a)⟩
          simpa [weightedConcatenation] using hunit.symm.trans hcomp.symm
      | succ n =>
          rcases hα₀ rfl with ⟨hab, hα₀⟩
          cases hab
          have hα₀' : _root_.Path.Homotopic α (_root_.Path.refl a) := by
            simpa using hα₀
          have hcomp : _root_.Path.Homotopic
              (_root_.Path.trans α β)
              (_root_.Path.trans (_root_.Path.refl a) β) :=
            hα₀'.hcomp (_root_.Path.Homotopic.refl β)
          have hunit : _root_.Path.Homotopic
              (_root_.Path.trans (_root_.Path.refl a) β) β :=
            ⟨_root_.Path.Homotopy.reflTrans β⟩
          simpa [weightedConcatenation] using hunit.symm.trans hcomp.symm
  | succ m =>
      cases n with
      | zero =>
          rcases hβ₀ rfl with ⟨hbc, hβ₀⟩
          cases hbc
          have hβ₀' : _root_.Path.Homotopic β (_root_.Path.refl b) := by
            simpa using hβ₀
          have hcomp : _root_.Path.Homotopic
              (_root_.Path.trans α β)
              (_root_.Path.trans α (_root_.Path.refl b)) :=
            (_root_.Path.Homotopic.refl α).hcomp hβ₀'
          have hunit : _root_.Path.Homotopic
              (_root_.Path.trans α (_root_.Path.refl b)) α :=
            ⟨_root_.Path.Homotopy.transRefl α⟩
          simpa [weightedConcatenation] using hunit.symm.trans hcomp.symm
      | succ n =>
          exact ⟨(_root_.Path.Homotopy.reparam
            (_root_.Path.trans α β) w.map w.continuous_map w.map_zero w.map_one).symm⟩

/-! ## Invariance -/

/-- Weighted concatenation is invariant under endpoint-fixed homotopy of both
factors and under changing the slot reparametrization. -/
theorem weightedConcatenationInvariant
    {X : Type u} [TopologicalSpace X]
    {a b c : X}
    {m n m' n' : Nat}
    {w : WeightedSlotReparam m n}
    {w' : WeightedSlotReparam m' n'}
    {α α' : _root_.Path a b} {β β' : _root_.Path b c}
    (hα : _root_.Path.Homotopic α α')
    (hβ : _root_.Path.Homotopic β β')
    (hα₀ : m = 0 → EndpointNull α)
    (hβ₀ : n = 0 → EndpointNull β)
    (hα'₀ : m' = 0 → EndpointNull α')
    (hβ'₀ : n' = 0 → EndpointNull β') :
    _root_.Path.Homotopic
      (weightedConcatenation w (fun h => (hα₀ h).endpoint_eq)
        (fun h => (hβ₀ h).endpoint_eq) α β)
      (weightedConcatenation w' (fun h => (hα'₀ h).endpoint_eq)
        (fun h => (hβ'₀ h).endpoint_eq) α' β') := by
  exact
    (weightedConcatenation_homotopic_to_fixed w
      (fun h => (hα₀ h).endpoint_eq)
      (fun h => (hβ₀ h).endpoint_eq) α β hα₀ hβ₀).trans
      ((hα.hcomp hβ).trans
        (weightedConcatenation_homotopic_to_fixed w'
          (fun h => (hα'₀ h).endpoint_eq)
          (fun h => (hβ'₀ h).endpoint_eq) α' β' hα'₀ hβ'₀).symm)

/-- The concrete positive-slot reparametrization used by the flat-word model. -/
noncomputable def balancedSlotReparam
    (m n : Nat) (hm : 0 < m) (hn : 0 < n) : WeightedSlotReparam m n where
  map := balancedSlotMap m n hm hn
  continuous_map := continuous_balancedSlotMap m n hm hn
  map_zero := balancedSlotMap_zero m n hm hn
  map_one := balancedSlotMap_one m n hm hn

theorem weightedConcatenationInvariant_balanced
    {X : Type u} [TopologicalSpace X]
    {a b c : X}
    {m n m' n' : Nat}
    {α α' : _root_.Path a b} {β β' : _root_.Path b c}
    (hm : 0 < m) (hn : 0 < n) (hm' : 0 < m') (hn' : 0 < n')
    (hα : _root_.Path.Homotopic α α')
    (hβ : _root_.Path.Homotopic β β') :
    _root_.Path.Homotopic
      (weightedConcatenation (balancedSlotReparam m n hm hn)
        (by omega) (by omega) α β)
      (weightedConcatenation (balancedSlotReparam m' n' hm' hn')
        (by omega) (by omega) α' β') := by
  apply weightedConcatenationInvariant hα hβ
  · intro h
    exact False.elim (by omega)
  · intro h
    exact False.elim (by omega)
  · intro h
    exact False.elim (by omega)
  · intro h
    exact False.elim (by omega)

end GeometricTopology
end Path
end ComputationalPaths
