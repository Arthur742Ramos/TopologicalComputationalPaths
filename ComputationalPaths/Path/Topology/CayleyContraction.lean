import ComputationalPaths.Path.Topology.CayleyFlatWalk
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# A constructed contraction of the geometric Cayley tree

The reduced-word root paths have equal edge durations. On each closed edge,
contraction travels along the root path of the farther endpoint, with its
parameter proportional to distance from the root. Exact prefix identities
identify the formulas at both endpoints. Joint continuity descends through
the actual closed-edge quotient; simple connectivity is a consequence.
-/

namespace ComputationalPaths.Path.GeometricTopology.CayleyContraction

open CayleyTreeGeometry CayleyFlatWalk RoseReducedWords Topology
open scoped unitInterval

noncomputable section

def edgeFormula (g : G) (i : Label) (τ : unitInterval) (t : ℝ) : Tree :=
  if FreeGroup.norm g < FreeGroup.norm (g * FreeGroup.of i) then
    (rootPath (g * FreeGroup.of i)).extend
      ((1 - (τ : ℝ)) * ((FreeGroup.norm g : ℝ) + t) /
        ((FreeGroup.norm g + 1 : ℕ) : ℝ))
  else
    (rootPath g).extend
      ((1 - (τ : ℝ)) * ((FreeGroup.norm (g * FreeGroup.of i) : ℝ) + 1 - t) /
        ((FreeGroup.norm (g * FreeGroup.of i) + 1 : ℕ) : ℝ))

theorem edgeFormula_zero (g : G) (i : Label) (τ : unitInterval) :
    edgeFormula g i τ 0 = rootPath g (unitInterval.symm τ) := by
  unfold edgeFormula
  split_ifs with h
  · have he : (1 - (τ : ℝ)) * ((FreeGroup.norm g : ℝ) + 0) /
        ((FreeGroup.norm g + 1 : ℕ) : ℝ) =
        (FreeGroup.norm g : ℝ) / ((FreeGroup.norm g + 1 : ℕ) : ℝ) *
          (unitInterval.symm τ : ℝ) := by
      simp only [unitInterval.coe_symm_eq]
      ring
    rw [he, outward_prefix g i h]
  · have he : (1 - (τ : ℝ)) * ((FreeGroup.norm (g * FreeGroup.of i) : ℝ) + 1 - 0) /
        ((FreeGroup.norm (g * FreeGroup.of i) + 1 : ℕ) : ℝ) =
        (unitInterval.symm τ : ℝ) := by
      simp only [unitInterval.coe_symm_eq, Nat.cast_add, Nat.cast_one]
      field_simp [show (FreeGroup.norm (g * FreeGroup.of i) : ℝ) + 1 ≠ 0 from by positivity]
      ring
    rw [he, _root_.Path.extend_extends']

theorem edgeFormula_one (g : G) (i : Label) (τ : unitInterval) :
    edgeFormula g i τ 1 = rootPath (g * FreeGroup.of i) (unitInterval.symm τ) := by
  unfold edgeFormula
  split_ifs with h
  · have he : (1 - (τ : ℝ)) * ((FreeGroup.norm g : ℝ) + 1) /
        ((FreeGroup.norm g + 1 : ℕ) : ℝ) = (unitInterval.symm τ : ℝ) := by
      simp only [unitInterval.coe_symm_eq, Nat.cast_add, Nat.cast_one]
      field_simp [show (FreeGroup.norm g : ℝ) + 1 ≠ 0 from by positivity]
    rw [he, _root_.Path.extend_extends']
  · have hi := (CayleyReducedPrefix.norm_lt_or_lt g i).resolve_left h
    have he : (1 - (τ : ℝ)) * ((FreeGroup.norm (g * FreeGroup.of i) : ℝ) + 1 - 1) /
        ((FreeGroup.norm (g * FreeGroup.of i) + 1 : ℕ) : ℝ) =
        (FreeGroup.norm (g * FreeGroup.of i) : ℝ) /
          ((FreeGroup.norm (g * FreeGroup.of i) + 1 : ℕ) : ℝ) *
          (unitInterval.symm τ : ℝ) := by
      simp only [unitInterval.coe_symm_eq]
      ring
    rw [he, inward_prefix g i hi]

def contract (τ : unitInterval) : Tree → Tree
  | .vertex g => rootPath g (unitInterval.symm τ)
  | .inner g i t => edgeFormula g i τ (t : ℝ)

theorem contract_key (τ : unitInterval) (r : Raw) :
    contract τ (key r) = edgeFormula r.1.1 r.1.2 τ (r.2 : ℝ) := by
  unfold key
  split_ifs with h0 h1
  · simp only [contract, h0, edgeFormula_zero]
  · simp only [contract, h1, edgeFormula_one]
  · rfl

theorem continuous_edgeFormula (g : G) (i : Label) :
    Continuous (fun p : unitInterval × unitInterval => edgeFormula g i p.1 (p.2 : ℝ)) := by
  unfold edgeFormula
  split_ifs
  · exact (rootPath (g * FreeGroup.of i)).extend.continuous.comp (by fun_prop)
  · exact (rootPath g).extend.continuous.comp (by fun_prop)

theorem continuous_contract :
    Continuous (fun p : unitInterval × Tree => contract p.1 p.2) := by
  apply key_isQuotientMap.continuous_lift_prod_right
  have hf : Continuous (fun p : (G × Label) × (unitInterval × unitInterval) =>
      edgeFormula p.1.1 p.1.2 p.2.1 (p.2.2 : ℝ)) :=
    continuous_prod_of_discrete_left.mpr (fun e => continuous_edgeFormula e.1 e.2)
  have hm : Continuous (fun p : unitInterval × Raw => (p.2.1, (p.1, p.2.2))) := by
    fun_prop
  simpa only [contract_key, Function.comp_def] using hf.comp hm

theorem contract_zero (z : Tree) : contract 0 z = z := by
  cases z with
  | vertex g => simp [contract]
  | inner g i t =>
    let u : unitInterval := ⟨t, le_of_lt t.2.1, le_of_lt t.2.2⟩
    have hu : edge g i u = Tree.inner g i t := key_interior g i t
    change edgeFormula g i 0 (t : ℝ) = _
    unfold edgeFormula
    split_ifs with h
    · simpa only [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero, one_mul] using
        (outward_last_edge g i h u).trans hu
    · have hi := (CayleyReducedPrefix.norm_lt_or_lt g i).resolve_left h
      have he := inward_last_edge g i hi (unitInterval.symm u)
      rw [unitInterval.symm_symm] at he
      have ht : (FreeGroup.norm (g * FreeGroup.of i) : ℝ) +
          (unitInterval.symm u : ℝ) =
          (FreeGroup.norm (g * FreeGroup.of i) : ℝ) + 1 - (t : ℝ) := by
        simp only [unitInterval.coe_symm_eq, u]
        ring
      rw [ht] at he
      simpa only [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero, one_mul] using he.trans hu

theorem contract_one (z : Tree) : contract 1 z = Tree.vertex 1 := by
  cases z with
  | vertex g => simp [contract]
  | inner g i t => simp [contract, edgeFormula]

theorem contract_root (τ : unitInterval) : contract τ (Tree.vertex 1) = Tree.vertex 1 := by
  exact rootPath_one _

def homotopy : (ContinuousMap.id Tree).Homotopy
    (ContinuousMap.const Tree (Tree.vertex 1)) where
  toFun p := contract p.1 p.2
  continuous_toFun := continuous_contract
  map_zero_left := contract_zero
  map_one_left := contract_one

theorem contractible : ContractibleSpace Tree :=
  (contractible_iff_id_nullhomotopic Tree).mpr ⟨Tree.vertex 1, ⟨homotopy⟩⟩

theorem simplyConnected : SimplyConnectedSpace Tree := by
  letI := contractible
  infer_instance

end
end ComputationalPaths.Path.GeometricTopology.CayleyContraction
