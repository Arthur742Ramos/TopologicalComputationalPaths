import ComputationalPaths.Path.Topology.EndpointVaryingLadder
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Reparametrization toward endpoint absorption

The maps below squeeze a path into the middle of the interval and leave
constant tails. Every compact-open neighborhood of a path contains such a
reparametrization with positive tail length. This is the first half of the
endpoint absorption argument for the global path-class projection.
-/

namespace ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup

open Set Topology
open scoped unitInterval ContinuousMap

/-- A path parameter map with short constant tails. At parameter zero it is
the identity. -/
noncomputable def squeeze (epsilon t : I) : I :=
  Set.projIcc (0 : ℝ) 1 zero_le_one
    ((1 + 2 * (epsilon : ℝ)) * (t : ℝ) - (epsilon : ℝ))

private theorem continuous_squeeze_uncurry :
    Continuous (fun p : I × I => squeeze p.1 p.2) := by
  unfold squeeze
  fun_prop

theorem squeeze_at_zero (t : I) : squeeze 0 t = t := by
  simp [squeeze, Set.projIcc_of_mem, t.property]

theorem squeeze_start (epsilon : I) : squeeze epsilon 0 = 0 := by
  rw [squeeze]
  apply projIcc_eq_zero.mpr
  simp only [Set.Icc.coe_zero, mul_zero, zero_sub]
  exact neg_nonpos.mpr epsilon.property.1

theorem squeeze_end (epsilon : I) : squeeze epsilon 1 = 1 := by
  rw [squeeze]
  apply projIcc_eq_one.mpr
  simp only [Set.Icc.coe_one, mul_one]
  have he := epsilon.property.1
  linarith

/-- The squeeze map as a compact-open continuous map. -/
noncomputable def squeezeCM (epsilon : I) : C(I, I) :=
  ⟨squeeze epsilon, continuous_squeeze_uncurry.comp
    (continuous_const.prodMk continuous_id)⟩

theorem continuous_squeezeCM : Continuous squeezeCM := by
  apply ContinuousMap.continuous_of_continuous_uncurry squeezeCM
  exact continuous_squeeze_uncurry

theorem squeezeCM_zero : squeezeCM 0 = ContinuousMap.id I := by
  ext t
  exact congrArg Subtype.val (squeeze_at_zero t)

private theorem continuous_squeezed_path {X : Type*} [TopologicalSpace X]
    (gamma : C(I, X)) :
    Continuous (fun epsilon : I => gamma.comp (squeezeCM epsilon)) := by
  exact (ContinuousMap.continuous_postcomp gamma).comp continuous_squeezeCM

private noncomputable def epsilonSeq (n : ℕ) : I :=
  ⟨(1 : ℝ) / ((n : ℝ) + 1), by
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity)).2
      nlinarith [Nat.cast_nonneg (α := ℝ) n]⟩

private theorem epsilonSeq_pos (n : ℕ) : (0 : I) < epsilonSeq n := by
  change (0 : ℝ) < (1 : ℝ) / ((n : ℝ) + 1)
  positivity

private theorem epsilonSeq_tendsto_zero :
    Filter.Tendsto epsilonSeq Filter.atTop (𝓝 (0 : I)) := by
  apply tendsto_subtype_rng.mpr
  simpa [epsilonSeq] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Every compact-open neighborhood contains a positive-tail
reparametrization of its center path. -/
theorem exists_positive_squeeze_in_open
    {X : Type*} [TopologicalSpace X]
    (gamma : C(I, X)) {W : Set C(I, X)}
    (hW : IsOpen W) (hgamma : gamma ∈ W) :
    ∃ epsilon : I, 0 < epsilon ∧ gamma.comp (squeezeCM epsilon) ∈ W := by
  have htend : Filter.Tendsto
      (fun n : ℕ => gamma.comp (squeezeCM (epsilonSeq n)))
      Filter.atTop (𝓝 gamma) := by
    have h := ((continuous_squeezed_path gamma).continuousAt.tendsto).comp
      epsilonSeq_tendsto_zero
    simpa only [Function.comp_def, squeezeCM_zero, ContinuousMap.comp_id] using h
  have hevent := htend.eventually (hW.mem_nhds hgamma)
  obtain ⟨n, hn⟩ := hevent.exists
  exact ⟨epsilonSeq n, epsilonSeq_pos n, hn⟩

end ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup
