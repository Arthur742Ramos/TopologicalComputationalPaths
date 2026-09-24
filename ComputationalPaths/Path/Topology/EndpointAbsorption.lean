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


open Set Topology
open scoped unitInterval ContinuousMap

private noncomputable def whiskerScale (epsilon : I) : ℝ :=
  1 + 2 * (epsilon : ℝ)

private noncomputable def whiskerCut0 (epsilon : I) : ℝ :=
  (epsilon : ℝ) / whiskerScale epsilon

private noncomputable def whiskerCut1 (epsilon : I) : ℝ :=
  (1 + (epsilon : ℝ)) / whiskerScale epsilon

private theorem whisker_scale_pos (epsilon : I) :
    0 < whiskerScale epsilon := by
  dsimp [whiskerScale]
  have he := epsilon.property.1
  linarith

private theorem whisker_cuts (epsilon : I) (he : (0 : I) < epsilon) :
    0 < whiskerCut0 epsilon ∧
      whiskerCut0 epsilon < whiskerCut1 epsilon ∧
      whiskerCut1 epsilon < 1 := by
  have hreal : (0 : ℝ) < epsilon := he
  have hd := whisker_scale_pos epsilon
  dsimp [whiskerCut0, whiskerCut1, whiskerScale] at *
  constructor
  · positivity
  constructor
  · apply div_lt_div_of_pos_right (by linarith) hd
  · apply (div_lt_iff₀ hd).2
    nlinarith

private theorem whisker_cut0_left (epsilon : I) (he : (0 : I) < epsilon) :
    whiskerScale epsilon / (epsilon : ℝ) * whiskerCut0 epsilon = 1 := by
  have hreal : (0 : ℝ) < epsilon := he
  have hd := whisker_scale_pos epsilon
  dsimp [whiskerCut0]
  field_simp

private theorem whisker_cut0_middle (epsilon : I) :
    whiskerScale epsilon * whiskerCut0 epsilon - (epsilon : ℝ) = 0 := by
  have hd := whisker_scale_pos epsilon
  dsimp [whiskerCut0]
  field_simp
  ring

private theorem whisker_cut1_middle (epsilon : I) :
    whiskerScale epsilon * whiskerCut1 epsilon - (epsilon : ℝ) = 1 := by
  have hd := whisker_scale_pos epsilon
  dsimp [whiskerCut1]
  field_simp
  ring

private theorem whisker_middle_span (epsilon : I) :
    whiskerScale epsilon *
      (whiskerCut1 epsilon - whiskerCut0 epsilon) = 1 := by
  calc
    _ = (whiskerScale epsilon * whiskerCut1 epsilon - (epsilon : ℝ)) -
        (whiskerScale epsilon * whiskerCut0 epsilon - (epsilon : ℝ)) := by ring
    _ = 1 := by rw [whisker_cut1_middle, whisker_cut0_middle]; ring

private theorem whisker_cut1_right (epsilon : I) :
    whiskerScale epsilon / (epsilon : ℝ) *
      (whiskerCut1 epsilon - whiskerCut1 epsilon) = 0 := by
  simp

private theorem whisker_end_right (epsilon : I) (he : (0 : I) < epsilon) :
    whiskerScale epsilon / (epsilon : ℝ) *
      (1 - whiskerCut1 epsilon) = 1 := by
  have hreal : (0 : ℝ) < epsilon := he
  have hd := whisker_scale_pos epsilon
  dsimp [whiskerCut1, whiskerScale] at *
  field_simp
  ring

private noncomputable def whiskerFun
    {X : Type*} [TopologicalSpace X]
    (epsilon : I) (_he : (0 : I) < epsilon)
    {a' a b b' : X} (alpha : _root_.Path a' a)
    (gamma : _root_.Path a b) (beta : _root_.Path b b') :
    ℝ → X := fun t =>
  if t ≤ whiskerCut0 epsilon then
    alpha.extend (whiskerScale epsilon / (epsilon : ℝ) * t)
  else if t ≤ whiskerCut1 epsilon then
    gamma.extend (whiskerScale epsilon * t - (epsilon : ℝ))
  else
    beta.extend (whiskerScale epsilon / (epsilon : ℝ) *
      (t - whiskerCut1 epsilon))

private theorem continuous_whiskerFun
    {X : Type*} [TopologicalSpace X]
    (epsilon : I) (he : (0 : I) < epsilon)
    {a' a b b' : X} (alpha : _root_.Path a' a)
    (gamma : _root_.Path a b) (beta : _root_.Path b b') :
    Continuous (whiskerFun epsilon he alpha gamma beta) := by
  let middleRight : ℝ → X := fun t =>
    if t ≤ whiskerCut1 epsilon then
      gamma.extend (whiskerScale epsilon * t - (epsilon : ℝ))
    else beta.extend (whiskerScale epsilon / (epsilon : ℝ) *
      (t - whiskerCut1 epsilon))
  have hMiddleRight : Continuous middleRight := by
    apply Continuous.if_le
    · exact gamma.continuous_extend.comp (by fun_prop)
    · exact beta.continuous_extend.comp (by fun_prop)
    · exact continuous_id
    · exact continuous_const
    · intro t ht
      subst t
      rw [whisker_cut1_middle, whisker_cut1_right,
        gamma.extend_one, beta.extend_zero]
  change Continuous (fun t : ℝ =>
    if t ≤ whiskerCut0 epsilon then
      alpha.extend (whiskerScale epsilon / (epsilon : ℝ) * t)
    else middleRight t)
  apply Continuous.if_le
  · exact alpha.continuous_extend.comp (by fun_prop)
  · exact hMiddleRight
  · exact continuous_id
  · exact continuous_const
  · intro t ht
    subst t
    have hcut := (whisker_cuts epsilon he).2.1.le
    dsimp [middleRight]
    rw [if_pos hcut, whisker_cut0_left epsilon he,
      whisker_cut0_middle, alpha.extend_one, gamma.extend_zero]

private theorem whiskerFun_start
    {X : Type*} [TopologicalSpace X]
    (epsilon : I) (he : (0 : I) < epsilon)
    {a' a b b' : X} (alpha : _root_.Path a' a)
    (gamma : _root_.Path a b) (beta : _root_.Path b b') :
    whiskerFun epsilon he alpha gamma beta 0 = a' := by
  have hcut := (whisker_cuts epsilon he).1.le
  simp [whiskerFun, hcut, alpha.extend_zero]

private theorem whiskerFun_end
    {X : Type*} [TopologicalSpace X]
    (epsilon : I) (he : (0 : I) < epsilon)
    {a' a b b' : X} (alpha : _root_.Path a' a)
    (gamma : _root_.Path a b) (beta : _root_.Path b b') :
    whiskerFun epsilon he alpha gamma beta 1 = b' := by
  have hc0 : ¬ (1 : ℝ) ≤ whiskerCut0 epsilon := by
    have h := whisker_cuts epsilon he
    linarith
  have hc1 : ¬ (1 : ℝ) ≤ whiskerCut1 epsilon := by
    have h := whisker_cuts epsilon he
    linarith
  simp [whiskerFun, hc0, hc1, whisker_end_right epsilon he,
    beta.extend_one]

noncomputable def whiskerPath
    {X : Type*} [TopologicalSpace X]
    (epsilon : I) (he : (0 : I) < epsilon)
    {a' a b b' : X} (alpha : _root_.Path a' a)
    (gamma : _root_.Path a b) (beta : _root_.Path b b') :
    _root_.Path a' b' :=
  _root_.Path.ofLine
    (continuous_whiskerFun epsilon he alpha gamma beta).continuousOn
    (whiskerFun_start epsilon he alpha gamma beta)
    (whiskerFun_end epsilon he alpha gamma beta)

private theorem whiskerPath_apply
    {X : Type*} [TopologicalSpace X]
    (epsilon : I) (he : (0 : I) < epsilon)
    {a' a b b' : X} (alpha : _root_.Path a' a)
    (gamma : _root_.Path a b) (beta : _root_.Path b b') (t : I) :
    whiskerPath epsilon he alpha gamma beta t =
      whiskerFun epsilon he alpha gamma beta t := rfl

private theorem whiskerFun_refl_eq_extend
    {X : Type*} [TopologicalSpace X]
    (epsilon : I) (he : (0 : I) < epsilon)
    {a b : X} (gamma : _root_.Path a b) (t : ℝ) :
    whiskerFun epsilon he (_root_.Path.refl a) gamma
      (_root_.Path.refl b) t =
      gamma.extend (whiskerScale epsilon * t - (epsilon : ℝ)) := by
  have hd := whisker_scale_pos epsilon
  by_cases h0 : t ≤ whiskerCut0 epsilon
  · have hmid : whiskerScale epsilon * t - (epsilon : ℝ) ≤ 0 := by
      have hmul := mul_le_mul_of_nonneg_left h0 hd.le
      linarith [whisker_cut0_middle epsilon]
    simp [whiskerFun, h0, _root_.Path.refl_extend,
      gamma.extend_of_le_zero hmid]
  · by_cases h1 : t ≤ whiskerCut1 epsilon
    · simp [whiskerFun, h0, h1]
    · have hmid : 1 ≤ whiskerScale epsilon * t - (epsilon : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge h1)) hd.le
        linarith [whisker_cut1_middle epsilon]
      simp [whiskerFun, h0, h1, _root_.Path.refl_extend,
        gamma.extend_of_one_le hmid]

private theorem whiskerPath_refl
    {X : Type*} [TopologicalSpace X]
    (epsilon : I) (he : (0 : I) < epsilon)
    {a b : X} (gamma : _root_.Path a b) :
    (whiskerPath epsilon he (_root_.Path.refl a) gamma
      (_root_.Path.refl b)).toContinuousMap =
      gamma.toContinuousMap.comp (squeezeCM epsilon) := by
  ext t
  change whiskerFun epsilon he (_root_.Path.refl a) gamma
    (_root_.Path.refl b) t = gamma (squeeze epsilon t)
  rw [whiskerFun_refl_eq_extend]
  rfl

private theorem exists_whisker_neighborhoods
    {X : Type*} [TopologicalSpace X]
    {a b : X} (gamma : _root_.Path a b)
    (epsilon : I) (he : (0 : I) < epsilon)
    {W : Set C(I, X)} (hW : IsOpen W)
    (hsqueezed : gamma.toContinuousMap.comp (squeezeCM epsilon) ∈ W) :
    ∃ U0 U1 : Set X, IsOpen U0 ∧ a ∈ U0 ∧ IsOpen U1 ∧ b ∈ U1 ∧
      ∀ {a' b' : X} (alpha : _root_.Path a' a)
        (beta : _root_.Path b b'),
        range alpha ⊆ U0 → range beta ⊆ U1 →
          (whiskerPath epsilon he alpha gamma beta).toContinuousMap ∈ W := by
  obtain ⟨S, hSf, hSdata, hSsub⟩ :=
    ContinuousMap.mem_nhds_iff.mp (hW.mem_nhds hsqueezed)
  let U0 : Set X := ⋂ KU ∈ S, ⋂ (_ : a ∈ KU.2), KU.2
  let U1 : Set X := ⋂ KU ∈ S, ⋂ (_ : b ∈ KU.2), KU.2
  have hU0open : IsOpen U0 := by
    dsimp [U0]
    apply hSf.isOpen_biInter
    intro KU hKU
    by_cases haU : a ∈ KU.2
    · simpa [haU] using (hSdata KU.1 KU.2 hKU).2.1
    · simp [haU]
  have hU1open : IsOpen U1 := by
    dsimp [U1]
    apply hSf.isOpen_biInter
    intro KU hKU
    by_cases hbU : b ∈ KU.2
    · simpa [hbU] using (hSdata KU.1 KU.2 hKU).2.1
    · simp [hbU]
  have haU0 : a ∈ U0 := by simp [U0]
  have hbU1 : b ∈ U1 := by simp [U1]
  refine ⟨U0, U1, hU0open, haU0, hU1open, hbU1, ?_⟩
  intro a' b' alpha beta halpha hbeta
  apply hSsub
  intro K U hKU t ht
  have hbase : (gamma.toContinuousMap.comp (squeezeCM epsilon)) t ∈ U :=
    (hSdata K U hKU).2.2 ht
  have hd := whisker_scale_pos epsilon
  by_cases h0 : (t : ℝ) ≤ whiskerCut0 epsilon
  · have hmid : whiskerScale epsilon * (t : ℝ) - (epsilon : ℝ) ≤ 0 := by
      have hmul := mul_le_mul_of_nonneg_left h0 hd.le
      linarith [whisker_cut0_middle epsilon]
    have haU : a ∈ U := by
      have heq : (gamma.toContinuousMap.comp (squeezeCM epsilon)) t = a := by
        calc
          _ = gamma.extend (whiskerScale epsilon * (t : ℝ) - (epsilon : ℝ)) := rfl
          _ = a := gamma.extend_of_le_zero hmid
      simpa [heq] using hbase
    have hmem : alpha.extend
        (whiskerScale epsilon / (epsilon : ℝ) * (t : ℝ)) ∈ U0 := by
      apply halpha
      rw [← alpha.extend_range]
      exact ⟨_, rfl⟩
    have hsub : U0 ⊆ U := by
      intro z hz
      simp only [U0, Set.mem_iInter] at hz
      exact hz (K, U) hKU haU
    change whiskerFun epsilon he alpha gamma beta t ∈ U
    simpa [whiskerFun, h0] using hsub hmem
  · by_cases h1 : (t : ℝ) ≤ whiskerCut1 epsilon
    · change whiskerFun epsilon he alpha gamma beta t ∈ U
      change gamma.extend (whiskerScale epsilon * (t : ℝ) - (epsilon : ℝ)) ∈ U
        at hbase
      simpa [whiskerFun, h0, h1] using hbase
    · have hmid : 1 ≤ whiskerScale epsilon * (t : ℝ) - (epsilon : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left
          (le_of_lt (lt_of_not_ge h1)) hd.le
        linarith [whisker_cut1_middle epsilon]
      have hbU : b ∈ U := by
        have heq : (gamma.toContinuousMap.comp (squeezeCM epsilon)) t = b := by
          calc
            _ = gamma.extend (whiskerScale epsilon * (t : ℝ) - (epsilon : ℝ)) := rfl
            _ = b := gamma.extend_of_one_le hmid
        simpa [heq] using hbase
      have hmem : beta.extend (whiskerScale epsilon / (epsilon : ℝ) *
          ((t : ℝ) - whiskerCut1 epsilon)) ∈ U1 := by
        apply hbeta
        rw [← beta.extend_range]
        exact ⟨_, rfl⟩
      have hsub : U1 ⊆ U := by
        intro z hz
        simp only [U1, Set.mem_iInter] at hz
        exact hz (K, U) hKU hbU
      change whiskerFun epsilon he alpha gamma beta t ∈ U
      simpa [whiskerFun, h0, h1] using hsub hmem

private noncomputable def whiskerReparamReal
    (epsilon : I) (t : ℝ) : ℝ :=
  if t ≤ 1 / 2 then 2 * whiskerCut0 epsilon * t
  else if t ≤ 3 / 4 then
    whiskerCut0 epsilon + 4 * (whiskerCut1 epsilon - whiskerCut0 epsilon) *
      (t - 1 / 2)
  else
    whiskerCut1 epsilon + 4 * (1 - whiskerCut1 epsilon) * (t - 3 / 4)

private theorem whiskerReparamReal_continuous (epsilon : I) :
    Continuous (whiskerReparamReal epsilon) := by
  have hright : Continuous (fun t : ℝ =>
      if t ≤ 3 / 4 then
        whiskerCut0 epsilon + 4 * (whiskerCut1 epsilon - whiskerCut0 epsilon) *
          (t - 1 / 2)
      else whiskerCut1 epsilon + 4 * (1 - whiskerCut1 epsilon) * (t - 3 / 4)) := by
    apply Continuous.if_le
    · fun_prop
    · fun_prop
    · exact continuous_id
    · exact continuous_const
    · intro t ht
      subst t
      ring
  change Continuous (fun t : ℝ =>
    if t ≤ 1 / 2 then 2 * whiskerCut0 epsilon * t
    else if t ≤ 3 / 4 then
      whiskerCut0 epsilon + 4 * (whiskerCut1 epsilon - whiskerCut0 epsilon) *
        (t - 1 / 2)
    else whiskerCut1 epsilon + 4 * (1 - whiskerCut1 epsilon) * (t - 3 / 4))
  apply Continuous.if_le
  · fun_prop
  · exact hright
  · exact continuous_id
  · exact continuous_const
  · intro t ht
    subst t
    norm_num
    ring

private theorem whiskerReparamReal_mem
    (epsilon : I) (he : (0 : I) < epsilon) (t : I) :
    whiskerReparamReal epsilon t ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hc0, hc01, hc1⟩ := whisker_cuts epsilon he
  have ht0 : (0 : ℝ) ≤ t := t.property.1
  have ht1 : (t : ℝ) ≤ 1 := t.property.2
  dsimp [whiskerReparamReal]
  split_ifs with h0 h1
  · constructor <;> nlinarith
  · constructor <;> nlinarith
  · constructor <;> nlinarith

private noncomputable def whiskerReparam
    (epsilon : I) (he : (0 : I) < epsilon) : I → I :=
  fun t => ⟨whiskerReparamReal epsilon t,
    whiskerReparamReal_mem epsilon he t⟩

private theorem whiskerReparam_continuous
    (epsilon : I) (he : (0 : I) < epsilon) :
    Continuous (whiskerReparam epsilon he) :=
  (whiskerReparamReal_continuous epsilon).comp continuous_subtype_val |>.subtype_mk _

private theorem whiskerReparam_zero
    (epsilon : I) (he : (0 : I) < epsilon) :
    whiskerReparam epsilon he 0 = 0 := by
  apply Subtype.ext
  norm_num [whiskerReparam, whiskerReparamReal]

private theorem whiskerReparam_one
    (epsilon : I) (he : (0 : I) < epsilon) :
    whiskerReparam epsilon he 1 = 1 := by
  apply Subtype.ext
  norm_num [whiskerReparam, whiskerReparamReal]
  ring

private theorem whiskerPath_reparam
    {X : Type*} [TopologicalSpace X]
    (epsilon : I) (he : (0 : I) < epsilon)
    {a' a b b' : X} (alpha : _root_.Path a' a)
    (gamma : _root_.Path a b) (beta : _root_.Path b b') :
    (whiskerPath epsilon he alpha gamma beta).reparam
      (whiskerReparam epsilon he)
      (whiskerReparam_continuous epsilon he)
      (whiskerReparam_zero epsilon he)
      (whiskerReparam_one epsilon he) =
      alpha.trans (gamma.trans beta) := by
  ext t
  change whiskerFun epsilon he alpha gamma beta (whiskerReparam epsilon he t) =
    (alpha.trans (gamma.trans beta)) t
  by_cases h0 : (t : ℝ) ≤ 1 / 2
  · rw [_root_.Path.trans_apply, dif_pos h0]
    have hp : (whiskerReparam epsilon he t : ℝ) =
        2 * whiskerCut0 epsilon * (t : ℝ) := by
      change (if (t : ℝ) ≤ 1 / 2 then 2 * whiskerCut0 epsilon * (t : ℝ)
        else if (t : ℝ) ≤ 3 / 4 then
          whiskerCut0 epsilon + 4 * (whiskerCut1 epsilon - whiskerCut0 epsilon) *
            ((t : ℝ) - 1 / 2)
        else whiskerCut1 epsilon + 4 * (1 - whiskerCut1 epsilon) *
          ((t : ℝ) - 3 / 4)) = _
      rw [if_pos h0]
    have hc := (whisker_cuts epsilon he).1
    have hple : (whiskerReparam epsilon he t : ℝ) ≤ whiskerCut0 epsilon := by
      rw [hp]
      nlinarith [mul_nonneg (le_of_lt hc)
        (show 0 ≤ (1 / 2 : ℝ) - (t : ℝ) by linarith)]
    have heq : whiskerFun epsilon he alpha gamma beta
        (whiskerReparam epsilon he t) = alpha.extend (2 * (t : ℝ)) := by
      unfold whiskerFun
      rw [if_pos hple, hp]
      congr 1
      calc
        whiskerScale epsilon / (epsilon : ℝ) *
            (2 * whiskerCut0 epsilon * (t : ℝ)) =
            (whiskerScale epsilon / (epsilon : ℝ) * whiskerCut0 epsilon) *
              (2 * (t : ℝ)) := by ring
        _ = 2 * (t : ℝ) := by rw [whisker_cut0_left epsilon he]; ring
    rw [heq, _root_.Path.extend_apply alpha]
  · by_cases h1 : (t : ℝ) ≤ 3 / 4
    · rw [_root_.Path.trans_apply, dif_neg h0]
      rw [_root_.Path.trans_apply]
      have hi : 2 * (t : ℝ) - 1 ≤ 1 / 2 := by linarith
      simp only [dif_pos hi]
      have hp : (whiskerReparam epsilon he t : ℝ) =
          whiskerCut0 epsilon + 4 *
            (whiskerCut1 epsilon - whiskerCut0 epsilon) *
            ((t : ℝ) - 1 / 2) := by
        change (if (t : ℝ) ≤ 1 / 2 then 2 * whiskerCut0 epsilon * (t : ℝ)
          else if (t : ℝ) ≤ 3 / 4 then
            whiskerCut0 epsilon + 4 *
              (whiskerCut1 epsilon - whiskerCut0 epsilon) *
              ((t : ℝ) - 1 / 2)
          else whiskerCut1 epsilon + 4 * (1 - whiskerCut1 epsilon) *
            ((t : ℝ) - 3 / 4)) = _
        rw [if_neg h0, if_pos h1]
      obtain ⟨hc0, hc01, hc1⟩ := whisker_cuts epsilon he
      have hp0 : ¬ (whiskerReparam epsilon he t : ℝ) ≤
          whiskerCut0 epsilon := by
        rw [hp]
        nlinarith [mul_pos (sub_pos.mpr hc01)
          (show (0 : ℝ) < (t : ℝ) - 1 / 2 by linarith)]
      have hp1 : (whiskerReparam epsilon he t : ℝ) ≤
          whiskerCut1 epsilon := by
        rw [hp]
        nlinarith [mul_nonneg (le_of_lt (sub_pos.mpr hc01))
          (show (0 : ℝ) ≤ 3 / 4 - (t : ℝ) by linarith)]
      have heq : whiskerFun epsilon he alpha gamma beta
          (whiskerReparam epsilon he t) = gamma.extend (2 * (2 * (t : ℝ) - 1)) := by
        unfold whiskerFun
        rw [if_neg hp0, if_pos hp1, hp]
        congr 1
        calc
          whiskerScale epsilon *
              (whiskerCut0 epsilon + 4 *
                (whiskerCut1 epsilon - whiskerCut0 epsilon) *
                ((t : ℝ) - 1 / 2)) - (epsilon : ℝ) =
              (whiskerScale epsilon * whiskerCut0 epsilon - (epsilon : ℝ)) +
                4 * (whiskerScale epsilon *
                  (whiskerCut1 epsilon - whiskerCut0 epsilon)) *
                  ((t : ℝ) - 1 / 2) := by ring
          _ = 2 * (2 * (t : ℝ) - 1) := by
            rw [whisker_cut0_middle, whisker_middle_span]
            ring
      rw [heq, _root_.Path.extend_apply gamma]
    · rw [_root_.Path.trans_apply, dif_neg h0]
      rw [_root_.Path.trans_apply]
      have hi : ¬ 2 * (t : ℝ) - 1 ≤ 1 / 2 := by linarith
      simp only [dif_neg hi]
      have hp : (whiskerReparam epsilon he t : ℝ) =
          whiskerCut1 epsilon + 4 * (1 - whiskerCut1 epsilon) *
            ((t : ℝ) - 3 / 4) := by
        change (if (t : ℝ) ≤ 1 / 2 then 2 * whiskerCut0 epsilon * (t : ℝ)
          else if (t : ℝ) ≤ 3 / 4 then
            whiskerCut0 epsilon + 4 *
              (whiskerCut1 epsilon - whiskerCut0 epsilon) *
              ((t : ℝ) - 1 / 2)
          else whiskerCut1 epsilon + 4 * (1 - whiskerCut1 epsilon) *
            ((t : ℝ) - 3 / 4)) = _
        rw [if_neg h0, if_neg h1]
      obtain ⟨hc0, hc01, hc1⟩ := whisker_cuts epsilon he
      have hp1 : ¬ (whiskerReparam epsilon he t : ℝ) ≤
          whiskerCut1 epsilon := by
        rw [hp]
        nlinarith [mul_pos (show (0 : ℝ) < 1 - whiskerCut1 epsilon by linarith)
          (show (0 : ℝ) < (t : ℝ) - 3 / 4 by linarith)]
      have hp0 : ¬ (whiskerReparam epsilon he t : ℝ) ≤
          whiskerCut0 epsilon := by
        have := lt_of_not_ge hp1
        linarith
      have heq : whiskerFun epsilon he alpha gamma beta
          (whiskerReparam epsilon he t) =
          beta.extend (2 * (2 * (t : ℝ) - 1) - 1) := by
        unfold whiskerFun
        rw [if_neg hp0, if_neg hp1, hp]
        congr 1
        calc
          whiskerScale epsilon / (epsilon : ℝ) *
              (whiskerCut1 epsilon + 4 * (1 - whiskerCut1 epsilon) *
                ((t : ℝ) - 3 / 4) - whiskerCut1 epsilon) =
              (whiskerScale epsilon / (epsilon : ℝ) *
                (1 - whiskerCut1 epsilon)) *
                (4 * ((t : ℝ) - 3 / 4)) := by ring
          _ = 2 * (2 * (t : ℝ) - 1) - 1 := by
            rw [whisker_end_right epsilon he]
            ring
      rw [heq, _root_.Path.extend_apply beta]

private theorem whiskerPath_homotopic_trans
    {X : Type*} [TopologicalSpace X]
    (epsilon : I) (he : (0 : I) < epsilon)
    {a' a b b' : X} (alpha : _root_.Path a' a)
    (gamma : _root_.Path a b) (beta : _root_.Path b b') :
    (whiskerPath epsilon he alpha gamma beta).Homotopic
      (alpha.trans (gamma.trans beta)) := by
  rw [← whiskerPath_reparam epsilon he alpha gamma beta]
  exact ⟨_root_.Path.Homotopy.reparam _ _
    (whiskerReparam_continuous epsilon he)
    (whiskerReparam_zero epsilon he)
    (whiskerReparam_one epsilon he)⟩

/-- A compact-open neighborhood of a path absorbs sufficiently short endpoint
connectors while preserving the prescribed concatenation homotopy class. -/
theorem exists_endpoint_absorption
    {X : Type*} [TopologicalSpace X]
    {a b : X} (gamma : _root_.Path a b)
    {W : Set C(I, X)} (hW : IsOpen W)
    (hgamma : gamma.toContinuousMap ∈ W) :
    ∃ U0 U1 : Set X, IsOpen U0 ∧ a ∈ U0 ∧ IsOpen U1 ∧ b ∈ U1 ∧
      ∀ {a' b' : X} (alpha : _root_.Path a' a)
        (beta : _root_.Path b b'),
        range alpha ⊆ U0 → range beta ⊆ U1 →
          ∃ delta : _root_.Path a' b',
            delta.toContinuousMap ∈ W ∧
              delta.Homotopic (alpha.trans (gamma.trans beta)) := by
  obtain ⟨epsilon, he, hsqueezed⟩ :=
    exists_positive_squeeze_in_open gamma.toContinuousMap hW hgamma
  obtain ⟨U0, U1, hU0open, haU0, hU1open, hbU1, hWneigh⟩ :=
    exists_whisker_neighborhoods gamma epsilon he hW hsqueezed
  refine ⟨U0, U1, hU0open, haU0, hU1open, hbU1, ?_⟩
  intro a' b' alpha beta halpha hbeta
  exact ⟨whiskerPath epsilon he alpha gamma beta,
    hWneigh alpha beta halpha hbeta,
    whiskerPath_homotopic_trans epsilon he alpha gamma beta⟩


end ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup
