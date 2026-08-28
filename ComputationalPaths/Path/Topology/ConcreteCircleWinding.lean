/-
# Concrete topological winding classification of the additive circle

This standalone module proves the winding classification of genuine continuous
loops in Mathlib's additive circle `ℝ ⧸ ℤ`, using an explicit universal-cover
lifting argument.

The first substantive step is the covering map

```
ℝ → AddCircle (1 : ℝ).
```

Mathlib supplies the local additive-circle chart but not the corresponding
covering-map theorem.  We construct an evenly covered punctured-circle
neighborhood explicitly.  Its sheet number is the floor of the translated real
coordinate.
-/

import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.AddCircle.Real

namespace ComputationalPaths
namespace Path
namespace GeometricTopology
namespace ConcreteCircleWinding

open Set Topology

noncomputable section

attribute [local instance] _root_.Path.Homotopic.setoid

/-- Mathlib's unit additive circle. -/
abbrev TopologicalCircle : Type :=
  AddCircle (1 : ℝ)

/-- Universal-cover projection of the unit additive circle. -/
def circleCover : ℝ → TopologicalCircle :=
  fun x => (x : AddCircle (1 : ℝ))

@[continuity] theorem continuous_circleCover :
    Continuous circleCover :=
  AddCircle.continuous_mk' 1

@[simp] theorem circleCover_intCast (n : ℤ) :
    circleCover (n : ℝ) = 0 := by
  rw [circleCover, AddCircle.coe_eq_zero_iff]
  exact ⟨n, by simp⟩

@[simp] theorem circleCover_add_intCast (x : ℝ) (n : ℤ) :
    circleCover (x + n) = circleCover x := by
  simp [circleCover]

/-- Cut point opposite the representative `a` in the chosen length-one chart. -/
def cut (a : ℝ) : ℝ :=
  a - 1 / 2

/-- The standard additive-circle chart with cut at `cut a`. -/
def circleChart (a : ℝ) :
    OpenPartialHomeomorph ℝ TopologicalCircle :=
  AddCircle.openPartialHomeomorphCoe 1 (cut a)

@[simp] theorem circleChart_source (a : ℝ) :
    (circleChart a).source = Ioo (cut a) (cut a + 1) :=
  rfl

@[simp] theorem circleChart_target (a : ℝ) :
    (circleChart a).target = ({circleCover (cut a)} : Set TopologicalCircle)ᶜ :=
  rfl

/-- The representative and its chart cut determine distinct points of the
additive circle. -/
theorem circleCover_ne_cut (a : ℝ) :
    circleCover a ≠ circleCover (cut a) := by
  intro h
  have hcut : cut a ∈ Ico (cut a) (cut a + 1) := by
    constructor <;> simp [cut]
  have ha : a ∈ Ico (cut a) (cut a + 1) := by
    constructor <;> dsimp [cut] <;> linarith
  have : a = cut a :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico ha hcut).mp h
  dsimp [cut] at this
  linarith

/-- Sheet index of a real point relative to the chart cut. -/
def sheet (a e : ℝ) : ℤ :=
  ⌊e - cut a⌋

/-- A point lying over the punctured chart is strictly inside the interval
selected by its sheet index. -/
theorem shifted_mem_chart_source (a e : ℝ)
    (he : circleCover e ≠ circleCover (cut a)) :
    e - (sheet a e : ℝ) ∈ (circleChart a).source := by
  rw [circleChart_source]
  let n := sheet a e
  have hnle : (n : ℝ) ≤ e - cut a :=
    Int.floor_le _
  have hnne : (n : ℝ) ≠ e - cut a := by
    intro hn
    apply he
    have heq : e = cut a + (n : ℝ) := by linarith
    rw [heq, circleCover_add_intCast]
  have hnlt : (n : ℝ) < e - cut a :=
    lt_of_le_of_ne hnle hnne
  have hlt : e - cut a < (n : ℝ) + 1 :=
    Int.lt_floor_add_one _
  constructor <;> dsimp [n, sheet] at * <;> linarith

/-- The floor sheet is locally constant away from the chart cuts. -/
theorem continuous_sheet_on_chart (a : ℝ) :
    Continuous
      (fun e :
        circleCover ⁻¹' ({circleCover (cut a)} : Set TopologicalCircle)ᶜ =>
        sheet a e.1) := by
  rw [continuous_iff_continuousAt]
  intro e
  let n := sheet a e.1
  let t : ℝ := e.1 - cut a
  have hne : circleCover e.1 ≠ circleCover (cut a) :=
    e.2
  have hnle : (n : ℝ) ≤ t :=
    Int.floor_le _
  have hnne : (n : ℝ) ≠ t := by
    intro hn
    apply hne
    have heq : e.1 = cut a + (n : ℝ) := by
      dsimp [t] at hn
      linarith
    rw [heq, circleCover_add_intCast]
  have hnlt : (n : ℝ) < t :=
    lt_of_le_of_ne hnle hnne
  have htlt : t < (n : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hnhds :
      {y :
          circleCover ⁻¹'
            ({circleCover (cut a)} : Set TopologicalCircle)ᶜ |
        y.1 - cut a ∈ Ioo (n : ℝ) ((n : ℝ) + 1)} ∈ 𝓝 e := by
    apply (isOpen_Ioo.preimage
      (continuous_subtype_val.sub continuous_const)).mem_nhds
    exact ⟨hnlt, htlt⟩
  have heq :
      (fun y :
          circleCover ⁻¹'
            ({circleCover (cut a)} : Set TopologicalCircle)ᶜ =>
        sheet a y.1) =ᶠ[𝓝 e] fun _ => n :=
    Filter.mem_of_superset hnhds fun y hy =>
      Int.floor_eq_iff.mpr ⟨hy.1.le, hy.2⟩
  exact (continuousAt_congr heq).2 continuousAt_const

/-- Explicit evenly-covered punctured neighborhood around `↑a`. -/
noncomputable def circleEvenlyCoveredHomeomorph (a : ℝ) :
    circleCover ⁻¹' ({circleCover (cut a)} : Set TopologicalCircle)ᶜ ≃ₜ
      ((({circleCover (cut a)} : Set TopologicalCircle)ᶜ :
        Set TopologicalCircle) × ℤ) := by
  let U : Set TopologicalCircle :=
    ({circleCover (cut a)} : Set TopologicalCircle)ᶜ
  let chart := circleChart a
  let toFun :
      circleCover ⁻¹' U → U × ℤ :=
    fun e => (⟨circleCover e.1, e.2⟩, sheet a e.1)
  let invFun :
      U × ℤ → circleCover ⁻¹' U :=
    fun un =>
      ⟨chart.invFun un.1.1 + (un.2 : ℝ), by
        change circleCover (chart.invFun un.1.1 + (un.2 : ℝ)) ∈ U
        rw [circleCover_add_intCast]
        have hr :
            circleCover (chart.invFun un.1.1) = un.1.1 := by
          simpa [chart, circleChart, circleCover] using
            chart.right_inv un.1.2
        rw [hr]
        exact un.1.2⟩
  refine
    { toFun := toFun
      invFun := invFun
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro e
    apply Subtype.ext
    let n := sheet a e.1
    let y : ℝ := e.1 - (n : ℝ)
    have hy : y ∈ chart.source := by
      exact shifted_mem_chart_source a e.1 e.2
    have hcover : circleCover y = circleCover e.1 := by
      dsimp [y]
      have : e.1 = (e.1 - (n : ℝ)) + (n : ℝ) := by ring
      conv_rhs => rw [this, circleCover_add_intCast]
    have hinv : chart.invFun (circleCover e.1) = y := by
      rw [← hcover]
      exact chart.left_inv hy
    dsimp [invFun, toFun]
    change chart.invFun (circleCover e.1) + (sheet a e.1 : ℝ) = e.1
    rw [hinv]
    dsimp [y]
    ring
  · intro un
    apply Prod.ext
    · apply Subtype.ext
      dsimp [toFun, invFun]
      rw [circleCover_add_intCast]
      exact chart.right_inv un.1.2
    · dsimp [toFun, invFun]
      have hb : chart.invFun un.1.1 ∈ chart.source :=
        chart.map_target un.1.2
      have hb0 : 0 ≤ chart.invFun un.1.1 - cut a := by
        rw [circleChart_source] at hb
        linarith [hb.1]
      have hb1 : chart.invFun un.1.1 - cut a < 1 := by
        rw [circleChart_source] at hb
        linarith [hb.2]
      have hfloor :
          ⌊chart.invFun un.1.1 - cut a⌋ = (0 : ℤ) :=
        Int.floor_eq_zero_iff.mpr ⟨hb0, hb1⟩
      change
        ⌊chart.invFun un.1.1 + (un.2 : ℝ) - cut a⌋ = un.2
      have hrearr :
          chart.invFun un.1.1 + (un.2 : ℝ) - cut a =
            (chart.invFun un.1.1 - cut a) + (un.2 : ℝ) := by
        ring
      rw [hrearr, Int.floor_add_intCast, hfloor, zero_add]
  · dsimp [toFun, U]
    apply Continuous.prodMk
    · exact (continuous_circleCover.comp continuous_subtype_val).subtype_mk _
    · exact continuous_sheet_on_chart a
  · dsimp [invFun]
    apply Continuous.subtype_mk
    · have hchart :
          Continuous
            (fun u : U => chart.invFun u.1) := by
        exact continuousOn_iff_continuous_restrict.mp
          chart.continuousOn_invFun
      exact
        (hchart.comp continuous_fst).add
          (continuous_of_discreteTopology.comp continuous_snd)

/-- Every point of `AddCircle 1` has an evenly-covered neighborhood for the
quotient map from `ℝ`. -/
theorem isEvenlyCovered_circleCover (a : ℝ) :
    IsEvenlyCovered circleCover (circleCover a) ℤ := by
  refine ⟨inferInstance,
    ({circleCover (cut a)} : Set TopologicalCircle)ᶜ,
    circleCover_ne_cut a,
    isOpen_compl_singleton,
    isOpen_compl_singleton.preimage continuous_circleCover,
    circleEvenlyCoveredHomeomorph a,
    ?_⟩
  intro e
  rfl

/-- The quotient projection `ℝ → ℝ ⧸ ℤ` is a covering map. -/
theorem isCoveringMap_circleCover :
    IsCoveringMap circleCover := by
  intro x
  obtain ⟨a, _, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) x
  exact (isEvenlyCovered_circleCover a).to_isEvenlyCovered_preimage

/-! ## Topological winding number -/

/-- Based loops in Mathlib's unit additive circle, modulo topological
endpoint-fixed homotopy. -/
abbrev TopologicalLoopQuot : Type :=
  _root_.Path.Homotopic.Quotient
    (0 : TopologicalCircle) (0 : TopologicalCircle)

private theorem loop_start_eq_cover_zero
    (γ : _root_.Path (0 : TopologicalCircle) 0) :
    γ.toContinuousMap 0 = circleCover 0 := by
  change γ.toContinuousMap 0 = (0 : TopologicalCircle)
  exact γ.source

/-- Canonical lift of a based circle loop starting at `0 : ℝ`. -/
noncomputable def liftLoop
    (γ : _root_.Path (0 : TopologicalCircle) 0) :
    C(unitInterval, ℝ) :=
  isCoveringMap_circleCover.liftPath γ.toContinuousMap 0
    (loop_start_eq_cover_zero γ)

@[simp] theorem liftLoop_zero
    (γ : _root_.Path (0 : TopologicalCircle) 0) :
    liftLoop γ 0 = 0 :=
  isCoveringMap_circleCover.liftPath_zero _ _ _

theorem circleCover_liftLoop
    (γ : _root_.Path (0 : TopologicalCircle) 0) :
    circleCover ∘ liftLoop γ = γ.toContinuousMap :=
  isCoveringMap_circleCover.liftPath_lifts _ _ _

theorem circleCover_liftLoop_one
    (γ : _root_.Path (0 : TopologicalCircle) 0) :
    circleCover (liftLoop γ 1) = 0 := by
  have h := congr_fun (circleCover_liftLoop γ) 1
  simpa using h.trans γ.target

/-- Integer winding of a concrete topological loop, computed as the floor of
the endpoint of its lift. -/
noncomputable def windingPath
    (γ : _root_.Path (0 : TopologicalCircle) 0) : ℤ :=
  ⌊liftLoop γ 1⌋

/-- The lifted endpoint is exactly the integer selected by `windingPath`. -/
theorem windingPath_cast_eq_liftLoop_one
    (γ : _root_.Path (0 : TopologicalCircle) 0) :
    (windingPath γ : ℝ) = liftLoop γ 1 := by
  obtain ⟨n, hn⟩ :=
    (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp
      (circleCover_liftLoop_one γ)
  have hn' : (n : ℝ) = liftLoop γ 1 := by
    simpa using hn
  have hw : windingPath γ = n := by
    unfold windingPath
    rw [← hn', Int.floor_intCast]
  calc
    (windingPath γ : ℝ) = (n : ℝ) := by exact_mod_cast hw
    _ = liftLoop γ 1 := hn'

/-- Topological winding is invariant under endpoint-fixed loop homotopy. -/
theorem windingPath_eq_of_homotopic
    {γ₀ γ₁ : _root_.Path (0 : TopologicalCircle) 0}
    (h : γ₀.Homotopic γ₁) :
    windingPath γ₀ = windingPath γ₁ := by
  have hend :=
    isCoveringMap_circleCover.liftPath_apply_one_eq_of_homotopicRel
      h 0 (loop_start_eq_cover_zero γ₀) (loop_start_eq_cover_zero γ₁)
  exact _root_.congrArg Int.floor (by simpa [liftLoop] using hend)

/-- Winding number on topological loop homotopy classes. -/
noncomputable def topologicalWinding :
    TopologicalLoopQuot → ℤ :=
  Quotient.lift windingPath
    (fun _ _ h => windingPath_eq_of_homotopic h)

/-- Straight lift from `0` to the integer `n`. -/
noncomputable def straightLift (n : ℤ) :
    C(unitInterval, ℝ) where
  toFun t := (t : ℝ) * (n : ℝ)
  continuous_toFun := by fun_prop

/-- Standard topological loop of winding `n`. -/
noncomputable def standardLoop (n : ℤ) :
    _root_.Path (0 : TopologicalCircle) 0 where
  toFun t := circleCover ((t : ℝ) * (n : ℝ))
  continuous_toFun :=
    continuous_circleCover.comp
      (continuous_subtype_val.mul continuous_const)
  source' := by simp [circleCover]
  target' := by simp [circleCover]

theorem liftLoop_standardLoop (n : ℤ) :
    liftLoop (standardLoop n) = straightLift n := by
  apply Eq.symm
  unfold liftLoop
  rw [isCoveringMap_circleCover.eq_liftPath_iff']
  constructor
  · rfl
  · simp [straightLift]

@[simp] theorem windingPath_standardLoop (n : ℤ) :
    windingPath (standardLoop n) = n := by
  rw [windingPath, liftLoop_standardLoop]
  simp [straightLift]

/-- Decode an integer as the class of the standard topological loop. -/
noncomputable def decodeTopologicalWinding (n : ℤ) :
    TopologicalLoopQuot :=
  Quotient.mk' (standardLoop n)

@[simp] theorem topologicalWinding_decode (n : ℤ) :
    topologicalWinding (decodeTopologicalWinding n) = n :=
  windingPath_standardLoop n

/-- The canonical lift as a path in `ℝ`. -/
noncomputable def liftLoopPath
    (γ : _root_.Path (0 : TopologicalCircle) 0) :
    _root_.Path (0 : ℝ) (liftLoop γ 1) where
  toContinuousMap := liftLoop γ
  source' := liftLoop_zero γ
  target' := rfl

theorem circleCover_liftLoopPath_extend
    (γ : _root_.Path (0 : TopologicalCircle) 0) (t : ℝ) :
    circleCover ((liftLoopPath γ).extend t) = γ.extend t := by
  by_cases h0 : t ≤ 0
  · rw [_root_.Path.extend_of_le_zero _ h0,
      _root_.Path.extend_of_le_zero _ h0]
    simp [circleCover]
  by_cases h1 : 1 ≤ t
  · rw [_root_.Path.extend_of_one_le _ h1,
      _root_.Path.extend_of_one_le _ h1]
    exact circleCover_liftLoop_one γ
  have ht : t ∈ Icc (0 : ℝ) 1 :=
    ⟨le_of_not_ge h0, le_of_not_ge h1⟩
  rw [_root_.Path.extend_apply _ ht,
    _root_.Path.extend_apply _ ht]
  exact congr_fun (circleCover_liftLoop γ) ⟨t, ht⟩

/-- Lift of `δ`, translated to start where the lift of `γ` ends. -/
noncomputable def shiftedLiftLoopPath
    (γ δ : _root_.Path (0 : TopologicalCircle) 0) :
    _root_.Path (liftLoop γ 1) (liftLoop γ 1 + liftLoop δ 1) where
  toFun t := liftLoop γ 1 + liftLoop δ t
  continuous_toFun := continuous_const.add (liftLoop δ).continuous
  source' := by simp
  target' := rfl

@[simp] theorem circleCover_add_liftLoop_one
    (γ : _root_.Path (0 : TopologicalCircle) 0) (x : ℝ) :
    circleCover (liftLoop γ 1 + x) = circleCover x := by
  calc
    circleCover (liftLoop γ 1 + x) =
        circleCover (liftLoop γ 1) + circleCover x := rfl
    _ = circleCover x := by
      rw [circleCover_liftLoop_one, zero_add]

theorem circleCover_shiftedLiftLoopPath_extend
    (γ δ : _root_.Path (0 : TopologicalCircle) 0) (t : ℝ) :
    circleCover ((shiftedLiftLoopPath γ δ).extend t) = δ.extend t := by
  by_cases h0 : t ≤ 0
  · rw [_root_.Path.extend_of_le_zero _ h0,
      _root_.Path.extend_of_le_zero _ h0]
    simpa [circleCover] using circleCover_liftLoop_one γ
  by_cases h1 : 1 ≤ t
  · rw [_root_.Path.extend_of_one_le _ h1,
      _root_.Path.extend_of_one_le _ h1]
    rw [circleCover_add_liftLoop_one, circleCover_liftLoop_one]
  have ht : t ∈ Icc (0 : ℝ) 1 :=
    ⟨le_of_not_ge h0, le_of_not_ge h1⟩
  rw [_root_.Path.extend_apply _ ht,
    _root_.Path.extend_apply _ ht]
  change
    circleCover (liftLoop γ 1 + liftLoop δ ⟨t, ht⟩) =
      δ ⟨t, ht⟩
  rw [circleCover_add_liftLoop_one]
  exact congr_fun (circleCover_liftLoop δ) ⟨t, ht⟩

/-- Candidate lift of loop concatenation. -/
noncomputable def combinedLiftLoopPath
    (γ δ : _root_.Path (0 : TopologicalCircle) 0) :
    _root_.Path (0 : ℝ) (liftLoop γ 1 + liftLoop δ 1) :=
  (liftLoopPath γ).trans (shiftedLiftLoopPath γ δ)

theorem combinedLiftLoopPath_lifts
    (γ δ : _root_.Path (0 : TopologicalCircle) 0) :
    circleCover ∘ (combinedLiftLoopPath γ δ).toContinuousMap =
      (γ.trans δ).toContinuousMap := by
  funext t
  change
    circleCover
        (((liftLoopPath γ).trans (shiftedLiftLoopPath γ δ)) t) =
      (γ.trans δ) t
  rw [_root_.Path.trans_apply, _root_.Path.trans_apply]
  split_ifs
  · exact congr_fun (circleCover_liftLoop γ) _
  · change
      circleCover (liftLoop γ 1 + liftLoop δ _) = δ _
    rw [circleCover_add_liftLoop_one]
    exact congr_fun (circleCover_liftLoop δ) _

theorem liftLoop_trans
    (γ δ : _root_.Path (0 : TopologicalCircle) 0) :
    liftLoop (γ.trans δ) =
      (combinedLiftLoopPath γ δ).toContinuousMap := by
  apply Eq.symm
  unfold liftLoop
  rw [isCoveringMap_circleCover.eq_liftPath_iff']
  refine ⟨combinedLiftLoopPath_lifts γ δ, ?_⟩
  change (combinedLiftLoopPath γ δ).toContinuousMap 0 = 0
  simp [combinedLiftLoopPath, liftLoopPath, shiftedLiftLoopPath]

/-- Winding is additive under topological loop concatenation. -/
theorem windingPath_trans
    (γ δ : _root_.Path (0 : TopologicalCircle) 0) :
    windingPath (γ.trans δ) = windingPath γ + windingPath δ := by
  have htrans := windingPath_cast_eq_liftLoop_one (γ.trans δ)
  rw [liftLoop_trans] at htrans
  have hend :
      (combinedLiftLoopPath γ δ).toContinuousMap 1 =
        liftLoop γ 1 + liftLoop δ 1 := by
    simp [combinedLiftLoopPath]
  rw [hend] at htrans
  have hγ := windingPath_cast_eq_liftLoop_one γ
  have hδ := windingPath_cast_eq_liftLoop_one δ
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_add]
  calc
    (windingPath (γ.trans δ) : ℝ) =
        liftLoop γ 1 + liftLoop δ 1 := htrans
    _ = (windingPath γ : ℝ) + (windingPath δ : ℝ) := by
      rw [hγ, hδ]

/-- Topological winding is additive on loop homotopy classes. -/
theorem topologicalWinding_comp
    (x y : TopologicalLoopQuot) :
    topologicalWinding
        (_root_.Path.Homotopic.Quotient.trans x y) =
      topologicalWinding x + topologicalWinding y := by
  induction x using Quotient.ind with
  | _ γ =>
      induction y using Quotient.ind with
      | _ δ =>
          exact windingPath_trans γ δ

/-- Straight path to the lifted endpoint, indexed by winding number. -/
noncomputable def straightWindingPath
    (γ : _root_.Path (0 : TopologicalCircle) 0) :
    _root_.Path (0 : ℝ) (liftLoop γ 1) where
  toFun t := (t : ℝ) * (windingPath γ : ℝ)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by
    simpa using windingPath_cast_eq_liftLoop_one γ

/-- Projection of the canonical lift, with its endpoints expressed at the
circle basepoint. -/
noncomputable def projectedLiftLoopPath
    (γ : _root_.Path (0 : TopologicalCircle) 0) :
    _root_.Path (0 : TopologicalCircle) 0 where
  toFun t := circleCover (liftLoop γ t)
  continuous_toFun :=
    continuous_circleCover.comp (liftLoop γ).continuous
  source' := by simp [circleCover]
  target' := circleCover_liftLoop_one γ

/-- Projection of the straight winding path. -/
noncomputable def projectedStraightWindingPath
    (γ : _root_.Path (0 : TopologicalCircle) 0) :
    _root_.Path (0 : TopologicalCircle) 0 where
  toFun t := circleCover ((t : ℝ) * (windingPath γ : ℝ))
  continuous_toFun :=
    continuous_circleCover.comp
      (continuous_subtype_val.mul continuous_const)
  source' := by simp [circleCover]
  target' := by simp

theorem projectedLiftLoopPath_eq
    (γ : _root_.Path (0 : TopologicalCircle) 0) :
    projectedLiftLoopPath γ = γ := by
  ext t
  exact congr_fun (circleCover_liftLoop γ) t

theorem projectedStraightWindingPath_eq
    (γ : _root_.Path (0 : TopologicalCircle) 0) :
    projectedStraightWindingPath γ =
      standardLoop (windingPath γ) :=
  rfl

/-- Every topological circle loop is homotopic to its standard winding loop. -/
theorem standardLoop_homotopic
    (γ : _root_.Path (0 : TopologicalCircle) 0) :
    (standardLoop (windingPath γ)).Homotopic γ := by
  have hreal :
      (straightWindingPath γ).Homotopic (liftLoopPath γ) :=
    SimplyConnectedSpace.paths_homotopic _ _
  let coverMap : C(ℝ, TopologicalCircle) :=
    ⟨circleCover, continuous_circleCover⟩
  have hmap :=
    _root_.Path.Homotopic.map hreal
      coverMap
  have hprojected :
      (projectedStraightWindingPath γ).Homotopic
        (projectedLiftLoopPath γ) := by
    have hsource : (0 : TopologicalCircle) = coverMap 0 := by
      simp [coverMap, circleCover]
    have htarget :
        (0 : TopologicalCircle) = coverMap (liftLoop γ 1) := by
      simpa [coverMap] using (circleCover_liftLoop_one γ).symm
    have hcast := _root_.Path.Homotopic.pathCast hmap hsource htarget
    have hstraight :
        ((straightWindingPath γ).map coverMap.continuous).cast hsource htarget =
          projectedStraightWindingPath γ := by
      apply _root_.Path.ext
      funext t
      rfl
    have hlift :
        ((liftLoopPath γ).map coverMap.continuous).cast hsource htarget =
          projectedLiftLoopPath γ := by
      apply _root_.Path.ext
      funext t
      rfl
    rw [hstraight, hlift] at hcast
    exact hcast
  simpa [projectedStraightWindingPath_eq, projectedLiftLoopPath_eq] using
    hprojected

theorem decode_topologicalWinding (x : TopologicalLoopQuot) :
    decodeTopologicalWinding (topologicalWinding x) = x := by
  induction x using Quotient.ind with
  | _ γ =>
      exact Quotient.sound (standardLoop_homotopic γ)

/-- Topological circle loops modulo homotopy are classified by winding number. -/
noncomputable def topologicalLoopQuotEquivInt :
    Equiv TopologicalLoopQuot ℤ where
  toFun := topologicalWinding
  invFun := decodeTopologicalWinding
  left_inv := decode_topologicalWinding
  right_inv := topologicalWinding_decode

theorem windingPath_refl :
    windingPath (_root_.Path.refl (0 : TopologicalCircle)) = 0 := by
  have h :
      standardLoop 0 = _root_.Path.refl (0 : TopologicalCircle) := by
    ext t
    simp [standardLoop, circleCover]
  rw [← h]
  exact windingPath_standardLoop 0

end
end ConcreteCircleWinding
end GeometricTopology
end Path
end ComputationalPaths
