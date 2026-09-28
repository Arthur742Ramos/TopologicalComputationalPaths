import ComputationalPaths.Path.Topology.ContinuousGeometricStepSystem
import ComputationalPaths.Path.Topology.ContinuousGeometricStepSystemMap
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homotopy.Product
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Horizontal and vertical steps in a product

The product of two geometric step systems uses horizontal steps indexed by
`StepX × Y` and vertical steps indexed by `X × StepY`.  Each realization
holds the other coordinate fixed.  The step-system maps are continuous in
the compact-open topology.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

universe u v w z

variable {X : Type u} [TopologicalSpace X]
  {Y : Type v} [TopologicalSpace Y]
  {StepX : Type w} [TopologicalSpace StepX]
  {StepY : Type z} [TopologicalSpace StepY]

abbrev ProductStep (StepX Y X StepY : Type*) :=
  (StepX × Y) ⊕ (X × StepY)

noncomputable def productGeometricStepSystem
    (S : ContinuousGeometricStepSystem X StepX)
    (T : ContinuousGeometricStepSystem Y StepY) :
    ContinuousGeometricStepSystem (X × Y)
      (ProductStep StepX Y X StepY) where
  src := Sum.elim (fun ey => (S.src ey.1, ey.2))
    (fun xf => (xf.1, T.src xf.2))
  tgt := Sum.elim (fun ey => (S.tgt ey.1, ey.2))
    (fun xf => (xf.1, T.tgt xf.2))
  realize
    | .inl ey => (S.realize ey.1).prod (_root_.Path.refl ey.2)
    | .inr xf => (_root_.Path.refl xf.1).prod (T.realize xf.2)
  continuous_src := by
    apply continuous_sumElim.2
    constructor
    · exact (S.continuous_src.comp continuous_fst).prodMk continuous_snd
    · exact continuous_fst.prodMk (T.continuous_src.comp continuous_snd)
  continuous_tgt := by
    apply continuous_sumElim.2
    constructor
    · exact (S.continuous_tgt.comp continuous_fst).prodMk continuous_snd
    · exact continuous_fst.prodMk (T.continuous_tgt.comp continuous_snd)
  continuous_realize := by
    have hleft : Continuous (fun (ey : StepX × Y) =>
        ((S.realize ey.1).prod (_root_.Path.refl ey.2)).toContinuousMap) := by
      let swap : C(Y × X, X × Y) :=
        ⟨Prod.swap, continuous_snd.prodMk continuous_fst⟩
      have hinput : Continuous (fun ey : StepX × Y =>
          (ey.2, (S.realize ey.1).toContinuousMap)) :=
        continuous_snd.prodMk (S.continuous_realization.comp continuous_fst)
      have h := (ContinuousMap.continuous_postcomp swap).comp
        (ContinuousMap.continuous_prodMk_const.comp hinput)
      convert h using 1
      funext ey
      apply ContinuousMap.ext
      intro t
      rfl
    have hright : Continuous (fun (xf : X × StepY) =>
        ((_root_.Path.refl xf.1).prod (T.realize xf.2)).toContinuousMap) := by
      have hinput : Continuous (fun xf : X × StepY =>
          (xf.1, (T.realize xf.2).toContinuousMap)) :=
        continuous_fst.prodMk (T.continuous_realization.comp continuous_snd)
      convert ContinuousMap.continuous_prodMk_const.comp hinput using 1
      funext xf
      apply ContinuousMap.ext
      intro t
      rfl
    have h := (continuous_sumElim).2 ⟨hleft, hright⟩
    convert h using 1
    funext step
    cases step <;> rfl

/-- The two edge routes around a product rectangle are homotopic with
fixed endpoints. This supplies the geometric soundness of interchange. -/
theorem productInterchange_sound
    {x₀ x₁ : X} {y₀ y₁ : Y}
    (p : _root_.Path x₀ x₁) (q : _root_.Path y₀ y₁) :
    _root_.Path.Homotopic
      ((p.prod (_root_.Path.refl y₀)).trans
        ((_root_.Path.refl x₁).prod q))
      (((_root_.Path.refl x₀).prod q).trans
        (p.prod (_root_.Path.refl y₁))) := by
  rw [_root_.Path.trans_prod_eq_prod_trans,
    _root_.Path.trans_prod_eq_prod_trans]
  have hx : (p.trans (_root_.Path.refl x₁)).Homotopic
      ((_root_.Path.refl x₀).trans p) :=
    (_root_.Path.Homotopic.trans_refl p).trans
      (_root_.Path.Homotopic.refl_trans p).symm
  have hy : ((_root_.Path.refl y₀).trans q).Homotopic
      (q.trans (_root_.Path.refl y₁)) :=
    (_root_.Path.Homotopic.refl_trans q).trans
      (_root_.Path.Homotopic.trans_refl q).symm
  exact ⟨_root_.Path.Homotopic.prodHomotopy hx.some hy.some⟩

/-- Include an `X`-step horizontally at a fixed `Y`-coordinate. -/
noncomputable def horizontalSystemMap
    (S : ContinuousGeometricStepSystem X StepX)
    (T : ContinuousGeometricStepSystem Y StepY) (y : Y) :
    ContinuousGeometricStepSystemMap S (productGeometricStepSystem S T) where
  map := ⟨fun x => (x, y), continuous_id.prodMk continuous_const⟩
  stepMap := fun e => Sum.inl (e, y)
  map_src := by intro e; rfl
  map_tgt := by intro e; rfl
  map_realize := by
    intro e
    apply _root_.Path.ext
    funext t
    rfl

/-- Include a `Y`-step vertically at a fixed `X`-coordinate. -/
noncomputable def verticalSystemMap
    (S : ContinuousGeometricStepSystem X StepX)
    (T : ContinuousGeometricStepSystem Y StepY) (x : X) :
    ContinuousGeometricStepSystemMap T (productGeometricStepSystem S T) where
  map := ⟨fun y => (x, y), continuous_const.prodMk continuous_id⟩
  stepMap := fun f => Sum.inr (x, f)
  map_src := by intro f; rfl
  map_tgt := by intro f; rfl
  map_realize := by
    intro f
    apply _root_.Path.ext
    funext t
    rfl

end GeometricTopology
end Path
end ComputationalPaths
