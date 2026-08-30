import ComputationalPaths.Path.Topology.ConcreteCircleWinding

/-!
# Concrete topological torus winding classification

The torus is the product of two copies of the additive circle
`AddCircle (1 : ℝ)`.  This file records the product winding theorem for
ordinary interval paths.  It is deliberately separate from the older
synthetic `torusPiOne` carrier: the quotient here is the quotient of genuine
continuous torus loops by endpoint-fixed homotopy.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

namespace TopologicalTorus

open ConcreteCircleWinding

attribute [local instance] _root_.Path.Homotopic.setoid

abbrev Carrier : Type := TopologicalCircle × TopologicalCircle

noncomputable abbrev base : Carrier := (0, 0)

abbrev Loop : Type := _root_.Path base base

noncomputable def coordinateFst (γ : Loop) :
    _root_.Path (0 : TopologicalCircle) 0 :=
  γ.map ContinuousMap.fst.continuous

noncomputable def coordinateSnd (γ : Loop) :
    _root_.Path (0 : TopologicalCircle) 0 :=
  γ.map ContinuousMap.snd.continuous

noncomputable def standardLoop (m n : ℤ) : Loop :=
  (ConcreteCircleWinding.standardLoop m).prod
    (ConcreteCircleWinding.standardLoop n)

noncomputable def winding (γ : Loop) : ℤ × ℤ :=
  (windingPath (coordinateFst γ), windingPath (coordinateSnd γ))

theorem coordinateFst_standardLoop (m n : ℤ) :
    coordinateFst (standardLoop m n) =
      ConcreteCircleWinding.standardLoop m := by
  apply _root_.Path.ext
  funext t
  rfl

theorem coordinateSnd_standardLoop (m n : ℤ) :
    coordinateSnd (standardLoop m n) =
      ConcreteCircleWinding.standardLoop n := by
  apply _root_.Path.ext
  funext t
  rfl

@[simp] theorem winding_standardLoop (m n : ℤ) :
    winding (standardLoop m n) = (m, n) := by
  apply Prod.ext
  · change windingPath (coordinateFst (standardLoop m n)) = m
    rw [coordinateFst_standardLoop]
    exact windingPath_standardLoop m
  · change windingPath (coordinateSnd (standardLoop m n)) = n
    rw [coordinateSnd_standardLoop]
    exact windingPath_standardLoop n

theorem winding_eq_of_homotopic {γ δ : Loop}
    (h : γ.Homotopic δ) : winding γ = winding δ := by
  apply Prod.ext
  · have h0 : (0 : TopologicalCircle) = ContinuousMap.fst base := by
      change (0 : TopologicalCircle) = 0
      rfl
    have hc := _root_.Path.Homotopic.pathCast (h.map ContinuousMap.fst) h0 h0
    have hγ :
        ((γ.map ContinuousMap.fst.continuous).cast h0 h0) = coordinateFst γ := by
      apply _root_.Path.ext
      funext t
      rfl
    have hδ :
        ((δ.map ContinuousMap.fst.continuous).cast h0 h0) = coordinateFst δ := by
      apply _root_.Path.ext
      funext t
      rfl
    rw [hγ, hδ] at hc
    exact windingPath_eq_of_homotopic hc
  · have h0 : (0 : TopologicalCircle) = ContinuousMap.snd base := by
      change (0 : TopologicalCircle) = 0
      rfl
    have hc := _root_.Path.Homotopic.pathCast (h.map ContinuousMap.snd) h0 h0
    have hγ :
        ((γ.map ContinuousMap.snd.continuous).cast h0 h0) = coordinateSnd γ := by
      apply _root_.Path.ext
      funext t
      rfl
    have hδ :
        ((δ.map ContinuousMap.snd.continuous).cast h0 h0) = coordinateSnd δ := by
      apply _root_.Path.ext
      funext t
      rfl
    rw [hγ, hδ] at hc
    exact windingPath_eq_of_homotopic hc

theorem coordinate_product_eq (γ : Loop) :
    (coordinateFst γ).prod (coordinateSnd γ) = γ := by
  apply _root_.Path.ext
  funext t
  rfl

theorem coordinateFst_trans (γ δ : Loop) :
    coordinateFst (γ.trans δ) = (coordinateFst γ).trans (coordinateFst δ) := by
  unfold coordinateFst
  exact _root_.Path.map_trans γ δ ContinuousMap.fst.continuous

theorem coordinateSnd_trans (γ δ : Loop) :
    coordinateSnd (γ.trans δ) = (coordinateSnd γ).trans (coordinateSnd δ) := by
  unfold coordinateSnd
  exact _root_.Path.map_trans γ δ ContinuousMap.snd.continuous

theorem winding_trans (γ δ : Loop) :
    winding (γ.trans δ) =
      ((winding γ).1 + (winding δ).1,
        (winding γ).2 + (winding δ).2) := by
  apply Prod.ext
  · change windingPath (coordinateFst (γ.trans δ)) = _
    rw [coordinateFst_trans, windingPath_trans]
    rfl
  · change windingPath (coordinateSnd (γ.trans δ)) = _
    rw [coordinateSnd_trans, windingPath_trans]
    rfl

theorem winding_identity :
    winding (_root_.Path.refl base) = (0, 0) := by
  apply Prod.ext
  · change windingPath (coordinateFst (_root_.Path.refl base)) = 0
    rw [show coordinateFst (_root_.Path.refl base) =
      _root_.Path.refl (0 : TopologicalCircle) by
        apply _root_.Path.ext
        funext t
        rfl]
    exact windingPath_refl
  · change windingPath (coordinateSnd (_root_.Path.refl base)) = 0
    rw [show coordinateSnd (_root_.Path.refl base) =
      _root_.Path.refl (0 : TopologicalCircle) by
        apply _root_.Path.ext
        funext t
        rfl]
    exact windingPath_refl

noncomputable def firstFactorLoop (m : ℤ) : Loop :=
  (ConcreteCircleWinding.standardLoop m).prod
    (_root_.Path.refl (0 : TopologicalCircle))

noncomputable def secondFactorLoop (n : ℤ) : Loop :=
  (_root_.Path.refl (0 : TopologicalCircle)).prod
    (ConcreteCircleWinding.standardLoop n)

noncomputable def sequentialLoop (m n : ℤ) : Loop :=
  (firstFactorLoop m).trans (secondFactorLoop n)

theorem winding_firstFactorLoop (m : ℤ) :
    winding (firstFactorLoop m) = (m, 0) := by
  apply Prod.ext
  · change windingPath (coordinateFst (firstFactorLoop m)) = m
    rw [show coordinateFst (firstFactorLoop m) =
      ConcreteCircleWinding.standardLoop m by
        apply _root_.Path.ext
        funext t
        rfl]
    exact windingPath_standardLoop m
  · change windingPath (coordinateSnd (firstFactorLoop m)) = 0
    rw [show coordinateSnd (firstFactorLoop m) =
      _root_.Path.refl (0 : TopologicalCircle) by
        apply _root_.Path.ext
        funext t
        rfl]
    exact windingPath_refl

theorem winding_secondFactorLoop (n : ℤ) :
    winding (secondFactorLoop n) = (0, n) := by
  apply Prod.ext
  · change windingPath (coordinateFst (secondFactorLoop n)) = 0
    rw [show coordinateFst (secondFactorLoop n) =
      _root_.Path.refl (0 : TopologicalCircle) by
        apply _root_.Path.ext
        funext t
        rfl]
    exact windingPath_refl
  · change windingPath (coordinateSnd (secondFactorLoop n)) = n
    rw [show coordinateSnd (secondFactorLoop n) =
      ConcreteCircleWinding.standardLoop n by
        apply _root_.Path.ext
        funext t
        rfl]
    exact windingPath_standardLoop n

@[simp] theorem winding_sequentialLoop (m n : ℤ) :
    winding (sequentialLoop m n) = (m, n) := by
  rw [sequentialLoop, winding_trans, winding_firstFactorLoop,
    winding_secondFactorLoop]
  simp

theorem standardLoop_homotopic (γ : Loop) :
    (standardLoop (winding γ).1 (winding γ).2).Homotopic γ := by
  have hfst := ConcreteCircleWinding.standardLoop_homotopic
    (coordinateFst γ)
  have hsnd := ConcreteCircleWinding.standardLoop_homotopic
    (coordinateSnd γ)
  rcases hfst with ⟨hfst⟩
  rcases hsnd with ⟨hsnd⟩
  have hprod := _root_.Path.Homotopic.prodHomotopy hfst hsnd
  rw [coordinate_product_eq γ] at hprod
  exact ⟨hprod⟩

theorem standardLoop_homotopic_sequentialLoop (m n : ℤ) :
    (standardLoop m n).Homotopic (sequentialLoop m n) := by
  simpa only [winding_sequentialLoop] using
    (standardLoop_homotopic (sequentialLoop m n))

abbrev LoopQuot : Type :=
  _root_.Path.Homotopic.Quotient base base

noncomputable def encode : LoopQuot → ℤ × ℤ :=
  Quotient.lift winding (fun _ _ h => winding_eq_of_homotopic h)

theorem encode_identity :
    encode (Quotient.mk' (_root_.Path.refl base)) = (0, 0) := by
  change winding (_root_.Path.refl base) = (0, 0)
  exact winding_identity

theorem encode_trans (x y : LoopQuot) :
    encode (_root_.Path.Homotopic.Quotient.trans x y) =
      ((encode x).1 + (encode y).1,
        (encode x).2 + (encode y).2) := by
  induction x using Quotient.ind with
  | _ γ =>
      induction y using Quotient.ind with
      | _ δ =>
          change winding (γ.trans δ) = _
          exact winding_trans γ δ

noncomputable def decode (z : ℤ × ℤ) : LoopQuot :=
  Quotient.mk' (standardLoop z.1 z.2)

@[simp] theorem encode_decode (z : ℤ × ℤ) :
    encode (decode z) = z := by
  change winding (standardLoop z.1 z.2) = z
  exact winding_standardLoop z.1 z.2

theorem decode_encode (x : LoopQuot) :
    decode (encode x) = x := by
  refine Quotient.inductionOn x ?_
  intro γ
  exact Quotient.sound (standardLoop_homotopic γ)

noncomputable def equivIntProd : LoopQuot ≃ (ℤ × ℤ) where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode


end TopologicalTorus
end GeometricTopology
end Path
end ComputationalPaths
