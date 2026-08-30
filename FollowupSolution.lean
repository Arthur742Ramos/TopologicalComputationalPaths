import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Homotopy.Product
import Mathlib.Topology.Instances.AddCircle.Real
import ComputationalPaths

/-!
# Follow-up solution: quotient-topological finite-torus winding

The proof uses coordinatewise universal-cover winding.  A local zero-chart
contraction proves winding locally constant on the compact-open circle-loop
space.  Finite products then yield a continuous complete invariant, and the
general discrete-classifier theorem upgrades the algebraic classification to
a homeomorphism while forcing the quotient square and quotient operations to
have the desired topology.
-/

namespace TopologicalComputationalPathsFollowup

open Set Topology
open scoped ContinuousMap Topology

attribute [local instance] _root_.Path.Homotopic.setoid

abbrev Circle : Type := AddCircle (1 : ℝ)
abbrev FiniteTorus (n : ℕ) : Type := Fin n → Circle
noncomputable abbrev base (n : ℕ) : FiniteTorus n := fun _ => 0
abbrev Loop (n : ℕ) : Type := _root_.Path (base n) (base n)
abbrev LoopQuot (n : ℕ) : Type :=
  _root_.Path.Homotopic.Quotient (base n) (base n)
abbrev WindingVector (n : ℕ) : Type := Fin n → ℤ

noncomputable instance loopQuotTopology (n : ℕ) :
    TopologicalSpace (LoopQuot n) :=
  TopologicalSpace.coinduced
    (Quotient.mk' : Loop n → LoopQuot n) inferInstance

structure FiniteTorusTopologicalClassification (n : ℕ) where
  winding : Loop n → WindingVector n
  standardLoop : WindingVector n → Loop n
  classifier : LoopQuot n ≃ₜ WindingVector n
  classifier_mk :
    ∀ γ : Loop n, classifier (Quotient.mk' γ) = winding γ
  winding_standard :
    ∀ z : WindingVector n, winding (standardLoop z) = z
  standard_complete :
    ∀ γ : Loop n, (standardLoop (winding γ)).Homotopic γ
  winding_identity :
    winding (_root_.Path.refl (base n)) = 0
  winding_trans :
    ∀ γ δ : Loop n, winding (γ.trans δ) = winding γ + winding δ
  classifier_trans :
    ∀ x y : LoopQuot n,
      classifier (_root_.Path.Homotopic.Quotient.trans x y) =
        classifier x + classifier y
  quotient_discrete : DiscreteTopology (LoopQuot n)
  homotopy_classes_open :
    ∀ γ : Loop n, IsOpen {δ : Loop n | _root_.Path.Homotopic γ δ}
  quotient_square :
    IsQuotientMap
      (fun p : Loop n × Loop n =>
        ((Quotient.mk' p.1 : LoopQuot n),
          (Quotient.mk' p.2 : LoopQuot n)))
  quotient_trans_continuous :
    Continuous
      (fun p : LoopQuot n × LoopQuot n =>
        _root_.Path.Homotopic.Quotient.trans p.1 p.2)
  quotient_symm_continuous :
    Continuous
      (_root_.Path.Homotopic.Quotient.symm :
        LoopQuot n → LoopQuot n)

open ComputationalPaths.Path.GeometricTopology

theorem main_result (n : ℕ) :
    Nonempty (FiniteTorusTopologicalClassification n) := by
  exact ⟨{
    winding := FiniteTorusWinding.winding
    standardLoop := FiniteTorusWinding.standardLoop
    classifier := FiniteTorusWinding.loopQuotHomeomorphIntVector n
    classifier_mk := by
      intro γ
      rfl
    winding_standard := FiniteTorusWinding.winding_standardLoop
    standard_complete := FiniteTorusWinding.standardLoop_homotopic
    winding_identity := FiniteTorusWinding.winding_identity
    winding_trans := FiniteTorusWinding.winding_trans
    classifier_trans := FiniteTorusWinding.encode_trans
    quotient_discrete := inferInstance
    homotopy_classes_open := FiniteTorusWinding.isOpen_homotopyClass
    quotient_square := FiniteTorusWinding.loopQuotientProd_isQuotientMap n
    quotient_trans_continuous := FiniteTorusWinding.continuous_quotientTrans n
    quotient_symm_continuous := FiniteTorusWinding.continuous_quotientSymm n }⟩

end TopologicalComputationalPathsFollowup
