import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Homotopy.Product
import Mathlib.Topology.Homotopy.HSpaces
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Maps.OpenQuotient

/-!
# Follow-up challenge: quotient-topological fundamental groups

First prove, for every pointed space, that the compact-open based-loop quotient
is a quasitopological group: reversal and both one-variable translations are
continuous.  Prove the exact criterion that this quotient is discrete if and
only if the null-homotopy class is open.  Derive open quotient projection,
the product-quotient property, and joint continuity of multiplication in the
positive case.

Then instantiate the criterion for every finite product of additive circles,
including an explicit winding classification by the integer lattice.
-/

namespace TopologicalComputationalPathsFollowup

open Set Topology
open scoped ContinuousMap Topology

attribute [local instance] _root_.Path.Homotopic.setoid

universe u

abbrev GenericLoop (X : Type u) [TopologicalSpace X] (x : X) : Type u :=
  _root_.Path x x

abbrev GenericLoopQuot (X : Type u) [TopologicalSpace X] (x : X) : Type u :=
  _root_.Path.Homotopic.Quotient x x

noncomputable local instance genericLoopQuotTopologicalSpace
    (X : Type u) [TopologicalSpace X] (x : X) :
    TopologicalSpace (GenericLoopQuot X x) :=
  TopologicalSpace.coinduced
    (Quotient.mk' : GenericLoop X x → GenericLoopQuot X x) inferInstance

def nullHomotopyClass
    (X : Type u) [TopologicalSpace X] (x : X) : Set (GenericLoop X x) :=
  {γ | γ.Homotopic (_root_.Path.refl x)}

/-- Space-independent theory of the quotient-topological fundamental group. -/
structure QuotientTopologicalFundamentalGroupTheory where
  quotient_symm_continuous :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      Continuous
        (_root_.Path.Homotopic.Quotient.symm :
          GenericLoopQuot X x → GenericLoopQuot X x)
  quotient_trans_left_continuous :
    ∀ (X : Type u) [TopologicalSpace X] (x : X)
      (a : GenericLoopQuot X x),
      Continuous
        (fun b : GenericLoopQuot X x =>
          _root_.Path.Homotopic.Quotient.trans a b)
  quotient_trans_right_continuous :
    ∀ (X : Type u) [TopologicalSpace X] (x : X)
      (b : GenericLoopQuot X x),
      Continuous
        (fun a : GenericLoopQuot X x =>
          _root_.Path.Homotopic.Quotient.trans a b)
  quotient_homogeneous :
    ∀ (X : Type u) [TopologicalSpace X] (x : X)
      (a b : GenericLoopQuot X x),
      ∃ e : GenericLoopQuot X x ≃ₜ GenericLoopQuot X x, e a = b
  quotient_discrete_iff_null_class_open :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      DiscreteTopology (GenericLoopQuot X x) ↔
        IsOpen (nullHomotopyClass X x)
  homotopy_classes_open_of_null_class_open :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      IsOpen (nullHomotopyClass X x) →
      ∀ γ : GenericLoop X x,
        IsOpen {δ : GenericLoop X x | γ.Homotopic δ}
  quotient_open_of_null_class_open :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      IsOpen (nullHomotopyClass X x) →
      IsOpenQuotientMap
        (Quotient.mk' : GenericLoop X x → GenericLoopQuot X x)
  quotient_square_of_null_class_open :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      IsOpen (nullHomotopyClass X x) →
      IsQuotientMap
        (fun p : GenericLoop X x × GenericLoop X x =>
          ((Quotient.mk' p.1 : GenericLoopQuot X x),
            (Quotient.mk' p.2 : GenericLoopQuot X x)))
  quotient_trans_continuous_of_null_class_open :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      IsOpen (nullHomotopyClass X x) →
      Continuous
        (fun p : GenericLoopQuot X x × GenericLoopQuot X x =>
          _root_.Path.Homotopic.Quotient.trans p.1 p.2)

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

/-- Full publication-facing certificate for the finite-torus theorem. -/
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
  null_class_open :
    IsOpen (nullHomotopyClass (FiniteTorus n) (base n))
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

/-- The general criterion and its winding-classified finite-torus family. -/
theorem main_result :
    Nonempty QuotientTopologicalFundamentalGroupTheory ∧
      ∀ n : ℕ, Nonempty (FiniteTorusTopologicalClassification n) := by
  sorry

end TopologicalComputationalPathsFollowup
