import Mathlib.Topology.Homotopy.Product
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Int.DivMod

/-! Self-contained statement: concrete torus semantics and executable solver.
No repository imports, supplied classifier, or abstract cost observable. -/

namespace ComputationalPaths.Path.GeometricTopology
namespace ConcreteCircleWinding
abbrev TopologicalCircle : Type := AddCircle (1 : ℝ)
def circleCover : ℝ → TopologicalCircle := fun x => (x : AddCircle (1 : ℝ))
@[continuity] theorem continuous_circleCover : Continuous circleCover :=
  AddCircle.continuous_mk' 1
noncomputable def standardLoop (n : ℤ) : _root_.Path (0 : TopologicalCircle) 0 where
  toFun t := circleCover ((t : ℝ) * (n : ℝ))
  continuous_toFun := continuous_circleCover.comp
    (continuous_subtype_val.mul continuous_const)
  source' := by simp [circleCover]
  target' := by simp [circleCover]
end ConcreteCircleWinding

namespace FiniteTorusWinding
open ConcreteCircleWinding
open scoped ContinuousMap BigOperators
attribute [local instance] _root_.Path.Homotopic.setoid
abbrev Carrier (n : ℕ) : Type := Fin n → TopologicalCircle
noncomputable abbrev base (n : ℕ) : Carrier n := fun _ => 0
abbrev Loop (n : ℕ) : Type := _root_.Path (base n) (base n)
abbrev LoopQuot (n : ℕ) : Type := _root_.Path.Homotopic.Quotient (base n) (base n)
noncomputable def standardLoop {n : ℕ} (z : Fin n → ℤ) : Loop n :=
  _root_.Path.pi (fun i => ConcreteCircleWinding.standardLoop (z i))
noncomputable def decode {n : ℕ} (z : Fin n → ℤ) : LoopQuot n :=
  Quotient.mk' (standardLoop z)
noncomputable def matrixMap {n m : ℕ} (A : Fin m → Fin n → ℤ) :
    C(Carrier n, Carrier m) :=
  ⟨fun x j => ∑ i : Fin n, A j i • x i,
    continuous_pi (fun j => continuous_finsetSum Finset.univ (fun i _ =>
      (continuous_apply i).zsmul (A j i)))⟩
lemma matrixMap_base {n m : ℕ} (A : Fin m → Fin n → ℤ) :
    matrixMap A (base n) = base m := by
  funext j
  simp [matrixMap, base]
noncomputable def matrixMapQuotientMap {n m : ℕ}
    (A : Fin m → Fin n → ℤ) : LoopQuot n → LoopQuot m :=
  fun q => (_root_.Path.Homotopic.Quotient.map q (matrixMap A)).cast
    (matrixMap_base A).symm (matrixMap_base A).symm
end FiniteTorusWinding

namespace CertifiedTorusPreimage
open Matrix
abbrev Vec (n : ℕ) := Fin n → ℤ
abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℤ
structure Certificate (m n : ℕ) where
  L : Mat m m
  Linv : Mat m m
  R : Mat n m
  T : Mat m n
  d : Vec m
def Certificate.Valid {m n : ℕ} (c : Certificate m n) (A : Mat m n) : Prop :=
  c.Linv * c.L = 1 ∧
  c.L * A = diagonal c.d * c.T ∧
  c.L * A * c.R = diagonal c.d ∧
  ∀ i, c.d i = 0 → ∀ j, c.T i j = 0
instance {m n : ℕ} (c : Certificate m n) (A : Mat m n) :
    Decidable (c.Valid A) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
def Certificate.transformed {m n : ℕ} (c : Certificate m n) (z : Vec m) : Vec m :=
  c.L.mulVec z
def Certificate.candidate {m n : ℕ} (c : Certificate m n) (z : Vec m) : Vec n :=
  c.R.mulVec (fun i => c.transformed z i / c.d i)
def Certificate.kernelGenerator {m n : ℕ} (c : Certificate m n) : Mat n n :=
  1 - c.R * c.T
def Certificate.firstFailure {m n : ℕ} (c : Certificate m n) (z : Vec m) :
    Option (Fin m) :=
  (List.finRange m).find? (fun i => decide (¬ c.d i ∣ c.transformed z i))
inductive Outcome (m n : ℕ) where
  | invalid
  | solved (x : Vec n)
  | obstructed (row : Fin m)
def solve {m n : ℕ} (A : Mat m n) (c : Certificate m n) (z : Vec m) : Outcome m n :=
  if c.Valid A then
    match c.firstFailure z with
    | none => .solved (c.candidate z)
    | some i => .obstructed i
  else .invalid
def Outcome.Correct {m n : ℕ} (A : Mat m n) (c : Certificate m n) (z : Vec m) :
    Outcome m n → Prop
  | .invalid => ¬ c.Valid A
  | .solved x => c.Valid A ∧ A.mulVec x = z ∧
      ∀ y, A.mulVec y = z ↔ ∃ v, y = x + c.kernelGenerator.mulVec v
  | .obstructed i => c.Valid A ∧ ¬ c.d i ∣ c.transformed z i ∧
      ¬ ∃ x, A.mulVec x = z
namespace Torus
open FiniteTorusWinding
def TopologicallyCorrect {m n : ℕ} (A : Mat m n) (c : Certificate m n)
    (z : Vec m) : Outcome m n → Prop
  | .invalid => ¬ c.Valid A
  | .solved x => c.Valid A ∧ matrixMapQuotientMap A (decode x) = decode z ∧
      ∀ q, matrixMapQuotientMap A q = decode z ↔
        ∃ v, q = decode (x + c.kernelGenerator.mulVec v)
  | .obstructed i => c.Valid A ∧ ¬ c.d i ∣ c.transformed z i ∧
      ¬ ∃ q, matrixMapQuotientMap A q = decode z
end Torus
end CertifiedTorusPreimage
end ComputationalPaths.Path.GeometricTopology

namespace TorusPreimageSubmission
open ComputationalPaths.Path.GeometricTopology.CertifiedTorusPreimage
/-- Each executed answer has its literal topological meaning; successful
answers parameterize every homotopy-class preimage, not just one witness. -/
theorem main_result {m n : ℕ} (A : Mat m n) :
    (∃ c : Certificate m n, c.Valid A) ∧
    ∀ (c : Certificate m n) (z : Vec m),
      Torus.TopologicallyCorrect A c z (solve A c z) := by
  sorry
end TorusPreimageSubmission
