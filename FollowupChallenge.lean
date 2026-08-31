import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Homotopy.Product
import Mathlib.Topology.Homotopy.HSpaces
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Maps.OpenQuotient
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.Topology.Homotopy.Lifting
import ComputationalPaths.Path.Topology.SemilocallySimplyConnected

/-!
# Follow-up challenge: quotient-topological fundamental groups

First prove that the compact-open based-loop quotient is functorial under
continuous maps, invariant under homeomorphism and change of basepoint along
a path, and preserves binary products whenever the product of the two loop
projections is a quotient map.  For every pointed space, prove that it is a
quasitopological group: reversal and both one-variable translations are
continuous.  Prove the exact criterion that this quotient is discrete if and
only if the null-homotopy class is open.  Derive open quotient projection,
the quotient-square property, and joint continuity of multiplication in the
positive case.

Then instantiate the criterion for every finite product of additive circles,
including an explicit winding classification by the integer lattice.
In locally path-connected spaces, also prove the converse finite-ladder
criterion: semilocal simple connectivity is equivalent to discreteness of
every based quotient fundamental group, and every based-loop homotopy class is
open.  The finite-torus certificate additionally exposes the all-basepoint
semilocal consequence and the all-basepoint integer-lattice classifier from
the basepoint-transport theorem.  The general certificate also records that
basepoint transport is independent of the chosen path representative up to
endpoint-fixed homotopy.
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

noncomputable local instance genericLoopQuotGroup
    (X : Type u) [TopologicalSpace X] (x : X) :
    Group (GenericLoopQuot X x) :=
  inferInstanceAs (Group (FundamentalGroup X x))

def nullHomotopyClass
    (X : Type u) [TopologicalSpace X] (x : X) : Set (GenericLoop X x) :=
  {γ | γ.Homotopic (_root_.Path.refl x)}

/-- Functorial, basepoint-invariant, product-compatible theory of the
quotient-topological fundamental group. -/
structure QuotientTopologicalFundamentalGroupTheory where
  quotient_map_continuous :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      (f : C(X, Y)) (x : X),
      Continuous
        (fun q : GenericLoopQuot X x =>
          _root_.Path.Homotopic.Quotient.map q f)
  quotient_map_id :
    ∀ (X : Type u) [TopologicalSpace X] (x : X)
      (q : GenericLoopQuot X x),
      _root_.Path.Homotopic.Quotient.map q (.id X) = q
  quotient_map_comp :
    ∀ (X Y Z : Type u)
      [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
      (f : C(X, Y)) (g : C(Y, Z)) (x : X)
      (q : GenericLoopQuot X x),
      _root_.Path.Homotopic.Quotient.map
          (_root_.Path.Homotopic.Quotient.map q f) g =
        _root_.Path.Homotopic.Quotient.map q (g.comp f)
  quotient_homeomorph_invariant :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      (e : X ≃ₜ Y) (x : X),
      ∃ E : GenericLoopQuot X x ≃ₜ GenericLoopQuot Y (e x),
        ∀ q : GenericLoopQuot X x,
          E q = _root_.Path.Homotopic.Quotient.map q ⟨e, e.continuous⟩
  quotient_homotopy_equiv_invariant :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      (e : ContinuousMap.HomotopyEquiv X Y) (x : X),
      ∃ E : GenericLoopQuot X x ≃ₜ GenericLoopQuot Y (e x),
        ∀ q : GenericLoopQuot X x,
          E q = _root_.Path.Homotopic.Quotient.map q e.toFun
  quotient_discrete_homotopy_invariant :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      (e : ContinuousMap.HomotopyEquiv X Y) (x : X),
      DiscreteTopology (GenericLoopQuot X x) ↔
        DiscreteTopology (GenericLoopQuot Y (e x))
  quotient_discrete_basepoint_invariant :
    ∀ (X : Type u) [TopologicalSpace X]
      {x₀ x₁ : X} (p : _root_.Path x₀ x₁),
      DiscreteTopology (GenericLoopQuot X x₀) ↔
        DiscreteTopology (GenericLoopQuot X x₁)
  quotient_trans_continuity_homotopy_invariant :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      (e : ContinuousMap.HomotopyEquiv X Y) (x : X),
      Continuous
          (fun p : GenericLoopQuot X x × GenericLoopQuot X x =>
            _root_.Path.Homotopic.Quotient.trans p.1 p.2) ↔
        Continuous
          (fun p : GenericLoopQuot Y (e x) × GenericLoopQuot Y (e x) =>
            _root_.Path.Homotopic.Quotient.trans p.1 p.2)
  quotient_basepoint_change :
    ∀ (X : Type u) [TopologicalSpace X] {x₀ x₁ : X}
      (p : _root_.Path x₀ x₁),
      ∃ E : GenericLoopQuot X x₀ ≃ₜ GenericLoopQuot X x₁,
        ∀ q : GenericLoopQuot X x₀,
          E q =
            _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (Quotient.mk' p.symm) q)
              (Quotient.mk' p)
  quotient_basepoint_change_homotopy_invariant :
    ∀ (X : Type u) [TopologicalSpace X] {x₀ x₁ : X}
      (p q : _root_.Path x₀ x₁),
      p.Homotopic q →
        ∀ z : GenericLoopQuot X x₀,
          _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (Quotient.mk' p.symm) z)
              (Quotient.mk' p) =
            _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (Quotient.mk' q.symm) z)
              (Quotient.mk' q)
  quotient_path_connected_basepoint_independent :
    ∀ (X : Type u) [TopologicalSpace X] [PathConnectedSpace X]
      (x₀ x₁ : X),
      Nonempty (GenericLoopQuot X x₀ ≃ₜ GenericLoopQuot X x₁)
  quotient_product_preserved :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      (x : X) (y : Y),
      IsQuotientMap
          (fun p : GenericLoop X x × GenericLoop Y y =>
            ((Quotient.mk' p.1 : GenericLoopQuot X x),
              (Quotient.mk' p.2 : GenericLoopQuot Y y))) →
        ∃ E : (GenericLoopQuot X x × GenericLoopQuot Y y) ≃ₜ
            GenericLoopQuot (X × Y) (x, y),
          ∀ q : GenericLoopQuot X x × GenericLoopQuot Y y,
            E q = _root_.Path.Homotopic.prod q.1 q.2
  quotient_product_hypothesis_sharp :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      (¬ Continuous
        (fun p : GenericLoopQuot X x × GenericLoopQuot X x =>
          _root_.Path.Homotopic.Quotient.trans p.1 p.2)) →
      ¬ IsQuotientMap
        (fun p : GenericLoop X x × GenericLoop X x =>
          ((Quotient.mk' p.1 : GenericLoopQuot X x),
            (Quotient.mk' p.2 : GenericLoopQuot X x)))
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
  quotient_t1_iff_null_class_closed :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      T1Space (GenericLoopQuot X x) ↔
        IsClosed (nullHomotopyClass X x)
  quotient_t1_iff_all_classes_closed :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      T1Space (GenericLoopQuot X x) ↔
        ∀ γ : GenericLoop X x,
          IsClosed {δ : GenericLoop X x | γ.Homotopic δ}
  quotient_discrete_implies_semilocally_simply_connected :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      DiscreteTopology (GenericLoopQuot X x) →
        ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.SemilocallySimplyConnectedAt
          X x
  quotient_discrete_iff_semilocally_simply_connected_in_locally_path_connected_spaces :
    ∀ (X : Type u) [TopologicalSpace X]
      [LocallyPathConnectedSpace X],
      ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.SemilocallySimplyConnected X ↔
        ∀ x : X, DiscreteTopology (GenericLoopQuot X x)
  homotopy_classes_open_of_semilocally_simply_connected :
    ∀ (X : Type u) [TopologicalSpace X]
      [LocallyPathConnectedSpace X],
      ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.SemilocallySimplyConnected X →
        ∀ x : X, ∀ γ : GenericLoop X x,
          IsOpen {δ : GenericLoop X x | γ.Homotopic δ}
  semilocally_simply_connected_homotopy_invariant :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      [LocallyPathConnectedSpace X] [LocallyPathConnectedSpace Y]
      (e : ContinuousMap.HomotopyEquiv X Y),
      ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.SemilocallySimplyConnected X ↔
        ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.SemilocallySimplyConnected Y
  covering_map_induces_injection :
    ∀ (E B : Type u) [TopologicalSpace E] [TopologicalSpace B]
      (p : E → B) (hp : IsCoveringMap p) (e : E),
      Function.Injective
        (fun q : GenericLoopQuot E e =>
          _root_.Path.Homotopic.Quotient.map q ⟨p, hp.continuous⟩)
  covering_map_image_is_monodromy_stabilizer :
    ∀ (E B : Type u) [TopologicalSpace E] [TopologicalSpace B]
      (p : E → B) (hp : IsCoveringMap p) (e : E)
      (q : GenericLoopQuot B (p e)),
      q ∈ Set.range (fun r : GenericLoopQuot E e =>
          _root_.Path.Homotopic.Quotient.map r ⟨p, hp.continuous⟩) ↔
        hp.monodromy q ⟨e, rfl⟩ = ⟨e, rfl⟩
  quotient_topological_group_agreement :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      Continuous
          (fun p : GenericLoopQuot X x × GenericLoopQuot X x =>
            _root_.Path.Homotopic.Quotient.trans p.1 p.2) ↔
        Nonempty (ContinuousMul (GenericLoopQuot X x))
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
  classifier_at :
    ∀ x : FiniteTorus n,
      ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.LoopQuot
          (FiniteTorus n) x ≃ₜ WindingVector n
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
  quotient_discrete_at :
    ∀ x : FiniteTorus n,
      DiscreteTopology
        (ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.LoopQuot
          (FiniteTorus n) x)
  semilocally_simply_connected :
    ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.SemilocallySimplyConnected
      (FiniteTorus n)
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
