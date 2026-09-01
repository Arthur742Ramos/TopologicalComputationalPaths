import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Homotopy.Product
import Mathlib.Topology.Homotopy.HSpaces
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Maps.OpenQuotient
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Follow-up challenge: quotient-topological fundamental groups

This statement-side module exposes the selected certificate: finite-torus
winding classification together with rectangular lattice-cokernel composition,
Smith-normal-form, determinant-index, and prime-power torsion profiles.  The
challenge deliberately imports only Mathlib and allowed packages so Palomar can
compile it in a clean canonical environment.
-/
namespace TopologicalComputationalPathsFollowup
open Set Topology
open scoped ContinuousMap Topology
open scoped BigOperators
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

/-! The challenge intentionally contains only statement-side definitions.  In
    particular, these aliases avoid depending on the candidate's compiled
    `ComputationalPaths` library when Palomar compiles the challenge in its
    clean scratch environment. -/

def semilocallySimplyConnectedAt
    (X : Type u) [TopologicalSpace X] (x : X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∀ γ : GenericLoop X x, Set.range γ ⊆ U →
      γ.Homotopic (_root_.Path.refl x)

def semilocallySimplyConnected
    (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ x : X, semilocallySimplyConnectedAt X x

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
  quotient_map_trans :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      (f : C(X, Y)) {x₀ x₁ x₂ : X}
      (P : _root_.Path.Homotopic.Quotient x₀ x₁)
      (Q : _root_.Path.Homotopic.Quotient x₁ x₂),
      _root_.Path.Homotopic.Quotient.map
          (_root_.Path.Homotopic.Quotient.trans P Q) f =
        _root_.Path.Homotopic.Quotient.trans
          (_root_.Path.Homotopic.Quotient.map P f)
          (_root_.Path.Homotopic.Quotient.map Q f)
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
  quotient_trans_continuity_basepoint_invariant :
    ∀ (X : Type u) [TopologicalSpace X] {x₀ x₁ : X}
      (p : _root_.Path x₀ x₁),
      Continuous
          (fun q : GenericLoopQuot X x₀ × GenericLoopQuot X x₀ =>
            _root_.Path.Homotopic.Quotient.trans q.1 q.2) ↔
        Continuous
          (fun q : GenericLoopQuot X x₁ × GenericLoopQuot X x₁ =>
            _root_.Path.Homotopic.Quotient.trans q.1 q.2)
  quotient_trans_continuity_all_basepoints :
    ∀ (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] (x₀ : X),
      Continuous
          (fun q : GenericLoopQuot X x₀ × GenericLoopQuot X x₀ =>
            _root_.Path.Homotopic.Quotient.trans q.1 q.2) ↔
        ∀ x : X, Continuous
          (fun q : GenericLoopQuot X x × GenericLoopQuot X x =>
            _root_.Path.Homotopic.Quotient.trans q.1 q.2)
  quotient_discrete_all_basepoints :
    ∀ (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] (x₀ : X),
      DiscreteTopology (GenericLoopQuot X x₀) ↔
        ∀ x : X, DiscreteTopology (GenericLoopQuot X x)
  quotient_t1_homotopy_invariant :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      (e : ContinuousMap.HomotopyEquiv X Y) (x : X),
      T1Space (GenericLoopQuot X x) ↔
        T1Space (GenericLoopQuot Y (e x))
  quotient_t1_basepoint_invariant :
    ∀ (X : Type u) [TopologicalSpace X] {x₀ x₁ : X}
      (p : _root_.Path x₀ x₁),
      T1Space (GenericLoopQuot X x₀) ↔
        T1Space (GenericLoopQuot X x₁)
  quotient_t1_all_basepoints :
    ∀ (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] (x₀ : X),
      T1Space (GenericLoopQuot X x₀) ↔
        ∀ x : X, T1Space (GenericLoopQuot X x)
  quotient_t1_all_basepoints_homotopy_invariant :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      [PathConnectedSpace X] [PathConnectedSpace Y]
      (e : ContinuousMap.HomotopyEquiv X Y) (x₀ : X),
      (∀ x : X, T1Space (GenericLoopQuot X x)) ↔
        ∀ y : Y, T1Space (GenericLoopQuot Y y)
  quotient_trans_continuity_all_basepoints_homotopy_invariant :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      [PathConnectedSpace X] [PathConnectedSpace Y]
      (e : ContinuousMap.HomotopyEquiv X Y) (x₀ : X),
      (∀ x : X, Continuous
        (fun q : GenericLoopQuot X x × GenericLoopQuot X x =>
          _root_.Path.Homotopic.Quotient.trans q.1 q.2)) ↔
        ∀ y : Y, Continuous
          (fun q : GenericLoopQuot Y y × GenericLoopQuot Y y =>
            _root_.Path.Homotopic.Quotient.trans q.1 q.2)
  quotient_topological_group_all_basepoints :
    ∀ (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] (x₀ : X),
      Nonempty (ContinuousMul (GenericLoopQuot X x₀)) ↔
        ∀ x : X, Nonempty (ContinuousMul (GenericLoopQuot X x))
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
  quotient_basepoint_change_relative_comm :
    ∀ (X : Type u) [TopologicalSpace X] {x₀ x₁ : X}
      (p q : _root_.Path x₀ x₁),
      (∀ b : GenericLoopQuot X x₁,
        _root_.Path.Homotopic.Quotient.trans
            (_root_.Path.Homotopic.Quotient.trans
              (Quotient.mk' p.symm) (Quotient.mk' q)) b =
          _root_.Path.Homotopic.Quotient.trans b
            (_root_.Path.Homotopic.Quotient.trans
              (Quotient.mk' p.symm) (Quotient.mk' q))) →
        ∀ z : GenericLoopQuot X x₀,
          _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (Quotient.mk' p.symm) z)
              (Quotient.mk' p) =
            _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (Quotient.mk' q.symm) z)
              (Quotient.mk' q)
  quotient_basepoint_change_relative_comm_iff :
    ∀ (X : Type u) [TopologicalSpace X] {x₀ x₁ : X}
      (p q : _root_.Path x₀ x₁),
      (∀ z : GenericLoopQuot X x₀,
        _root_.Path.Homotopic.Quotient.trans
            (_root_.Path.Homotopic.Quotient.trans
              (Quotient.mk' p.symm) z)
              (Quotient.mk' p) =
          _root_.Path.Homotopic.Quotient.trans
            (_root_.Path.Homotopic.Quotient.trans
              (Quotient.mk' q.symm) z)
            (Quotient.mk' q)) ↔
      (∀ b : GenericLoopQuot X x₁,
        _root_.Path.Homotopic.Quotient.trans
            (_root_.Path.Homotopic.Quotient.trans
              (Quotient.mk' p.symm) (Quotient.mk' q)) b =
          _root_.Path.Homotopic.Quotient.trans b
            (_root_.Path.Homotopic.Quotient.trans
              (Quotient.mk' p.symm) (Quotient.mk' q)))
  quotient_basepoint_change_target_comm :
    ∀ (X : Type u) [TopologicalSpace X] {x₀ x₁ : X}
      (p q : _root_.Path x₀ x₁),
      (∀ a b : GenericLoopQuot X x₁, a * b = b * a) →
        ∀ z : GenericLoopQuot X x₀,
          _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (Quotient.mk' p.symm) z)
              (Quotient.mk' p) =
            _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (Quotient.mk' q.symm) z)
              (Quotient.mk' q)
  quotient_basepoint_change_composition :
    ∀ (X : Type u) [TopologicalSpace X]
      {x₀ x₁ x₂ : X} (p : _root_.Path x₀ x₁) (q : _root_.Path x₁ x₂),
      ∀ z : GenericLoopQuot X x₀,
        _root_.Path.Homotopic.Quotient.trans
            (_root_.Path.Homotopic.Quotient.trans
              (Quotient.mk' q.symm)
              (_root_.Path.Homotopic.Quotient.trans
                (_root_.Path.Homotopic.Quotient.trans
                  (Quotient.mk' p.symm) z)
                (Quotient.mk' p)))
            (Quotient.mk' q) =
            _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (Quotient.mk' (p.trans q).symm) z)
              (Quotient.mk' (p.trans q))
  quotient_basepoint_change_identity :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      ∀ z : GenericLoopQuot X x,
        _root_.Path.Homotopic.Quotient.trans
            (_root_.Path.Homotopic.Quotient.trans
              (Quotient.mk' (_root_.Path.refl x)) z)
            (Quotient.mk' (_root_.Path.refl x)) = z
  quotient_basepoint_change_reverse :
    ∀ (X : Type u) [TopologicalSpace X]
      {x₀ x₁ : X} (p : _root_.Path x₀ x₁),
      ∀ z : GenericLoopQuot X x₁,
        _root_.Path.Homotopic.Quotient.trans
            (_root_.Path.Homotopic.Quotient.trans
              (Quotient.mk' p.symm)
              (_root_.Path.Homotopic.Quotient.trans
                (_root_.Path.Homotopic.Quotient.trans
                  (Quotient.mk' p) z)
                (Quotient.mk' p.symm)))
            (Quotient.mk' p) = z
  quotient_basepoint_change_naturality :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      (f : C(X, Y)) {x₀ x₁ : X} (p : _root_.Path x₀ x₁)
      (q : GenericLoopQuot X x₀),
      _root_.Path.Homotopic.Quotient.map
          (_root_.Path.Homotopic.Quotient.trans
            (_root_.Path.Homotopic.Quotient.trans
              (Quotient.mk' p.symm) q)
            (Quotient.mk' p)) f =
        _root_.Path.Homotopic.Quotient.trans
          (_root_.Path.Homotopic.Quotient.trans
            (Quotient.mk' (p.map f.continuous).symm)
            (_root_.Path.Homotopic.Quotient.map q f))
          (Quotient.mk' (p.map f.continuous))
  quotient_map_homotopy_naturality :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      {f g : C(X, Y)} (H : f.Homotopy g) (x : X)
      (q : GenericLoopQuot X x),
      _root_.Path.Homotopic.Quotient.trans
          (_root_.Path.Homotopic.Quotient.trans
            (Quotient.mk' (H.evalAt x).symm)
            (_root_.Path.Homotopic.Quotient.map q f))
            (Quotient.mk' (H.evalAt x)) =
        _root_.Path.Homotopic.Quotient.map q g
  quotient_map_eq_of_pointed_homotopy :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      {f g : C(X, Y)} (H : f.Homotopy g) (x : X)
      (hfix : ∀ t : unitInterval, H (t, x) = f x),
      FundamentalGroup.mapOfEq f
          (show f x = g x by
            exact (hfix 1).symm.trans (H.apply_one x)) =
        FundamentalGroup.map g x
  quotient_path_connected_basepoint_independent :
    ∀ (X : Type u) [TopologicalSpace X] [PathConnectedSpace X]
      (x₀ x₁ : X),
      Nonempty (GenericLoopQuot X x₀ ≃ₜ* GenericLoopQuot X x₁)
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
        semilocallySimplyConnectedAt X x
  quotient_discrete_iff_semilocally_simply_connected_in_locally_path_connected_spaces :
    ∀ (X : Type u) [TopologicalSpace X]
      [LocallyPathConnectedSpace X],
      semilocallySimplyConnected X ↔
        ∀ x : X, DiscreteTopology (GenericLoopQuot X x)
  homotopy_classes_open_of_semilocally_simply_connected :
    ∀ (X : Type u) [TopologicalSpace X]
      [LocallyPathConnectedSpace X],
      semilocallySimplyConnected X →
        ∀ x : X, ∀ γ : GenericLoop X x,
          IsOpen {δ : GenericLoop X x | γ.Homotopic δ}
  semilocally_simply_connected_homotopy_invariant :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      [LocallyPathConnectedSpace X] [LocallyPathConnectedSpace Y]
      (e : ContinuousMap.HomotopyEquiv X Y),
      semilocallySimplyConnected X ↔
        semilocallySimplyConnected Y
  semilocally_simply_connected_iff_quotient_discrete_at_of_path_connected :
    ∀ (X : Type u) [TopologicalSpace X]
      [LocallyPathConnectedSpace X] [PathConnectedSpace X] (x₀ : X),
      semilocallySimplyConnected X ↔
        DiscreteTopology (GenericLoopQuot X x₀)
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
abbrev BasepointLoopQuot (n : ℕ) (x : FiniteTorus n) : Type :=
  _root_.Path.Homotopic.Quotient x x
abbrev WindingVector (n : ℕ) : Type := Fin n → ℤ
/-! Matrix actions are the canonical Mathlib linear maps, viewed additively. -/
noncomputable def matrixAction {n m : ℕ} (A : Fin m → Fin n → ℤ) :
    (Fin n → ℤ) →+ (Fin m → ℤ) := (Matrix.mulVecLin A).toAddMonoidHom
def matrixCompose {n m k : ℕ}
    (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ) :
    Fin k → Fin n → ℤ :=
  fun l i => ∑ j : Fin m, B l j * A j i
/-- Coordinate-selection maps between finite tori, used to state winding
naturality without importing the substantive implementation. -/
noncomputable def coordinateProjection {n m : ℕ} (f : Fin m → Fin n) :
    C(FiniteTorus n, FiniteTorus m) :=
  ⟨fun x j => x (f j), continuous_pi (fun j => continuous_apply (f j))⟩
noncomputable def coordinateReindex {n m : ℕ} (f : Fin m → Fin n) :
    WindingVector n → WindingVector m :=
  fun z j => z (f j)

/-! Integer matrices act on the finite torus itself, not only on its winding
    lattice.  The endpoint cast in the quotient map is kept explicit so that
    the selected certificate can state the actual topological naturality
    square. -/
noncomputable def matrixMap {n m : ℕ} (A : Fin m → Fin n → ℤ) :
    C(FiniteTorus n, FiniteTorus m) :=
  ⟨fun x j => ∑ i : Fin n, A j i • x i,
    continuous_pi (fun j =>
      continuous_finsetSum Finset.univ (fun i _ =>
        (continuous_apply i).zsmul (A j i)))⟩

lemma matrixMap_base {n m : ℕ} (A : Fin m → Fin n → ℤ) :
    matrixMap A (base n) = base m := by
  funext j
  simp [matrixMap, base]

noncomputable def matrixMapQuotientMap {n m : ℕ}
    (A : Fin m → Fin n → ℤ) : LoopQuot n → LoopQuot m :=
  fun q =>
    (_root_.Path.Homotopic.Quotient.map q (matrixMap A)).cast
      (matrixMap_base A).symm (matrixMap_base A).symm

/-! Smith factors are copied into the standalone statement surface so the
    Comparator challenge can expose the arithmetic criterion without
    importing the substantive project implementation. -/
noncomputable def smithNormalFormFactor
    {m r : ℕ} {N : Submodule ℤ (Fin m → ℤ)}
    (snf : Module.Basis.SmithNormalForm N (Fin m) r) (i : Fin m) : ℤ :=
  if h : i ∈ Set.range snf.f then snf.a (Classical.choose h) else 0

noncomputable def smithFactor {n m : ℕ} (A : Fin m → Fin n → ℤ) (i : Fin m) : ℤ := smithNormalFormFactor (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m)) (matrixAction A).range.toIntSubmodule).2 i

noncomputable instance loopQuotTopology (n : ℕ) :
    TopologicalSpace (LoopQuot n) :=
  TopologicalSpace.coinduced
    (Quotient.mk' : Loop n → LoopQuot n) inferInstance
noncomputable instance basepointLoopQuotTopology (n : ℕ) (x : FiniteTorus n) :
    TopologicalSpace (BasepointLoopQuot n x) :=
  TopologicalSpace.coinduced
    (Quotient.mk' : _root_.Path x x → BasepointLoopQuot n x) inferInstance
/-- Full publication-facing certificate for the finite-torus theorem. -/
structure FiniteTorusTopologicalClassification (n : ℕ) where
  winding : Loop n → WindingVector n
  winding_coordinate_projection :
    ∀ (f : Fin n → Fin n) (γ : Loop n),
      winding (γ.map (coordinateProjection f).continuous) =
        fun j => winding γ (f j)
  standardLoop : WindingVector n → Loop n
  standard_loop_coordinate_projection :
    ∀ (f : Fin n → Fin n) (z : WindingVector n),
      (standardLoop z).map (coordinateProjection f).continuous =
        standardLoop (fun j => z (f j))
  classifier : LoopQuot n ≃ₜ WindingVector n
  classifier_coordinate_projection :
    ∀ (f : Fin n → Fin n) (q : LoopQuot n),
      classifier (_root_.Path.Homotopic.Quotient.map q (coordinateProjection f)) =
        fun j => classifier q (f j)
  classifier_continuous_mul_equiv :
    LoopQuot n ≃ₜ* Multiplicative (WindingVector n)
  classifier_multiplicative_coordinate_projection :
    ∀ (f : Fin n → Fin n) (q : LoopQuot n),
      Multiplicative.ofAdd (coordinateReindex f (classifier q)) =
        classifier_continuous_mul_equiv
          (_root_.Path.Homotopic.Quotient.map q (coordinateProjection f))
  classifier_continuous_mul_equiv_at :
    ∀ x : FiniteTorus n,
      BasepointLoopQuot n x ≃ₜ* Multiplicative (WindingVector n)
  classifier_continuous_mul_equiv_at_path :
    ∀ (x : FiniteTorus n) (p : _root_.Path (base n) x),
      BasepointLoopQuot n x ≃ₜ* Multiplicative (WindingVector n)
  classifier_at_path_coordinate_projection :
    ∀ (f : Fin n → Fin n) (x : FiniteTorus n)
      (p : _root_.Path (base n) x)
      (q : BasepointLoopQuot n x),
      classifier_continuous_mul_equiv_at_path
          (coordinateProjection f x)
          (p.map (coordinateProjection f).continuous)
          (_root_.Path.Homotopic.Quotient.map q (coordinateProjection f)) =
        Multiplicative.ofAdd
          (coordinateReindex f
            (Multiplicative.toAdd
              (classifier_continuous_mul_equiv_at_path x p q)))
  classifier_at_coordinate_projection :
    ∀ (f : Fin n → Fin n) (x : FiniteTorus n)
      (q : BasepointLoopQuot n x),
      classifier_continuous_mul_equiv_at
          (coordinateProjection f x)
          (_root_.Path.Homotopic.Quotient.map q (coordinateProjection f)) =
        Multiplicative.ofAdd
          (coordinateReindex f
            (Multiplicative.toAdd
              (classifier_continuous_mul_equiv_at x q)))
  classifier_continuous_mul_equiv_at_path_independent :
    ∀ (x : FiniteTorus n) (p q : _root_.Path (base n) x),
      classifier_continuous_mul_equiv_at_path x p =
        classifier_continuous_mul_equiv_at_path x q
  quotient_mul_commutative :
    ∀ x y : LoopQuot n, x * y = y * x
  quotient_mul_commutative_at :
    ∀ (x : FiniteTorus n)
      (p q : BasepointLoopQuot n x),
      p * q = q * p
  classifier_at :
    ∀ x : FiniteTorus n,
      BasepointLoopQuot n x ≃ₜ WindingVector n
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
        (BasepointLoopQuot n x)
  semilocally_simply_connected :
    semilocallySimplyConnected (FiniteTorus n)
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
  matrix_cokernel_short_exact :
    ∀ (A B : Fin n → Fin n → ℤ) (hB : Matrix.det B ≠ 0),
      ∃ f : (Fin n → ℤ) ⧸ (matrixAction A).range →+
          (Fin n → ℤ) ⧸ (matrixAction (matrixCompose A B)).range,
      ∃ g : (Fin n → ℤ) ⧸ (matrixAction (matrixCompose A B)).range →+
          (Fin n → ℤ) ⧸ (matrixAction B).range,
      ∃ e : (((Fin n → ℤ) ⧸ (matrixAction (matrixCompose A B)).range) ⧸ g.ker) ≃+
          (Fin n → ℤ) ⧸ (matrixAction B).range,
        Function.Injective f ∧ g.ker = f.range ∧ Function.Surjective g
  matrix_cokernel_rectangular_short_exact :
    ∀ {n m k : ℕ} (A : Fin m → Fin n → ℤ)
      (B : Fin k → Fin m → ℤ)
      (hB : Function.Injective (matrixAction B)),
      ∃ f : (Fin m → ℤ) ⧸ (matrixAction A).range →+
          (Fin k → ℤ) ⧸
            (matrixAction (matrixCompose A B)).range,
      ∃ g : (Fin k → ℤ) ⧸
          (matrixAction (matrixCompose A B)).range →+
          (Fin k → ℤ) ⧸ (matrixAction B).range,
      ∃ e : (((Fin k → ℤ) ⧸
          (matrixAction (matrixCompose A B)).range) ⧸ g.ker) ≃+
          (Fin k → ℤ) ⧸ (matrixAction B).range,
        Function.Injective f ∧ g.ker = f.range ∧ Function.Surjective g
  matrix_cokernel_exponent_lcm_dvd :
    ∀ (A B : Fin n → Fin n → ℤ)
      (hB : Function.Injective (matrixAction B)),
      Nat.lcm
          (AddMonoid.exponent ((Fin n → ℤ) ⧸ (matrixAction A).range))
          (AddMonoid.exponent ((Fin n → ℤ) ⧸ (matrixAction B).range)) ∣
        AddMonoid.exponent
          ((Fin n → ℤ) ⧸ (matrixAction (matrixCompose A B)).range)
  matrix_cokernel_rectangular_exponent_lcm_dvd :
    ∀ {n m k : ℕ} (A : Fin m → Fin n → ℤ)
      (B : Fin k → Fin m → ℤ)
      (hB : Function.Injective (matrixAction B)),
      Nat.lcm
          (AddMonoid.exponent ((Fin m → ℤ) ⧸ (matrixAction A).range))
          (AddMonoid.exponent ((Fin k → ℤ) ⧸ (matrixAction B).range)) ∣
        AddMonoid.exponent
          ((Fin k → ℤ) ⧸ (matrixAction (matrixCompose A B)).range)
  matrix_cokernel_exponent_eq_mul_of_coprime :
    ∀ (A B : Fin n → Fin n → ℤ)
      (hB : Function.Injective (matrixAction B))
      (hcop : Nat.Coprime
        (AddMonoid.exponent ((Fin n → ℤ) ⧸ (matrixAction A).range))
        (AddMonoid.exponent ((Fin n → ℤ) ⧸ (matrixAction B).range))),
      AddMonoid.exponent
          ((Fin n → ℤ) ⧸ (matrixAction (matrixCompose A B)).range) =
        AddMonoid.exponent ((Fin n → ℤ) ⧸ (matrixAction A).range) *
          AddMonoid.exponent ((Fin n → ℤ) ⧸ (matrixAction B).range)
  matrix_cokernel_rectangular_exponent_eq_mul_of_coprime :
    ∀ {n m k : ℕ} (A : Fin m → Fin n → ℤ)
      (B : Fin k → Fin m → ℤ)
      (hB : Function.Injective (matrixAction B))
      (hcop : Nat.Coprime
        (AddMonoid.exponent ((Fin m → ℤ) ⧸ (matrixAction A).range))
        (AddMonoid.exponent ((Fin k → ℤ) ⧸ (matrixAction B).range))),
      AddMonoid.exponent
          ((Fin k → ℤ) ⧸ (matrixAction (matrixCompose A B)).range) =
        AddMonoid.exponent ((Fin m → ℤ) ⧸ (matrixAction A).range) *
          AddMonoid.exponent ((Fin k → ℤ) ⧸ (matrixAction B).range)
  matrix_cokernel_exponent_eq_mul_of_det_coprime :
    ∀ (A B : Fin n → Fin n → ℤ) (hB : Matrix.det B ≠ 0)
      (hcop : Nat.Coprime (Matrix.det A).natAbs (Matrix.det B).natAbs),
      AddMonoid.exponent
          ((Fin n → ℤ) ⧸ (matrixAction (matrixCompose A B)).range) =
        AddMonoid.exponent ((Fin n → ℤ) ⧸ (matrixAction A).range) *
          AddMonoid.exponent ((Fin n → ℤ) ⧸ (matrixAction B).range)
  matrix_cokernel_exponent_prime_dvd_iff :
    ∀ (A B : Fin n → Fin n → ℤ)
      (hB : Function.Injective (matrixAction B)) (p : ℕ)
      (hp : Nat.Prime p),
      p ∣ AddMonoid.exponent
          ((Fin n → ℤ) ⧸ (matrixAction (matrixCompose A B)).range) ↔
        p ∣ AddMonoid.exponent ((Fin n → ℤ) ⧸ (matrixAction A).range) ∨
          p ∣ AddMonoid.exponent ((Fin n → ℤ) ⧸ (matrixAction B).range)
  matrix_cokernel_rectangular_exponent_prime_dvd_iff :
    ∀ {n m k : ℕ} (A : Fin m → Fin n → ℤ)
      (B : Fin k → Fin m → ℤ)
      (hB : Function.Injective (matrixAction B)) (p : ℕ)
      (hp : Nat.Prime p),
      p ∣ AddMonoid.exponent
          ((Fin k → ℤ) ⧸ (matrixAction (matrixCompose A B)).range) ↔
        p ∣ AddMonoid.exponent ((Fin m → ℤ) ⧸ (matrixAction A).range) ∨
          p ∣ AddMonoid.exponent ((Fin k → ℤ) ⧸ (matrixAction B).range)
  matrix_cokernel_exponent_prime_dvd_iff_of_det_ne_zero :
    ∀ (A B : Fin n → Fin n → ℤ) (hB : Matrix.det B ≠ 0)
      (p : ℕ) (hp : Nat.Prime p),
      p ∣ AddMonoid.exponent
          ((Fin n → ℤ) ⧸ (matrixAction (matrixCompose A B)).range) ↔
        p ∣ AddMonoid.exponent ((Fin n → ℤ) ⧸ (matrixAction A).range) ∨
          p ∣ AddMonoid.exponent ((Fin n → ℤ) ⧸ (matrixAction B).range)
  matrix_cokernel_exponent_eq_smithFactorLcm :
    ∀ {n m : ℕ} (A : Fin m → Fin n → ℤ),
      AddMonoid.exponent
          ((Fin m → ℤ) ⧸ (matrixAction A).range.toIntSubmodule) =
        Finset.univ.lcm (fun i : Fin m =>
          (smithNormalFormFactor (Submodule.smithNormalForm
            (Pi.basisFun ℤ (Fin m))
            (matrixAction A).range.toIntSubmodule).2 i).natAbs)
  matrix_cokernel_exponent_factorization_eq_smithFactor_sup :
    ∀ {n m : ℕ} (A : Fin m → Fin n → ℤ)
      (h : ∀ i : Fin m, smithFactor A i ≠ 0) (p : ℕ),
      (AddMonoid.exponent ((Fin m → ℤ) ⧸ (matrixAction A).range.toIntSubmodule)).factorization p =
        Finset.univ.sup (fun i : Fin m => (smithFactor A i).natAbs.factorization p)
  matrix_cokernel_addOrderOf_factorization_eq_smithCoordinate_sup :
    ∀ {n m : ℕ} (A : Fin m → Fin n → ℤ)
      (h : ∀ i : Fin m, smithFactor A i ≠ 0) (x : Fin m → ℤ) (p : ℕ),
      (addOrderOf (Submodule.Quotient.mk x :
        (Fin m → ℤ) ⧸ (matrixAction A).range.toIntSubmodule)).factorization p =
        Finset.univ.sup (fun i : Fin m =>
          (addOrderOf (Int.quotientSpanEquivZMod (smithFactor A i)
            (Submodule.Quotient.mk
              (((Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
                (matrixAction A).range.toIntSubmodule).2.bM.equivFun x) i)))).factorization p)
  matrix_cokernel_exponent_prime_dvd_iff_smithFactor :
    ∀ (A : Fin n → Fin n → ℤ) (p : ℕ) (hp : Nat.Prime p),
      p ∣ AddMonoid.exponent
          ((Fin n → ℤ) ⧸ (matrixAction A).range) ↔
        ∃ i : Fin n, p ∣ (smithNormalFormFactor
          (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin n))
            (matrixAction A).range.toIntSubmodule).2 i).natAbs
  matrix_cokernel_rectangular_exponent_prime_dvd_iff_smithFactor :
    ∀ {n m : ℕ} (A : Fin m → Fin n → ℤ) (p : ℕ)
      (hp : Nat.Prime p),
      p ∣ AddMonoid.exponent
          ((Fin m → ℤ) ⧸ (matrixAction A).range.toIntSubmodule) ↔
        ∃ i : Fin m, p ∣ (smithNormalFormFactor
          (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
            (matrixAction A).range.toIntSubmodule).2 i).natAbs

/-! This is the selected, self-contained follow-up certificate.  Its first
    field is a family of complete winding classifiers: each classifier agrees
    with the concrete winding invariant on representatives, identifies
    quotient concatenation with lattice addition through a continuous
    equivalence into the multiplicative lattice model, and intertwines the
    induced matrix map on finite-torus loop quotients with the integer matrix
    action.  It also records exact image, injectivity, and surjectivity
    transfer, including the square determinant criteria.  The remaining
    fields record the rectangular lattice exactness, Smith decomposition,
    determinant index, and prime-power torsion consequences.  Every type in
    this declaration is defined above or supplied by Mathlib, so the canonical
    challenge does not depend on candidate-local compiled modules. -/
structure FiniteTorusWindingMatrixCompatibility where
  winding : ∀ n : ℕ, Loop n → WindingVector n
  standardLoop : ∀ n : ℕ, WindingVector n → Loop n
  classifier : ∀ n : ℕ, LoopQuot n ≃ₜ Multiplicative (WindingVector n)
  classifier_mk :
    ∀ (n : ℕ) (γ : Loop n),
      Multiplicative.toAdd (classifier n (Quotient.mk' γ)) = winding n γ
  winding_standard :
    ∀ (n : ℕ) (z : WindingVector n), winding n (standardLoop n z) = z
  standard_complete :
    ∀ (n : ℕ) (γ : Loop n),
      (standardLoop n (winding n γ)).Homotopic γ
  winding_identity :
    ∀ (n : ℕ), winding n (_root_.Path.refl (base n)) = 0
  winding_trans :
    ∀ (n : ℕ) (γ δ : Loop n),
      winding n (γ.trans δ) = winding n γ + winding n δ
  classifier_trans :
    ∀ (n : ℕ) (x y : LoopQuot n),
      Multiplicative.toAdd (classifier n (_root_.Path.Homotopic.Quotient.trans x y)) =
        Multiplicative.toAdd (classifier n x) + Multiplicative.toAdd (classifier n y)
  classifier_matrix_map :
    ∀ {n m : ℕ} (A : Fin m → Fin n → ℤ) (q : LoopQuot n),
      Multiplicative.toAdd (classifier m (matrixMapQuotientMap A q)) =
        matrixAction A (Multiplicative.toAdd (classifier n q))
  matrix_map_composition :
    ∀ {n m k : ℕ} (A : Fin m → Fin n → ℤ)
      (B : Fin k → Fin m → ℤ) (q : LoopQuot n),
      matrixMapQuotientMap B (matrixMapQuotientMap A q) =
        matrixMapQuotientMap (matrixCompose A B) q
  matrix_map_image_iff :
    ∀ {n m : ℕ} (A : Fin m → Fin n → ℤ) (q : LoopQuot m),
      q ∈ Set.range (matrixMapQuotientMap A) ↔
        Multiplicative.toAdd (classifier m q) ∈ Set.range (matrixAction A)
  matrix_map_injective_iff :
    ∀ {n m : ℕ} (A : Fin m → Fin n → ℤ),
      Function.Injective (matrixMapQuotientMap A) ↔
        Function.Injective (matrixAction A)
  matrix_map_surjective_iff :
    ∀ {n m : ℕ} (A : Fin m → Fin n → ℤ),
      Function.Surjective (matrixMapQuotientMap A) ↔
        Function.Surjective (matrixAction A)
  matrix_map_injective_iff_det_ne_zero :
    ∀ {n : ℕ} (A : Fin n → Fin n → ℤ),
      Function.Injective (matrixMapQuotientMap A) ↔ Matrix.det A ≠ 0
  matrix_map_surjective_iff_isUnit_det :
    ∀ {n : ℕ} (A : Fin n → Fin n → ℤ),
      Function.Surjective (matrixMapQuotientMap A) ↔ IsUnit (Matrix.det A)

structure TopologicalSmithExactnessCertificate where
  winding_matrix_compatibility :
    Nonempty FiniteTorusWindingMatrixCompatibility
  matrix_composition :
    ∀ {n m k : ℕ} (A : Fin m → Fin n → ℤ)
      (B : Fin k → Fin m → ℤ) (z : Fin n → ℤ),
      matrixAction B (matrixAction A z) =
        matrixAction (matrixCompose A B) z
  rectangular_composition_profile :
    ∀ {n m k : ℕ} (A : Fin m → Fin n → ℤ)
      (B : Fin k → Fin m → ℤ)
      (_hB : Function.Injective (matrixAction B)),
      Nat.card ((Fin m → ℤ) ⧸ (matrixAction A).range) *
          Nat.card ((Fin k → ℤ) ⧸ (matrixAction B).range) =
        Nat.card ((Fin k → ℤ) ⧸
          ((matrixAction B).comp (matrixAction A)).range) ∧
      ((Finite ((Fin m → ℤ) ⧸ (matrixAction A).range) ∧
          Finite ((Fin k → ℤ) ⧸ (matrixAction B).range)) ↔
        Finite ((Fin k → ℤ) ⧸
          ((matrixAction B).comp (matrixAction A)).range)) ∧
      (∀ (p : ℕ) (_hp : Nat.Prime p),
        p ∣ AddMonoid.exponent
            ((Fin k → ℤ) ⧸ ((matrixAction B).comp (matrixAction A)).range) ↔
          p ∣ AddMonoid.exponent ((Fin m → ℤ) ⧸ (matrixAction A).range) ∨
            p ∣ AddMonoid.exponent ((Fin k → ℤ) ⧸ (matrixAction B).range)) ∧
      (∀ (_hcop : Nat.Coprime
          (AddMonoid.exponent ((Fin m → ℤ) ⧸ (matrixAction A).range))
          (AddMonoid.exponent ((Fin k → ℤ) ⧸ (matrixAction B).range))),
        AddMonoid.exponent
            ((Fin k → ℤ) ⧸ ((matrixAction B).comp (matrixAction A)).range) =
          AddMonoid.exponent ((Fin m → ℤ) ⧸ (matrixAction A).range) *
            AddMonoid.exponent ((Fin k → ℤ) ⧸ (matrixAction B).range))
  smith_cokernel_profile :
    ∀ {n m : ℕ} (A : Fin m → Fin n → ℤ),
      Nonempty
          (((Fin m → ℤ) ⧸ (matrixAction A).range.toIntSubmodule) ≃+
            (∀ i : Fin m, ZMod (smithNormalFormFactor
              (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
                (matrixAction A).range.toIntSubmodule).2 i).natAbs)) ∧
      (Finite ((Fin m → ℤ) ⧸ (matrixAction A).range.toIntSubmodule) ↔
        Module.finrank ℤ ((matrixAction A).range.toIntSubmodule) =
          Module.finrank ℤ (Fin m → ℤ)) ∧
      (AddMonoid.exponent
          ((Fin m → ℤ) ⧸ (matrixAction A).range.toIntSubmodule) =
        Finset.univ.lcm (fun i : Fin m =>
          (smithNormalFormFactor
            (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
              (matrixAction A).range.toIntSubmodule).2 i).natAbs)) ∧
      (∀ (p : ℕ) (_hp : Nat.Prime p),
        p ∣ AddMonoid.exponent
            ((Fin m → ℤ) ⧸ (matrixAction A).range.toIntSubmodule) ↔
          ∃ i : Fin m, p ∣ (smithNormalFormFactor
            (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
              (matrixAction A).range.toIntSubmodule).2 i).natAbs)
  determinant_index :
    ∀ {n : ℕ} (A : Fin n → Fin n → ℤ)
      (hA : Matrix.det A ≠ 0),
      Nat.card ((Fin n → ℤ) ⧸ (matrixAction A).range.toIntSubmodule) =
        Int.natAbs (Matrix.det A)
  prime_power_torsion_profile :
    ∀ {n m : ℕ} (A : Fin m → Fin n → ℤ)
      (_hA : ∀ i : Fin m, smithNormalFormFactor
        (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
          (matrixAction A).range.toIntSubmodule).2 i ≠ 0),
      Nonempty
          (((Fin m → ℤ) ⧸ (matrixAction A).range.toIntSubmodule) ≃+
            (∀ i : Fin m, ∀ p : (smithNormalFormFactor
              (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
                (matrixAction A).range.toIntSubmodule).2 i).natAbs.primeFactors,
              ZMod (p ^ ((smithNormalFormFactor
                (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
                  (matrixAction A).range.toIntSubmodule).2 i).natAbs.factorization p)))) ∧
        Nat.card ((Fin m → ℤ) ⧸ (matrixAction A).range.toIntSubmodule) =
          ∏ i : Fin m, ∏ p : (smithNormalFormFactor
            (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
              (matrixAction A).range.toIntSubmodule).2 i).natAbs.primeFactors,
            (p : ℕ) ^ ((smithNormalFormFactor
              (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
                (matrixAction A).range.toIntSubmodule).2 i).natAbs.factorization p)
/-- The substantive topological--Smith composition-and-classification theorem
    selected by Comparator. -/
theorem topological_smith_exactness :
    Nonempty TopologicalSmithExactnessCertificate := by
  sorry

end TopologicalComputationalPathsFollowup
