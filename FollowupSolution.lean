import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Homotopy.Product
import Mathlib.Topology.Homotopy.HSpaces
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Maps.OpenQuotient
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.Topology.Homotopy.Lifting
import ComputationalPaths

/-!
# Follow-up solution: quotient-topological fundamental groups

The general proof descends compact-open postcomposition, path conjugation,
and pointwise path products through quotient universal properties.  This
gives continuous induced homomorphisms, homeomorphism and basepoint
invariance, and a sharp product-preservation theorem.  The application uses
coordinatewise universal-cover winding: a local zero-chart contraction makes
winding locally constant, and finite products yield a continuous complete
invariant and the discrete quotient consequences.  For locally path-connected
spaces, it also supplies the finite compact-open subdivision and ladder proof
of openness of every homotopy class, hence the converse semilocal/discrete
equivalence.  The finite-torus certificate transports discreteness from the
zero basepoint to every point and records semilocal simple connectivity
globally, together with a common integer-lattice homeomorphism for every
based quotient.  It also identifies the actual quotient multiplication with
the lattice operation through a continuous `Multiplicative` equivalence, and
proves commutativity at every basepoint.  The finite-torus winding vector is
natural under coordinate-selection maps, with the core theorem allowing
arbitrary source and target dimensions.  The standard representatives and
quotient classifier satisfy the matching
reindexing equations as well.  The continuous multiplicative lattice
classifier satisfies the same reindexing law, including selections between
different finite dimensions.  The path-based classifier is also natural at
arbitrary torus basepoints after mapping the chosen transport path.
Abelian-target path independence yields the same statement for the canonical
classifier without exposing a path choice.
The lattice reindexings are also continuous additive morphisms with identity
and composition coherence.
Basepoint-change maps are additionally shown to depend only
on endpoint-fixed homotopy classes of paths, to act identically on constant
paths, and to compose along concatenated paths.
Reversing a path is proved to give the inverse transport, completing the
groupoid-action coherence.
The certificate also exposes preservation of path-class concatenation under
continuous maps and the associated naturality square for basepoint transport.
It also exposes the pointed conjugacy relation for homotopic maps.  The
topological-group boundary is likewise transported between any two basepoints
joined by a path.  A homotopy that fixes the chosen basepoint throughout
therefore gives equal induced based homomorphisms after endpoint casting.
More generally, the relative loop criterion exactly characterizes when two
transports agree; in an abelian target quotient, the same transport is independent of the
chosen path even when no endpoint-fixed homotopy between the paths is given.
On a path-connected space, the joint-continuity boundary can consequently be
checked at one basepoint or uniformly at all basepoints.  Discreteness and
the genuine topological-group structure satisfy the same one-point reduction,
the global continuity property is homotopy-invariant between path-connected
spaces, and locally path-connected path-connected spaces have a
one-basepoint semilocal criterion.  T1 separation is likewise invariant under
homotopy and path transport, reduces to one basepoint on path-connected
spaces, and is homotopy-invariant as a global property.
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
  semilocally_simply_connected_iff_quotient_discrete_at_of_path_connected :
    ∀ (X : Type u) [TopologicalSpace X]
      [LocallyPathConnectedSpace X] [PathConnectedSpace X] (x₀ : X),
      ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.SemilocallySimplyConnected X ↔
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
abbrev WindingVector (n : ℕ) : Type := Fin n → ℤ

/- Coordinate-selection maps between finite tori, used to state winding
   naturality without importing the substantive implementation. -/
noncomputable def coordinateProjection {n m : ℕ} (f : Fin m → Fin n) :
    C(FiniteTorus n, FiniteTorus m) :=
  ⟨fun x j => x (f j), continuous_pi (fun j => continuous_apply (f j))⟩

noncomputable def coordinateReindex {n m : ℕ} (f : Fin m → Fin n) :
    WindingVector n → WindingVector m :=
  fun z j => z (f j)

noncomputable instance loopQuotTopology (n : ℕ) :
    TopologicalSpace (LoopQuot n) :=
  TopologicalSpace.coinduced
    (Quotient.mk' : Loop n → LoopQuot n) inferInstance

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
      ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.LoopQuot
          (FiniteTorus n) x ≃ₜ* Multiplicative (WindingVector n)
  classifier_continuous_mul_equiv_at_path :
    ∀ (x : FiniteTorus n) (p : _root_.Path (base n) x),
      ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.LoopQuot
          (FiniteTorus n) x ≃ₜ* Multiplicative (WindingVector n)
  classifier_at_path_coordinate_projection :
    ∀ (f : Fin n → Fin n) (x : FiniteTorus n)
      (p : _root_.Path (base n) x)
      (q : ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.LoopQuot
        (FiniteTorus n) x),
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
      (q : ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.LoopQuot
        (FiniteTorus n) x),
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
      (p q : ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.LoopQuot
        (FiniteTorus n) x),
      p * q = q * p
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

open ComputationalPaths.Path.GeometricTopology

theorem main_result :
    Nonempty QuotientTopologicalFundamentalGroupTheory ∧
      ∀ n : ℕ, Nonempty (FiniteTorusTopologicalClassification n) := by
  constructor
  · exact ⟨{
      quotient_map_continuous :=
        by
          intro X Y _ _ f x
          exact QuotientFundamentalGroup.continuous_quotientMap f x
      quotient_map_id := by
        intro X _ x q
        exact QuotientFundamentalGroup.quotientMap_id x q
      quotient_map_comp := by
        intro X Y Z _ _ _ f g x q
        exact QuotientFundamentalGroup.quotientMap_comp f g x q
      quotient_map_trans := by
        intro X Y _ _ f x₀ x₁ x₂ P Q
        exact QuotientFundamentalGroup.quotientMap_trans f P Q
      quotient_homeomorph_invariant := by
        intro X Y _ _ e x
        refine ⟨
          (QuotientFundamentalGroup.homeomorphInducedContinuousMulEquiv
            e x).toHomeomorph,
          ?_⟩
        intro q
        rfl
      quotient_homotopy_equiv_invariant := by
        intro X Y _ _ e x
        refine ⟨
          (QuotientFundamentalGroup.homotopyEquivInducedContinuousMulEquiv
            e x).toHomeomorph,
          ?_⟩
        intro q
        rfl
      quotient_discrete_homotopy_invariant := by
        intro X Y _ _ e x
        exact
          QuotientFundamentalGroup.quotientDiscreteTopology_iff_of_homotopyEquiv
            e x
      quotient_discrete_basepoint_invariant := by
        intro X _ x₀ x₁ p
        exact QuotientFundamentalGroup.quotientDiscreteTopology_iff_of_path p
      quotient_trans_continuity_homotopy_invariant := by
        intro X Y _ _ e x
        exact
          QuotientFundamentalGroup.quotientTransContinuous_iff_of_homotopyEquiv
            e x
      quotient_trans_continuity_basepoint_invariant := by
        intro X _ x₀ x₁ p
        exact QuotientFundamentalGroup.quotientTransContinuous_iff_of_path p
      quotient_trans_continuity_all_basepoints := by
        intro X _ _ x₀
        exact
          QuotientFundamentalGroup.quotientTransContinuous_iff_forall_of_pathConnected
            x₀
      quotient_discrete_all_basepoints := by
        intro X _ _ x₀
        exact
          QuotientFundamentalGroup.quotientDiscreteTopology_iff_forall_of_pathConnected
            x₀
      quotient_t1_homotopy_invariant := by
        intro X Y _ _ e x
        exact
          QuotientFundamentalGroup.quotientT1Topology_iff_of_homotopyEquiv
            e x
      quotient_t1_basepoint_invariant := by
        intro X _ x₀ x₁ p
        exact QuotientFundamentalGroup.quotientT1Topology_iff_of_path p
      quotient_t1_all_basepoints := by
        intro X _ _ x₀
        exact
          QuotientFundamentalGroup.quotientT1Topology_iff_forall_of_pathConnected
            x₀
      quotient_t1_all_basepoints_homotopy_invariant := by
        intro X Y _ _ _ _ e x₀
        exact
          QuotientFundamentalGroup.quotientT1Topology_iff_forall_of_pathConnected_homotopyEquiv
            e x₀
      quotient_trans_continuity_all_basepoints_homotopy_invariant := by
        intro X Y _ _ _ _ e x₀
        exact
          QuotientFundamentalGroup.quotientTransContinuous_iff_forall_of_pathConnected_homotopyEquiv
            e x₀
      quotient_topological_group_all_basepoints := by
        intro X _ _ x₀
        exact
          QuotientFundamentalGroup.quotientContinuousMul_iff_forall_of_pathConnected
            x₀
      quotient_basepoint_change := by
        intro X _ x₀ x₁ p
        refine ⟨
          (QuotientFundamentalGroup.basepointChangeContinuousMulEquiv
            p).toHomeomorph,
          ?_⟩
        exact QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_apply p
      quotient_basepoint_change_homotopy_invariant := by
        intro X _ x₀ x₁ p q h z
        have he :=
          QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_eq_of_homotopic
            p q h
        have hz := congrArg (fun E => E z) he
        rw [QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_apply,
          QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_apply] at hz
        exact hz
      quotient_basepoint_change_relative_comm := by
        intro X _ x₀ x₁ p q hcentral z
        have he :=
          QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_eq_of_relative_comm
            p q hcentral
        have hz := congrArg (fun E => E z) he
        rw [QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_apply,
          QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_apply] at hz
        exact hz
      quotient_basepoint_change_relative_comm_iff := by
        intro X _ x₀ x₁ p q
        constructor
        · intro h z
          have he :
              QuotientFundamentalGroup.basepointChangeContinuousMulEquiv p =
                QuotientFundamentalGroup.basepointChangeContinuousMulEquiv q := by
            ext w
            rw [QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_apply,
              QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_apply]
            exact h w
          exact
            (QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_eq_iff_relative_comm
              p q).mp he z
        · intro h z
          have he :=
            (QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_eq_iff_relative_comm
              p q).mpr h
          have hz := congrArg (fun E => E z) he
          rw [QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_apply,
            QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_apply] at hz
          exact hz
      quotient_basepoint_change_target_comm := by
        intro X _ x₀ x₁ p q hcomm z
        have he :=
          QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_eq_of_target_comm
            p q hcomm
        have hz := congrArg (fun E => E z) he
        rw [QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_apply,
          QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_apply] at hz
        exact hz
      quotient_basepoint_change_composition := by
        intro X _ x₀ x₁ x₂ p q z
        have he :=
          QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_trans p q
        have hz := congrArg (fun E => E z) he
        rw [ContinuousMulEquiv.trans_apply,
          QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_apply,
          QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_apply,
          QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_apply] at hz
        exact hz
      quotient_basepoint_change_identity := by
        intro X _ x z
        have he :=
          QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_refl x
        have hz := congrArg (fun E => E z) he
        rw [QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_apply] at hz
        exact hz
      quotient_basepoint_change_reverse := by
        intro X _ x₀ x₁ p z
        have hsymm :=
          QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_symm p
        have hcancel :=
          (QuotientFundamentalGroup.basepointChangeContinuousMulEquiv p).apply_symm_apply z
        rw [hsymm] at hcancel
        rw [QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_apply,
          QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_apply] at hcancel
        change
          (( _root_.Path.Homotopic.Quotient.mk p.symm).trans
            (((_root_.Path.Homotopic.Quotient.mk p).trans z).trans
              (_root_.Path.Homotopic.Quotient.mk p.symm))).trans
            (_root_.Path.Homotopic.Quotient.mk p) = z
        simpa only [_root_.Path.symm_symm] using hcancel
      quotient_basepoint_change_naturality := by
        intro X Y _ _ f x₀ x₁ p q
        have hz :=
          QuotientFundamentalGroup.basepointChange_quotientMap_naturality
            p f q
        rw [QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_apply,
          QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_apply] at hz
        exact hz
      quotient_map_homotopy_naturality := by
        intro X Y _ _ f g H x q
        have hz :=
          QuotientFundamentalGroup.basepointChange_quotientMap_homotopy
            H x q
        rw [QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_apply] at hz
        exact hz
      quotient_map_eq_of_pointed_homotopy := by
        intro X Y _ _ f g H x hfix
        exact QuotientFundamentalGroup.quotientMap_eq_of_pointedHomotopy
          H x hfix
      quotient_path_connected_basepoint_independent := by
        intro X _ _ x₀ x₁
        exact ⟨
          (QuotientFundamentalGroup.pathConnectedBasepointContinuousMulEquiv
            x₀ x₁)⟩
      quotient_product_preserved := by
        intro X Y _ _ x y hprod
        change IsQuotientMap
          (QuotientFundamentalGroup.loopQuotientProdMap x y) at hprod
        refine ⟨
          QuotientFundamentalGroup.quotientProductHomeomorph x y hprod,
          ?_⟩
        intro q
        rfl
      quotient_product_hypothesis_sharp :=
        QuotientFundamentalGroup.not_isQuotientMap_loopQuotientProd_of_not_continuous
      quotient_symm_continuous :=
        QuotientFundamentalGroup.continuous_quotientSymm
      quotient_trans_left_continuous :=
        QuotientFundamentalGroup.continuous_quotientTrans_left
      quotient_trans_right_continuous :=
        QuotientFundamentalGroup.continuous_quotientTrans_right
      quotient_homogeneous :=
        QuotientFundamentalGroup.quotientHomogeneous
      quotient_discrete_iff_null_class_open :=
        QuotientFundamentalGroup.discreteTopology_iff_isOpen_nullHomotopyClass
      quotient_t1_iff_null_class_closed :=
        QuotientFundamentalGroup.t1Space_iff_isClosed_nullHomotopyClass
      quotient_t1_iff_all_classes_closed :=
        QuotientFundamentalGroup.t1Space_iff_all_homotopyClasses_closed
      quotient_discrete_implies_semilocally_simply_connected := by
        intro X _ x hdiscrete
        letI : DiscreteTopology (GenericLoopQuot X x) := hdiscrete
        exact QuotientFundamentalGroup.semilocallySimplyConnectedAt_of_discreteTopology
          X x
      quotient_discrete_iff_semilocally_simply_connected_in_locally_path_connected_spaces := by
        intro X _ _
        exact QuotientFundamentalGroup.semilocallySimplyConnected_iff_quotientDiscreteTopology X
      homotopy_classes_open_of_semilocally_simply_connected := by
        intro X _ _ hsemi x gamma
        exact QuotientFundamentalGroup.isOpen_homotopyClass_of_semilocallySimplyConnected
          X hsemi x gamma
      semilocally_simply_connected_homotopy_invariant := by
        intro X Y _ _ _ _ e
        exact
          QuotientFundamentalGroup.semilocallySimplyConnected_iff_of_homotopyEquiv
            X e
      semilocally_simply_connected_iff_quotient_discrete_at_of_path_connected := by
        intro X _ _ _ x₀
        exact
          QuotientFundamentalGroup.semilocallySimplyConnected_iff_quotientDiscreteTopology_at
            X x₀
      covering_map_induces_injection := by
        intro E B _ _ p hp e
        exact QuotientFundamentalGroup.inducedContinuousMonoidHom_injective_of_isCoveringMap
          hp e
      covering_map_image_is_monodromy_stabilizer := by
        intro E B _ _ p hp e q
        exact QuotientFundamentalGroup.mem_range_inducedContinuousMonoidHom_iff_monodromy_fixed
          hp e q
      quotient_topological_group_agreement :=
        QuotientFundamentalGroup.continuous_quotientTrans_iff_topologicalGroupStructure
      homotopy_classes_open_of_null_class_open :=
        QuotientFundamentalGroup.isOpen_homotopyClass_of_isOpen_nullHomotopyClass
      quotient_open_of_null_class_open :=
        QuotientFundamentalGroup.loopQuotient_isOpenQuotientMap
      quotient_square_of_null_class_open :=
        QuotientFundamentalGroup.loopQuotientProd_isQuotientMap
      quotient_trans_continuous_of_null_class_open :=
        QuotientFundamentalGroup.continuous_quotientTrans }⟩
  · intro n
    exact ⟨{
    winding := FiniteTorusWinding.winding
    winding_coordinate_projection := by
      intro f γ
      change FiniteTorusWinding.winding
          (γ.map (FiniteTorusWinding.coordinateProjection f).continuous) =
        fun j => FiniteTorusWinding.winding γ (f j)
      exact FiniteTorusWinding.winding_coordinateProjection f γ
    standard_loop_coordinate_projection := by
      intro f z
      change
        (FiniteTorusWinding.standardLoop z).map
            (FiniteTorusWinding.coordinateProjection f).continuous =
          FiniteTorusWinding.standardLoop (fun j => z (f j))
      exact FiniteTorusWinding.standardLoop_coordinateProjection f z
    classifier_coordinate_projection := by
      intro f q
      change FiniteTorusWinding.encode
          (_root_.Path.Homotopic.Quotient.map q
            (FiniteTorusWinding.coordinateProjection f)) =
        fun j => FiniteTorusWinding.encode q (f j)
      exact FiniteTorusWinding.encode_coordinateProjection f q
    standardLoop := FiniteTorusWinding.standardLoop
    classifier := FiniteTorusWinding.loopQuotHomeomorphIntVector n
    classifier_continuous_mul_equiv :=
      FiniteTorusWinding.loopQuotContinuousMulEquivIntVector n
    classifier_multiplicative_coordinate_projection := by
      intro f q
      change Multiplicative.ofAdd
          (FiniteTorusWinding.coordinateReindex f
            (FiniteTorusWinding.loopQuotHomeomorphIntVector n q)) =
        (FiniteTorusWinding.loopQuotContinuousMulEquivIntVector n)
          (_root_.Path.Homotopic.Quotient.map q
            (FiniteTorusWinding.coordinateProjection f))
      exact
        FiniteTorusWinding.loopQuotContinuousMulEquivIntVector_coordinateProjection
          f q
    classifier_continuous_mul_equiv_at := by
      intro x
      exact FiniteTorusWinding.loopQuotContinuousMulEquivIntVector_at n x
    classifier_continuous_mul_equiv_at_path := by
      intro x p
      exact FiniteTorusWinding.loopQuotContinuousMulEquivIntVector_at_path n x p
    classifier_at_path_coordinate_projection := by
      intro f x p q
      change
        (FiniteTorusWinding.loopQuotContinuousMulEquivIntVector_at_path n
          (FiniteTorusWinding.coordinateProjection f x)
          (p.map (FiniteTorusWinding.coordinateProjection f).continuous))
            (_root_.Path.Homotopic.Quotient.map q
              (FiniteTorusWinding.coordinateProjection f)) =
          Multiplicative.ofAdd
            (FiniteTorusWinding.coordinateReindex f
              (Multiplicative.toAdd
                ((FiniteTorusWinding.loopQuotContinuousMulEquivIntVector_at_path
                    n x p) q)))
      exact
        FiniteTorusWinding.loopQuotContinuousMulEquivIntVector_at_path_coordinateProjection
          f x p q
    classifier_at_coordinate_projection := by
      intro f x q
      change
        (FiniteTorusWinding.loopQuotContinuousMulEquivIntVector_at n
          (FiniteTorusWinding.coordinateProjection f x))
            (_root_.Path.Homotopic.Quotient.map q
              (FiniteTorusWinding.coordinateProjection f)) =
          Multiplicative.ofAdd
            (FiniteTorusWinding.coordinateReindex f
              (Multiplicative.toAdd
                ((FiniteTorusWinding.loopQuotContinuousMulEquivIntVector_at
                    n x) q)))
      exact
        FiniteTorusWinding.loopQuotContinuousMulEquivIntVector_at_coordinateProjection
          f x q
    classifier_continuous_mul_equiv_at_path_independent := by
      intro x p q
      exact FiniteTorusWinding.loopQuotContinuousMulEquivIntVector_at_path_eq n x p q
    quotient_mul_commutative := by
      intro x y
      change
        _root_.Path.Homotopic.Quotient.trans y x =
          _root_.Path.Homotopic.Quotient.trans x y
      exact FiniteTorusWinding.quotientTrans_comm y x
    quotient_mul_commutative_at := by
      intro x p q
      exact FiniteTorusWinding.quotientMul_comm_at n x p q
    classifier_at := FiniteTorusWinding.loopQuotHomeomorphIntVector_at n
    classifier_mk := by
      intro γ
      rfl
    winding_standard := FiniteTorusWinding.winding_standardLoop
    standard_complete := FiniteTorusWinding.standardLoop_homotopic
    winding_identity := FiniteTorusWinding.winding_identity
    winding_trans := FiniteTorusWinding.winding_trans
    classifier_trans := FiniteTorusWinding.encode_trans
    quotient_discrete := inferInstance
    quotient_discrete_at := FiniteTorusWinding.loopQuotDiscreteTopology_at n
    semilocally_simply_connected :=
      FiniteTorusWinding.semilocallySimplyConnected n
    null_class_open := FiniteTorusWinding.isOpen_nullHomotopyClass n
    homotopy_classes_open := FiniteTorusWinding.isOpen_homotopyClass
    quotient_square := FiniteTorusWinding.loopQuotientProd_isQuotientMap n
    quotient_trans_continuous := FiniteTorusWinding.continuous_quotientTrans n
    quotient_symm_continuous := FiniteTorusWinding.continuous_quotientSymm n }⟩

end TopologicalComputationalPathsFollowup
