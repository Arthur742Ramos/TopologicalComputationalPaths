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
equivalence.
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
      quotient_basepoint_change := by
        intro X _ x₀ x₁ p
        refine ⟨
          (QuotientFundamentalGroup.basepointChangeContinuousMulEquiv
            p).toHomeomorph,
          ?_⟩
        exact QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_apply p
      quotient_path_connected_basepoint_independent := by
        intro X _ _ x₀ x₁
        exact ⟨
          (QuotientFundamentalGroup.pathConnectedBasepointContinuousMulEquiv
            x₀ x₁).toHomeomorph⟩
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
    null_class_open := FiniteTorusWinding.isOpen_nullHomotopyClass n
    homotopy_classes_open := FiniteTorusWinding.isOpen_homotopyClass
    quotient_square := FiniteTorusWinding.loopQuotientProd_isQuotientMap n
    quotient_trans_continuous := FiniteTorusWinding.continuous_quotientTrans n
    quotient_symm_continuous := FiniteTorusWinding.continuous_quotientSymm n }⟩

end TopologicalComputationalPathsFollowup
