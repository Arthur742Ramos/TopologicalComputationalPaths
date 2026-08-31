import ComputationalPaths.Path.Topology.TopologicalWindingHomeomorph
import ComputationalPaths.Path.Topology.QuotientFundamentalGroup
import ComputationalPaths.Path.Topology.SemilocallySimplyConnected
import Mathlib.Topology.Homotopy.Product
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Finite-dimensional topological torus winding

For every `n`, genuine based loops in the finite product `(S¹)ⁿ`, modulo
endpoint-fixed homotopy, are classified by `Fin n → ℤ`.  The classification
is first proved algebraically by coordinate winding and explicit standard
loops, then upgraded to a homeomorphism for the compact-open/final quotient
topology.  In particular, the quotient is discrete, its quotient square is a
quotient map, and loop-class composition and reversal are continuous for the
ordinary product topology.  The classifier is also a continuous
multiplicative equivalence to the integer lattice (viewed through
`Multiplicative`), so quotient concatenation is commutative at the zero
basepoint and, by continuous basepoint transport, at every torus point.
The abelian target transport theorem further shows that the resulting
path-based lattice classifier at each point is independent of the explicit
path used to transport it.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open Set Topology
open scoped ContinuousMap Topology

noncomputable section

namespace FiniteTorusWinding

open ConcreteCircleWinding

attribute [local instance] _root_.Path.Homotopic.setoid

/-! The functorial quotient module keeps the fundamental-group instance local.
We reuse that exact instance here so the multiplicative certificate below is
definitionally the usual fundamental-group multiplication. -/
noncomputable local instance functorialLoopQuotGroup
    (X : Type*) [TopologicalSpace X] (x : X) :
    Group (QuotientFundamentalGroup.LoopQuot X x) :=
  QuotientFundamentalGroup.functorialLoopQuotGroup X x

/-- The `n`-dimensional torus as a finite product of additive circles. -/
abbrev Carrier (n : ℕ) : Type := Fin n → TopologicalCircle

/-- The all-zero basepoint of the finite torus. -/
noncomputable abbrev base (n : ℕ) : Carrier n := fun _ => 0

/-- Genuine compact-open based loops in the finite torus. -/
abbrev Loop (n : ℕ) : Type := _root_.Path (base n) (base n)

/-- Projection of a finite-torus loop to one circle coordinate. -/
noncomputable def coordinate {n : ℕ} (i : Fin n) (γ : Loop n) :
    ConcreteCircleWinding.TopologicalLoop :=
  γ.map (continuous_apply i)

/-- Coordinatewise winding vector. -/
noncomputable def winding {n : ℕ} (γ : Loop n) : Fin n → ℤ :=
  fun i => windingPath (coordinate i γ)

/-- The standard loop with a prescribed integer winding in each coordinate. -/
noncomputable def standardLoop {n : ℕ} (z : Fin n → ℤ) : Loop n :=
  _root_.Path.pi (fun i => ConcreteCircleWinding.standardLoop (z i))

@[simp] theorem coordinate_standardLoop {n : ℕ} (z : Fin n → ℤ) (i : Fin n) :
    coordinate i (standardLoop z) = ConcreteCircleWinding.standardLoop (z i) := by
  apply _root_.Path.ext
  funext t
  rfl

@[simp] theorem winding_standardLoop {n : ℕ} (z : Fin n → ℤ) :
    winding (standardLoop z) = z := by
  funext i
  simp [winding]

theorem winding_eq_of_homotopic {n : ℕ} {γ δ : Loop n}
    (h : γ.Homotopic δ) : winding γ = winding δ := by
  funext i
  exact windingPath_eq_of_homotopic (h.map ⟨_, continuous_apply i⟩)

theorem coordinate_pi_eq (γ : Loop n) :
    _root_.Path.pi (fun i => coordinate i γ) = γ := by
  apply _root_.Path.ext
  funext t
  funext i
  rfl

/-- Every finite-torus loop is endpoint-fixed homotopic to the coordinatewise
standard loop selected by its winding vector. -/
theorem standardLoop_homotopic {n : ℕ} (γ : Loop n) :
    (standardLoop (winding γ)).Homotopic γ := by
  have hcoord : ∀ i, (ConcreteCircleWinding.standardLoop (winding γ i)).Homotopic
      (coordinate i γ) := fun i => ConcreteCircleWinding.standardLoop_homotopic _
  have hpi :
      (_root_.Path.pi
        (fun i => ConcreteCircleWinding.standardLoop (winding γ i))).Homotopic
        (_root_.Path.pi (fun i => coordinate i γ)) := by
    refine ⟨_root_.Path.Homotopic.piHomotopy _ _ (fun i => ?_)⟩
    exact Classical.choice (hcoord i)
  simpa only [standardLoop, coordinate_pi_eq] using hpi

/-- Coordinate winding is a complete invariant of based finite-torus loops. -/
theorem homotopic_iff_winding_eq {n : ℕ} (γ δ : Loop n) :
    γ.Homotopic δ ↔ winding γ = winding δ := by
  constructor
  · exact winding_eq_of_homotopic
  · intro h
    exact (standardLoop_homotopic γ).symm.trans (h ▸ standardLoop_homotopic δ)

theorem coordinate_trans {n : ℕ} (i : Fin n) (γ δ : Loop n) :
    coordinate i (γ.trans δ) = (coordinate i γ).trans (coordinate i δ) := by
  exact _root_.Path.map_trans γ δ (continuous_apply i)

theorem winding_trans {n : ℕ} (γ δ : Loop n) :
    winding (γ.trans δ) = winding γ + winding δ := by
  funext i
  change windingPath (coordinate i (γ.trans δ)) = _
  rw [coordinate_trans, windingPath_trans]
  rfl

theorem winding_identity {n : ℕ} :
    winding (_root_.Path.refl (base n)) = 0 := by
  funext i
  change windingPath (coordinate i (_root_.Path.refl (base n))) = 0
  rw [show coordinate i (_root_.Path.refl (base n)) =
      _root_.Path.refl (0 : TopologicalCircle) by
    apply _root_.Path.ext
    funext t
    rfl]
  exact windingPath_refl

/-- Based finite-torus loop classes. -/
abbrev LoopQuot (n : ℕ) : Type :=
  _root_.Path.Homotopic.Quotient (base n) (base n)

/-- Winding descended to loop homotopy classes. -/
noncomputable def encode {n : ℕ} : LoopQuot n → Fin n → ℤ :=
  Quotient.lift winding (fun _ _ h => winding_eq_of_homotopic h)

/-- Standard loop class for an integer vector. -/
noncomputable def decode {n : ℕ} (z : Fin n → ℤ) : LoopQuot n :=
  Quotient.mk' (standardLoop z)

@[simp] theorem encode_decode {n : ℕ} (z : Fin n → ℤ) :
    encode (decode z) = z :=
  winding_standardLoop z

theorem decode_encode {n : ℕ} (x : LoopQuot n) : decode (encode x) = x := by
  refine Quotient.inductionOn x ?_
  intro γ
  exact Quotient.sound (standardLoop_homotopic γ)

/-- Algebraic classification of finite-torus loop classes. -/
noncomputable def equivIntVector (n : ℕ) : LoopQuot n ≃ (Fin n → ℤ) where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

/-- The additive-group structure transported from the integer winding lattice. -/
noncomputable instance loopQuotAddGroup (n : ℕ) : AddGroup (LoopQuot n) :=
  (equivIntVector n).addGroup

/-- Winding as an additive equivalence. -/
noncomputable def loopQuotAddEquivIntVector (n : ℕ) :
    LoopQuot n ≃+ (Fin n → ℤ) where
  toEquiv := equivIntVector n
  map_add' x y := by
    change encode (decode (encode x + encode y)) = encode x + encode y
    exact encode_decode _

theorem encode_trans {n : ℕ} (x y : LoopQuot n) :
    encode (_root_.Path.Homotopic.Quotient.trans x y) = encode x + encode y := by
  induction x using Quotient.ind with
  | _ γ =>
      induction y using Quotient.ind with
      | _ δ => exact winding_trans γ δ

/-- Under the transported additive structure, addition is exactly
concatenation of loop homotopy classes. -/
theorem quotientTrans_eq_add {n : ℕ} (x y : LoopQuot n) :
    _root_.Path.Homotopic.Quotient.trans x y = x + y := by
  apply (equivIntVector n).injective
  change encode (_root_.Path.Homotopic.Quotient.trans x y) = encode (x + y)
  rw [encode_trans]
  exact (loopQuotAddEquivIntVector n).map_add x y |>.symm

/-- The ordinary final quotient topology on finite-torus loop classes. -/
noncomputable instance loopQuotTopologicalSpace (n : ℕ) :
    TopologicalSpace (LoopQuot n) :=
  TopologicalSpace.coinduced (Quotient.mk' : Loop n → LoopQuot n) inferInstance

theorem continuous_coordinate {n : ℕ} (i : Fin n) :
    Continuous (coordinate i : Loop n → ConcreteCircleWinding.TopologicalLoop) := by
  apply continuous_induced_rng.2
  exact (ContinuousMap.continuous_postcomp ⟨_, continuous_apply i⟩).comp
    continuous_induced_dom

/-- Coordinate winding is continuous into the discrete integer-vector space. -/
theorem continuous_winding {n : ℕ} :
    Continuous (winding : Loop n → Fin n → ℤ) := by
  apply continuous_pi
  intro i
  exact ConcreteCircleWinding.continuous_windingPath.comp (continuous_coordinate i)

theorem continuous_encode {n : ℕ} :
    Continuous (encode : LoopQuot n → Fin n → ℤ) := by
  apply Continuous.quotient_lift
  exact continuous_winding

/-- The null-homotopy class is open in the compact-open finite-torus loop
space.  This is the exact hypothesis in the general quotient-topological
fundamental-group discreteness criterion. -/
theorem isOpen_nullHomotopyClass (n : ℕ) :
    IsOpen
      (QuotientFundamentalGroup.nullHomotopyClass (Carrier n) (base n)) := by
  have hopen :
      IsOpen (winding ⁻¹' ({0} : Set (Fin n → ℤ))) :=
    (isOpen_discrete _).preimage continuous_winding
  convert hopen using 1
  ext γ
  change γ.Homotopic (_root_.Path.refl (base n)) ↔ winding γ = 0
  rw [homotopic_iff_winding_eq, winding_identity]

/-- Finite-torus winding as a continuous complete invariant. -/
noncomputable def windingCompleteInvariant (n : ℕ) :
    ContinuousCompleteInvariant (Loop n) (LoopQuot n) (Fin n → ℤ) where
  quotient := Quotient.mk'
  quotient_isQuotientMap := isQuotientMap_quotient_mk'
  invariant := winding
  classifier := equivIntVector n
  classifier_quotient := rfl
  invariant_continuous := continuous_winding

/-- The finite-torus loop quotient is discrete. -/
noncomputable instance loopQuotDiscreteTopology (n : ℕ) :
    DiscreteTopology (LoopQuot n) :=
  QuotientFundamentalGroup.quotientDiscreteTopology
    (Carrier n) (base n) (isOpen_nullHomotopyClass n)

/-- Every based quotient fundamental group of a finite torus is discrete.
The zero-basepoint classification is transported to an arbitrary point along
the explicit path supplied by path-connectedness of the indexed product. -/
theorem loopQuotDiscreteTopology_at (n : ℕ) (x : Carrier n) :
    DiscreteTopology
      (QuotientFundamentalGroup.LoopQuot (Carrier n) x) := by
  let p : _root_.Path (base n) x := PathConnectedSpace.somePath (base n) x
  have hbase : DiscreteTopology (LoopQuot n) := loopQuotDiscreteTopology n
  have hpath := QuotientFundamentalGroup.quotientDiscreteTopology_iff_of_path p
  exact hpath.mp hbase

/-- Finite-dimensional tori are semilocally simply connected at every point,
as witnessed by the discrete quotient criterion. -/
theorem semilocallySimplyConnected (n : ℕ) :
    QuotientFundamentalGroup.SemilocallySimplyConnected (Carrier n) := by
  intro x
  letI : DiscreteTopology
      (QuotientFundamentalGroup.LoopQuot (Carrier n) x) :=
    loopQuotDiscreteTopology_at n x
  exact QuotientFundamentalGroup.semilocallySimplyConnectedAt_of_discreteTopology
    (Carrier n) x

/-- The quotient-topological fundamental group of `(S¹)ⁿ` is homeomorphic to
the discrete integer lattice `ℤⁿ`. -/
noncomputable def loopQuotHomeomorphIntVector (n : ℕ) :
    LoopQuot n ≃ₜ (Fin n → ℤ) :=
  (windingCompleteInvariant n).classifierHomeomorph

/-- Every based quotient fundamental group of a finite torus has the same
integer-lattice model.  The model at the all-zero basepoint is transported
along a path supplied by path-connectedness. -/
noncomputable def loopQuotHomeomorphIntVector_at (n : ℕ) (x : Carrier n) :
    QuotientFundamentalGroup.LoopQuot (Carrier n) x ≃ₜ (Fin n → ℤ) :=
  by
    letI : Group
        (QuotientFundamentalGroup.LoopQuot (Carrier n) (base n)) :=
      inferInstanceAs (Group (FundamentalGroup (Carrier n) (base n)))
    letI : Group
        (QuotientFundamentalGroup.LoopQuot (Carrier n) x) :=
      inferInstanceAs (Group (FundamentalGroup (Carrier n) x))
    exact
      ((QuotientFundamentalGroup.pathConnectedBasepointContinuousMulEquiv
          (X := Carrier n) (base n) x).toHomeomorph.symm).trans
        (loopQuotHomeomorphIntVector n)

/-- Winding is simultaneously an additive equivalence and a homeomorphism. -/
noncomputable def loopQuotContinuousAddEquivIntVector (n : ℕ) :
    LoopQuot n ≃ₜ+ (Fin n → ℤ) where
  __ := loopQuotAddEquivIntVector n
  continuous_toFun := continuous_encode
  continuous_invFun := continuous_of_discreteTopology

/-! The additive classifier above is also a classifier for the actual
fundamental-group multiplication.  `Multiplicative` is only a type synonym;
its multiplication is the addition of the integer lattice. -/

/-- The finite-torus quotient fundamental group is continuously isomorphic,
as a multiplicative group, to the integer lattice. -/
noncomputable def loopQuotContinuousMulEquivIntVector (n : ℕ) :
    LoopQuot n ≃ₜ* Multiplicative (Fin n → ℤ) :=
  ContinuousMulEquiv.mk' (loopQuotHomeomorphIntVector n) <| by
    intro x y
    change encode (x * y) = encode x + encode y
    change encode (_root_.Path.Homotopic.Quotient.trans y x) =
      encode x + encode y
    simpa [add_comm] using encode_trans y x

/-- The same integer-lattice model works at every torus basepoint, and the
basepoint transport is a continuous multiplicative equivalence. -/
noncomputable def loopQuotContinuousMulEquivIntVector_at
    (n : ℕ) (x : Carrier n) :
    QuotientFundamentalGroup.LoopQuot (Carrier n) x ≃ₜ*
      Multiplicative (Fin n → ℤ) := by
  exact
    (QuotientFundamentalGroup.pathConnectedBasepointContinuousMulEquiv
      (X := Carrier n) (base n) x).symm.trans
      (loopQuotContinuousMulEquivIntVector n)

/-- Concatenation of finite-torus loop classes is commutative. -/
theorem quotientTrans_comm {n : ℕ} (x y : LoopQuot n) :
    _root_.Path.Homotopic.Quotient.trans x y =
      _root_.Path.Homotopic.Quotient.trans y x := by
  apply (loopQuotHomeomorphIntVector n).injective
  change encode (_root_.Path.Homotopic.Quotient.trans x y) =
    encode (_root_.Path.Homotopic.Quotient.trans y x)
  rw [encode_trans, encode_trans, add_comm]

/-- The fundamental group of every finite torus is abelian, at every chosen
basepoint. -/
theorem quotientMul_comm_at (n : ℕ) (x : Carrier n)
    (p q : QuotientFundamentalGroup.LoopQuot (Carrier n) x) :
    p * q = q * p := by
  let e := loopQuotContinuousMulEquivIntVector_at n x
  apply e.injective
  calc
    e (p * q) = e p * e q := e.map_mul p q
    _ = e q * e p := mul_comm _ _
    _ = e (q * p) := (e.map_mul q p).symm

/-! A classifier may be built using any explicit path from the canonical
basepoint.  The abelian target theorem in the functorial quotient module
shows that this extra path choice is immaterial. -/

/-- Classifier at a chosen torus basepoint along an explicit path. -/
noncomputable def loopQuotContinuousMulEquivIntVector_at_path
    (n : ℕ) (x : Carrier n)
    (p : _root_.Path (base n) x) :
    QuotientFundamentalGroup.LoopQuot (Carrier n) x ≃ₜ*
      Multiplicative (Fin n → ℤ) :=
  (QuotientFundamentalGroup.basepointChangeContinuousMulEquiv p).symm.trans
    (loopQuotContinuousMulEquivIntVector n)

/-- The explicit-path lattice classifier is independent of the chosen path. -/
theorem loopQuotContinuousMulEquivIntVector_at_path_eq
    (n : ℕ) (x : Carrier n)
    (p q : _root_.Path (base n) x) :
    loopQuotContinuousMulEquivIntVector_at_path n x p =
      loopQuotContinuousMulEquivIntVector_at_path n x q := by
  have hpq :=
    QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_eq_of_target_comm
      p q (quotientMul_comm_at n x)
  simp only [loopQuotContinuousMulEquivIntVector_at_path]
  rw [hpq]

/-- Every finite-torus loop homotopy class is open in the compact-open loop
space. -/
theorem isOpen_homotopyClass {n : ℕ} (γ : Loop n) :
    IsOpen {δ : Loop n | γ.Homotopic δ} := by
  exact
    QuotientFundamentalGroup.isOpen_homotopyClass_of_isOpen_nullHomotopyClass
      (Carrier n) (base n) (isOpen_nullHomotopyClass n) γ

/-- Finite-torus loop homotopy as a Mathlib discrete quotient relation. -/
noncomputable def loopHomotopyDiscreteQuotient (n : ℕ) :
    DiscreteQuotient (Loop n) where
  toSetoid := _root_.Path.Homotopic.setoid (base n) (base n)
  isOpen_setOf_rel := isOpen_homotopyClass

/-- The square of the finite-torus loop quotient map is a quotient map. -/
theorem loopQuotientProd_isQuotientMap (n : ℕ) :
    IsQuotientMap
      (fun p : Loop n × Loop n =>
        ((Quotient.mk' p.1 : LoopQuot n), (Quotient.mk' p.2 : LoopQuot n))) := by
  exact QuotientFundamentalGroup.loopQuotientProd_isQuotientMap
    (Carrier n) (base n) (isOpen_nullHomotopyClass n)

/-- Loop-class composition is continuous for the ordinary product topology. -/
theorem continuous_quotientTrans (n : ℕ) :
    Continuous
      (fun p : LoopQuot n × LoopQuot n =>
        _root_.Path.Homotopic.Quotient.trans p.1 p.2) :=
  QuotientFundamentalGroup.continuous_quotientTrans
    (Carrier n) (base n) (isOpen_nullHomotopyClass n)

/-- Loop-class reversal is continuous. -/
theorem continuous_quotientSymm (n : ℕ) :
    Continuous
      (_root_.Path.Homotopic.Quotient.symm : LoopQuot n → LoopQuot n) :=
  QuotientFundamentalGroup.continuous_quotientSymm (Carrier n) (base n)

end FiniteTorusWinding

end
end GeometricTopology
end Path
end ComputationalPaths
