import ComputationalPaths.Path.Topology.ConcreteTorusWinding
import ComputationalPaths.Path.Topology.ContinuousCompleteInvariant
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.DiscreteQuotient
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Topological winding homeomorphisms

The circle and torus winding modules classify based loop homotopy classes as
types.  This file strengthens those classifications topologically.  The
homotopy quotients carry their final quotient topologies, and the winding
invariants are locally constant for the compact-open topology on path spaces.

For the circle, local constancy is proved geometrically.  A loop `δ` sufficiently
close to a fixed loop `γ` has pointwise difference `δ - γ` inside the standard
punctured-circle chart around zero.  Contracting the unique real chart lift of
that difference gives an explicit endpoint-fixed homotopy from `γ` to `δ`.
Consequently the quotient loop space is discrete and winding is a
homeomorphism with `ℤ`.  The torus statement follows coordinatewise.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open Set Topology
open scoped ContinuousMap Topology

noncomputable section

namespace ConcreteCircleWinding

attribute [local instance] _root_.Path.Homotopic.setoid

/-- The based circle loop space before quotienting by endpoint-fixed homotopy. -/
abbrev TopologicalLoop : Type :=
  _root_.Path (0 : TopologicalCircle) (0 : TopologicalCircle)

/-- The ordinary quotient topology on based circle-loop homotopy classes. -/
noncomputable instance topologicalLoopQuotTopologicalSpace :
    TopologicalSpace TopologicalLoopQuot :=
  TopologicalSpace.coinduced
    (Quotient.mk' : TopologicalLoop → TopologicalLoopQuot) inferInstance

/-- Pointwise additive difference of two based circle loops. -/
noncomputable def loopDifference
    (γ δ : TopologicalLoop) : C(unitInterval, TopologicalCircle) :=
  δ.toContinuousMap - γ.toContinuousMap

theorem continuous_loopDifference (γ : TopologicalLoop) :
    Continuous (fun δ : TopologicalLoop => loopDifference γ δ) := by
  exact continuous_induced_dom.sub continuous_const

/-- Zero lies in the target of the standard chart centred at zero. -/
theorem zero_mem_circleChart_target :
    (0 : TopologicalCircle) ∈ (circleChart 0).target := by
  rw [circleChart_target]
  exact circleCover_ne_cut 0

@[simp] theorem circleCover_zero : circleCover 0 = (0 : TopologicalCircle) := by
  simpa using circleCover_intCast 0

@[simp] theorem circleChart_zero_inv_zero :
    (circleChart 0).invFun (0 : TopologicalCircle) = 0 := by
  have hzero : (0 : ℝ) ∈ (circleChart 0).source := by
    rw [circleChart_source]
    constructor <;> norm_num [cut]
  have h := (circleChart 0).left_inv hzero
  simpa [circleChart, circleCover] using h

/-- The real chart lift of a pointwise-small loop difference. -/
noncomputable def localDifferenceLift
    (γ δ : TopologicalLoop)
    (hsmall : Set.range (loopDifference γ δ) ⊆ (circleChart 0).target) :
    C(unitInterval, ℝ) where
  toFun t := (circleChart 0).invFun (loopDifference γ δ t)
  continuous_toFun := by
    apply continuousOn_univ.mp
    exact (circleChart 0).continuousOn_invFun.comp
      ((loopDifference γ δ).continuous.continuousOn)
      (fun t _ => hsmall ⟨t, rfl⟩)

theorem circleCover_localDifferenceLift
    (γ δ : TopologicalLoop)
    (hsmall : Set.range (loopDifference γ δ) ⊆ (circleChart 0).target)
    (t : unitInterval) :
    circleCover (localDifferenceLift γ δ hsmall t) = loopDifference γ δ t := by
  have hright := (circleChart 0).right_inv (hsmall ⟨t, rfl⟩)
  simp [localDifferenceLift, circleChart, circleCover] at hright ⊢

@[simp] theorem localDifferenceLift_zero
    (γ δ : TopologicalLoop)
    (hsmall : Set.range (loopDifference γ δ) ⊆ (circleChart 0).target) :
    localDifferenceLift γ δ hsmall 0 = 0 := by
  change (circleChart 0).invFun (δ 0 - γ 0) = 0
  rw [δ.source, γ.source]
  simp

@[simp] theorem localDifferenceLift_one
    (γ δ : TopologicalLoop)
    (hsmall : Set.range (loopDifference γ δ) ⊆ (circleChart 0).target) :
    localDifferenceLift γ δ hsmall 1 = 0 := by
  change (circleChart 0).invFun (δ 1 - γ 1) = 0
  rw [δ.target, γ.target]
  simp

/-- Loops whose pointwise difference stays in the zero chart are homotopic
relative to their endpoints. -/
theorem homotopic_of_difference_range_subset
    (γ δ : TopologicalLoop)
    (hsmall : Set.range (loopDifference γ δ) ⊆ (circleChart 0).target) :
    γ.Homotopic δ := by
  refine ⟨{
    toFun := fun st =>
      γ st.2 + circleCover ((st.1 : ℝ) * localDifferenceLift γ δ hsmall st.2)
    continuous_toFun := by
      exact (γ.continuous.comp continuous_snd).add
        (continuous_circleCover.comp
          ((continuous_subtype_val.comp continuous_fst).mul
            ((localDifferenceLift γ δ hsmall).continuous.comp continuous_snd)))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    simp
  · intro t
    change γ t + circleCover (1 * localDifferenceLift γ δ hsmall t) = δ t
    rw [one_mul, circleCover_localDifferenceLift]
    simp [loopDifference]
  · intro s t ht
    rcases ht with rfl | ht
    · simp
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      simp

/-- Compact-open neighborhood in which winding is forced to be constant. -/
def windingNeighborhood (γ : TopologicalLoop) : Set TopologicalLoop :=
  {δ | Set.range (loopDifference γ δ) ⊆ (circleChart 0).target}

theorem isOpen_windingNeighborhood (γ : TopologicalLoop) :
    IsOpen (windingNeighborhood γ) := by
  have hopen :
      IsOpen {f : C(unitInterval, TopologicalCircle) |
        Set.range f ⊆ (circleChart 0).target} :=
    ContinuousMap.isOpen_setOf_range_subset (circleChart 0).open_target
  exact hopen.preimage (continuous_loopDifference γ)

theorem mem_windingNeighborhood_self (γ : TopologicalLoop) :
    γ ∈ windingNeighborhood γ := by
  intro x hx
  rcases hx with ⟨t, rfl⟩
  simpa [loopDifference] using zero_mem_circleChart_target

/-- Winding is locally constant on the compact-open based loop space. -/
theorem isLocallyConstant_windingPath :
    IsLocallyConstant (windingPath : TopologicalLoop → ℤ) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro γ
  refine ⟨windingNeighborhood γ, isOpen_windingNeighborhood γ,
    mem_windingNeighborhood_self γ, ?_⟩
  intro δ hδ
  exact windingPath_eq_of_homotopic
    (homotopic_of_difference_range_subset γ δ hδ).symm

/-- Circle loops are homotopic exactly when their winding numbers agree. -/
theorem homotopic_iff_windingPath_eq (γ δ : TopologicalLoop) :
    γ.Homotopic δ ↔ windingPath γ = windingPath δ := by
  constructor
  · exact windingPath_eq_of_homotopic
  · intro h
    exact (standardLoop_homotopic γ).symm.trans (h ▸ standardLoop_homotopic δ)

/-- Every based circle-loop homotopy class is open in the compact-open loop
space.  Thus endpoint-fixed homotopy is a discrete quotient relation. -/
theorem isOpen_homotopyClass (γ : TopologicalLoop) :
    IsOpen {δ : TopologicalLoop | γ.Homotopic δ} := by
  rw [isOpen_iff_forall_mem_open]
  intro δ hγδ
  refine ⟨windingNeighborhood δ, ?_, isOpen_windingNeighborhood δ,
    mem_windingNeighborhood_self δ⟩
  intro ε hδε
  exact hγδ.trans (homotopic_of_difference_range_subset δ ε hδε)

/-- Based circle-loop homotopy, viewed as a Mathlib `DiscreteQuotient`. -/
noncomputable def loopHomotopyDiscreteQuotient :
    DiscreteQuotient TopologicalLoop where
  toSetoid := _root_.Path.Homotopic.setoid 0 0
  isOpen_setOf_rel := isOpen_homotopyClass

theorem continuous_windingPath :
    Continuous (windingPath : TopologicalLoop → ℤ) :=
  isLocallyConstant_windingPath.continuous

/-- Winding is continuous from the quotient topology on based loop classes. -/
theorem continuous_topologicalWinding :
    Continuous (topologicalWinding : TopologicalLoopQuot → ℤ) := by
  apply Continuous.quotient_lift
  exact continuous_windingPath

/-- Winding is a continuous complete invariant of the final circle-loop
quotient. -/
noncomputable def windingCompleteInvariant :
    ContinuousCompleteInvariant TopologicalLoop TopologicalLoopQuot ℤ where
  quotient := Quotient.mk'
  quotient_isQuotientMap := isQuotientMap_quotient_mk'
  invariant := windingPath
  classifier := topologicalLoopQuotEquivInt
  classifier_quotient := rfl
  invariant_continuous := continuous_windingPath

/-- The quotient-topologized circle fundamental group is discrete. -/
noncomputable instance topologicalLoopQuotDiscreteTopology :
    DiscreteTopology TopologicalLoopQuot :=
  windingCompleteInvariant.quotientDiscreteTopology

/-- Topological winding is a homeomorphism from the quotient loop space to
the discrete integers. -/
noncomputable def topologicalLoopQuotHomeomorphInt :
    TopologicalLoopQuot ≃ₜ ℤ :=
  windingCompleteInvariant.classifierHomeomorph

/-- The product of two circle loop-quotient maps is quotient. -/
theorem loopQuotientProd_isQuotientMap :
    Topology.IsQuotientMap
      (fun p : TopologicalLoop × TopologicalLoop =>
        ((Quotient.mk' p.1 : TopologicalLoopQuot),
          (Quotient.mk' p.2 : TopologicalLoopQuot))) := by
  change Topology.IsQuotientMap
    (Prod.map windingCompleteInvariant.quotient
      windingCompleteInvariant.quotient)
  exact windingCompleteInvariant.quotientProd_isQuotientMap

/-- Composition of circle loop classes is continuous for the ordinary
product topology. -/
theorem continuous_quotientTrans :
    Continuous
      (fun p : TopologicalLoopQuot × TopologicalLoopQuot =>
        _root_.Path.Homotopic.Quotient.trans p.1 p.2) :=
  continuous_of_discreteTopology

/-- Reversal of circle loop classes is continuous. -/
theorem continuous_quotientSymm :
    Continuous
      (_root_.Path.Homotopic.Quotient.symm :
        TopologicalLoopQuot → TopologicalLoopQuot) :=
  continuous_of_discreteTopology

end ConcreteCircleWinding

namespace TopologicalTorus

open ConcreteCircleWinding

attribute [local instance] _root_.Path.Homotopic.setoid

/-- The ordinary quotient topology on based torus-loop homotopy classes. -/
noncomputable instance loopQuotTopologicalSpace : TopologicalSpace LoopQuot :=
  TopologicalSpace.coinduced (Quotient.mk' : Loop → LoopQuot) inferInstance

theorem continuous_coordinateFst :
    Continuous (coordinateFst : Loop → ConcreteCircleWinding.TopologicalLoop) := by
  apply continuous_induced_rng.2
  exact (ContinuousMap.continuous_postcomp ContinuousMap.fst).comp
    continuous_induced_dom

theorem continuous_coordinateSnd :
    Continuous (coordinateSnd : Loop → ConcreteCircleWinding.TopologicalLoop) := by
  apply continuous_induced_rng.2
  exact (ContinuousMap.continuous_postcomp ContinuousMap.snd).comp
    continuous_induced_dom

theorem continuous_winding : Continuous (winding : Loop → ℤ × ℤ) := by
  exact (ConcreteCircleWinding.continuous_windingPath.comp
    continuous_coordinateFst).prodMk
      (ConcreteCircleWinding.continuous_windingPath.comp continuous_coordinateSnd)

/-- Torus loops are homotopic exactly when both coordinate winding numbers
agree. -/
theorem homotopic_iff_winding_eq (γ δ : Loop) :
    γ.Homotopic δ ↔ winding γ = winding δ := by
  constructor
  · exact winding_eq_of_homotopic
  · intro h
    exact (standardLoop_homotopic γ).symm.trans (h ▸ standardLoop_homotopic δ)

/-- Every based torus-loop homotopy class is open in the compact-open loop
space. -/
theorem isOpen_homotopyClass (γ : Loop) :
    IsOpen {δ : Loop | γ.Homotopic δ} := by
  have hopen : IsOpen (winding ⁻¹' ({winding γ} : Set (ℤ × ℤ))) :=
    (isOpen_discrete {winding γ}).preimage continuous_winding
  convert hopen using 1
  ext δ
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
  exact (homotopic_iff_winding_eq γ δ).trans eq_comm

/-- Based torus-loop homotopy as a Mathlib `DiscreteQuotient`. -/
noncomputable def loopHomotopyDiscreteQuotient : DiscreteQuotient Loop where
  toSetoid := _root_.Path.Homotopic.setoid base base
  isOpen_setOf_rel := isOpen_homotopyClass

theorem continuous_encode : Continuous (encode : LoopQuot → ℤ × ℤ) := by
  apply Continuous.quotient_lift
  exact continuous_winding

/-- Coordinate winding is a continuous complete invariant of the final torus
loop quotient. -/
noncomputable def windingCompleteInvariant :
    ContinuousCompleteInvariant Loop LoopQuot (ℤ × ℤ) where
  quotient := Quotient.mk'
  quotient_isQuotientMap := isQuotientMap_quotient_mk'
  invariant := winding
  classifier := equivIntProd
  classifier_quotient := rfl
  invariant_continuous := continuous_winding

/-- The quotient-topologized torus fundamental group is discrete. -/
noncomputable instance loopQuotDiscreteTopology : DiscreteTopology LoopQuot :=
  windingCompleteInvariant.quotientDiscreteTopology

/-- Coordinate winding is a homeomorphism from the torus loop quotient to
the discrete lattice `ℤ × ℤ`. -/
noncomputable def loopQuotHomeomorphIntProd : LoopQuot ≃ₜ (ℤ × ℤ) where
  toEquiv := windingCompleteInvariant.classifierHomeomorph.toEquiv
  continuous_toFun := windingCompleteInvariant.classifierHomeomorph.continuous
  continuous_invFun := windingCompleteInvariant.classifierHomeomorph.symm.continuous

/-- The product of two torus loop-quotient maps is quotient. -/
theorem loopQuotientProd_isQuotientMap :
    Topology.IsQuotientMap
      (fun p : Loop × Loop =>
        ((Quotient.mk' p.1 : LoopQuot), (Quotient.mk' p.2 : LoopQuot))) := by
  change Topology.IsQuotientMap
    (Prod.map windingCompleteInvariant.quotient
      windingCompleteInvariant.quotient)
  exact windingCompleteInvariant.quotientProd_isQuotientMap

/-- Composition of torus loop classes is continuous for the ordinary product
topology. -/
theorem continuous_quotientTrans :
    Continuous
      (fun p : LoopQuot × LoopQuot =>
        _root_.Path.Homotopic.Quotient.trans p.1 p.2) :=
  continuous_of_discreteTopology

/-- Reversal of torus loop classes is continuous. -/
theorem continuous_quotientSymm :
    Continuous
      (_root_.Path.Homotopic.Quotient.symm : LoopQuot → LoopQuot) :=
  continuous_of_discreteTopology

end TopologicalTorus

end
end GeometricTopology
end Path
end ComputationalPaths
