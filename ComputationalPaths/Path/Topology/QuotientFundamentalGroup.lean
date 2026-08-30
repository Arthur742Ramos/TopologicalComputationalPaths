import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Homotopy.HSpaces
import Mathlib.Topology.Maps.OpenQuotient

/-!
# The quotient-topological fundamental group

For an arbitrary pointed space, the endpoint-fixed homotopy quotient of the
compact-open based loop space need not be a topological group: multiplication
can fail to be jointly continuous.  It is nevertheless a quasitopological
group.  Reversal is continuous, and multiplication is continuous in each
variable separately.

This module proves those assertions directly from the quotient universal
property.  It then isolates an exact discreteness criterion: the quotient is
discrete if and only if the null-homotopy class is open in the compact-open
loop space.  In the positive case the quotient map is open, its square is a
quotient map, and multiplication becomes jointly continuous.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open Set Topology

noncomputable section

namespace QuotientFundamentalGroup

universe u

variable (X : Type u) [TopologicalSpace X] (x : X)

/-- The compact-open based loop space of `(X, x)`. -/
abbrev Loop : Type u := _root_.Path x x

/-- Endpoint-fixed homotopy classes of based loops. -/
abbrev LoopQuot : Type u := _root_.Path.Homotopic.Quotient x x

attribute [local instance] _root_.Path.Homotopic.setoid

/-- The final quotient topology on based-loop homotopy classes.  The low
priority lets a namespace-specific but definitionally equal instance take
precedence in concrete applications. -/
noncomputable instance (priority := 100) loopQuotTopologicalSpace :
    TopologicalSpace (LoopQuot X x) :=
  TopologicalSpace.coinduced
    (Quotient.mk' : Loop X x → LoopQuot X x) inferInstance

noncomputable local instance loopQuotGroup : Group (LoopQuot X x) :=
  inferInstanceAs (Group (FundamentalGroup X x))

/-- The based-loop projection is a quotient map by construction. -/
theorem loopQuotient_isQuotientMap :
    IsQuotientMap (Quotient.mk' : Loop X x → LoopQuot X x) :=
  isQuotientMap_quotient_mk'

/-- Reversal is continuous on the quotient for every pointed space. -/
theorem continuous_quotientSymm :
    Continuous
      (_root_.Path.Homotopic.Quotient.symm :
        LoopQuot X x → LoopQuot X x) := by
  apply Continuous.quotient_lift
  exact (loopQuotient_isQuotientMap X x).continuous.comp
    (_root_.Path.continuous_symm (X := X) (x := x) (y := x))

/-- Quotient multiplication is continuous in its second variable. -/
theorem continuous_quotientTrans_left (a : LoopQuot X x) :
    Continuous
      (fun b : LoopQuot X x =>
        _root_.Path.Homotopic.Quotient.trans a b) := by
  induction a using Quotient.ind with
  | _ γ =>
      apply Continuous.quotient_lift
      exact (loopQuotient_isQuotientMap X x).continuous.comp
        (Continuous.path_trans (X := X) continuous_const continuous_id)

/-- Quotient multiplication is continuous in its first variable. -/
theorem continuous_quotientTrans_right (b : LoopQuot X x) :
    Continuous
      (fun a : LoopQuot X x =>
        _root_.Path.Homotopic.Quotient.trans a b) := by
  induction b using Quotient.ind with
  | _ δ =>
      apply Continuous.quotient_lift
      exact (loopQuotient_isQuotientMap X x).continuous.comp
        (Continuous.path_trans (X := X) continuous_id continuous_const)

/-- The quotient-topological fundamental group is a quasitopological group:
inversion is continuous and multiplication is separately continuous. -/
theorem quasitopologicalGroupLaws :
    Continuous
        (_root_.Path.Homotopic.Quotient.symm :
          LoopQuot X x → LoopQuot X x) ∧
      (∀ a : LoopQuot X x,
        Continuous
          (fun b : LoopQuot X x =>
            _root_.Path.Homotopic.Quotient.trans a b)) ∧
      (∀ b : LoopQuot X x,
        Continuous
          (fun a : LoopQuot X x =>
            _root_.Path.Homotopic.Quotient.trans a b)) :=
  ⟨continuous_quotientSymm X x,
    continuous_quotientTrans_left X x,
    continuous_quotientTrans_right X x⟩

/-- Right translation is a homeomorphism, although multiplication need not be
jointly continuous.  In path order this sends `b` to `a.trans b`. -/
noncomputable def quotientRightTranslationHomeomorph
    (a : LoopQuot X x) : LoopQuot X x ≃ₜ LoopQuot X x where
  toFun b := _root_.Path.Homotopic.Quotient.trans a b
  invFun b :=
    _root_.Path.Homotopic.Quotient.trans
      (_root_.Path.Homotopic.Quotient.symm a) b
  left_inv b := by
    change (b * a) * a⁻¹ = b
    simp
  right_inv b := by
    change (b * a⁻¹) * a = b
    simp
  continuous_toFun := continuous_quotientTrans_left X x a
  continuous_invFun :=
    continuous_quotientTrans_left X x
      (_root_.Path.Homotopic.Quotient.symm a)

/-- The quotient-topological fundamental group is homogeneous for every
pointed space. -/
theorem quotientHomogeneous (a b : LoopQuot X x) :
    ∃ e : LoopQuot X x ≃ₜ LoopQuot X x, e a = b := by
  let c : LoopQuot X x := a⁻¹ * b
  refine ⟨quotientRightTranslationHomeomorph X x c, ?_⟩
  change a * (a⁻¹ * b) = b
  simp

/-- The endpoint-fixed homotopy class of the constant based loop. -/
def nullHomotopyClass : Set (Loop X x) :=
  {γ | γ.Homotopic (_root_.Path.refl x)}

theorem preimage_singleton_refl :
    (Quotient.mk' : Loop X x → LoopQuot X x) ⁻¹'
        {_root_.Path.Homotopic.Quotient.refl x} =
      nullHomotopyClass X x := by
  ext γ
  change
    Quotient.mk' γ =
        _root_.Path.Homotopic.Quotient.refl x ↔
      γ.Homotopic (_root_.Path.refl x)
  rw [← _root_.Path.Homotopic.Quotient.mk_refl]
  exact _root_.Path.Homotopic.Quotient.eq

/-- The identity class is open precisely when the null-homotopy class is open
upstairs in the compact-open loop space. -/
theorem isOpen_singleton_refl_iff :
    IsOpen ({_root_.Path.Homotopic.Quotient.refl x} :
      Set (LoopQuot X x)) ↔
      IsOpen (nullHomotopyClass X x) := by
  calc
    IsOpen ({_root_.Path.Homotopic.Quotient.refl x} :
      Set (LoopQuot X x)) ↔
        IsOpen
          ((Quotient.mk' : Loop X x → LoopQuot X x) ⁻¹'
            {_root_.Path.Homotopic.Quotient.refl x}) :=
      (loopQuotient_isQuotientMap X x).isOpen_preimage.symm
    _ ↔ IsOpen (nullHomotopyClass X x) := by
      rw [preimage_singleton_refl]

/-- Exact discreteness criterion for the quotient-topological fundamental
group: discreteness is equivalent to openness of the null-homotopy class in
the compact-open based loop space. -/
theorem discreteTopology_iff_isOpen_nullHomotopyClass :
    DiscreteTopology (LoopQuot X x) ↔
      IsOpen (nullHomotopyClass X x) := by
  constructor
  · intro hdiscrete
    letI : DiscreteTopology (LoopQuot X x) := hdiscrete
    exact (isOpen_singleton_refl_iff X x).mp (isOpen_discrete _)
  · intro hopen
    apply discreteTopology_iff_isOpen_singleton.mpr
    intro q
    have hopenRefl :
        IsOpen ({_root_.Path.Homotopic.Quotient.refl x} :
          Set (LoopQuot X x)) :=
      (isOpen_singleton_refl_iff X x).mpr hopen
    have hcontinuous :
        Continuous
          (fun y : LoopQuot X x =>
            _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.symm q) y) :=
      continuous_quotientTrans_left X x _
    have hpreimage :
        (fun y : LoopQuot X x =>
          _root_.Path.Homotopic.Quotient.trans
            (_root_.Path.Homotopic.Quotient.symm q) y) ⁻¹'
              {_root_.Path.Homotopic.Quotient.refl x} = {q} := by
      ext y
      change y * q⁻¹ = 1 ↔ y = q
      exact mul_inv_eq_one
    rw [← hpreimage]
    exact hopenRefl.preimage hcontinuous

/-- Openness of the null class supplies the discrete quotient topology. -/
theorem quotientDiscreteTopology
    (hopen : IsOpen (nullHomotopyClass X x)) :
    DiscreteTopology (LoopQuot X x) :=
  (discreteTopology_iff_isOpen_nullHomotopyClass X x).mpr hopen

/-- Under the exact discreteness criterion, every endpoint-fixed homotopy
class is open in the compact-open loop space. -/
theorem isOpen_homotopyClass_of_isOpen_nullHomotopyClass
    (hopen : IsOpen (nullHomotopyClass X x)) (γ : Loop X x) :
    IsOpen {δ : Loop X x | γ.Homotopic δ} := by
  have hdiscrete : DiscreteTopology (LoopQuot X x) :=
    quotientDiscreteTopology X x hopen
  have hopenSingleton :
      IsOpen ({Quotient.mk' γ} : Set (LoopQuot X x)) :=
    @isOpen_discrete (LoopQuot X x)
      (loopQuotTopologicalSpace X x) hdiscrete _
  have hopenFiber :
      IsOpen
        ((Quotient.mk' : Loop X x → LoopQuot X x) ⁻¹'
          ({Quotient.mk' γ} : Set (LoopQuot X x))) :=
    hopenSingleton.preimage (loopQuotient_isQuotientMap X x).continuous
  convert hopenFiber using 1
  ext δ
  change γ.Homotopic δ ↔ Quotient.mk' δ = Quotient.mk' γ
  constructor
  · intro h
    exact Quotient.sound h.symm
  · intro h
    exact (Quotient.exact h).symm

/-- Under the exact discreteness criterion, the loop projection is an open
quotient map. -/
theorem loopQuotient_isOpenQuotientMap
    (hopen : IsOpen (nullHomotopyClass X x)) :
    IsOpenQuotientMap
      (Quotient.mk' : Loop X x → LoopQuot X x) := by
  have hdiscrete : DiscreteTopology (LoopQuot X x) :=
    quotientDiscreteTopology X x hopen
  exact
    { surjective := (loopQuotient_isQuotientMap X x).surjective
      continuous := (loopQuotient_isQuotientMap X x).continuous
      isOpenMap := fun U _ =>
        @isOpen_discrete (LoopQuot X x)
          (loopQuotTopologicalSpace X x) hdiscrete _ }

/-- Under the exact discreteness criterion, the square of the loop projection
is again a quotient map. -/
theorem loopQuotientProd_isQuotientMap
    (hopen : IsOpen (nullHomotopyClass X x)) :
    IsQuotientMap
      (fun p : Loop X x × Loop X x =>
        ((Quotient.mk' p.1 : LoopQuot X x),
          (Quotient.mk' p.2 : LoopQuot X x))) := by
  change IsQuotientMap
    (Prod.map
      (Quotient.mk' : Loop X x → LoopQuot X x)
      (Quotient.mk' : Loop X x → LoopQuot X x))
  exact
    ((loopQuotient_isOpenQuotientMap X x hopen).prodMap
      (loopQuotient_isOpenQuotientMap X x hopen)).isQuotientMap

/-- Under the exact discreteness criterion, quotient multiplication is jointly
continuous for the ordinary product topology. -/
theorem continuous_quotientTrans
    (hopen : IsOpen (nullHomotopyClass X x)) :
    Continuous
      (fun p : LoopQuot X x × LoopQuot X x =>
        _root_.Path.Homotopic.Quotient.trans p.1 p.2) := by
  letI : DiscreteTopology (LoopQuot X x) :=
    quotientDiscreteTopology X x hopen
  exact continuous_of_discreteTopology

end QuotientFundamentalGroup

end
end GeometricTopology
end Path
end ComputationalPaths
