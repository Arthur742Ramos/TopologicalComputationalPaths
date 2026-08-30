import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Homotopy.Product
import ComputationalPaths.Path.Topology.QuotientFundamentalGroup

/-!
# Functoriality and product structure of the quotient fundamental group

This module upgrades the quotient-topological fundamental group from a
pointwise construction to a functorial invariant. Continuous maps induce
continuous homomorphisms, homeomorphisms induce continuous multiplicative
equivalences, and paths between basepoints induce continuous multiplicative
equivalences between the corresponding quotient fundamental groups.

It also isolates the exact topological hypothesis under which the ordinary
product of two quotient fundamental groups represents the quotient
fundamental group of the product space: the product of the two loop-quotient
maps must itself be a quotient map.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open CategoryTheory Topology

noncomputable section

namespace QuotientFundamentalGroup

universe u v

variable {X : Type u} {Y : Type v}
variable [TopologicalSpace X] [TopologicalSpace Y]

attribute [local instance] _root_.Path.Homotopic.setoid

noncomputable local instance functorialLoopQuotGroup
    (Z : Type*) [TopologicalSpace Z] (z : Z) : Group (LoopQuot Z z) :=
  inferInstanceAs (Group (FundamentalGroup Z z))

/-- Postcomposition by a continuous map is continuous on compact-open based
loop spaces. -/
theorem continuous_loopMap (f : C(X, Y)) (x : X) :
    Continuous
      (fun γ : Loop X x => γ.map f.continuous) := by
  apply continuous_induced_rng.mpr
  exact (ContinuousMap.continuous_postcomp f).comp continuous_induced_dom

/-- A continuous map induces a continuous map on quotient-topological
fundamental groups. -/
theorem continuous_quotientMap (f : C(X, Y)) (x : X) :
    Continuous
      (fun q : LoopQuot X x =>
        _root_.Path.Homotopic.Quotient.map q f) := by
  apply Continuous.quotient_lift
  exact (loopQuotient_isQuotientMap Y (f x)).continuous.comp
    (continuous_loopMap f x)

/-- Endpoint casts along an equality are continuous for the quotient
topologies. -/
theorem continuous_quotientCast {x x' : X} (h : x' = x) :
    Continuous
      (fun q : LoopQuot X x =>
        _root_.Path.Homotopic.Quotient.cast q h h) := by
  cases h
  exact continuous_id.congr fun q =>
    _root_.Path.Homotopic.Quotient.cast_rfl_rfl q |>.symm

/-- The homomorphism on fundamental groups induced by a continuous map,
bundled with its continuity for the quotient topologies. -/
def inducedContinuousMonoidHom (f : C(X, Y)) (x : X) :
    LoopQuot X x →ₜ* LoopQuot Y (f x) where
  toMonoidHom := FundamentalGroup.map f x
  continuous_toFun := continuous_quotientMap f x

@[simp]
theorem inducedContinuousMonoidHom_apply
    (f : C(X, Y)) (x : X) (q : LoopQuot X x) :
    inducedContinuousMonoidHom f x q =
      _root_.Path.Homotopic.Quotient.map q f :=
  rfl

@[simp]
theorem quotientMap_id (x : X) (q : LoopQuot X x) :
    _root_.Path.Homotopic.Quotient.map q (.id X) = q := by
  induction q using _root_.Path.Homotopic.Quotient.ind with
  | mk γ => rfl

theorem quotientMap_comp {Z : Type*} [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (x : X) (q : LoopQuot X x) :
    _root_.Path.Homotopic.Quotient.map
        (_root_.Path.Homotopic.Quotient.map q f) g =
      _root_.Path.Homotopic.Quotient.map q (g.comp f) :=
  _root_.Path.Homotopic.Quotient.map_comp.symm

/-- The quotient-topological fundamental group is invariant under pointed
homeomorphism, as a continuous multiplicative equivalence. -/
def homeomorphInducedContinuousMulEquiv (e : X ≃ₜ Y) (x : X) :
    LoopQuot X x ≃ₜ* LoopQuot Y (e x) where
  toFun q := _root_.Path.Homotopic.Quotient.map q ⟨e, e.continuous⟩
  invFun q :=
    (_root_.Path.Homotopic.Quotient.map q ⟨e.symm, e.symm.continuous⟩).cast
      (e.left_inv x).symm (e.left_inv x).symm
  left_inv q := by
    induction q using _root_.Path.Homotopic.Quotient.ind with
    | mk γ =>
        apply congrArg Quotient.mk'
        ext t
        exact e.left_inv _
  right_inv q := by
    induction q using _root_.Path.Homotopic.Quotient.ind with
    | mk γ =>
        apply congrArg Quotient.mk'
        ext t
        simp
  map_mul' q r := (FundamentalGroup.map ⟨e, e.continuous⟩ x).map_mul q r
  continuous_toFun := continuous_quotientMap ⟨e, e.continuous⟩ x
  continuous_invFun := by
    have hmap := continuous_quotientMap ⟨e.symm, e.symm.continuous⟩ (e x)
    exact (continuous_quotientCast (X := X) (e.left_inv x).symm).comp hmap

@[simp]
theorem homeomorphInducedContinuousMulEquiv_apply
    (e : X ≃ₜ Y) (x : X) (q : LoopQuot X x) :
    homeomorphInducedContinuousMulEquiv e x q =
      _root_.Path.Homotopic.Quotient.map q ⟨e, e.continuous⟩ :=
  rfl

/-- Conjugation by a path is continuous between the quotient fundamental
groups at its endpoints. -/
theorem continuous_basepointChange {x₀ x₁ : X} (p : _root_.Path x₀ x₁) :
    Continuous
      (fun q : LoopQuot X x₀ =>
        _root_.Path.Homotopic.Quotient.trans
          (_root_.Path.Homotopic.Quotient.trans
            (Quotient.mk' p.symm) q)
          (Quotient.mk' p)) := by
  apply (loopQuotient_isQuotientMap X x₀).continuous_iff.mpr
  exact (loopQuotient_isQuotientMap X x₁).continuous.comp
    (Continuous.path_trans
      (Continuous.path_trans continuous_const continuous_id)
      continuous_const)

/-- The inverse conjugation associated to a basepoint-changing path is
continuous. -/
theorem continuous_basepointChangeInverse {x₀ x₁ : X}
    (p : _root_.Path x₀ x₁) :
    Continuous
      (fun q : LoopQuot X x₁ =>
        _root_.Path.Homotopic.Quotient.trans
          (_root_.Path.Homotopic.Quotient.trans
            (Quotient.mk' p) q)
          (Quotient.mk' p.symm)) := by
  apply (loopQuotient_isQuotientMap X x₁).continuous_iff.mpr
  exact (loopQuotient_isQuotientMap X x₀).continuous.comp
    (Continuous.path_trans
      (Continuous.path_trans continuous_const continuous_id)
      continuous_const)

/-- A path between basepoints induces a continuous multiplicative
equivalence of quotient-topological fundamental groups. -/
def basepointChangeContinuousMulEquiv {x₀ x₁ : X}
    (p : _root_.Path x₀ x₁) : LoopQuot X x₀ ≃ₜ* LoopQuot X x₁ where
  toMulEquiv := FundamentalGroup.fundamentalGroupMulEquivOfPath p
  continuous_toFun := by
    let α :=
      (CategoryTheory.Groupoid.isoEquivHom
        (FundamentalGroupoid.mk x₀) (FundamentalGroupoid.mk x₁)).symm
        (Quotient.mk' p)
    exact (continuous_basepointChange p).congr fun q => by
      calc
        _ = (α.inv ≫ q) ≫ α.hom := rfl
        _ = α.inv ≫ q ≫ α.hom := Category.assoc _ _ _
        _ = α.conj q := (CategoryTheory.Iso.conj_apply α q).symm
  continuous_invFun := by
    let α :=
      (CategoryTheory.Groupoid.isoEquivHom
        (FundamentalGroupoid.mk x₀) (FundamentalGroupoid.mk x₁)).symm
        (Quotient.mk' p)
    exact (continuous_basepointChangeInverse p).congr fun q => by
      calc
        _ = (α.symm.inv ≫ q) ≫ α.symm.hom := rfl
        _ = α.symm.inv ≫ q ≫ α.symm.hom := Category.assoc _ _ _
        _ = α.symm.conj q :=
          (CategoryTheory.Iso.conj_apply α.symm q).symm
        _ = α.conj.symm q := by
          apply α.conj.injective
          simp

@[simp]
theorem basepointChangeContinuousMulEquiv_apply {x₀ x₁ : X}
    (p : _root_.Path x₀ x₁) (q : LoopQuot X x₀) :
    basepointChangeContinuousMulEquiv p q =
      _root_.Path.Homotopic.Quotient.trans
        (_root_.Path.Homotopic.Quotient.trans
          (Quotient.mk' p.symm) q)
        (Quotient.mk' p) := by
  let α :=
    (CategoryTheory.Groupoid.isoEquivHom
      (FundamentalGroupoid.mk x₀) (FundamentalGroupoid.mk x₁)).symm
      (Quotient.mk' p)
  change α.conj q = _
  calc
    α.conj q = α.inv ≫ q ≫ α.hom := CategoryTheory.Iso.conj_apply α q
    _ = (α.inv ≫ q) ≫ α.hom := (Category.assoc _ _ _).symm
    _ = _ := rfl

/-- On a path-connected space, the quotient-topological fundamental group is
independent of the chosen basepoint up to continuous multiplicative
equivalence. -/
def pathConnectedBasepointContinuousMulEquiv [PathConnectedSpace X]
    (x₀ x₁ : X) : LoopQuot X x₀ ≃ₜ* LoopQuot X x₁ :=
  basepointChangeContinuousMulEquiv (PathConnectedSpace.somePath x₀ x₁)

/-- Pointwise product of loops is continuous for the compact-open path
topologies. -/
theorem continuous_loopProd (x : X) (y : Y) :
    Continuous
      (fun p : Loop X x × Loop Y y => p.1.prod p.2) := by
  apply _root_.Path.continuous_uncurry_iff.mp
  change Continuous
    (fun p : (Loop X x × Loop Y y) × unitInterval =>
      (p.1.1 p.2, p.1.2 p.2))
  fun_prop

/-- The product of the two based-loop quotient maps. -/
def loopQuotientProdMap (x : X) (y : Y) :
    Loop X x × Loop Y y → LoopQuot X x × LoopQuot Y y :=
  Prod.map Quotient.mk' Quotient.mk'

/-- If the product of the loop-quotient maps is a quotient map, then the
product of path-homotopy classes is continuous for the ordinary product
topology. -/
theorem continuous_quotientProd (x : X) (y : Y)
    (hprod : IsQuotientMap (loopQuotientProdMap x y)) :
    Continuous
      (fun q : LoopQuot X x × LoopQuot Y y =>
        _root_.Path.Homotopic.prod q.1 q.2) := by
  apply hprod.continuous_iff.mpr
  exact (loopQuotient_isQuotientMap (X × Y) (x, y)).continuous.comp
    (continuous_loopProd x y)

/-- Algebraically, the quotient fundamental group of a product is the
product of the quotient fundamental groups. -/
def quotientProductEquiv (x : X) (y : Y) :
    (LoopQuot X x × LoopQuot Y y) ≃ LoopQuot (X × Y) (x, y) where
  toFun q := _root_.Path.Homotopic.prod q.1 q.2
  invFun q :=
    (_root_.Path.Homotopic.projLeft q,
      _root_.Path.Homotopic.projRight q)
  left_inv q := by
    apply Prod.ext
    · exact _root_.Path.Homotopic.projLeft_prod q.1 q.2
    · exact _root_.Path.Homotopic.projRight_prod q.1 q.2
  right_inv q :=
    _root_.Path.Homotopic.prod_projLeft_projRight q

/-- The inverse of the product equivalence, given by the two coordinate
projections, is always continuous. -/
theorem continuous_quotientProductProjections (x : X) (y : Y) :
    Continuous (quotientProductEquiv x y).invFun := by
  exact
    (continuous_quotientMap ContinuousMap.fst (x, y)).prodMk
      (continuous_quotientMap ContinuousMap.snd (x, y))

/-- Under the exact product-quotient hypothesis, the quotient fundamental
group of a product is homeomorphic to the ordinary product of the quotient
fundamental groups. -/
def quotientProductHomeomorph (x : X) (y : Y)
    (hprod : IsQuotientMap (loopQuotientProdMap x y)) :
    (LoopQuot X x × LoopQuot Y y) ≃ₜ LoopQuot (X × Y) (x, y) where
  toEquiv := quotientProductEquiv x y
  continuous_toFun := continuous_quotientProd x y hprod
  continuous_invFun := continuous_quotientProductProjections x y

@[simp]
theorem quotientProductHomeomorph_apply (x : X) (y : Y)
    (hprod : IsQuotientMap (loopQuotientProdMap x y))
    (q : LoopQuot X x × LoopQuot Y y) :
    quotientProductHomeomorph x y hprod q =
      _root_.Path.Homotopic.prod q.1 q.2 :=
  rfl

/-- The product homeomorphism respects fundamental-group multiplication. -/
def quotientProductContinuousMulEquiv (x : X) (y : Y)
    (hprod : IsQuotientMap (loopQuotientProdMap x y)) :
    (LoopQuot X x × LoopQuot Y y) ≃ₜ* LoopQuot (X × Y) (x, y) :=
  ContinuousMulEquiv.mk' (quotientProductHomeomorph x y hprod) <| by
    rintro ⟨q₁, q₂⟩ ⟨r₁, r₂⟩
    exact
      (_root_.Path.Homotopic.comp_prod_eq_prod_comp r₁ r₂ q₁ q₂).symm

end QuotientFundamentalGroup

end
end GeometricTopology
end Path
end ComputationalPaths
