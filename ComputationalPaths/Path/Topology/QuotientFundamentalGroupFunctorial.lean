import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Product
import ComputationalPaths.Path.Topology.QuotientFundamentalGroup

/-!
# Functoriality and product structure of the quotient fundamental group

This module upgrades the quotient-topological fundamental group from a
pointwise construction to a functorial invariant. Continuous maps induce
continuous homomorphisms, homeomorphisms induce continuous multiplicative
equivalences, and paths between basepoints induce continuous multiplicative
equivalences between the corresponding quotient fundamental groups.
Quotient path composition is preserved by continuous maps, and basepoint
transport is natural for those induced maps.  Consequently, quotient
discreteness and the joint-continuity boundary are invariant under both
homotopy equivalence and path-based basepoint change.

Homotopies of continuous maps induce the expected conjugacy relation on
quotient maps, witnessed by the path traced by the homotopy at each basepoint.
When that path is pointwise constant, the induced based homomorphisms agree
after the canonical endpoint cast.
On a path-connected space, joint continuity at one basepoint is therefore
equivalent to joint continuity at every basepoint; the same one-point test
holds for discreteness and for the genuine topological-group structure.  The
global joint-continuity property is itself invariant under homotopy
equivalences between path-connected spaces.

It also isolates the exact topological hypothesis under which the ordinary
product of two quotient fundamental groups represents the quotient
fundamental group of the product space: the product of the two loop-quotient
maps must itself be a quotient map.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open CategoryTheory Topology
open scoped ContinuousMap

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

/-- Quotient functoriality preserves concatenation of path classes. -/
theorem quotientMap_trans {x₀ x₁ x₂ : X}
    (f : C(X, Y))
    (P : _root_.Path.Homotopic.Quotient x₀ x₁)
    (Q : _root_.Path.Homotopic.Quotient x₁ x₂) :
    _root_.Path.Homotopic.Quotient.map
        (_root_.Path.Homotopic.Quotient.trans P Q) f =
      _root_.Path.Homotopic.Quotient.trans
        (_root_.Path.Homotopic.Quotient.map P f)
        (_root_.Path.Homotopic.Quotient.map Q f) := by
  induction P using _root_.Path.Homotopic.Quotient.ind with
  | mk P =>
      induction Q using _root_.Path.Homotopic.Quotient.ind with
      | mk Q =>
          conv_lhs =>
            rw [← _root_.Path.Homotopic.Quotient.mk_trans]
            rw [← _root_.Path.Homotopic.Quotient.mk_map]
          rw [_root_.Path.map_trans]
          rfl

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
          (_root_.Path.Homotopic.Quotient.mk p.symm) q)
        (_root_.Path.Homotopic.Quotient.mk p) := by
  let α :=
    (CategoryTheory.Groupoid.isoEquivHom
      (FundamentalGroupoid.mk x₀) (FundamentalGroupoid.mk x₁)).symm
      (_root_.Path.Homotopic.Quotient.mk p)
  change α.conj q = _
  calc
    α.conj q = α.inv ≫ q ≫ α.hom := CategoryTheory.Iso.conj_apply α q
    _ = (α.inv ≫ q) ≫ α.hom := (Category.assoc _ _ _).symm
    _ = _ := rfl

/-- Basepoint transport depends only on the endpoint-fixed homotopy class of
the chosen path.  This is the coherence needed to use path transport as a
quotient-topological construction rather than as a choice of representative.
-/
theorem basepointChangeContinuousMulEquiv_eq_of_homotopic
    {x₀ x₁ : X} (p q : _root_.Path x₀ x₁) (h : p.Homotopic q) :
    basepointChangeContinuousMulEquiv p =
      basepointChangeContinuousMulEquiv q := by
  ext r
  rw [basepointChangeContinuousMulEquiv_apply,
    basepointChangeContinuousMulEquiv_apply]
  apply congrArg₂ (fun a b =>
      _root_.Path.Homotopic.Quotient.trans
        (_root_.Path.Homotopic.Quotient.trans a r) b)
  · exact Quotient.sound h.symm₂
  · exact Quotient.sound h

/-- Basepoint transport is compatible with concatenation of paths.  Thus the
continuous multiplicative equivalences form a coherent transport system on
the fundamental-groupoid basepoints. -/
theorem basepointChangeContinuousMulEquiv_trans
    {x₀ x₁ x₂ : X} (p : _root_.Path x₀ x₁) (q : _root_.Path x₁ x₂) :
    (basepointChangeContinuousMulEquiv p).trans
        (basepointChangeContinuousMulEquiv q) =
      basepointChangeContinuousMulEquiv (p.trans q) := by
  ext r
  rw [ContinuousMulEquiv.trans_apply,
    basepointChangeContinuousMulEquiv_apply,
    basepointChangeContinuousMulEquiv_apply,
    basepointChangeContinuousMulEquiv_apply]
  simp

/-! Together with homotopy-class independence and concatenation compatibility,
the next identity law records the unit of the path-transport system. -/

/-- Transport along a constant path is the identity equivalence. -/
theorem basepointChangeContinuousMulEquiv_refl (x : X) :
    basepointChangeContinuousMulEquiv (_root_.Path.refl x) =
      ContinuousMulEquiv.refl (LoopQuot X x) := by
  ext r
  rw [basepointChangeContinuousMulEquiv_apply]
  simp

/-- Basepoint transport is natural for continuous maps: mapping a conjugated
loop class agrees with conjugating the mapped class along the mapped path. -/
theorem basepointChange_quotientMap_naturality
    {x₀ x₁ : X} (p : _root_.Path x₀ x₁) (f : C(X, Y))
    (q : LoopQuot X x₀) :
    _root_.Path.Homotopic.Quotient.map
        (basepointChangeContinuousMulEquiv p q) f =
      basepointChangeContinuousMulEquiv (p.map f.continuous)
        (_root_.Path.Homotopic.Quotient.map q f) := by
  rw [basepointChangeContinuousMulEquiv_apply,
    basepointChangeContinuousMulEquiv_apply]
  rw [quotientMap_trans, quotientMap_trans]
  simp only [← _root_.Path.Homotopic.Quotient.mk_map, _root_.Path.map_symm]

/-- Discreteness of the quotient topology is independent of the chosen
basepoint along a path. -/
theorem quotientDiscreteTopology_iff_of_path {x₀ x₁ : X}
    (p : _root_.Path x₀ x₁) :
    DiscreteTopology (LoopQuot X x₀) ↔
      DiscreteTopology (LoopQuot X x₁) :=
  (basepointChangeContinuousMulEquiv p).toHomeomorph.discreteTopology_iff

/-- Homotopic maps induce conjugate maps on quotient fundamental groups,
where the conjugation follows the path traced by the basepoint through the
homotopy.  This is the pointed form of homotopy naturality. -/
theorem basepointChange_quotientMap_homotopy {f g : C(X, Y)}
    (H : f.Homotopy g) (x : X) (q : LoopQuot X x) :
    basepointChangeContinuousMulEquiv (H.evalAt x)
        (_root_.Path.Homotopic.Quotient.map q f) =
      _root_.Path.Homotopic.Quotient.map q g := by
  rw [basepointChangeContinuousMulEquiv_apply]
  have hn := (FundamentalGroupoidFunctor.homotopicMapsNatIso H).naturality q
  dsimp [FundamentalGroupoidFunctor.homotopicMapsNatIso] at hn
  change _root_.Path.Homotopic.Quotient.trans
      (_root_.Path.Homotopic.Quotient.map q f)
      (_root_.Path.Homotopic.Quotient.mk (H.evalAt x)) =
    _root_.Path.Homotopic.Quotient.trans
      (_root_.Path.Homotopic.Quotient.mk (H.evalAt x))
      (_root_.Path.Homotopic.Quotient.map q g) at hn
  rw [_root_.Path.Homotopic.Quotient.mk_symm,
    _root_.Path.Homotopic.Quotient.trans_assoc, hn,
    ← _root_.Path.Homotopic.Quotient.trans_assoc,
    _root_.Path.Homotopic.Quotient.symm_trans,
    _root_.Path.Homotopic.Quotient.refl_trans]

/-- A homotopy that fixes the chosen basepoint induces the same based map.
The endpoint equality is handled by `FundamentalGroup.mapOfEq`, so the result
is an equality of homomorphisms with a common target basepoint. -/
theorem quotientMap_eq_of_pointedHomotopy
    {f g : C(X, Y)} (H : f.Homotopy g) (x : X)
    (hfix : ∀ t : unitInterval, H (t, x) = f x) :
    FundamentalGroup.mapOfEq f
        (show f x = g x by
          exact (hfix 1).symm.trans (H.apply_one x)) =
      FundamentalGroup.map g x := by
  let hfg : f x = g x := (hfix 1).symm.trans (H.apply_one x)
  ext q
  rw [FundamentalGroup.mapOfEq_apply]
  change (_root_.Path.Homotopic.Quotient.map q f).cast hfg.symm hfg.symm =
    _root_.Path.Homotopic.Quotient.map q g
  have hpath : H.evalAt x = (_root_.Path.refl (f x)).cast rfl hfg.symm := by
    apply _root_.Path.ext
    funext t
    exact hfix t
  have htransport := basepointChange_quotientMap_homotopy H x q
  rw [hpath] at htransport
  rw [basepointChangeContinuousMulEquiv_apply] at htransport
  simp only [_root_.Path.Homotopic.Quotient.mk_symm,
    _root_.Path.Homotopic.Quotient.mk_cast,
    _root_.Path.Homotopic.Quotient.mk_refl] at htransport
  induction q using _root_.Path.Homotopic.Quotient.ind with
  | mk γ =>
      have hfirst :
          ((_root_.Path.Homotopic.Quotient.refl (f x)).cast rfl hfg.symm).symm =
            (_root_.Path.Homotopic.Quotient.refl (f x)).cast hfg.symm rfl := by
        change
          _root_.Path.Homotopic.Quotient.mk
              ((_root_.Path.refl (f x)).cast rfl hfg.symm).symm =
            _root_.Path.Homotopic.Quotient.mk
              ((_root_.Path.refl (f x)).cast hfg.symm rfl)
        apply Quotient.sound
        rw [← _root_.Path.cast_symm]
        exact _root_.Path.Homotopic.refl _
      have hlast :
          (_root_.Path.Homotopic.Quotient.refl (f x)).cast rfl hfg.symm =
            (_root_.Path.Homotopic.Quotient.refl (g x)).cast hfg rfl := by
        have hcast_id {a b : Y} (h : a = b) :
            (_root_.Path.Homotopic.Quotient.refl a).cast rfl h.symm =
              (_root_.Path.Homotopic.Quotient.refl b).cast h rfl := by
          cases h
          rfl
        exact hcast_id hfg
      have hcat := FundamentalGroupoid.conj_eqToHom
        (X := Y) hfg.symm hfg.symm
          (p := _root_.Path.Homotopic.Quotient.map (Quotient.mk' γ) f)
      rw [FundamentalGroupoid.eqToHom_eq] at hcat
      rw [FundamentalGroupoid.eqToHom_eq hfg] at hcat
      rw [← Category.assoc] at hcat
      change
        (_root_.Path.Homotopic.Quotient.map (Quotient.mk' γ) f).cast
            hfg.symm hfg.symm = _
      rw [hfirst, hlast] at htransport
      exact hcat.symm.trans htransport

/-- The algebraic equivalence on fundamental groups induced by a homotopy
equivalence, obtained from full faithfulness of the corresponding
fundamental-groupoid equivalence. -/
noncomputable def homotopyEquivInducedMulEquiv
    (e : X ≃ₕ Y) (x : X) :
    LoopQuot X x ≃* LoopQuot Y (e x) :=
  (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor
    |>.mulEquivEnd (FundamentalGroupoid.mk x)

@[simp]
theorem homotopyEquivInducedMulEquiv_apply
    (e : X ≃ₕ Y) (x : X) (q : LoopQuot X x) :
    homotopyEquivInducedMulEquiv e x q =
      _root_.Path.Homotopic.Quotient.map q e.toFun :=
  rfl

/-- A homotopy equivalence induces a continuous multiplicative equivalence
of quotient-topological fundamental groups.  The inverse is postcomposition
by the homotopy inverse followed by basepoint change along the chosen
left-inverse homotopy. -/
noncomputable def homotopyEquivInducedContinuousMulEquiv
    (e : X ≃ₕ Y) (x : X) :
    LoopQuot X x ≃ₜ* LoopQuot Y (e x) := by
  let H := e.left_inv.some
  let p := H.evalAt x
  let forward : LoopQuot X x → LoopQuot Y (e x) :=
    fun q => _root_.Path.Homotopic.Quotient.map q e.toFun
  let inverse : LoopQuot Y (e x) → LoopQuot X x :=
    fun q => basepointChangeContinuousMulEquiv p
      (_root_.Path.Homotopic.Quotient.map q e.invFun)
  have hleft : Function.LeftInverse inverse forward := by
    intro q
    change basepointChangeContinuousMulEquiv p
        (_root_.Path.Homotopic.Quotient.map
          (_root_.Path.Homotopic.Quotient.map q e.toFun)
          e.invFun) = q
    rw [quotientMap_comp]
    simpa only [p, H, quotientMap_id] using
      basepointChange_quotientMap_homotopy H x q
  have hsurj : Function.Surjective forward := by
    change Function.Surjective (homotopyEquivInducedMulEquiv e x)
    exact (homotopyEquivInducedMulEquiv e x).surjective
  refine
    { toFun := forward
      invFun := inverse
      left_inv := hleft
      right_inv := hleft.rightInverse_of_surjective hsurj
      map_mul' := ?_
      continuous_toFun := continuous_quotientMap e.toFun x
      continuous_invFun := ?_ }
  · intro q r
    exact (FundamentalGroup.map e.toFun x).map_mul q r
  · exact (basepointChangeContinuousMulEquiv p).continuous.comp
      (continuous_quotientMap e.invFun (e x))

@[simp]
theorem homotopyEquivInducedContinuousMulEquiv_apply
    (e : X ≃ₕ Y) (x : X) (q : LoopQuot X x) :
    homotopyEquivInducedContinuousMulEquiv e x q =
      _root_.Path.Homotopic.Quotient.map q e.toFun :=
  rfl

/-- Discreteness of the quotient topology is invariant under a homotopy
equivalence at corresponding basepoints. -/
theorem quotientDiscreteTopology_iff_of_homotopyEquiv
    (e : X ≃ₕ Y) (x : X) :
    DiscreteTopology (LoopQuot X x) ↔
      DiscreteTopology (LoopQuot Y (e x)) :=
  (homotopyEquivInducedContinuousMulEquiv e x).toHomeomorph.discreteTopology_iff

/-- Joint continuity of multiplication is transported by a continuous
multiplicative equivalence. -/
theorem continuousMul_iff_of_continuousMulEquiv
    {G : Type u} {H : Type v} [TopologicalSpace G] [TopologicalSpace H]
    [Mul G] [Mul H] (e : G ≃ₜ* H) :
    Nonempty (ContinuousMul G) ↔ Nonempty (ContinuousMul H) := by
  constructor
  · rintro ⟨hG⟩
    letI : ContinuousMul G := hG
    have hpre : Continuous (fun p : H × H => e.symm p.1 * e.symm p.2) :=
      continuous_mul.comp
        ((e.symm.continuous_toFun.comp continuous_fst).prodMk
          (e.symm.continuous_toFun.comp continuous_snd))
    have hpost : Continuous (fun p : H × H =>
        e (e.symm p.1 * e.symm p.2)) :=
      e.continuous_toFun.comp hpre
    refine ⟨{ continuous_mul := ?_ }⟩
    convert hpost using 1
    ext p
    simp
  · rintro ⟨hH⟩
    letI : ContinuousMul H := hH
    have hpre : Continuous (fun p : G × G => e p.1 * e p.2) :=
      continuous_mul.comp
        ((e.continuous_toFun.comp continuous_fst).prodMk
          (e.continuous_toFun.comp continuous_snd))
    have hpost : Continuous (fun p : G × G =>
        e.symm (e p.1 * e p.2)) :=
      e.symm.continuous_toFun.comp hpre
    refine ⟨{ continuous_mul := ?_ }⟩
    convert hpost using 1
    ext p
    simp

/-- The topological-group boundary for quotient multiplication is invariant
under homotopy equivalence at corresponding basepoints. -/
theorem quotientContinuousMul_iff_of_homotopyEquiv
    (e : X ≃ₕ Y) (x : X) :
    Nonempty (ContinuousMul (LoopQuot X x)) ↔
      Nonempty (ContinuousMul (LoopQuot Y (e x))) :=
  continuousMul_iff_of_continuousMulEquiv
    (homotopyEquivInducedContinuousMulEquiv e x)

/-- Joint continuity of quotient concatenation is invariant under homotopy
equivalence at corresponding basepoints. -/
theorem quotientTransContinuous_iff_of_homotopyEquiv
    (e : X ≃ₕ Y) (x : X) :
    Continuous
        (fun p : LoopQuot X x × LoopQuot X x =>
          _root_.Path.Homotopic.Quotient.trans p.1 p.2) ↔
      Continuous
        (fun p : LoopQuot Y (e x) × LoopQuot Y (e x) =>
          _root_.Path.Homotopic.Quotient.trans p.1 p.2) := by
  rw [continuous_quotientTrans_iff_topologicalGroupStructure,
    continuous_quotientTrans_iff_topologicalGroupStructure]
  exact quotientContinuousMul_iff_of_homotopyEquiv e x

/-- Joint continuity of quotient concatenation is independent of the chosen
basepoint along a path. -/
theorem quotientTransContinuous_iff_of_path {x₀ x₁ : X}
    (p : _root_.Path x₀ x₁) :
    Continuous
        (fun q : LoopQuot X x₀ × LoopQuot X x₀ =>
          _root_.Path.Homotopic.Quotient.trans q.1 q.2) ↔
      Continuous
        (fun q : LoopQuot X x₁ × LoopQuot X x₁ =>
          _root_.Path.Homotopic.Quotient.trans q.1 q.2) := by
  rw [continuous_quotientTrans_iff_topologicalGroupStructure,
    continuous_quotientTrans_iff_topologicalGroupStructure]
  exact continuousMul_iff_of_continuousMulEquiv
    (basepointChangeContinuousMulEquiv p)

/-- On a path-connected space, checking joint continuity at one basepoint is
equivalent to checking it at every basepoint. -/
theorem quotientTransContinuous_iff_forall_of_pathConnected
    [PathConnectedSpace X] (x₀ : X) :
    Continuous
        (fun p : LoopQuot X x₀ × LoopQuot X x₀ =>
          _root_.Path.Homotopic.Quotient.trans p.1 p.2) ↔
      ∀ x : X, Continuous
        (fun p : LoopQuot X x × LoopQuot X x =>
          _root_.Path.Homotopic.Quotient.trans p.1 p.2) := by
  constructor
  · intro h x
    let p : _root_.Path x₀ x := PathConnectedSpace.somePath x₀ x
    exact (quotientTransContinuous_iff_of_path p).mp h
  · intro h
    exact h x₀

/-- On a path-connected space, discreteness at one basepoint is equivalent to
discreteness at every basepoint. -/
theorem quotientDiscreteTopology_iff_forall_of_pathConnected
    [PathConnectedSpace X] (x₀ : X) :
    DiscreteTopology (LoopQuot X x₀) ↔
      ∀ x : X, DiscreteTopology (LoopQuot X x) := by
  constructor
  · intro h x
    let p : _root_.Path x₀ x := PathConnectedSpace.somePath x₀ x
    exact (quotientDiscreteTopology_iff_of_path p).mp h
  · intro h
    exact h x₀

/-- The global joint-continuity criterion is invariant under a homotopy
equivalence between path-connected spaces. -/
theorem quotientTransContinuous_iff_forall_of_pathConnected_homotopyEquiv
    [PathConnectedSpace X] [PathConnectedSpace Y]
    (e : X ≃ₕ Y) (x₀ : X) :
    (∀ x : X, Continuous
      (fun p : LoopQuot X x × LoopQuot X x =>
        _root_.Path.Homotopic.Quotient.trans p.1 p.2)) ↔
      ∀ y : Y, Continuous
        (fun p : LoopQuot Y y × LoopQuot Y y =>
          _root_.Path.Homotopic.Quotient.trans p.1 p.2) := by
  constructor
  · intro h
    have htarget : Continuous
        (fun p : LoopQuot Y (e x₀) × LoopQuot Y (e x₀) =>
          _root_.Path.Homotopic.Quotient.trans p.1 p.2) :=
      (quotientTransContinuous_iff_of_homotopyEquiv e x₀).mp (h x₀)
    exact
      (quotientTransContinuous_iff_forall_of_pathConnected (e x₀)).mp htarget
  · intro h
    have hsource : Continuous
        (fun p : LoopQuot X x₀ × LoopQuot X x₀ =>
          _root_.Path.Homotopic.Quotient.trans p.1 p.2) :=
      (quotientTransContinuous_iff_of_homotopyEquiv e x₀).mpr
        (h (e x₀))
    exact
      (quotientTransContinuous_iff_forall_of_pathConnected x₀).mp hsource

/-- On a path-connected space, the quotient is a genuine topological group at
one basepoint exactly when it is one at every basepoint. -/
theorem quotientContinuousMul_iff_forall_of_pathConnected
    [PathConnectedSpace X] (x₀ : X) :
    Nonempty (ContinuousMul (LoopQuot X x₀)) ↔
      ∀ x : X, Nonempty (ContinuousMul (LoopQuot X x)) := by
  constructor
  · intro h
    have htrans :=
      (continuous_quotientTrans_iff_topologicalGroupStructure
        (X := X) (x := x₀)).mpr h
    have hall :=
      (quotientTransContinuous_iff_forall_of_pathConnected (X := X) x₀).mp
        htrans
    intro x
    exact
      (continuous_quotientTrans_iff_topologicalGroupStructure
        (X := X) (x := x)).mp (hall x)
  · intro h
    have hall : ∀ x : X, Continuous
        (fun p : LoopQuot X x × LoopQuot X x =>
          _root_.Path.Homotopic.Quotient.trans p.1 p.2) := by
      intro x
      exact
        (continuous_quotientTrans_iff_topologicalGroupStructure
          (X := X) (x := x)).mpr (h x)
    exact
      (continuous_quotientTrans_iff_topologicalGroupStructure
        (X := X) (x := x₀)).mp
        ((quotientTransContinuous_iff_forall_of_pathConnected (X := X) x₀).mpr
          hall)

/-- A covering map induces an injective continuous homomorphism on
quotient-topological fundamental groups.  The injectivity is the unique
path-lifting theorem, while continuity comes from compact-open
postcomposition and quotient descent. -/
theorem inducedContinuousMonoidHom_injective_of_isCoveringMap
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (hp : IsCoveringMap p) (e : E) :
    Function.Injective
      (inducedContinuousMonoidHom ⟨p, hp.continuous⟩ e) :=
  hp.injective_path_homotopic_map e e

/-- The image of the fundamental-group homomorphism induced by a covering
map is exactly the stabilizer of the chosen point in the monodromy action. -/
theorem mem_range_inducedContinuousMonoidHom_iff_monodromy_fixed
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (hp : IsCoveringMap p) (e : E)
    (q : LoopQuot B (p e)) :
    q ∈ Set.range (inducedContinuousMonoidHom ⟨p, hp.continuous⟩ e) ↔
      hp.monodromy q ⟨e, rfl⟩ = ⟨e, rfl⟩ := by
  constructor
  · rintro ⟨r, rfl⟩
    exact hp.monodromy_map r
  · intro hfix
    let e₀ : p ⁻¹' {p e} := ⟨e, rfl⟩
    let Γ := hp.liftPathQuotient q e₀
    have hend : (hp.monodromy q e₀).1 = e :=
      congrArg Subtype.val hfix
    let r : LoopQuot E e := Γ.cast rfl hend.symm
    refine ⟨r, ?_⟩
    change _root_.Path.Homotopic.Quotient.map r ⟨p, hp.continuous⟩ = q
    dsimp [r]
    rw [_root_.Path.Homotopic.Quotient.map_cast,
      hp.map_liftPathQuotient]
    convert _root_.Path.Homotopic.Quotient.cast_rfl_rfl q
    all_goals try rfl
    all_goals try simp [e₀, hend]
    exact _root_.Path.Homotopic.Quotient.cast_heq _ _

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

section IndexedProducts

universe w

variable {ι : Type w} {Z : ι → Type u}
variable [∀ i, TopologicalSpace (Z i)]

/-- Coordinatewise assembly of an indexed family of based paths is
continuous for the compact-open path topologies. -/
theorem continuous_loopPi (z : ∀ i, Z i) :
    Continuous
      (fun γ : ∀ i, Loop (Z i) (z i) => _root_.Path.pi γ) := by
  apply _root_.Path.continuous_uncurry_iff.mp
  change Continuous
    (fun p : (∀ i, Loop (Z i) (z i)) × unitInterval =>
      fun i => p.1 i p.2)
  fun_prop

/-- The indexed product of the based-loop quotient maps. -/
def loopQuotientPiMap (z : ∀ i, Z i) :
    (∀ i, Loop (Z i) (z i)) → (∀ i, LoopQuot (Z i) (z i)) :=
  fun γ i => Quotient.mk' (γ i)

/-- Under the exact indexed product-quotient hypothesis, assembly of a
family of path classes is continuous. -/
theorem continuous_quotientPi (z : ∀ i, Z i)
    (hpi : IsQuotientMap (loopQuotientPiMap z)) :
    Continuous
      (fun q : ∀ i, LoopQuot (Z i) (z i) =>
        _root_.Path.Homotopic.pi q) := by
  apply hpi.continuous_iff.mpr
  exact ((loopQuotient_isQuotientMap (∀ i, Z i) z).continuous.comp
    (continuous_loopPi z)).congr fun γ =>
      (_root_.Path.Homotopic.pi_lift γ).symm

/-- Algebraic indexed-product classification of based path classes. -/
def quotientPiEquiv (z : ∀ i, Z i) :
    (∀ i, LoopQuot (Z i) (z i)) ≃
      LoopQuot (∀ i, Z i) z where
  toFun := _root_.Path.Homotopic.pi
  invFun q i := _root_.Path.Homotopic.proj i q
  left_inv q := funext fun i => _root_.Path.Homotopic.proj_pi i q
  right_inv := _root_.Path.Homotopic.pi_proj

/-- All coordinate projections from the quotient fundamental group of an
indexed product are jointly continuous. -/
theorem continuous_quotientPiProjections (z : ∀ i, Z i) :
    Continuous (quotientPiEquiv z).invFun := by
  apply continuous_pi
  intro i
  exact continuous_quotientMap ⟨_, continuous_apply i⟩ z

/-- The quotient fundamental group preserves an indexed product whenever
the indexed product of loop quotient maps is itself a quotient map. -/
def quotientPiHomeomorph (z : ∀ i, Z i)
    (hpi : IsQuotientMap (loopQuotientPiMap z)) :
    (∀ i, LoopQuot (Z i) (z i)) ≃ₜ
      LoopQuot (∀ i, Z i) z where
  toEquiv := quotientPiEquiv z
  continuous_toFun := continuous_quotientPi z hpi
  continuous_invFun := continuous_quotientPiProjections z

/-- Multiplicative indexed-product preservation under the exact quotient
hypothesis. -/
def quotientPiContinuousMulEquiv (z : ∀ i, Z i)
    (hpi : IsQuotientMap (loopQuotientPiMap z)) :
    (∀ i, LoopQuot (Z i) (z i)) ≃ₜ*
      LoopQuot (∀ i, Z i) z :=
  ContinuousMulEquiv.mk' (quotientPiHomeomorph z hpi) <| by
    intro q r
    exact (_root_.Path.Homotopic.comp_pi_eq_pi_comp r q).symm

end IndexedProducts

end QuotientFundamentalGroup

end
end GeometricTopology
end Path
end ComputationalPaths
