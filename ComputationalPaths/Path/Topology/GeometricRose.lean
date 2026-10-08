import ComputationalPaths.Path.Topology.ConcreteCircleWinding
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Separation.Hausdorff

/-!
# The actual topological rose with two circle edges

The space is the quotient of two genuine additive circles identifying exactly
their zero points. Its quotient topology is identified with the coordinate
axes inside the product torus. The two circle inclusions have continuous
retractions and punctured open charts. Their based loops are non-null-homotopic
and geometrically different, as witnessed by the circle winding theorem.

This construction supplies the geometric carrier and primitive paths for a
two-generator scoped presentation. Noncommutation and full geometric
completeness require a covering-space argument and are not asserted here.
-/

namespace ComputationalPaths.Path.GeometricTopology.GeometricRose

open Set Topology
open ConcreteCircleWinding

noncomputable section

abbrev Circle := TopologicalCircle
abbrev Raw := Circle ⊕ Circle

def rawBase : Raw → Prop := Sum.elim (· = 0) (· = 0)

/-- The only cross-component identification is the pair of basepoints. -/
def gluedSetoid : Setoid Raw where
  r p q := p = q ∨ (rawBase p ∧ rawBase q)
  iseqv := by
    constructor
    · intro p; exact Or.inl rfl
    · intro p q h
      rcases h with h | ⟨hp, hq⟩
      · exact Or.inl h.symm
      · exact Or.inr ⟨hq, hp⟩
    · intro p q r hpq hqr
      rcases hpq with rfl | ⟨hp, hq⟩
      · exact hqr
      · rcases hqr with rfl | ⟨_, hr⟩
        · exact Or.inr ⟨hp, hq⟩
        · exact Or.inr ⟨hp, hr⟩

abbrev Rose := Quotient gluedSetoid

def project : Raw → Rose := Quotient.mk gluedSetoid

theorem project_isQuotientMap : IsQuotientMap project := isQuotientMap_quotient_mk'
theorem continuous_project : Continuous project := continuous_quotient_mk'

def leftInclude (x : Circle) : Rose := project (.inl x)
def rightInclude (x : Circle) : Rose := project (.inr x)
def base : Rose := leftInclude 0

theorem continuous_leftInclude : Continuous leftInclude := continuous_project.comp continuous_inl
theorem continuous_rightInclude : Continuous rightInclude := continuous_project.comp continuous_inr

@[simp] theorem leftInclude_eq_rightInclude (x y : Circle) :
    leftInclude x = rightInclude y ↔ x = 0 ∧ y = 0 := by
  rw [leftInclude, rightInclude, project, Quotient.eq]
  change (Sum.inl x = Sum.inr y ∨ (x = 0 ∧ y = 0)) ↔ _
  simp

@[simp] theorem rightInclude_zero : rightInclude 0 = base := by
  exact ((leftInclude_eq_rightInclude 0 0).2 ⟨rfl, rfl⟩).symm

theorem joined_base (r : Rose) : Joined base r := by
  induction r using Quotient.ind with
  | _ p =>
    cases p with
    | inl x => exact ⟨(PathConnectedSpace.somePath (0 : Circle) x).map continuous_leftInclude⟩
    | inr x =>
      exact ⟨((PathConnectedSpace.somePath (0 : Circle) x).map continuous_rightInclude).cast
        rightInclude_zero.symm rfl⟩

instance : PathConnectedSpace Rose where
  nonempty := ⟨base⟩
  joined p q := (joined_base p).symm.trans (joined_base q)

def leftRaw : Raw → Circle := Sum.elim id (fun _ => 0)
def rightRaw : Raw → Circle := Sum.elim (fun _ => 0) id

private theorem leftRaw_respects {p q : Raw} (h : gluedSetoid.r p q) : leftRaw p = leftRaw q := by
  rcases h with rfl | ⟨hp, hq⟩
  · rfl
  · cases p <;> cases q <;> simp_all [rawBase, leftRaw]

private theorem rightRaw_respects {p q : Raw} (h : gluedSetoid.r p q) : rightRaw p = rightRaw q := by
  rcases h with rfl | ⟨hp, hq⟩
  · rfl
  · cases p <;> cases q <;> simp_all [rawBase, rightRaw]

def leftRetract : Rose → Circle := Quotient.lift leftRaw (fun _ _ h => leftRaw_respects h)
def rightRetract : Rose → Circle := Quotient.lift rightRaw (fun _ _ h => rightRaw_respects h)

theorem continuous_leftRetract : Continuous leftRetract := by
  have h : Continuous leftRaw := continuous_sum_dom.2 ⟨continuous_id, continuous_const⟩
  exact h.quotient_lift _
theorem continuous_rightRetract : Continuous rightRetract := by
  have h : Continuous rightRaw := continuous_sum_dom.2 ⟨continuous_const, continuous_id⟩
  exact h.quotient_lift _

@[simp] theorem leftRetract_leftInclude (x : Circle) : leftRetract (leftInclude x) = x := rfl
@[simp] theorem leftRetract_rightInclude (x : Circle) : leftRetract (rightInclude x) = 0 := rfl
@[simp] theorem rightRetract_leftInclude (x : Circle) : rightRetract (leftInclude x) = 0 := rfl
@[simp] theorem rightRetract_rightInclude (x : Circle) : rightRetract (rightInclude x) = x := rfl
@[simp] theorem leftRetract_base : leftRetract base = 0 := rfl
@[simp] theorem rightRetract_base : rightRetract base = 0 := rfl

theorem leftInclude_isEmbedding : IsEmbedding leftInclude :=
  IsEmbedding.of_leftInverse leftRetract_leftInclude continuous_leftRetract continuous_leftInclude
theorem rightInclude_isEmbedding : IsEmbedding rightInclude :=
  IsEmbedding.of_leftInverse rightRetract_rightInclude continuous_rightRetract continuous_rightInclude

/-- Junction neighborhoods are assembled from neighborhoods in the two circles. -/
def star (U V : Set Circle) : Set Rose := leftRetract ⁻¹' U ∩ rightRetract ⁻¹' V

theorem isOpen_star {U V : Set Circle} (hU : IsOpen U) (hV : IsOpen V) :
    IsOpen (star U V) :=
  (hU.preimage continuous_leftRetract).inter (hV.preimage continuous_rightRetract)

theorem base_mem_star {U V : Set Circle} (hU : (0 : Circle) ∈ U) (hV : (0 : Circle) ∈ V) :
    base ∈ star U V := ⟨hU, hV⟩

theorem leftInclude_preimage_star (U V : Set Circle) (hV : (0 : Circle) ∈ V) :
    leftInclude ⁻¹' star U V = U := by
  ext x
  simp [star, hV]

theorem rightInclude_preimage_star (U V : Set Circle) (hU : (0 : Circle) ∈ U) :
    rightInclude ⁻¹' star U V = V := by
  ext x
  simp [star, hU]

theorem star_eq_images (U V : Set Circle) (hU : (0 : Circle) ∈ U) (hV : (0 : Circle) ∈ V) :
    star U V = leftInclude '' U ∪ rightInclude '' V := by
  apply Set.Subset.antisymm
  · intro r hr
    induction r using Quotient.ind with
    | _ p =>
      cases p with
      | inl x => exact Or.inl ⟨x, hr.1, rfl⟩
      | inr x => exact Or.inr ⟨x, hr.2, rfl⟩
  · rintro r (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨hx, hV⟩
    · exact ⟨hU, hx⟩

/-- A concrete ambient geometric model: the two coordinate circles in a torus. -/
abbrev Axes := {z : Circle × Circle // z.1 = 0 ∨ z.2 = 0}

def toAxes (r : Rose) : Axes :=
  ⟨(leftRetract r, rightRetract r), by
    induction r using Quotient.ind with
    | _ p => cases p <;> simp [leftRetract, rightRetract, leftRaw, rightRaw]⟩

theorem continuous_toAxes : Continuous toAxes :=
  (continuous_leftRetract.prodMk continuous_rightRetract).subtype_mk _

@[simp] theorem toAxes_leftInclude (x : Circle) : (toAxes (leftInclude x)).val = (x, 0) := rfl
@[simp] theorem toAxes_rightInclude (x : Circle) : (toAxes (rightInclude x)).val = (0, x) := rfl

theorem toAxes_injective : Function.Injective toAxes := by
  intro p q h
  induction p using Quotient.ind with
  | _ p =>
    induction q using Quotient.ind with
    | _ q =>
      have hv := _root_.congrArg Subtype.val h
      cases p with
      | inl x =>
        cases q with
        | inl y =>
          have hxy : x = y := _root_.congrArg Prod.fst hv
          exact _root_.congrArg leftInclude hxy
        | inr y =>
          apply (leftInclude_eq_rightInclude x y).2
          exact ⟨_root_.congrArg Prod.fst hv, (_root_.congrArg Prod.snd hv).symm⟩
      | inr x =>
        cases q with
        | inl y =>
          apply ((leftInclude_eq_rightInclude y x).2 _).symm
          exact ⟨(_root_.congrArg Prod.fst hv).symm, _root_.congrArg Prod.snd hv⟩
        | inr y =>
          have hxy : x = y := _root_.congrArg Prod.snd hv
          exact _root_.congrArg rightInclude hxy

theorem toAxes_surjective : Function.Surjective toAxes := by
  rintro ⟨⟨x, y⟩, h⟩
  rcases h with hx | hy
  · refine ⟨rightInclude y, ?_⟩
    apply Subtype.ext
    change (0, y) = (x, y)
    exact Prod.ext hx.symm rfl
  · refine ⟨leftInclude x, ?_⟩
    apply Subtype.ext
    change (x, 0) = (x, y)
    exact Prod.ext rfl hy.symm

/-- The quotient topology agrees with the concrete subspace topology. -/
def axesHomeomorph : Rose ≃ₜ Axes :=
  (Equiv.ofBijective toAxes ⟨toAxes_injective, toAxes_surjective⟩).toHomeomorphOfContinuousClosed
    continuous_toAxes continuous_toAxes.isClosedMap

instance : T2Space Rose := axesHomeomorph.symm.t2Space

def leftPuncture : Set Rose := leftInclude '' {x : Circle | x ≠ 0}
def rightPuncture : Set Rose := rightInclude '' {x : Circle | x ≠ 0}

theorem leftPuncture_eq : leftPuncture = {r : Rose | leftRetract r ≠ 0} := by
  ext r
  induction r using Quotient.ind with
  | _ p =>
    cases p with
    | inl x =>
      change (∃ y, y ≠ 0 ∧ leftInclude y = leftInclude x) ↔ x ≠ 0
      constructor
      · rintro ⟨y, hy, h⟩
        have : y = x := leftInclude_isEmbedding.injective h
        simpa [this] using hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    | inr x =>
      change (∃ y, y ≠ 0 ∧ leftInclude y = rightInclude x) ↔ ¬(0 : Circle) = 0
      constructor
      · rintro ⟨y, hy, h⟩
        exact (hy ((leftInclude_eq_rightInclude y x).1 h).1).elim
      · simp

theorem rightPuncture_eq : rightPuncture = {r : Rose | rightRetract r ≠ 0} := by
  ext r
  induction r using Quotient.ind with
  | _ p =>
    cases p with
    | inl x =>
      change (∃ y, y ≠ 0 ∧ rightInclude y = leftInclude x) ↔ ¬(0 : Circle) = 0
      constructor
      · rintro ⟨y, hy, h⟩
        exact (hy ((leftInclude_eq_rightInclude x y).1 h.symm).2).elim
      · simp
    | inr x =>
      change (∃ y, y ≠ 0 ∧ rightInclude y = rightInclude x) ↔ x ≠ 0
      constructor
      · rintro ⟨y, hy, h⟩
        have : y = x := rightInclude_isEmbedding.injective h
        simpa [this] using hy
      · intro hx
        exact ⟨x, hx, rfl⟩

theorem isOpen_leftPuncture : IsOpen leftPuncture := by
  rw [leftPuncture_eq]
  exact isOpen_compl_singleton.preimage continuous_leftRetract

theorem isOpen_rightPuncture : IsOpen rightPuncture := by
  rw [rightPuncture_eq]
  exact isOpen_compl_singleton.preimage continuous_rightRetract

def leftPuncturedHomeomorph : {x : Circle | x ≠ 0} ≃ₜ leftPuncture :=
  leftInclude_isEmbedding.homeomorphImage _
def rightPuncturedHomeomorph : {x : Circle | x ≠ 0} ≃ₜ rightPuncture :=
  rightInclude_isEmbedding.homeomorphImage _

/-- Each punctured circle is an actual open interval, with its usual topology. -/
def puncturedCircleHomeomorph : Set.Ioo (0 : ℝ) 1 ≃ₜ {x : Circle | x ≠ 0} := by
  let e := AddCircle.openPartialHomeomorphCoe (1 : ℝ) 0
  exact (Homeomorph.setCongr (by ext x; simp [e, AddCircle.openPartialHomeomorphCoe,
    _root_.zero_add])).trans (e.toHomeomorphSourceTarget.trans
      (Homeomorph.setCongr (by ext x; simp [e, AddCircle.openPartialHomeomorphCoe])))

def leftIntervalChart : Set.Ioo (0 : ℝ) 1 ≃ₜ leftPuncture :=
  puncturedCircleHomeomorph.trans leftPuncturedHomeomorph

def rightIntervalChart : Set.Ioo (0 : ℝ) 1 ≃ₜ rightPuncture :=
  puncturedCircleHomeomorph.trans rightPuncturedHomeomorph

/-- The first genuine based edge loop traverses the left circle once. -/
def loopA : _root_.Path base base := (standardLoop 1).map continuous_leftInclude
/-- The second genuine based edge loop traverses the right circle once. -/
def loopB : _root_.Path base base :=
  ((standardLoop 1).map continuous_rightInclude).cast rightInclude_zero.symm rightInclude_zero.symm

@[simp] theorem loopA_apply (t : unitInterval) :
    loopA t = leftInclude (circleCover (t : ℝ)) := by
  change leftInclude (circleCover ((t : ℝ) * ((1 : ℤ) : ℝ))) = _
  norm_num

@[simp] theorem loopB_apply (t : unitInterval) :
    loopB t = rightInclude (circleCover (t : ℝ)) := by
  change rightInclude (circleCover ((t : ℝ) * ((1 : ℤ) : ℝ))) = _
  norm_num

@[simp] theorem leftRetract_loopA : loopA.map continuous_leftRetract = standardLoop 1 := by
  ext t
  rfl
@[simp] theorem rightRetract_loopA :
    loopA.map continuous_rightRetract = _root_.Path.refl (0 : Circle) := by
  ext t
  rfl
@[simp] theorem leftRetract_loopB :
    loopB.map continuous_leftRetract = _root_.Path.refl (0 : Circle) := by
  ext t
  rfl
@[simp] theorem rightRetract_loopB : loopB.map continuous_rightRetract = standardLoop 1 := by
  ext t
  rfl

theorem loopA_not_nullHomotopic : ¬loopA.Homotopic (_root_.Path.refl base) := by
  intro h
  have hm := h.map (⟨leftRetract, continuous_leftRetract⟩ : C(Rose, Circle))
  have hr : (_root_.Path.refl base).map continuous_leftRetract =
      _root_.Path.refl (0 : Circle) := by ext t; rfl
  rw [leftRetract_loopA, hr] at hm
  have hw := windingPath_eq_of_homotopic hm
  rw [windingPath_standardLoop, windingPath_refl] at hw
  omega

theorem loopB_not_nullHomotopic : ¬loopB.Homotopic (_root_.Path.refl base) := by
  intro h
  have hm := h.map (⟨rightRetract, continuous_rightRetract⟩ : C(Rose, Circle))
  have hr : (_root_.Path.refl base).map continuous_rightRetract =
      _root_.Path.refl (0 : Circle) := by ext t; rfl
  rw [rightRetract_loopB, hr] at hm
  have hw := windingPath_eq_of_homotopic hm
  rw [windingPath_standardLoop, windingPath_refl] at hw
  omega

theorem loopA_not_homotopic_loopB : ¬loopA.Homotopic loopB := by
  intro h
  have hm := h.map (⟨leftRetract, continuous_leftRetract⟩ : C(Rose, Circle))
  rw [leftRetract_loopA, leftRetract_loopB] at hm
  have hw := windingPath_eq_of_homotopic hm
  rw [windingPath_standardLoop, windingPath_refl] at hw
  omega

end
end ComputationalPaths.Path.GeometricTopology.GeometricRose
