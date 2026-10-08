import ComputationalPaths.Path.Topology.GeometricRose
import ComputationalPaths.Path.Topology.CayleyTreeGeometry

/-!
# The genuine Cayley-edge covering of the two-circle rose

The projection maps every free-group vertex to the actual junction, and each
unit interval edge to its actual circle edge. Its quotient-map property is
derived from the compact finite collection of closed circle edges. Its fibers
are proved to be exactly the translation orbits by injectivity of the open
circle interval charts. Local disjointness is supplied by the explicit edge
and vertex neighborhoods in `CayleyTreeGeometry`.

No geometric completeness or covering property is assumed.
-/

namespace ComputationalPaths.Path.GeometricTopology.CayleyRoseCovering

open Set Topology
open GeometricRose ConcreteCircleWinding RoseReducedWords
open CayleyTreeGeometry (G Tree Interior)

noncomputable section

def primitiveLoop (i : Label) : _root_.Path base base :=
  (RoseReducedWords.system loopA loopB).realize i

def project : Tree → Rose
  | .vertex _ => base
  | .inner _ .a t => leftInclude (circleCover (t : ℝ))
  | .inner _ .b t => rightInclude (circleCover (t : ℝ))

@[simp] theorem project_vertex (g : G) : project (.vertex g) = base := rfl
@[simp] theorem project_inner_a (g : G) (t : Interior) :
    project (.inner g .a t) = leftInclude (circleCover (t : ℝ)) := rfl
@[simp] theorem project_inner_b (g : G) (t : Interior) :
    project (.inner g .b t) = rightInclude (circleCover (t : ℝ)) := rfl

def edgeProjection (r : Label × unitInterval) : Rose := primitiveLoop r.1 r.2
def forgetVertex (r : CayleyTreeGeometry.Raw) : Label × unitInterval := (r.1.2, r.2)

theorem project_key (r : CayleyTreeGeometry.Raw) :
    project (CayleyTreeGeometry.key r) = edgeProjection (forgetVertex r) := by
  rcases r with ⟨⟨g, i⟩, t⟩
  unfold CayleyTreeGeometry.key
  split_ifs with h0 h1
  · have ht : t = 0 := Subtype.ext h0
    subst t
    simp [project, edgeProjection, forgetVertex]
  · have ht : t = 1 := Subtype.ext h1
    subst t
    simp [project, edgeProjection, forgetVertex]
  · cases i <;> simp [project, edgeProjection, forgetVertex, primitiveLoop,
      RoseReducedWords.system, loopA_apply, loopB_apply]

theorem continuous_edgeProjection : Continuous edgeProjection := by
  apply continuous_prod_of_discrete_left.mpr
  intro i
  exact (primitiveLoop i).continuous

theorem continuous_forgetVertex : Continuous forgetVertex :=
  (continuous_snd.comp continuous_fst).prodMk continuous_snd

theorem continuous_project : Continuous project := by
  apply CayleyTreeGeometry.key_isQuotientMap.continuous_iff.mpr
  simpa only [Function.comp_def, project_key] using
    continuous_edgeProjection.comp continuous_forgetVertex

theorem circleCover_interval_surjective (x : Circle) :
    ∃ t : unitInterval, circleCover (t : ℝ) = x := by
  have he : circleCover '' Set.Icc (0 : ℝ) 1 = Set.univ := by
    simpa [circleCover, _root_.zero_add] using AddCircle.coe_image_Icc_eq (1 : ℝ) (0 : ℝ)
  have hx : x ∈ circleCover '' Set.Icc (0 : ℝ) 1 := by rw [he]; trivial
  rcases hx with ⟨t, ht, htx⟩
  exact ⟨⟨t, ht⟩, htx⟩

theorem edgeProjection_surjective : Function.Surjective edgeProjection := by
  intro r
  induction r using Quotient.ind with
  | _ p =>
    cases p with
    | inl x =>
      obtain ⟨t, ht⟩ := circleCover_interval_surjective x
      refine ⟨(.a, t), ?_⟩
      change loopA t = leftInclude x
      rw [loopA_apply, ht]
    | inr x =>
      obtain ⟨t, ht⟩ := circleCover_interval_surjective x
      refine ⟨(.b, t), ?_⟩
      change loopB t = rightInclude x
      rw [loopB_apply, ht]

theorem edgeProjection_isQuotientMap : IsQuotientMap edgeProjection :=
  continuous_edgeProjection.isClosedMap.isQuotientMap
    continuous_edgeProjection edgeProjection_surjective

theorem forgetVertex_isQuotientMap : IsQuotientMap forgetVertex := by
  let sectionMap : Label × unitInterval → CayleyTreeGeometry.Raw :=
    fun r => ((1, r.1), r.2)
  have hs : Continuous sectionMap :=
    (continuous_const.prodMk continuous_fst).prodMk continuous_snd
  exact IsQuotientMap.of_inverse hs continuous_forgetVertex (fun _ => rfl)

theorem project_isQuotientMap : IsQuotientMap project := by
  apply CayleyTreeGeometry.key_isQuotientMap.of_comp_isQuotientMap
  have h := edgeProjection_isQuotientMap.comp forgetVertex_isQuotientMap
  simpa only [Function.comp_def, ← project_key] using h

theorem interior_circleCover_ne_zero (t : Interior) : circleCover (t : ℝ) ≠ 0 := by
  intro h
  have ht : (t : ℝ) ∈ Set.Ico (0 : ℝ) 1 := ⟨le_of_lt t.2.1, t.2.2⟩
  have hz : (t : ℝ) = 0 := (AddCircle.coe_eq_zero_iff_of_mem_Ico ht).mp h
  exact (ne_of_gt t.2.1) hz

theorem interior_circleCover_injective :
    Function.Injective (fun t : Interior => circleCover (t : ℝ)) := by
  intro t s h
  apply Subtype.ext
  have ht : (t : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    simpa only [_root_.zero_add] using (show (t : ℝ) ∈ Set.Ico (0 : ℝ) 1 from
      ⟨le_of_lt t.2.1, t.2.2⟩)
  have hs : (s : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    simpa only [_root_.zero_add] using (show (s : ℝ) ∈ Set.Ico (0 : ℝ) 1 from
      ⟨le_of_lt s.2.1, s.2.2⟩)
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico ht hs).mp h

@[simp] theorem project_smul (h : G) (z : Tree) : project (h • z) = project z := by
  cases z with
  | vertex g => rfl
  | inner g i t => cases i <;> rfl

theorem project_inner_ne_base (g : G) (i : Label) (t : Interior) :
    project (.inner g i t) ≠ base := by
  cases i with
  | a =>
    intro h
    have he := _root_.congrArg leftRetract h
    exact interior_circleCover_ne_zero t he
  | b =>
    intro h
    have he := _root_.congrArg rightRetract h
    exact interior_circleCover_ne_zero t he

theorem inner_coordinates_of_project_eq {g h : G} {i j : Label} {t s : Interior}
    (he : project (.inner g i t) = project (.inner h j s)) : i = j ∧ t = s := by
  cases i with
  | a =>
    cases j with
    | a =>
      exact ⟨rfl, interior_circleCover_injective (leftInclude_isEmbedding.injective he)⟩
    | b =>
      have hn := (leftInclude_eq_rightInclude (circleCover (t : ℝ))
        (circleCover (s : ℝ))).mp he
      exact (interior_circleCover_ne_zero t hn.1).elim
  | b =>
    cases j with
    | a =>
      have hn := (leftInclude_eq_rightInclude (circleCover (s : ℝ))
        (circleCover (t : ℝ))).mp he.symm
      exact (interior_circleCover_ne_zero t hn.2).elim
    | b =>
      exact ⟨rfl, interior_circleCover_injective (rightInclude_isEmbedding.injective he)⟩

theorem project_eq_iff_mem_orbit (z w : Tree) :
    project z = project w ↔ z ∈ MulAction.orbit G w := by
  constructor
  · intro he
    cases z with
    | vertex g =>
      cases w with
      | vertex h => exact ⟨g * h⁻¹, by simp⟩
      | inner h i t => exact (project_inner_ne_base h i t he.symm).elim
    | inner g i t =>
      cases w with
      | vertex h => exact (project_inner_ne_base g i t he).elim
      | inner h j s =>
        obtain ⟨rfl, rfl⟩ := inner_coordinates_of_project_eq he
        exact ⟨g * h⁻¹, by simp⟩
  · rintro ⟨h, rfl⟩
    exact project_smul h w

/-- The covering property follows from actual topology and exact fibers. -/
theorem covering : IsQuotientCoveringMap project G where
  __ := project_isQuotientMap
  continuous_const_smul := fun h => continuous_const_smul h
  apply_eq_iff_mem_orbit := project_eq_iff_mem_orbit _ _
  disjoint := CayleyTreeGeometry.disjoint_translates

theorem project_edge_apply (g : G) (i : Label) (t : unitInterval) :
    project (CayleyTreeGeometry.edge g i t) =
      (RoseReducedWords.system loopA loopB).realize i t :=
  project_key ((g, i), t)

theorem project_edge (g : G) (i : Label) :
    ((CayleyTreeGeometry.edge g i).map continuous_project).cast
      (project_vertex g).symm (project_vertex (g * FreeGroup.of i)).symm =
      (RoseReducedWords.system loopA loopB).realize i := by
  ext t
  exact project_edge_apply g i t

end
end ComputationalPaths.Path.GeometricTopology.CayleyRoseCovering
