import ComputationalPaths.Path.Topology.RoseReducedWords
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Geometric edges of the two-generator Cayley tree

The vertices are free-group words. Each oriented edge is a genuine unit
interval, from `g` to `g * of i`. The topology is the final topology of those
closed intervals: vertices are not isolated. Interior coordinates are retained
only to make the endpoint identifications explicit.

This module constructs the geometric carrier and its translation action.
The covering map to the rose and geometric completeness are separate results.
-/

namespace ComputationalPaths.Path.GeometricTopology.CayleyTreeGeometry

open Set Topology
open RoseReducedWords

noncomputable section

abbrev G := FreeGroup Label
instance : TopologicalSpace G := ⊥
instance : DiscreteTopology G := discreteTopology_bot G

abbrev Interior := Set.Ioo (0 : ℝ) 1
abbrev Raw := (G × Label) × unitInterval

/-- Every endpoint is a vertex; each open edge retains its coordinates. -/
inductive Tree
  | vertex : G → Tree
  | inner : G → Label → Interior → Tree

def key (r : Raw) : Tree :=
  if h₀ : (r.2 : ℝ) = 0 then .vertex r.1.1
  else if h₁ : (r.2 : ℝ) = 1 then .vertex (r.1.1 * FreeGroup.of r.1.2)
  else .inner r.1.1 r.1.2
    ⟨r.2, lt_of_le_of_ne r.2.2.1 (Ne.symm h₀),
      lt_of_le_of_ne r.2.2.2 h₁⟩

instance : TopologicalSpace Tree := TopologicalSpace.coinduced key inferInstance

@[simp] theorem key_zero (g : G) (i : Label) : key ((g, i), 0) = .vertex g := by
  simp [key]

@[simp] theorem key_one (g : G) (i : Label) :
    key ((g, i), 1) = .vertex (g * FreeGroup.of i) := by
  simp [key]

theorem key_interior (g : G) (i : Label) (t : Interior) :
    key ((g, i), ⟨t, le_of_lt t.2.1, le_of_lt t.2.2⟩) = .inner g i t := by
  simp only [key, ne_of_gt t.2.1, ne_of_lt t.2.2, dite_false]

theorem key_surjective : Function.Surjective key := by
  intro z
  cases z with
  | vertex g => exact ⟨((g, .a), 0), key_zero g .a⟩
  | inner g i t => exact ⟨((g, i), ⟨t, le_of_lt t.2.1, le_of_lt t.2.2⟩),
      key_interior g i t⟩

theorem key_isQuotientMap : IsQuotientMap key := ⟨⟨rfl⟩, key_surjective⟩
theorem continuous_key : Continuous key := key_isQuotientMap.continuous

/-- A closed geometric edge with the usual interval parameter. -/
def edge (g : G) (i : Label) :
    _root_.Path (Tree.vertex g) (Tree.vertex (g * FreeGroup.of i)) where
  toFun t := key ((g, i), t)
  continuous_toFun := continuous_key.comp (continuous_const.prodMk continuous_id)
  source' := key_zero g i
  target' := key_one g i

def translate (h : G) : Tree → Tree
  | .vertex g => .vertex (h * g)
  | .inner g i t => .inner (h * g) i t

instance : MulAction G Tree where
  smul := translate
  one_smul z := by
    show translate 1 z = z
    cases z <;> simp [translate]
  mul_smul h k z := by
    show translate (h * k) z = translate h (translate k z)
    cases z <;> simp [translate, mul_assoc]

@[simp] theorem smul_vertex (h g : G) : h • Tree.vertex g = .vertex (h * g) := rfl
@[simp] theorem smul_inner (h g : G) (i : Label) (t : Interior) :
    h • Tree.inner g i t = .inner (h * g) i t := rfl

theorem translate_key (h : G) (r : Raw) :
    h • key r = key ((h * r.1.1, r.1.2), r.2) := by
  unfold key
  split_ifs <;> simp [translate, HSMul.hSMul, SMul.smul, mul_assoc]

instance : ContinuousConstSMul G Tree where
  continuous_const_smul h := by
    apply key_isQuotientMap.continuous_iff.mpr
    have hc : Continuous (fun r : Raw => ((h * r.1.1, r.1.2), r.2)) :=
      ((continuous_of_discreteTopology : Continuous (fun p : G × Label =>
        (h * p.1, p.2))).comp continuous_fst).prodMk continuous_snd
    simpa only [Function.comp_def, translate_key] using continuous_key.comp hc

/-- Word distance on the vertices, extended affinely along every actual edge. -/
def distanceFrom (v : G) : Tree → ℝ
  | .vertex g => FreeGroup.norm (v⁻¹ * g)
  | .inner g i t =>
      (1 - (t : ℝ)) * (FreeGroup.norm (v⁻¹ * g) : ℝ) +
        (t : ℝ) * (FreeGroup.norm (v⁻¹ * (g * FreeGroup.of i)) : ℝ)

theorem distanceFrom_key (v : G) (r : Raw) :
    distanceFrom v (key r) =
      (1 - (r.2 : ℝ)) * (FreeGroup.norm (v⁻¹ * r.1.1) : ℝ) +
        (r.2 : ℝ) * (FreeGroup.norm (v⁻¹ * (r.1.1 * FreeGroup.of r.1.2)) : ℝ) := by
  by_cases h₀ : (r.2 : ℝ) = 0
  · simp [key, h₀, distanceFrom]
  · by_cases h₁ : (r.2 : ℝ) = 1
    · simp [key, h₁, distanceFrom]
    · simp [key, h₀, h₁, distanceFrom]

theorem continuous_distanceFrom (v : G) : Continuous (distanceFrom v) := by
  apply key_isQuotientMap.continuous_iff.mpr
  simp only [Function.comp_def, distanceFrom_key]
  apply continuous_prod_of_discrete_left.mpr
  intro p
  change Continuous (fun t : unitInterval =>
    (1 - (t : ℝ)) * (FreeGroup.norm (v⁻¹ * p.1) : ℝ) +
      (t : ℝ) * (FreeGroup.norm (v⁻¹ * (p.1 * FreeGroup.of p.2)) : ℝ))
  have hc : Continuous (fun t : unitInterval => (t : ℝ)) := continuous_subtype_val
  exact ((continuous_const.sub hc).mul continuous_const).add (hc.mul continuous_const)

@[simp] theorem distanceFrom_self (v : G) : distanceFrom v (.vertex v) = 0 := by
  simp [distanceFrom]

theorem distanceFrom_smul (v h : G) (z : Tree) :
    distanceFrom (h * v) (h • z) = distanceFrom v z := by
  cases z <;> simp [distanceFrom, mul_assoc]

theorem vertex_triangle (v w g : G) :
    (FreeGroup.norm (v⁻¹ * w) : ℝ) ≤
      (FreeGroup.norm (v⁻¹ * g) : ℝ) + (FreeGroup.norm (w⁻¹ * g) : ℝ) := by
  have ht := FreeGroup.norm_mul_le (v⁻¹ * g) (g⁻¹ * w)
  have hi : FreeGroup.norm (g⁻¹ * w) = FreeGroup.norm (w⁻¹ * g) := by
    simpa using (FreeGroup.norm_inv_eq (x := w⁻¹ * g))
  have hc : (v⁻¹ * g) * (g⁻¹ * w) = v⁻¹ * w := by simp [mul_assoc]
  rw [hc, hi] at ht
  exact_mod_cast ht

theorem distanceFrom_triangle (v w : G) (z : Tree) :
    (FreeGroup.norm (v⁻¹ * w) : ℝ) ≤ distanceFrom v z + distanceFrom w z := by
  cases z with
  | vertex g => exact vertex_triangle v w g
  | inner g i t =>
      have h₀ := vertex_triangle v w g
      have h₁ := vertex_triangle v w (g * FreeGroup.of i)
      have ht₀ := t.2.1
      have ht₁ := t.2.2
      have hw₀ := mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr (le_of_lt ht₁))
      have hw₁ := mul_le_mul_of_nonneg_left h₁ (le_of_lt ht₀)
      simp only [distanceFrom]
      nlinarith [hw₀, hw₁]

def vertexNeighborhood (v : G) : Set Tree := {z | distanceFrom v z < 1 / 3}

theorem isOpen_vertexNeighborhood (v : G) : IsOpen (vertexNeighborhood v) :=
  isOpen_lt (continuous_distanceFrom v) continuous_const

theorem vertex_mem_vertexNeighborhood (v : G) : .vertex v ∈ vertexNeighborhood v := by
  simp [vertexNeighborhood]

theorem vertexNeighborhood_disjoint {v w : G} (h : v ≠ w) :
    Disjoint (vertexNeighborhood v) (vertexNeighborhood w) := by
  apply Set.disjoint_left.mpr
  intro z hzv hzw
  have hn : FreeGroup.norm (v⁻¹ * w) ≠ 0 := by
    intro hn
    have he := FreeGroup.norm_eq_zero.mp hn
    exact h (inv_mul_eq_one.mp he)
  have hpos : 1 ≤ FreeGroup.norm (v⁻¹ * w) := Nat.one_le_iff_ne_zero.mpr hn
  have hp : (1 : ℝ) ≤ (FreeGroup.norm (v⁻¹ * w) : ℝ) := by exact_mod_cast hpos
  have ht := distanceFrom_triangle v w z
  change distanceFrom v z < 1 / 3 at hzv
  change distanceFrom w z < 1 / 3 at hzw
  linarith

/-- The open interior of one geometric edge. -/
def edgeInterior (g : G) (i : Label) : Set Tree :=
  {z | ∃ t : Interior, z = .inner g i t}

theorem key_preimage_edgeInterior (g : G) (i : Label) :
    key ⁻¹' edgeInterior g i =
      {r : Raw | r.1 = (g, i) ∧ 0 < (r.2 : ℝ) ∧ (r.2 : ℝ) < 1} := by
  ext r
  simp only [Set.mem_preimage, edgeInterior, Set.mem_setOf_eq]
  unfold key
  split_ifs with h₀ h₁
  · simp [h₀]
  · simp [h₁]
  · constructor
    · rintro ⟨t, ht⟩
      have hh := Tree.inner.inj ht
      exact ⟨Prod.ext hh.1 hh.2.1,
        lt_of_le_of_ne r.2.2.1 (Ne.symm h₀), lt_of_le_of_ne r.2.2.2 h₁⟩
    · rintro ⟨he, ht₀, ht₁⟩
      refine ⟨⟨r.2, ht₀, ht₁⟩, ?_⟩
      have hg := _root_.congrArg Prod.fst he
      have hi := _root_.congrArg Prod.snd he
      simp only [hg, hi]

theorem isOpen_edgeInterior (g : G) (i : Label) : IsOpen (edgeInterior g i) := by
  apply key_isQuotientMap.isCoinducing.isOpen_preimage.mp
  rw [key_preimage_edgeInterior]
  have ht : IsOpen {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} :=
    (isOpen_lt continuous_const continuous_subtype_val).inter
      (isOpen_lt continuous_subtype_val continuous_const)
  exact ((isOpen_discrete {p : G × Label | p = (g, i)}).preimage continuous_fst).inter
    (ht.preimage continuous_snd)

theorem disjoint_translates (z : Tree) :
    ∃ U ∈ 𝓝 z, ∀ h : G, ((h • ·) '' U ∩ U).Nonempty → h = 1 := by
  cases z with
  | vertex v =>
      refine ⟨vertexNeighborhood v,
        (isOpen_vertexNeighborhood v).mem_nhds (vertex_mem_vertexNeighborhood v), ?_⟩
      intro h hmeet
      by_contra hh
      have hv : h * v ≠ v := by
        intro he
        apply hh
        exact mul_right_cancel (he.trans (one_mul v).symm)
      obtain ⟨z, ⟨y, hy, rfl⟩, hz⟩ := hmeet
      have hhy : h • y ∈ vertexNeighborhood (h * v) := by
        simpa only [vertexNeighborhood, Set.mem_setOf_eq, distanceFrom_smul] using hy
      exact Set.disjoint_left.mp (vertexNeighborhood_disjoint hv) hhy hz
  | inner g i t =>
      refine ⟨edgeInterior g i,
        (isOpen_edgeInterior g i).mem_nhds ⟨t, rfl⟩, ?_⟩
      intro h hmeet
      obtain ⟨z, ⟨y, ⟨s, rfl⟩, rfl⟩, ⟨r, he⟩⟩ := hmeet
      have hg : h * g = g := by
        exact (Tree.inner.inj he).1
      exact mul_right_cancel (hg.trans (one_mul g).symm)

end
end ComputationalPaths.Path.GeometricTopology.CayleyTreeGeometry
