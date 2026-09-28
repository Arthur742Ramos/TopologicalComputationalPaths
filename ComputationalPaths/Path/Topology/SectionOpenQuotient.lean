import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Maps.OpenQuotient

/-!
# Open quotient maps after a split projection

This elementary lemma is used when a raw representative carries extra trace
data but has a continuous geometric projection with a continuous section.
For a composable-pair constraint on the quotient, the restricted product map
is quotient whenever the geometric quotient is open.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped Topology

variable {T U Q : Type*} [TopologicalSpace T] [TopologicalSpace U]
  [TopologicalSpace Q]

theorem restricted_product_isQuotient_of_section_open
    (f : T → U) (s : U → T) (q : U → Q)
    (hf : Continuous f) (hs : Continuous s)
    (hfs : ∀ u, f (s u) = u)
    (hq : IsOpenQuotientMap q) (C : Set (Q × Q)) :
    Topology.IsQuotientMap
      (C.restrictPreimage (Prod.map (q ∘ f) (q ∘ f))) := by
  let F : T × T → U × U := Prod.map f f
  let S : U × U → T × T := Prod.map s s
  let Qmap : U × U → Q × Q := Prod.map q q
  let R : (Qmap ∘ F) ⁻¹' C → Qmap ⁻¹' C :=
    fun x => ⟨F x.val, x.property⟩
  let Rsection : Qmap ⁻¹' C → (Qmap ∘ F) ⁻¹' C :=
    fun y => ⟨S y.val, by
      rcases y with ⟨⟨u, v⟩, hy⟩
      simpa [Qmap, F, S, hfs] using hy⟩
  have hR : Continuous R := by
    exact Continuous.subtype_mk
      ((hf.prodMap hf).comp continuous_subtype_val) _
  have hS : Continuous Rsection := by
    exact Continuous.subtype_mk
      ((hs.prodMap hs).comp continuous_subtype_val) _
  have hright : ∀ y, R (Rsection y) = y := by
    intro y
    apply Subtype.ext
    rcases y with ⟨⟨u, v⟩, hy⟩
    simp [R, Rsection, F, S, hfs]
  have hRq : Topology.IsQuotientMap R := by
    refine ⟨(Topology.isCoinducing_iff).2 ?_, ?_⟩
    · intro W
      constructor
      · intro hpre
        have h := hpre.preimage hS
        have hset : Rsection ⁻¹' (R ⁻¹' W) = W := by
          ext y
          simp [hright]
        simpa only [hset] using h
      · intro hW
        exact hW.preimage hR
    · intro y
      exact ⟨Rsection y, hright y⟩
  have hQ : Topology.IsQuotientMap
      (C.restrictPreimage Qmap) :=
    ((hq.prodMap hq).restrictPreimage C).isQuotientMap
  have hcomp := hQ.comp hRq
  change Topology.IsQuotientMap (C.restrictPreimage (Qmap ∘ F))
  exact hcomp

end GeometricTopology
end Path
end ComputationalPaths
