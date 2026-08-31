import ComputationalPaths.Path.Topology.QuotientFundamentalGroup

/-!
# Semilocal simple connectivity and quotient fundamental groups

This module defines semilocal simple connectivity in the endpoint-fixed form
needed by the quotient-topological fundamental group.  It proves directly
from the compact-open neighborhood basis that an open null-homotopy class
supplies a semilocally simply connected neighborhood of the basepoint.  In
particular, discreteness of the quotient fundamental group implies the
semilocal condition without local path-connectedness assumptions.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open Set Topology
open scoped ContinuousMap Topology

noncomputable section

namespace QuotientFundamentalGroup

universe u

variable (X : Type u) [TopologicalSpace X]

attribute [local instance] _root_.Path.Homotopic.setoid

/-- A space is semilocally simply connected at `x` when some open
neighborhood of `x` has the property that every loop based at `x` and lying
in that neighborhood is null-homotopic in the ambient space. -/
def SemilocallySimplyConnectedAt (x : X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∀ γ : Loop X x, range γ ⊆ U →
      γ.Homotopic (_root_.Path.refl x)

/-- Pointwise semilocal simple connectivity. -/
def SemilocallySimplyConnected : Prop :=
  ∀ x : X, SemilocallySimplyConnectedAt X x

/-- Openness of the null-homotopy class gives a semilocally simply connected
neighborhood of the basepoint. -/
theorem semilocallySimplyConnectedAt_of_isOpen_nullHomotopyClass
    (x : X) (hopen : IsOpen (nullHomotopyClass X x)) :
    SemilocallySimplyConnectedAt X x := by
  have hrefl : _root_.Path.refl x ∈ nullHomotopyClass X x :=
    _root_.Path.Homotopic.refl (_root_.Path.refl x)
  have hnhds : nullHomotopyClass X x ∈ 𝓝 (_root_.Path.refl x) :=
    hopen.mem_nhds hrefl
  rw [mem_nhds_induced] at hnhds
  rcases hnhds with ⟨V, hV, hVsub⟩
  rw [ContinuousMap.mem_nhds_iff] at hV
  rcases hV with ⟨S, hSfinite, hSdata, hSsub⟩
  let U : Set X :=
    ⋂ KU ∈ S, ⋂ (_ : KU.1.Nonempty), KU.2
  have hUopen : IsOpen U := by
    dsimp [U]
    apply hSfinite.isOpen_biInter
    intro KU hKU
    by_cases hKne : KU.1.Nonempty
    · simpa [hKne] using (hSdata KU.1 KU.2 hKU).2.1
    · simp [hKne]
  have hxU : x ∈ U := by
    simp only [U, mem_iInter]
    intro KU hKU hKne
    obtain ⟨t, ht⟩ := hKne
    exact (hSdata KU.1 KU.2 hKU).2.2 ht
  refine ⟨U, hUopen, hxU, ?_⟩
  intro γ hγU
  apply hVsub
  apply hSsub
  intro K W hKW t ht
  by_cases hKne : K.Nonempty
  · have hmemU : γ t ∈ U := hγU ⟨t, rfl⟩
    simp only [U, mem_iInter] at hmemU
    exact hmemU (K, W) hKW hKne
  · exact (hKne ⟨t, ht⟩).elim

/-- Discreteness of the quotient-topological fundamental group implies the
semilocal simple-connectivity condition at its basepoint. -/
theorem semilocallySimplyConnectedAt_of_discreteTopology
    (x : X) [DiscreteTopology (LoopQuot X x)] :
    SemilocallySimplyConnectedAt X x :=
  semilocallySimplyConnectedAt_of_isOpen_nullHomotopyClass X x
    ((discreteTopology_iff_isOpen_nullHomotopyClass X x).mp inferInstance)

end QuotientFundamentalGroup

end
end GeometricTopology
end Path
end ComputationalPaths
