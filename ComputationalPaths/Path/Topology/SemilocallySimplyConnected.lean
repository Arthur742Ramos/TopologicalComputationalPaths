import ComputationalPaths.Path.Topology.QuotientFundamentalGroup
import Mathlib.Topology.Connected.LocallyPathConnected

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

/-- Every loop contained in `U`, with arbitrary basepoint in `U`, is
null-homotopic in the ambient space.  This is the basepoint-uniform local
condition used in compact subdivision arguments. -/
def LoopsNullIn (U : Set X) : Prop :=
  ∀ y ∈ U, ∀ γ : Loop X y, range γ ⊆ U →
    γ.Homotopic (_root_.Path.refl y)

/-- Cancelling the two sides of a null-homotopic conjugate shows that its
middle loop is null-homotopic. -/
private theorem homotopic_refl_of_conjugate_homotopic_refl
    {x y : X} (α : _root_.Path x y) (γ : Loop X y)
    (h : (α.trans (γ.trans α.symm)).Homotopic (_root_.Path.refl x)) :
    γ.Homotopic (_root_.Path.refl y) := by
  let a := _root_.Path.Homotopic.Quotient.mk α
  let g := _root_.Path.Homotopic.Quotient.mk γ
  have hq : a.trans (g.trans a.symm) =
      _root_.Path.Homotopic.Quotient.refl x := by
    have hmk : _root_.Path.Homotopic.Quotient.mk
        (α.trans (γ.trans α.symm)) =
        _root_.Path.Homotopic.Quotient.mk (_root_.Path.refl x) :=
      _root_.Path.Homotopic.Quotient.eq.mpr h
    simpa only [a, g, _root_.Path.Homotopic.Quotient.mk_trans,
      _root_.Path.Homotopic.Quotient.mk_symm,
      _root_.Path.Homotopic.Quotient.mk_refl] using hmk
  have hcancel := congrArg
    (fun q => (a.symm.trans q).trans a) hq
  have hg : g = _root_.Path.Homotopic.Quotient.refl y := by
    simp only [_root_.Path.Homotopic.Quotient.trans_assoc,
      _root_.Path.Homotopic.Quotient.trans_refl] at hcancel
    rw [← _root_.Path.Homotopic.Quotient.trans_assoc,
      _root_.Path.Homotopic.Quotient.symm_trans,
      _root_.Path.Homotopic.Quotient.refl_trans,
      _root_.Path.Homotopic.Quotient.trans_refl] at hcancel
    exact hcancel
  exact _root_.Path.Homotopic.Quotient.eq.mp (by simpa [g] using hg)

/-- In a locally path-connected semilocally simply connected space, every
point has an open path-connected neighborhood on which loops based at any
point are null-homotopic in the ambient space. -/
theorem exists_open_pathConnected_loopsNullIn
    [LocallyPathConnectedSpace X]
    (hsemi : SemilocallySimplyConnected X) (x : X) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ IsPathConnected V ∧ LoopsNullIn X V := by
  rcases hsemi x with ⟨U, hUopen, hxU, hU⟩
  have hUnhds : U ∈ 𝓝 x := hUopen.mem_nhds hxU
  rcases ((isOpen_isPathConnected_basis x).mem_iff.mp hUnhds) with
    ⟨V, ⟨hVopen, hxV, hVpath⟩, hVU⟩
  refine ⟨V, hVopen, hxV, hVpath, ?_⟩
  intro y hyV γ hγV
  let joined : JoinedIn V x y := hVpath.joinedIn x hxV y hyV
  let α : _root_.Path x y := joined.somePath
  apply homotopic_refl_of_conjugate_homotopic_refl X α γ
  apply hU
  rw [_root_.Path.trans_range, _root_.Path.trans_range]
  refine union_subset (fun _ hz => ?_)
    (union_subset (fun _ hz => hVU (hγV hz)) ?_)
  · rcases hz with ⟨t, rfl⟩
    exact hVU (joined.somePath_mem t)
  · intro z hz
    rw [_root_.Path.symm_range] at hz
    rcases hz with ⟨t, rfl⟩
    exact hVU (joined.somePath_mem t)

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
