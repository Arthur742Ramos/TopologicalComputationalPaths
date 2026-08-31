import ComputationalPaths.Path.Topology.QuotientFundamentalGroup
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Subpath

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
open scoped ContinuousMap Topology unitInterval

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

/-- Every path in a locally path-connected semilocally simply connected
space has a finite monotone subdivision whose pieces lie in open
path-connected sets on which all ambient loops are null. -/
theorem exists_finite_null_subdivision
    [LocallyPathConnectedSpace X]
    (hsemi : SemilocallySimplyConnected X)
    {a b : X} (γ : _root_.Path a b) :
    ∃ n : ℕ, ∃ t : Fin (n + 1) → I, ∃ V : Fin n → Set X,
      t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧
      ∀ i : Fin n,
        IsOpen (V i) ∧ IsPathConnected (V i) ∧ LoopsNullIn X (V i) ∧
          range (γ.subpath (t i.castSucc) (t i.succ)) ⊆ V i := by
  choose V hVopen hγV hVpath hVnull using
    fun s : I => exists_open_pathConnected_loopsNullIn X hsemi (γ s)
  let c : I → Set I := fun s => γ ⁻¹' V s
  have hcopen : ∀ s, IsOpen (c s) :=
    fun s => (hVopen s).preimage γ.continuous
  have hccover : (univ : Set I) ⊆ ⋃ s, c s := by
    intro s _
    exact mem_iUnion.mpr ⟨s, hγV s⟩
  rcases exists_monotone_Icc_subset_open_cover_unitInterval hcopen hccover with
    ⟨tNat, htzero, htmono, ⟨m, htm⟩, hpieces⟩
  let t : Fin (m + 1) → I := fun i => tNat i
  choose idx hidx using fun i : Fin m => hpieces i
  let W : Fin m → Set X := fun i => V (idx i)
  refine ⟨m, t, W, ?_, ?_, ?_, ?_⟩
  · exact htzero
  · exact htm m le_rfl
  · intro i j hij
    exact htmono (by exact_mod_cast hij)
  · intro i
    refine ⟨hVopen (idx i), hVpath (idx i), hVnull (idx i), ?_⟩
    rw [_root_.Path.range_subpath_of_le]
    · rintro _ ⟨s, hs, rfl⟩
      exact hidx i hs
    · exact htmono (Nat.le_succ i)

/-- A compact-open subbasic condition remains open after restricting from
the continuous-map space to the based path space. -/
theorem isOpen_loops_mapsTo
    (x : X) {K : Set I} {U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) :
    IsOpen {γ : Loop X x | MapsTo γ K U} := by
  exact isOpen_induced
    (ContinuousMap.isOpen_setOf_mapsTo hK hU)

/-- A finite family of compact-open range conditions is open in the based
loop space. -/
theorem isOpen_loops_mapsTo_finite
    {x : X} {n : ℕ} (K : Fin n → Set I) (U : Fin n → Set X)
    (hK : ∀ i, IsCompact (K i)) (hU : ∀ i, IsOpen (U i)) :
    IsOpen {γ : Loop X x | ∀ i, MapsTo γ (K i) (U i)} := by
  rw [show {γ : Loop X x | ∀ i, MapsTo γ (K i) (U i)} =
      ⋂ i, {γ : Loop X x | MapsTo γ (K i) (U i)} by ext; simp]
  let S : Set (Fin n) := univ
  rw [show ⋂ i, {γ : Loop X x | MapsTo γ (K i) (U i)} =
      ⋂ i ∈ S, {γ : Loop X x | MapsTo γ (K i) (U i)} by simp [S]]
  exact (Set.toFinite S).isOpen_biInter fun i _ =>
    isOpen_loops_mapsTo X x (hK i) (hU i)

set_option backward.isDefEq.respectTransparency false in
/-- A finite ladder of homotopy-commuting path cells identifies the two
concatenated boundary paths, up to the two boundary connectors. -/
theorem homotopic_concat_of_homotopic_ladder
    {n : ℕ} (p q : Fin (n + 1) → X)
    (β : (i : Fin (n + 1)) → _root_.Path (p i) (q i))
    (F : (i : Fin n) → _root_.Path (p i.castSucc) (p i.succ))
    (G : (i : Fin n) → _root_.Path (q i.castSucc) (q i.succ))
    (hcell : ∀ i, (F i).Homotopic
      ((β i.castSucc).trans ((G i).trans (β i.succ).symm))) :
    (_root_.Path.concat p F).Homotopic
      ((β 0).trans ((_root_.Path.concat q G).trans (β (Fin.last n)).symm)) := by
  rw [← _root_.Path.Homotopic.Quotient.eq]
  induction n with
  | zero =>
      simp [_root_.Path.concat_zero]
  | succ n ih =>
      rw [_root_.Path.concat_succ, _root_.Path.concat_succ]
      simp only [_root_.Path.Homotopic.Quotient.mk_trans,
        _root_.Path.Homotopic.Quotient.mk_symm]
      have ih' := ih (p ∘ Fin.castSucc) (q ∘ Fin.castSucc)
        (fun i => β i.castSucc) (fun i => F i.castSucc)
        (fun i => G i.castSucc) (fun i => hcell i.castSucc)
      simp only [_root_.Path.Homotopic.Quotient.mk_trans,
        _root_.Path.Homotopic.Quotient.mk_symm] at ih'
      have hlast := _root_.Path.Homotopic.Quotient.eq.mpr
        (hcell (Fin.last n))
      simp only [_root_.Path.Homotopic.Quotient.mk_trans,
        _root_.Path.Homotopic.Quotient.mk_symm] at hlast
      rw [ih', hlast]
      simp only [_root_.Path.Homotopic.Quotient.trans_assoc]
      rw [← _root_.Path.Homotopic.Quotient.trans_assoc
        (_root_.Path.Homotopic.Quotient.mk (β (Fin.last n).castSucc)).symm
        (_root_.Path.Homotopic.Quotient.mk (β (Fin.last n).castSucc)),
        _root_.Path.Homotopic.Quotient.symm_trans,
        _root_.Path.Homotopic.Quotient.refl_trans]
      rfl

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
