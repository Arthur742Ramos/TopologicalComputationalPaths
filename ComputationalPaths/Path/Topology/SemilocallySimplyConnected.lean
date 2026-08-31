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
semilocal condition without local path-connectedness assumptions; conversely,
locally path-connected semilocal spaces have open classes and discrete
quotients by a finite subdivision and ladder argument.
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

/-- If the rectangular boundary formed by two horizontal paths and two
connectors is null-homotopic, then the horizontal paths commute with the
connectors up to endpoint-fixed homotopy. -/
theorem homotopic_of_boundary_homotopic_refl
    {p₀ p₁ q₀ q₁ : X}
    (F : _root_.Path p₀ p₁) (G : _root_.Path q₀ q₁)
    (b₀ : _root_.Path p₀ q₀) (b₁ : _root_.Path p₁ q₁)
    (h : (F.trans (b₁.trans (G.symm.trans b₀.symm))).Homotopic
      (_root_.Path.refl p₀)) :
    F.Homotopic (b₀.trans (G.trans b₁.symm)) := by
  let f := _root_.Path.Homotopic.Quotient.mk F
  let g := _root_.Path.Homotopic.Quotient.mk G
  let c₀ := _root_.Path.Homotopic.Quotient.mk b₀
  let c₁ := _root_.Path.Homotopic.Quotient.mk b₁
  have hq : f.trans (c₁.trans (g.symm.trans c₀.symm)) =
      _root_.Path.Homotopic.Quotient.refl p₀ := by
    have hmk := _root_.Path.Homotopic.Quotient.eq.mpr h
    simpa only [f, g, c₀, c₁,
      _root_.Path.Homotopic.Quotient.mk_trans,
      _root_.Path.Homotopic.Quotient.mk_symm,
      _root_.Path.Homotopic.Quotient.mk_refl] using hmk
  have h₁ := congrArg (fun z => z.trans c₀) hq
  simp only [_root_.Path.Homotopic.Quotient.trans_assoc,
    _root_.Path.Homotopic.Quotient.symm_trans,
    _root_.Path.Homotopic.Quotient.trans_refl,
    _root_.Path.Homotopic.Quotient.refl_trans] at h₁
  have h₂ := congrArg (fun z => z.trans g) h₁
  simp only [_root_.Path.Homotopic.Quotient.trans_assoc,
    _root_.Path.Homotopic.Quotient.symm_trans,
    _root_.Path.Homotopic.Quotient.trans_refl] at h₂
  have h₃ := congrArg (fun z => z.trans c₁.symm) h₂
  simp only [_root_.Path.Homotopic.Quotient.trans_assoc,
    _root_.Path.Homotopic.Quotient.trans_symm,
    _root_.Path.Homotopic.Quotient.trans_refl] at h₃
  exact _root_.Path.Homotopic.Quotient.eq.mp
    (by simpa [f, g, c₀, c₁] using h₃)

/-- A rectangular boundary with constant endpoint connectors is homotopic to
the middle path after transporting its endpoints along those connectors. -/
theorem homotopic_boundary_cast_refl
    {x a b c d : X} (C : _root_.Path b d)
    (ha : a = x) (hb : b = x) (hc : c = x) (hd : d = x) :
    (let B₀ : _root_.Path a b := (_root_.Path.refl x).cast ha hb
     let B₁ : _root_.Path c d := (_root_.Path.refl x).cast hc hd
     (B₀.trans (C.trans B₁.symm)).Homotopic
       (C.cast (ha.trans hb.symm) (hc.trans hd.symm))) := by
  cases ha
  cases hb
  cases hc
  cases hd
  simp only [_root_.Path.cast_rfl_rfl, _root_.Path.refl_symm]
  exact (_root_.Path.Homotopic.refl_trans _).trans
    (_root_.Path.Homotopic.trans_refl _)

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

/-- In a locally path-connected semilocally simply connected space, every
endpoint-fixed loop homotopy class is open in the compact-open loop space.
The proof uses a finite path subdivision and a path-connected refinement at
each subdivision vertex, then assembles the resulting null cells by a finite
ladder. -/
theorem isOpen_homotopyClass_of_semilocallySimplyConnected
    [LocallyPathConnectedSpace X]
    (hsemi : SemilocallySimplyConnected X) (x : X) (gamma : Loop X x) :
    IsOpen {delta : Loop X x | gamma.Homotopic delta} := by
  rw [isOpen_iff_forall_mem_open]
  intro eta heta
  rcases exists_finite_null_subdivision X hsemi eta with
    ⟨n, t, V, ht0, ht1, htmono, hV⟩
  cases n with
  | zero =>
      simp only [Fin.reduceLast] at ht1
      exact (zero_ne_one (ht0.symm.trans ht1)).elim
  | succ m =>
      choose hVopen hVpath hVnull hVrange using hV
      have hnode : ∀ j : Fin m, ∃ W : Set X,
          IsOpen W ∧ eta (t (j.succ.castSucc)) ∈ W ∧ IsPathConnected W ∧
            W ⊆ V j.castSucc ∩ V j.succ := by
        intro j
        have hleft : eta (t (j.succ.castSucc)) ∈ V j.castSucc := by
          have hidx : j.castSucc.succ = j.succ.castSucc := by ext; rfl
          rw [← hidx]
          apply hVrange j.castSucc
          exact Path.target_mem_range _
        have hright : eta (t (j.succ.castSucc)) ∈ V j.succ := by
          apply hVrange j.succ
          exact Path.source_mem_range _
        have hinterOpen : IsOpen (V j.castSucc ∩ V j.succ) :=
          (hVopen j.castSucc).inter (hVopen j.succ)
        rcases ((isOpen_isPathConnected_basis (eta (t (j.succ.castSucc)))).mem_iff.mp
          (hinterOpen.mem_nhds ⟨hleft, hright⟩)) with
          ⟨W, ⟨hWopen, hetaW, hWpath⟩, hWsub⟩
        exact ⟨W, hWopen, hetaW, hWpath, hWsub⟩
      choose W hWopen hetaW hWpath hWsub using hnode
      let Kseg : Fin (m + 1) → Set I := fun i => Icc (t i.castSucc) (t i.succ)
      let Knode : Fin m → Set I := fun j => {t (j.succ.castSucc)}
      let N : Set (Loop X x) :=
        {delta | ∀ i, MapsTo delta (Kseg i) (V i)} ∩
        {delta | ∀ j, MapsTo delta (Knode j) (W j)}
      have hNopen : IsOpen N := by
        apply IsOpen.inter
        · apply isOpen_loops_mapsTo_finite X Kseg V
          · intro i
            exact isCompact_Icc
          · exact hVopen
        · apply isOpen_loops_mapsTo_finite X Knode W
          · intro j
            exact isCompact_singleton
          · exact hWopen
      have hetaN : eta ∈ N := by
        constructor
        · intro i s hs
          apply hVrange i
          rw [Path.range_subpath_of_le]
          · exact ⟨s, hs, rfl⟩
          · exact htmono (Fin.castSucc_le_succ i)
        · intro j y hy
          change y ∈ ({t (j.succ.castSucc)} : Set I) at hy
          rw [mem_singleton_iff] at hy
          subst y
          exact hetaW j
      refine ⟨N, ?_, hNopen, hetaN⟩
      intro delta hdeltaN
      apply heta.trans
      let NodeU : Fin (m + 2) → Set X := fun i =>
        Fin.lastCases ({x} : Set X)
          (fun k => Fin.cases ({x} : Set X) (fun j => W j) k) i
      have hNodeLast : NodeU (Fin.last (m + 1)) = {x} := by
        simp [NodeU]
      have hNodeZeroCast : NodeU ((0 : Fin (m + 1)).castSucc) = {x} := by
        unfold NodeU
        convert (Fin.lastCases_castSucc (i := (0 : Fin (m + 1)))
          (motive := fun _ => Set X)
          (last := ({x} : Set X))
          (cast := fun k => Fin.cases ({x} : Set X) (fun j => W j) k)) using 1 <;> rfl
      have hzeroIdx : (0 : Fin (m + 1)).castSucc = (0 : Fin (m + 2)) := rfl
      have hNodeInternal (j : Fin m) : NodeU (j.succ.castSucc) = W j := by
        change Fin.lastCases ({x} : Set X)
          (fun k => Fin.cases ({x} : Set X) (fun j => W j) k)
            j.succ.castSucc = W j
        rw [Fin.lastCases_castSucc]
        rfl
      have hNodePath : ∀ i, IsPathConnected (NodeU i) := by
        intro i
        refine Fin.lastCases ?_ (fun k => Fin.cases ?_ (fun j => ?_) k) i
        · rw [hNodeLast]
          exact isPathConnected_singleton x
        · rw [hNodeZeroCast]
          exact isPathConnected_singleton x
        · rw [hNodeInternal]
          exact hWpath j
      have hetaNode : ∀ i, eta (t i) ∈ NodeU i := by
        intro i
        refine Fin.lastCases ?_ (fun k => Fin.cases ?_ (fun j => ?_) k) i
        · rw [hNodeLast, ht1]
          simp
        · rw [hNodeZeroCast, hzeroIdx, ht0]
          simp
        · rw [hNodeInternal]
          exact hetaW j
      have hdeltaNode : ∀ i, delta (t i) ∈ NodeU i := by
        intro i
        refine Fin.lastCases ?_ (fun k => Fin.cases ?_ (fun j => ?_) k) i
        · rw [hNodeLast, ht1]
          simp
        · rw [hNodeZeroCast, hzeroIdx, ht0]
          simp
        · have hj := hdeltaN.2 j
          have : delta (t (j.succ.castSucc)) ∈ W j := by
            apply hj
            simp [Knode]
          rw [hNodeInternal]
          exact this
      have hetaZero : eta (t 0) = x := by simpa [ht0] using eta.source
      have hdeltaZero : delta (t 0) = x := by simpa [ht0] using delta.source
      have hetaLast : eta (t (Fin.last (m + 1))) = x := by
        simpa [ht1] using eta.target
      have hdeltaLast : delta (t (Fin.last (m + 1))) = x := by
        simpa [ht1] using delta.target
      let betaZero : Path (eta (t 0)) (delta (t 0)) :=
        (Path.refl x).cast hetaZero hdeltaZero
      let betaLast : Path (eta (t (Fin.last (m + 1))))
          (delta (t (Fin.last (m + 1)))) :=
        (Path.refl x).cast hetaLast hdeltaLast
      let joinedInternal (j : Fin m) :
          JoinedIn (W j) (eta (t (j.succ.castSucc)))
            (delta (t (j.succ.castSucc))) :=
        (hWpath j).joinedIn _ (hetaW j) _ (by
          rw [← hNodeInternal j]
          exact hdeltaNode (j.succ.castSucc))
      let betaInternal (j : Fin m) :
          Path (eta (t (j.succ.castSucc))) (delta (t (j.succ.castSucc))) :=
        (joinedInternal j).somePath
      let beta (i : Fin (m + 2)) : Path (eta (t i)) (delta (t i)) :=
        Fin.lastCases betaLast
          (fun k => Fin.cases betaZero (fun j => betaInternal j) k) i
      have hbetaLastIdx : beta (Fin.last (m + 1)) = betaLast := by
        simp [beta]
      have hbetaZeroIdx : beta ((0 : Fin (m + 1)).castSucc) = betaZero := by
        unfold beta
        rw [Fin.lastCases_castSucc]
        rfl
      have hbetaInternalIdx (j : Fin m) :
          beta (j.succ.castSucc) = betaInternal j := by
        unfold beta
        rw [Fin.lastCases_castSucc]
        rfl
      have hbetaZeroRange : range betaZero ⊆ ({x} : Set X) := by
        simpa [betaZero, Path.cast] using (Path.refl_range (a := x))
      have hbetaLastRange : range betaLast ⊆ ({x} : Set X) := by
        simpa [betaLast, Path.cast] using (Path.refl_range (a := x))
      have hbetaRange : ∀ i, range (beta i) ⊆ NodeU i := by
        intro i
        refine Fin.lastCases ?_ (fun k => Fin.cases ?_ (fun j => ?_) k) i
        · rw [hNodeLast]
          intro _ hz
          rcases hz with ⟨s, rfl⟩
          unfold beta
          rw [Fin.lastCases_last]
          exact hbetaLastRange ⟨s, rfl⟩
        · rw [hNodeZeroCast]
          intro _ hz
          rcases hz with ⟨s, rfl⟩
          unfold beta
          rw [Fin.lastCases_castSucc]
          exact hbetaZeroRange ⟨s, rfl⟩
        · rw [hNodeInternal]
          intro _ hz
          rcases hz with ⟨s, rfl⟩
          unfold beta
          rw [Fin.lastCases_castSucc]
          exact (joinedInternal j).somePath_mem s
      have hdeltaRange : ∀ i : Fin (m + 1),
          range (delta.subpath (t i.castSucc) (t i.succ)) ⊆ V i := by
        intro i
        rw [Path.range_subpath_of_le]
        · rintro _ ⟨s, hs, rfl⟩
          exact hdeltaN.1 i hs
        · exact htmono (Fin.castSucc_le_succ i)
      have hNodeLeft : ∀ i : Fin (m + 1), NodeU i.castSucc ⊆ V i := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · rw [hNodeZeroCast]
          intro y hy
          have hyx : y = x := by simpa using hy
          subst y
          have hs := hVrange (0 : Fin (m + 1)) (Path.source_mem_range _)
          rw [hzeroIdx, ht0] at hs
          simpa using hs
        · rw [hNodeInternal j]
          intro z hz
          exact (hWsub j hz).2
      have hNodeRight : ∀ i : Fin (m + 1), NodeU i.succ ⊆ V i := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · have hlastIdx : (Fin.last m).succ = Fin.last (m + 1) := by ext; rfl
          rw [hlastIdx, hNodeLast]
          intro y hy
          have hyx : y = x := by simpa using hy
          subst y
          have hs := hVrange (Fin.last m) (Path.target_mem_range _)
          rw [hlastIdx, ht1] at hs
          simpa using hs
        · have hidx : j.castSucc.succ = j.succ.castSucc := by ext; rfl
          rw [hidx, hNodeInternal j]
          intro z hz
          exact (hWsub j hz).1
      have hbetaLeft : ∀ i : Fin (m + 1), range (beta i.castSucc) ⊆ V i := by
        intro i
        exact (hbetaRange i.castSucc).trans (hNodeLeft i)
      have hbetaRight : ∀ i : Fin (m + 1), range (beta i.succ) ⊆ V i := by
        intro i
        exact (hbetaRange i.succ).trans (hNodeRight i)
      have hcell : ∀ i : Fin (m + 1),
          (eta.subpath (t i.castSucc) (t i.succ)).Homotopic
            ((beta i.castSucc).trans
              ((delta.subpath (t i.castSucc) (t i.succ)).trans
                (beta i.succ).symm)) := by
        intro i
        apply homotopic_of_boundary_homotopic_refl
        apply hVnull i _
        · exact hVrange i (Path.source_mem_range _)
        · rw [Path.trans_range, Path.trans_range, Path.trans_range]
          refine union_subset (hVrange i) ?_
          refine union_subset (hbetaRight i) ?_
          refine union_subset ?_ (by
            rw [Path.symm_range]
            exact hbetaLeft i)
          rw [Path.symm_range]
          exact hdeltaRange i
      have hLadder := homotopic_concat_of_homotopic_ladder
        (p := fun i : Fin (m + 2) => eta (t i))
        (q := fun i : Fin (m + 2) => delta (t i))
        (β := beta)
        (F := fun i : Fin (m + 1) => eta.subpath (t i.castSucc) (t i.succ))
        (G := fun i : Fin (m + 1) => delta.subpath (t i.castSucc) (t i.succ))
        (hcell := hcell)
      let etaPath : Path (eta (t 0)) (eta (t (Fin.last (m + 1)))) :=
        eta.cast hetaZero hetaLast
      let deltaPath : Path (delta (t 0)) (delta (t (Fin.last (m + 1)))) :=
        delta.cast hdeltaZero hdeltaLast
      have hEtaSub : eta.subpath (t 0) (t (Fin.last (m + 1))) = etaPath := by
        ext s
        change eta (Icc.convexComb (t 0) (t (Fin.last (m + 1))) s) = eta s
        have hcomb : Icc.convexComb (t 0) (t (Fin.last (m + 1))) s = s := by
          rw [ht0, ht1]
          simp
        rw [hcomb]
      have hDeltaSub : delta.subpath (t 0) (t (Fin.last (m + 1))) = deltaPath := by
        ext s
        change delta (Icc.convexComb (t 0) (t (Fin.last (m + 1))) s) = delta s
        have hcomb : Icc.convexComb (t 0) (t (Fin.last (m + 1))) s = s := by
          rw [ht0, ht1]
          simp
        rw [hcomb]
      have hEtaConcat : etaPath.Homotopic
          (Path.concat (fun i : Fin (m + 2) => eta (t i))
            (fun i : Fin (m + 1) => eta.subpath (t i.castSucc) (t i.succ))) := by
        rw [← hEtaSub]
        exact (Path.Homotopic.concat_subpath eta t).symm
      have hDeltaConcat :
          (Path.concat (fun i : Fin (m + 2) => delta (t i))
            (fun i : Fin (m + 1) => delta.subpath (t i.castSucc) (t i.succ))).Homotopic deltaPath := by
        rw [← hDeltaSub]
        exact Path.Homotopic.concat_subpath delta t
      have hbetaZeroActual : beta (0 : Fin (m + 2)) = betaZero := by
        change beta ((0 : Fin (m + 1)).castSucc) = betaZero
        exact hbetaZeroIdx
      have hbetaLastActual : beta (Fin.last (m + 1)) = betaLast := by
        exact hbetaLastIdx
      have hleft : eta (t 0) = delta (t 0) := hetaZero.trans hdeltaZero.symm
      have hright : eta (t (Fin.last (m + 1))) =
          delta (t (Fin.last (m + 1))) := hetaLast.trans hdeltaLast.symm
      have hBoundary :
          (betaZero.trans
              ((Path.concat (fun i : Fin (m + 2) => delta (t i))
                (fun i : Fin (m + 1) => delta.subpath (t i.castSucc) (t i.succ))).trans
                betaLast.symm)).Homotopic
            ((Path.concat (fun i : Fin (m + 2) => delta (t i))
                (fun i : Fin (m + 1) => delta.subpath (t i.castSucc) (t i.succ))).cast
              hleft hright) := by
        simpa only [betaZero, betaLast] using
          (homotopic_boundary_cast_refl X
            (Path.concat (fun i : Fin (m + 2) => delta (t i))
              (fun i : Fin (m + 1) => delta.subpath (t i.castSucc) (t i.succ)))
            hetaZero hdeltaZero hetaLast hdeltaLast)
      have hLadder' :
          (Path.concat (fun i : Fin (m + 2) => eta (t i))
            (fun i : Fin (m + 1) => eta.subpath (t i.castSucc) (t i.succ))).Homotopic
            (betaZero.trans
              ((Path.concat (fun i : Fin (m + 2) => delta (t i))
                (fun i : Fin (m + 1) => delta.subpath (t i.castSucc) (t i.succ))).trans
                betaLast.symm)) := by
        simpa only [hbetaZeroActual, hbetaLastActual] using hLadder
      have hclose : etaPath.Homotopic
          (deltaPath.cast hleft hright) :=
        hEtaConcat.trans (hLadder'.trans (hBoundary.trans
          (hDeltaConcat.pathCast hleft hright)))
      have hfinal := hclose.pathCast hetaZero.symm hetaLast.symm
      convert hfinal using 1 <;> ext s <;> rfl

/-- The null-homotopy class is open under the same local hypotheses. -/
theorem isOpen_nullHomotopyClass_of_semilocallySimplyConnected
    [LocallyPathConnectedSpace X]
    (hsemi : SemilocallySimplyConnected X) (x : X) :
    IsOpen (nullHomotopyClass X x) := by
  have hopen := isOpen_homotopyClass_of_semilocallySimplyConnected
    X hsemi x (_root_.Path.refl x)
  convert hopen using 1
  ext γ
  constructor <;> intro h
  · exact h.symm
  · exact h.symm

/-- Local path-connectedness and semilocal simple connectivity force the
quotient-topological fundamental group at each basepoint to be discrete. -/
theorem quotientDiscreteTopology_of_semilocallySimplyConnected
    [LocallyPathConnectedSpace X]
    (hsemi : SemilocallySimplyConnected X) (x : X) :
    DiscreteTopology (LoopQuot X x) := by
  exact quotientDiscreteTopology X x
    (isOpen_nullHomotopyClass_of_semilocallySimplyConnected X hsemi x)

/-- Discreteness of the quotient-topological fundamental group implies the
semilocal simple-connectivity condition at its basepoint. -/
theorem semilocallySimplyConnectedAt_of_discreteTopology
    (x : X) [DiscreteTopology (LoopQuot X x)] :
    SemilocallySimplyConnectedAt X x :=
  semilocallySimplyConnectedAt_of_isOpen_nullHomotopyClass X x
    ((discreteTopology_iff_isOpen_nullHomotopyClass X x).mp inferInstance)

/-- In the locally path-connected setting, semilocal simple connectivity is
equivalent to discreteness of every based quotient fundamental group. -/
theorem semilocallySimplyConnected_iff_quotientDiscreteTopology
    [LocallyPathConnectedSpace X] :
    SemilocallySimplyConnected X ↔
      ∀ x : X, DiscreteTopology (LoopQuot X x) := by
  constructor
  · intro hsemi x
    exact quotientDiscreteTopology_of_semilocallySimplyConnected X hsemi x
  · intro hdiscrete x
    letI : DiscreteTopology (LoopQuot X x) := hdiscrete x
    exact semilocallySimplyConnectedAt_of_discreteTopology X x

end QuotientFundamentalGroup

end
end GeometricTopology
end Path
end ComputationalPaths
