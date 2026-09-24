import ComputationalPaths.Path.Topology.SemilocallySimplyConnected

/-!
# A local ladder for paths with varying endpoints

Finite null-homotopy subdivisions provide a compact-open neighborhood of a
path. Every path in that neighborhood differs from the original by endpoint
connector paths lying in arbitrarily prescribed endpoint neighborhoods.
This is the local ladder step in the proof that the global path-class
projection is open.
-/

namespace ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup

open Set Topology
open scoped ContinuousMap Topology unitInterval

universe u
variable {X : Type u} [TopologicalSpace X]

/-- Regard a continuous map on the unit interval as a path with its actual
endpoints. -/
def pathOfContinuousMap (delta : C(I, X)) : _root_.Path (delta 0) (delta 1) :=
  ⟨delta, rfl, rfl⟩

private theorem isOpen_mapsTo_finite
    {n : ℕ} (K : Fin n → Set I) (U : Fin n → Set X)
    (hK : ∀ i, IsCompact (K i)) (hU : ∀ i, IsOpen (U i)) :
    IsOpen {γ : C(I, X) | ∀ i, MapsTo γ (K i) (U i)} := by
  rw [show {γ : C(I, X) | ∀ i, MapsTo γ (K i) (U i)} =
      ⋂ i, {γ : C(I, X) | MapsTo γ (K i) (U i)} by ext; simp]
  let S : Set (Fin n) := univ
  rw [show ⋂ i, {γ : C(I, X) | MapsTo γ (K i) (U i)} =
      ⋂ i ∈ S, {γ : C(I, X) | MapsTo γ (K i) (U i)} by simp [S]]
  exact (Set.toFinite S).isOpen_biInter fun i _ =>
    ContinuousMap.isOpen_setOf_mapsTo (hK i) (hU i)

variable [LocallyPathConnectedSpace X]

/-- Local endpoint variation for compact-open paths. -/
theorem exists_endpoint_varying_ladder
    (hsemi : SemilocallySimplyConnected X)
    {a b : X} (eta : _root_.Path a b)
    {U0 U1 : Set X} (hU0 : IsOpen U0) (ha : a ∈ U0)
    (hU1 : IsOpen U1) (hb : b ∈ U1) :
    ∃ N : Set C(I, X), IsOpen N ∧ eta.toContinuousMap ∈ N ∧
      ∀ delta : C(I, X), delta ∈ N →
        ∃ beta0 : _root_.Path a (delta 0),
        ∃ beta1 : _root_.Path b (delta 1),
          range beta0 ⊆ U0 ∧ range beta1 ⊆ U1 ∧
          eta.Homotopic (beta0.trans ((pathOfContinuousMap delta).trans beta1.symm)) := by
  rcases exists_finite_null_subdivision X hsemi eta with
    ⟨n, t, V, ht0, ht1, htmono, hV⟩
  cases n with
  | zero =>
      simp only [Fin.reduceLast] at ht1
      exact (zero_ne_one (ht0.symm.trans ht1)).elim
  | succ m =>
      choose hVopen hVpath hVnull hVrange using hV
      have haV0 : a ∈ V 0 := by
        have hs := hVrange (0 : Fin (m + 1)) (_root_.Path.source_mem_range _)
        simpa [ht0, eta.source] using hs
      have hbVlast : b ∈ V (Fin.last m) := by
        have hs := hVrange (Fin.last m) (_root_.Path.target_mem_range _)
        have hidx : (Fin.last m).succ = Fin.last (m + 1) := by ext; rfl
        simpa [hidx, ht1, eta.target] using hs
      rcases ((isOpen_isPathConnected_basis a).mem_iff.mp
        ((hU0.inter (hVopen 0)).mem_nhds ⟨ha, haV0⟩)) with
        ⟨W0, ⟨hW0open, haW0, hW0path⟩, hW0sub⟩
      rcases ((isOpen_isPathConnected_basis b).mem_iff.mp
        ((hU1.inter (hVopen (Fin.last m))).mem_nhds ⟨hb, hbVlast⟩)) with
        ⟨Wlast, ⟨hWlastopen, hbWlast, hWlastpath⟩, hWlastsub⟩
      have hnode : ∀ j : Fin m, ∃ W : Set X,
          IsOpen W ∧ eta (t (j.succ.castSucc)) ∈ W ∧ IsPathConnected W ∧
            W ⊆ V j.castSucc ∩ V j.succ := by
        intro j
        have hleft : eta (t (j.succ.castSucc)) ∈ V j.castSucc := by
          have hidx : j.castSucc.succ = j.succ.castSucc := by ext; rfl
          rw [← hidx]
          exact hVrange j.castSucc (_root_.Path.target_mem_range _)
        have hright : eta (t (j.succ.castSucc)) ∈ V j.succ := by
          exact hVrange j.succ (_root_.Path.source_mem_range _)
        have hinterOpen : IsOpen (V j.castSucc ∩ V j.succ) :=
          (hVopen j.castSucc).inter (hVopen j.succ)
        rcases ((isOpen_isPathConnected_basis (eta (t (j.succ.castSucc)))).mem_iff.mp
          (hinterOpen.mem_nhds ⟨hleft, hright⟩)) with
          ⟨W, ⟨hWopen, hetaW, hWpath⟩, hWsub⟩
        exact ⟨W, hWopen, hetaW, hWpath, hWsub⟩
      choose W hWopen hetaW hWpath hWsub using hnode
      let NodeU : Fin (m + 2) → Set X := fun i =>
        Fin.lastCases Wlast (fun k => Fin.cases W0 (fun j => W j) k) i
      have hNodeLast : NodeU (Fin.last (m + 1)) = Wlast := by simp [NodeU]
      have hNodeZeroCast : NodeU ((0 : Fin (m + 1)).castSucc) = W0 := by
        unfold NodeU
        rw [Fin.lastCases_castSucc]
        rfl
      have hzeroIdx : (0 : Fin (m + 1)).castSucc = (0 : Fin (m + 2)) := rfl
      have hNodeInternal (j : Fin m) : NodeU (j.succ.castSucc) = W j := by
        unfold NodeU
        rw [Fin.lastCases_castSucc]
        rfl
      have hNodeOpen : ∀ i, IsOpen (NodeU i) := by
        intro i
        refine Fin.lastCases ?_ (fun k => Fin.cases ?_ (fun j => ?_) k) i
        · rw [hNodeLast]; exact hWlastopen
        · rw [hNodeZeroCast]; exact hW0open
        · rw [hNodeInternal]; exact hWopen j
      have hNodePath : ∀ i, IsPathConnected (NodeU i) := by
        intro i
        refine Fin.lastCases ?_ (fun k => Fin.cases ?_ (fun j => ?_) k) i
        · rw [hNodeLast]; exact hWlastpath
        · rw [hNodeZeroCast]; exact hW0path
        · rw [hNodeInternal]; exact hWpath j
      have hetaNode : ∀ i, eta (t i) ∈ NodeU i := by
        intro i
        refine Fin.lastCases ?_ (fun k => Fin.cases ?_ (fun j => ?_) k) i
        · rw [hNodeLast, ht1, eta.target]; exact hbWlast
        · rw [hNodeZeroCast, hzeroIdx, ht0, eta.source]; exact haW0
        · rw [hNodeInternal]; exact hetaW j
      let Kseg : Fin (m + 1) → Set I := fun i => Icc (t i.castSucc) (t i.succ)
      let Knode : Fin (m + 2) → Set I := fun i => {t i}
      let N : Set C(I, X) :=
        {delta | ∀ i, MapsTo delta (Kseg i) (V i)} ∩
        {delta | ∀ i, MapsTo delta (Knode i) (NodeU i)}
      have hNopen : IsOpen N := by
        apply IsOpen.inter
        · exact isOpen_mapsTo_finite Kseg V (fun _ => isCompact_Icc) hVopen
        · exact isOpen_mapsTo_finite Knode NodeU (fun _ => isCompact_singleton)
            hNodeOpen
      have hetaN : eta.toContinuousMap ∈ N := by
        constructor
        · intro i s hs
          apply hVrange i
          rw [_root_.Path.range_subpath_of_le]
          · exact ⟨s, hs, rfl⟩
          · exact htmono (Fin.castSucc_le_succ i)
        · intro i s hs
          change s ∈ ({t i} : Set I) at hs
          rw [mem_singleton_iff] at hs
          subst s
          exact hetaNode i
      refine ⟨N, hNopen, hetaN, ?_⟩
      intro delta hdeltaN
      have hdeltaNode : ∀ i, delta (t i) ∈ NodeU i := by
        intro i
        exact hdeltaN.2 i (mem_singleton (t i))
      let joined (i : Fin (m + 2)) :
          JoinedIn (NodeU i) (eta (t i)) (delta (t i)) :=
        (hNodePath i).joinedIn _ (hetaNode i) _ (hdeltaNode i)
      let beta (i : Fin (m + 2)) :
          _root_.Path (eta (t i)) (delta (t i)) :=
        (joined i).somePath
      have hbetaRange : ∀ i, range (beta i) ⊆ NodeU i := by
        intro i z hz
        rcases hz with ⟨s, rfl⟩
        exact (joined i).somePath_mem s
      have hdeltaRange : ∀ i : Fin (m + 1),
          range ((pathOfContinuousMap delta).subpath (t i.castSucc) (t i.succ)) ⊆ V i := by
        intro i
        rw [_root_.Path.range_subpath_of_le]
        · rintro _ ⟨s, hs, rfl⟩
          exact hdeltaN.1 i hs
        · exact htmono (Fin.castSucc_le_succ i)
      have hNodeLeft : ∀ i : Fin (m + 1), NodeU i.castSucc ⊆ V i := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · rw [hNodeZeroCast]
          intro z hz
          exact (hW0sub hz).2
        · rw [hNodeInternal j]
          intro z hz
          exact (hWsub j hz).2
      have hNodeRight : ∀ i : Fin (m + 1), NodeU i.succ ⊆ V i := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · have hlastIdx : (Fin.last m).succ = Fin.last (m + 1) := by ext; rfl
          rw [hlastIdx, hNodeLast]
          intro z hz
          exact (hWlastsub hz).2
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
              (((pathOfContinuousMap delta).subpath (t i.castSucc) (t i.succ)).trans
                (beta i.succ).symm)) := by
        intro i
        apply homotopic_of_boundary_homotopic_refl
        apply hVnull i _
        · exact hVrange i (_root_.Path.source_mem_range _)
        · rw [_root_.Path.trans_range, _root_.Path.trans_range,
            _root_.Path.trans_range]
          refine union_subset (hVrange i) ?_
          refine union_subset (hbetaRight i) ?_
          refine union_subset ?_ (by
            rw [_root_.Path.symm_range]
            exact hbetaLeft i)
          rw [_root_.Path.symm_range]
          exact hdeltaRange i
      have hLadder := homotopic_concat_of_homotopic_ladder
        (p := fun i : Fin (m + 2) => eta (t i))
        (q := fun i : Fin (m + 2) => delta (t i))
        (β := beta)
        (F := fun i : Fin (m + 1) => eta.subpath (t i.castSucc) (t i.succ))
        (G := fun i : Fin (m + 1) =>
          (pathOfContinuousMap delta).subpath (t i.castSucc) (t i.succ))
        (hcell := hcell)
      have hetaZero : eta (t 0) = a := by simpa [ht0] using eta.source
      have hetaLast : eta (t (Fin.last (m + 1))) = b := by
        simpa [ht1] using eta.target
      have hdeltaZero : delta (t 0) = delta 0 := by simp [ht0]
      have hdeltaLast : delta (t (Fin.last (m + 1))) = delta 1 := by
        simp [ht1]
      let etaAt : _root_.Path (eta (t 0)) (eta (t (Fin.last (m + 1)))) :=
        eta.cast hetaZero hetaLast
      let deltaAt : _root_.Path (delta (t 0))
          (delta (t (Fin.last (m + 1)))) :=
        (pathOfContinuousMap delta).cast hdeltaZero hdeltaLast
      have hEtaSub : eta.subpath (t 0) (t (Fin.last (m + 1))) = etaAt := by
        ext s
        change eta (Icc.convexComb (t 0) (t (Fin.last (m + 1))) s) = eta s
        have hcomb : Icc.convexComb (t 0) (t (Fin.last (m + 1))) s = s := by
          rw [ht0, ht1]
          simp
        rw [hcomb]
      have hDeltaSub : (pathOfContinuousMap delta).subpath (t 0)
          (t (Fin.last (m + 1))) = deltaAt := by
        ext s
        change delta (Icc.convexComb (t 0) (t (Fin.last (m + 1))) s) = delta s
        have hcomb : Icc.convexComb (t 0) (t (Fin.last (m + 1))) s = s := by
          rw [ht0, ht1]
          simp
        rw [hcomb]
      have hEtaConcat : etaAt.Homotopic
          (_root_.Path.concat (fun i : Fin (m + 2) => eta (t i))
            (fun i : Fin (m + 1) => eta.subpath (t i.castSucc) (t i.succ))) := by
        rw [← hEtaSub]
        exact (_root_.Path.Homotopic.concat_subpath eta t).symm
      have hDeltaConcat :
          (_root_.Path.concat (fun i : Fin (m + 2) => delta (t i))
            (fun i : Fin (m + 1) =>
              (pathOfContinuousMap delta).subpath (t i.castSucc) (t i.succ))).Homotopic deltaAt := by
        rw [← hDeltaSub]
        exact _root_.Path.Homotopic.concat_subpath (pathOfContinuousMap delta) t
      have hclose : etaAt.Homotopic
          ((beta 0).trans (deltaAt.trans (beta (Fin.last (m + 1))).symm)) :=
        hEtaConcat.trans (hLadder.trans
          ((_root_.Path.Homotopic.refl (beta 0)).hcomp
            (hDeltaConcat.hcomp
              (_root_.Path.Homotopic.refl (beta (Fin.last (m + 1))).symm))))
      let beta0 : _root_.Path a (delta 0) :=
        (beta 0).cast hetaZero.symm hdeltaZero.symm
      let beta1 : _root_.Path b (delta 1) :=
        (beta (Fin.last (m + 1))).cast hetaLast.symm hdeltaLast.symm
      refine ⟨beta0, beta1, ?_, ?_, ?_⟩
      · have hfirst : (0 : Fin (m + 2)) = ((0 : Fin (m + 1)).castSucc) := rfl
        rw [show range beta0 = range (beta 0) by rfl]
        exact (hbetaRange 0).trans (by
          rw [hfirst, hNodeZeroCast]
          exact fun z hz => (hW0sub hz).1)
      · rw [show range beta1 = range (beta (Fin.last (m + 1))) by rfl]
        exact (hbetaRange (Fin.last (m + 1))).trans (by
          rw [hNodeLast]
          exact fun z hz => (hWlastsub hz).1)
      · have hfinal := hclose.pathCast hetaZero.symm hetaLast.symm
        convert hfinal using 1 <;> ext s <;> rfl

end ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup
