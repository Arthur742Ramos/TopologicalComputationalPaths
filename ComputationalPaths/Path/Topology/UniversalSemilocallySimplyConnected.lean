import ComputationalPaths.Path.Topology.EndpointAbsorption
import ComputationalPaths.Path.Topology.EndpointVaryingLadder
import ComputationalPaths.Path.Topology.UniversalQuotientTransfer
import ComputationalPaths.Path.Topology.UniversalGlobalBasedFiber

namespace ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup

open Set Topology
open scoped ContinuousMap Topology unitInterval

private theorem homotopic_of_ladder_reverse
    {X : Type*} [TopologicalSpace X]
    {a b a' b' : X}
    (eta : _root_.Path a b) (delta : _root_.Path a' b')
    (beta0 : _root_.Path a a') (beta1 : _root_.Path b b')
    (h : eta.Homotopic (beta0.trans (delta.trans beta1.symm))) :
    delta.Homotopic (beta0.symm.trans (eta.trans beta1)) := by
  let e := _root_.Path.Homotopic.Quotient.mk eta
  let d := _root_.Path.Homotopic.Quotient.mk delta
  let c0 := _root_.Path.Homotopic.Quotient.mk beta0
  let c1 := _root_.Path.Homotopic.Quotient.mk beta1
  have hq : e = c0.trans (d.trans c1.symm) := by
    have hmk := _root_.Path.Homotopic.Quotient.eq.mpr h
    simpa only [e, d, c0, c1,
      _root_.Path.Homotopic.Quotient.mk_trans,
      _root_.Path.Homotopic.Quotient.mk_symm] using hmk
  have hq' := _root_.congrArg
    (fun z : _root_.Path.Homotopic.Quotient a b =>
      _root_.Path.Homotopic.Quotient.trans
        (_root_.Path.Homotopic.Quotient.symm c0)
        (_root_.Path.Homotopic.Quotient.trans z c1)) hq
  simp only [_root_.Path.Homotopic.Quotient.trans_assoc,
    _root_.Path.Homotopic.Quotient.symm_trans,
    _root_.Path.Homotopic.Quotient.trans_refl] at hq'
  have hleft : c0.symm.trans (c0.trans d) = d := by
    rw [← _root_.Path.Homotopic.Quotient.trans_assoc,
      _root_.Path.Homotopic.Quotient.symm_trans,
      _root_.Path.Homotopic.Quotient.refl_trans]
  rw [hleft] at hq'
  exact _root_.Path.Homotopic.Quotient.eq.mp
    (by simpa [e, d, c0, c1] using hq'.symm)

end ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup

namespace ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite

open scoped ContinuousMap Topology unitInterval
open QuotientFundamentalGroup

private theorem projectionCode_cast {A : Type*} [TopologicalSpace A]
    {a b a' b' : A} (ha : a = a') (hb : b = b')
    (q : _root_.Path.Homotopic.Quotient a b) :
    (⟨a, b, q⟩ : FundamentalArrowCode A) =
      ⟨a', b', q.cast ha.symm hb.symm⟩ := by
  cases ha
  cases hb
  simp

private theorem projection_code
    {A : Type*} [TopologicalSpace A]
    {a b : A} (gamma : _root_.Path a b) :
    (universalRealizedFundamentalArrowHomeomorph (A := A)
      (universalPathClassProjection (A := A) gamma.toContinuousMap)).val =
      (⟨a, b, _root_.Path.Homotopic.Quotient.mk gamma⟩ : FundamentalArrowCode A) := by
  change TotalOpenGeometricCompPath.totalCode
    (continuousPathStepSystem A)
    (universalTraceSensitiveChoice (A := A) gamma.toContinuousMap) = _
  let p : _root_.Path (gamma 0) (gamma 1) :=
    (continuousPathStep gamma.toContinuousMap).geometric
  change (⟨gamma 0, gamma 1, _root_.Path.Homotopic.Quotient.mk p⟩ : FundamentalArrowCode A) =
    ⟨a, b, _root_.Path.Homotopic.Quotient.mk gamma⟩
  rw [projectionCode_cast gamma.source gamma.target]
  have hpath : p.cast gamma.source.symm gamma.target.symm = gamma := by
    apply _root_.Path.ext
    funext t
    rfl
  have hq : (_root_.Path.Homotopic.Quotient.mk p).cast
      gamma.source.symm gamma.target.symm =
        _root_.Path.Homotopic.Quotient.mk gamma := by
    rw [← _root_.Path.Homotopic.Quotient.mk_cast, hpath]
  exact _root_.congrArg (fun q : _root_.Path.Homotopic.Quotient a b =>
    (⟨a, b, q⟩ : FundamentalArrowCode A)) hq

private theorem projection_eq_iff_homotopic
    {A : Type*} [TopologicalSpace A]
    {a b : A} (gamma delta : _root_.Path a b) :
    universalPathClassProjection (A := A) gamma.toContinuousMap =
      universalPathClassProjection (A := A) delta.toContinuousMap ↔
      gamma.Homotopic delta := by
  constructor
  · intro h
    have hcode :
        (⟨a, b, _root_.Path.Homotopic.Quotient.mk gamma⟩ : FundamentalArrowCode A) =
          ⟨a, b, _root_.Path.Homotopic.Quotient.mk delta⟩ := by
      rw [← projection_code gamma, ← projection_code delta]
      exact _root_.congrArg (fun c : ScopedClass
        (universalPresentation (A := A)) =>
        (universalRealizedFundamentalArrowHomeomorph (A := A) c).val) h
    have hrest :
        (⟨b, _root_.Path.Homotopic.Quotient.mk gamma⟩ :
          Σ y : A, _root_.Path.Homotopic.Quotient a y) =
        ⟨b, _root_.Path.Homotopic.Quotient.mk delta⟩ := by
      exact eq_of_heq (Sigma.ext_iff.mp hcode).2
    have hq : _root_.Path.Homotopic.Quotient.mk gamma = _root_.Path.Homotopic.Quotient.mk delta := by
      exact eq_of_heq (Sigma.ext_iff.mp hrest).2
    exact Quotient.exact hq
  · intro h
    apply (universalRealizedFundamentalArrowHomeomorph
      (A := A)).injective
    apply Subtype.ext
    rw [projection_code, projection_code]
    exact _root_.congrArg (fun q : _root_.Path.Homotopic.Quotient a b =>
      (⟨a, b, q⟩ : FundamentalArrowCode A)) (Quotient.sound h)

private theorem projection_eq_iff_varying_homotopic
    {A : Type*} [TopologicalSpace A]
    (gamma delta : C(I, A)) :
    universalPathClassProjection (A := A) gamma =
      universalPathClassProjection (A := A) delta ↔
      ∃ (hsrc : gamma 0 = delta 0) (htgt : gamma 1 = delta 1),
        (pathOfContinuousMap gamma).Homotopic
          ((pathOfContinuousMap delta).cast hsrc htgt) := by
  constructor
  · intro h
    have hcode :
        (⟨gamma 0, gamma 1,
          _root_.Path.Homotopic.Quotient.mk (pathOfContinuousMap gamma)⟩ :
            FundamentalArrowCode A) =
          ⟨delta 0, delta 1,
            _root_.Path.Homotopic.Quotient.mk (pathOfContinuousMap delta)⟩ := by
      rw [← projection_code (pathOfContinuousMap gamma),
        ← projection_code (pathOfContinuousMap delta)]
      exact _root_.congrArg (fun c : ScopedClass
        (universalPresentation (A := A)) =>
        (universalRealizedFundamentalArrowHomeomorph (A := A) c).val) h
    have hsrc : gamma 0 = delta 0 :=
      _root_.congrArg (fun c : FundamentalArrowCode A => c.1) hcode
    have htgt : gamma 1 = delta 1 :=
      _root_.congrArg (fun c : FundamentalArrowCode A => c.2.1) hcode
    have hcast :
        (⟨delta 0, delta 1,
          _root_.Path.Homotopic.Quotient.mk (pathOfContinuousMap delta)⟩ :
            FundamentalArrowCode A) =
          ⟨gamma 0, gamma 1,
            (_root_.Path.Homotopic.Quotient.mk (pathOfContinuousMap delta)).cast
              hsrc htgt⟩ := by
      simpa using projectionCode_cast hsrc.symm htgt.symm
        (_root_.Path.Homotopic.Quotient.mk (pathOfContinuousMap delta))
    have hcode' := hcode.trans hcast
    have hrest :
        (⟨gamma 1,
          _root_.Path.Homotopic.Quotient.mk (pathOfContinuousMap gamma)⟩ :
          Σ y : A, _root_.Path.Homotopic.Quotient (gamma 0) y) =
        ⟨gamma 1,
          (_root_.Path.Homotopic.Quotient.mk (pathOfContinuousMap delta)).cast
            hsrc htgt⟩ := by
      exact eq_of_heq (Sigma.ext_iff.mp hcode').2
    have hq : _root_.Path.Homotopic.Quotient.mk (pathOfContinuousMap gamma) =
        (_root_.Path.Homotopic.Quotient.mk (pathOfContinuousMap delta)).cast
          hsrc htgt := by
      exact eq_of_heq (Sigma.ext_iff.mp hrest).2
    rw [← _root_.Path.Homotopic.Quotient.mk_cast] at hq
    exact ⟨hsrc, htgt, Quotient.exact hq⟩
  · rintro ⟨hsrc, htgt, hhom⟩
    have hcm : ((pathOfContinuousMap delta).cast hsrc htgt).toContinuousMap =
        delta := by
      ext t
      rfl
    have hpath := (projection_eq_iff_homotopic
      (pathOfContinuousMap gamma)
      ((pathOfContinuousMap delta).cast hsrc htgt)).2 hhom
    rw [hcm] at hpath
    change universalPathClassProjection (A := A) gamma =
      universalPathClassProjection (A := A) delta at hpath
    exact hpath

/-- The universal path-class projection is open on locally path-connected,
semilocally simply connected spaces. -/
theorem universalPathClassProjection_isOpenMap_of_semilocallySimplyConnected
    {A : Type*} [TopologicalSpace A] [LocallyPathConnectedSpace A]
    (hsemi : QuotientFundamentalGroup.SemilocallySimplyConnected A) :
    IsOpenMap (universalPathClassProjection (A := A)) := by
  intro W hW
  apply (universalPathClassProjection_isQuotient (A := A)).isCoinducing.isOpen_preimage.mp
  apply isOpen_iff_forall_mem_open.mpr
  intro delta hdelta
  obtain ⟨eta, heta, hproj⟩ := hdelta
  obtain ⟨hsrc, htgt, hhom⟩ :=
    (projection_eq_iff_varying_homotopic eta delta).mp hproj
  let etaP := pathOfContinuousMap eta
  let deltaP := (pathOfContinuousMap delta).cast hsrc htgt
  have hdeltaCM : deltaP.toContinuousMap = delta := by
    ext t
    rfl
  obtain ⟨U0, U1, hU0open, haU0, hU1open, hbU1, habsorb⟩ :=
    exists_endpoint_absorption etaP hW heta
  obtain ⟨N, hNopen, hdeltaN, hLadder⟩ :=
    exists_endpoint_varying_ladder hsemi deltaP
      hU0open haU0 hU1open hbU1
  refine ⟨N, ?_, hNopen, ?_⟩
  · intro zeta hzeta
    obtain ⟨beta0, beta1, hbeta0, hbeta1, hL⟩ := hLadder zeta hzeta
    have hreverse := QuotientFundamentalGroup.homotopic_of_ladder_reverse
      deltaP (pathOfContinuousMap zeta) beta0 beta1 hL
    have hmiddle : (deltaP.trans beta1).Homotopic
        (etaP.trans beta1) :=
      _root_.Path.Homotopic.hcomp hhom.symm (_root_.Path.Homotopic.refl beta1)
    have hfull : (beta0.symm.trans (deltaP.trans beta1)).Homotopic
        (beta0.symm.trans (etaP.trans beta1)) :=
      _root_.Path.Homotopic.hcomp (_root_.Path.Homotopic.refl beta0.symm) hmiddle
    have hzetaHom := hreverse.trans hfull
    have hbeta0symm : Set.range beta0.symm ⊆ U0 := by
      rw [_root_.Path.symm_range]
      exact hbeta0
    obtain ⟨omega, homega, homegaHom⟩ :=
      habsorb beta0.symm beta1 hbeta0symm hbeta1
    have hpathHom : (pathOfContinuousMap zeta).Homotopic omega :=
      hzetaHom.trans homegaHom.symm
    have hprojEq := (projection_eq_iff_homotopic
      (pathOfContinuousMap zeta) omega).2 hpathHom
    refine ⟨omega.toContinuousMap, homega, ?_⟩
    change universalPathClassProjection (A := A) zeta =
      universalPathClassProjection (A := A) omega.toContinuousMap at hprojEq
    exact hprojEq.symm
  · simpa [hdeltaCM] using hdeltaN

theorem universalProductCompatibility_of_semilocallySimplyConnected
    {A : Type*} [TopologicalSpace A] [LocallyPathConnectedSpace A]
    (hsemi : QuotientFundamentalGroup.SemilocallySimplyConnected A) :
    ProductQuotientCompatibility (universalPresentation (A := A)) :=
  universalProductCompatibility_of_open_path_projection
    (universalPathClassProjection_isOpenMap_of_semilocallySimplyConnected hsemi)

theorem continuous_universalComposition_of_semilocallySimplyConnected
    {A : Type*} [TopologicalSpace A] [LocallyPathConnectedSpace A]
    (hsemi : QuotientFundamentalGroup.SemilocallySimplyConnected A) :
    Continuous (scopedCompositionOnProduct (universalPresentation (A := A)) :
      ScopedComposablePair (universalPresentation (A := A)) →
        ScopedClass (universalPresentation (A := A))) :=
  continuous_universalComposition_of_open_path_projection
    (universalPathClassProjection_isOpenMap_of_semilocallySimplyConnected hsemi)

noncomputable def universalBasedFiberHomeomorph_of_semilocallySimplyConnected
    {A : Type*} [TopologicalSpace A] [LocallyPathConnectedSpace A]
    (hsemi : QuotientFundamentalGroup.SemilocallySimplyConnected A) (x : A) :
    QuotientFundamentalGroup.LoopQuot A x ≃ₜ universalBasedArrowSet x :=
  basedGlobalFiberHomeomorph x
    (universalPathClassProjection_isOpenMap_of_semilocallySimplyConnected hsemi)

end ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite
