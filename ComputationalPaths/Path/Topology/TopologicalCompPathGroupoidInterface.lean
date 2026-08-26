import ComputationalPaths.Path.Topology.TotalCompPathHomotopyQuotient
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# The complete topological quotient interface for computational paths

The quotient of explicit composable representatives is the unconditional
topological composition domain.  This file makes that statement complete:
the quotient domain maps continuously and surjectively to the ordinary
composable-pair subspace of quotient arrows, and composition factors through
that map.  If the map is a quotient map, the usual product-level composition
is continuous as well.

The final conditional statement is exact, rather than an unrecorded
assumption.  In arbitrary topological spaces products of quotient maps need
not be quotient maps, so this is the strongest general theorem available
without imposing a compactly generated, open-quotient, or similar hypothesis.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

universe u v

namespace TotalOpenGeometricCompPath

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  (S : ContinuousGeometricStepSystem A Step)

/-! ## The ordinary composable-pair subspace of quotient arrows -/

abbrev ComposablePair :=
  {pq : TotalHomotopyClass S × TotalHomotopyClass S //
    quotientTgt S pq.1 = quotientSrc S pq.2}

def leftTotal (c : TotalComposable A Step S) :
    TotalOpenGeometricCompPath A Step S :=
  ⟨c.src, c.mid, c.left⟩

def rightTotal (c : TotalComposable A Step S) :
    TotalOpenGeometricCompPath A Step S :=
  ⟨c.mid, c.tgt, c.right⟩

theorem continuous_leftTotal :
    Continuous (leftTotal S : TotalComposable A Step S →
      TotalOpenGeometricCompPath A Step S) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun c : TotalComposable A Step S =>
    (c.src, (c.mid, (c.leftTraceLength,
      (c.leftTraceMap, c.leftGeometricMap)))))
  exact (TotalComposable.continuous_src S).prodMk <|
    (TotalComposable.continuous_mid S).prodMk <|
      (TotalComposable.continuous_leftTraceLength S).prodMk <|
        (TotalComposable.continuous_leftTraceMap S).prodMk
          (TotalComposable.continuous_leftGeometricMap S)

theorem continuous_rightTotal :
    Continuous (rightTotal S : TotalComposable A Step S →
      TotalOpenGeometricCompPath A Step S) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun c : TotalComposable A Step S =>
    (c.mid, (c.tgt, (c.rightTraceLength,
      (c.rightTraceMap, c.rightGeometricMap)))))
  exact (TotalComposable.continuous_mid S).prodMk <|
    (TotalComposable.continuous_tgt S).prodMk <|
      (TotalComposable.continuous_rightTraceLength S).prodMk <|
        (TotalComposable.continuous_rightTraceMap S).prodMk
          (TotalComposable.continuous_rightGeometricMap S)

/-! ## Code projections and quotient-domain projections -/

def composableCodeLeft : ComposableCode A → TotalPathCode A
  | ⟨a, b, _, pq⟩ => ⟨a, b, pq.1⟩

def composableCodeRight : ComposableCode A → TotalPathCode A
  | ⟨_, b, c, pq⟩ => ⟨b, c, pq.2⟩

theorem composableCode_ext_of_component_codes
    {x y : ComposableCode A}
    (hl : composableCodeLeft x = composableCodeLeft y)
    (hr : composableCodeRight x = composableCodeRight y) :
    x = y := by
  rcases x with ⟨a, b, c, pq⟩
  rcases y with ⟨a', b', c', pq'⟩
  have hlp := Sigma.ext_iff.mp hl
  cases hlp.1
  have hlrest :
      (⟨b, pq.1⟩ : Σ z, _root_.Path.Homotopic.Quotient a z) =
        ⟨b', pq'.1⟩ :=
    eq_of_heq hlp.2
  have hmid := _root_.congrArg Sigma.fst hlrest
  cases hmid
  have hp := eq_of_heq (Sigma.ext_iff.mp hlrest).2
  have hrp := Sigma.ext_iff.mp hr
  have htgt := hrp.1
  cases htgt
  have hrrest :
      (⟨c, pq.2⟩ : Σ z, _root_.Path.Homotopic.Quotient b z) =
        ⟨c', pq'.2⟩ :=
    eq_of_heq hrp.2
  have hctgt := (Sigma.ext_iff.mp hrrest).1
  cases hctgt
  have hq := eq_of_heq (Sigma.ext_iff.mp hrrest).2
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  exact Prod.ext hp hq

theorem totalCode_leftTotal (c : TotalComposable A Step S) :
    totalCode S (leftTotal S c) =
      composableCodeLeft (composableCode S c) :=
  rfl

theorem totalCode_rightTotal (c : TotalComposable A Step S) :
    totalCode S (rightTotal S c) =
      composableCodeRight (composableCode S c) :=
  rfl

theorem totalEquivalent_leftTotal {c d : TotalComposable A Step S}
    (h : composableEquivalent S c d) :
    totalEquivalent S (leftTotal S c) (leftTotal S d) := by
  change totalCode S (leftTotal S c) = totalCode S (leftTotal S d)
  rw [totalCode_leftTotal S c, totalCode_leftTotal S d]
  change composableCode S c = composableCode S d at h
  exact _root_.congrArg (composableCodeLeft (A := A)) h

theorem totalEquivalent_rightTotal {c d : TotalComposable A Step S}
    (h : composableEquivalent S c d) :
    totalEquivalent S (rightTotal S c) (rightTotal S d) := by
  change totalCode S (rightTotal S c) = totalCode S (rightTotal S d)
  rw [totalCode_rightTotal S c, totalCode_rightTotal S d]
  change composableCode S c = composableCode S d at h
  exact _root_.congrArg (composableCodeRight (A := A)) h

noncomputable def composableLeft
    (c : ComposableHomotopyClass S) : TotalHomotopyClass S :=
  Quotient.lift
    (fun c => totalQuotientMk S (leftTotal S c))
    (by
      intro c d h
      apply Quotient.sound
      exact totalEquivalent_leftTotal S h)
    c

noncomputable def composableRight
    (c : ComposableHomotopyClass S) : TotalHomotopyClass S :=
  Quotient.lift
    (fun c => totalQuotientMk S (rightTotal S c))
    (by
      intro c d h
      apply Quotient.sound
      exact totalEquivalent_rightTotal S h)
    c

theorem composableLeft_composableQuotientMk (c : TotalComposable A Step S) :
    composableLeft S (composableQuotientMk S c) =
      totalQuotientMk S (leftTotal S c) :=
  rfl

theorem composableRight_composableQuotientMk (c : TotalComposable A Step S) :
    composableRight S (composableQuotientMk S c) =
      totalQuotientMk S (rightTotal S c) :=
  rfl

theorem continuous_composableLeft :
    Continuous (composableLeft S : ComposableHomotopyClass S →
      TotalHomotopyClass S) := by
  apply Continuous.quotient_lift
  exact continuous_totalQuotientMk S |>.comp (continuous_leftTotal S)

theorem continuous_composableRight :
    Continuous (composableRight S : ComposableHomotopyClass S →
      TotalHomotopyClass S) := by
  apply Continuous.quotient_lift
  exact continuous_totalQuotientMk S |>.comp (continuous_rightTotal S)

/-! ## The canonical map from the quotient composable domain -/

noncomputable def composablePairMap
    (c : ComposableHomotopyClass S) : ComposablePair S :=
  Quotient.lift
    (fun c =>
      (⟨(totalQuotientMk S (leftTotal S c),
          totalQuotientMk S (rightTotal S c)), by
        rfl⟩ : ComposablePair S))
    (by
      intro c d h
      apply Subtype.ext
      apply Prod.ext
      · apply Quotient.sound
        exact totalEquivalent_leftTotal S h
      · apply Quotient.sound
        exact totalEquivalent_rightTotal S h)
    c

theorem composablePairMap_composableQuotientMk
    (c : TotalComposable A Step S) :
    composablePairMap S (composableQuotientMk S c) =
      (⟨(totalQuotientMk S (leftTotal S c),
          totalQuotientMk S (rightTotal S c)), by rfl⟩ : ComposablePair S) :=
  rfl

theorem continuous_composablePairMap :
    Continuous (composablePairMap S : ComposableHomotopyClass S →
      ComposablePair S) := by
  apply Continuous.quotient_lift
  have hleft : Continuous (fun c : TotalComposable A Step S =>
      totalQuotientMk S (leftTotal S c)) :=
    continuous_totalQuotientMk S |>.comp (continuous_leftTotal S)
  have hright : Continuous (fun c : TotalComposable A Step S =>
      totalQuotientMk S (rightTotal S c)) :=
    continuous_totalQuotientMk S |>.comp (continuous_rightTotal S)
  exact (hleft.prodMk hright).subtype_mk (fun c => rfl)

theorem composablePairMap_surjective :
    Function.Surjective (composablePairMap S :
      ComposableHomotopyClass S → ComposablePair S) := by
  intro x
  rcases x with ⟨⟨p, q⟩, h⟩
  have hvalue : ∃ a : ComposableHomotopyClass S,
      (composablePairMap S a).val = (p, q) := by
    revert h
    refine Quotient.inductionOn p ?_
    intro p h
    revert h
    refine Quotient.inductionOn q ?_
    intro q h
    rcases q with ⟨qsrc, qtgt, qpath⟩
    change p.tgt = qsrc at h
    cases h
    let c : TotalComposable A Step S :=
      ⟨p.src, p.tgt, qtgt, p.path, qpath⟩
    refine ⟨composableQuotientMk S c, ?_⟩
    apply Prod.ext <;> rfl
  rcases hvalue with ⟨a, ha⟩
  exact ⟨a, Subtype.ext ha⟩

/-! ## Product composition and its exact continuity criterion -/

theorem totalEquivalent_totalTrans_of_composablePairMap_eq
    {c d : TotalComposable A Step S}
    (h : composablePairMap S (composableQuotientMk S c) =
      composablePairMap S (composableQuotientMk S d)) :
    totalEquivalent S (totalTrans S c) (totalTrans S d) := by
  have hpair := _root_.congrArg Subtype.val h
  have hleftEq :
      totalQuotientMk S (leftTotal S c) =
        totalQuotientMk S (leftTotal S d) := by
    simpa only [composablePairMap_composableQuotientMk] using
      (_root_.congrArg Prod.fst hpair)
  have hrightEq :
      totalQuotientMk S (rightTotal S c) =
        totalQuotientMk S (rightTotal S d) := by
    simpa only [composablePairMap_composableQuotientMk] using
      (_root_.congrArg Prod.snd hpair)
  have hleft : totalEquivalent S (leftTotal S c) (leftTotal S d) := by
    exact Quotient.exact hleftEq
  have hright : totalEquivalent S (rightTotal S c) (rightTotal S d) := by
    exact Quotient.exact hrightEq
  change totalCode S (totalTrans S c) = totalCode S (totalTrans S d)
  rw [totalCode_trans S c, totalCode_trans S d]
  have hleftCode :
      composableCodeLeft (composableCode S c) =
        composableCodeLeft (composableCode S d) := by
    change totalCode S (leftTotal S c) = totalCode S (leftTotal S d) at hleft
    rw [totalCode_leftTotal S c, totalCode_leftTotal S d] at hleft
    exact hleft
  have hrightCode :
      composableCodeRight (composableCode S c) =
        composableCodeRight (composableCode S d) := by
    change totalCode S (rightTotal S c) = totalCode S (rightTotal S d) at hright
    rw [totalCode_rightTotal S c, totalCode_rightTotal S d] at hright
    exact hright
  exact _root_.congrArg (codeTrans (A := A))
    (composableCode_ext_of_component_codes hleftCode hrightCode)

theorem quotientTransFromComposable_respects_composablePairMap
    {c d : ComposableHomotopyClass S}
    (h : composablePairMap S c = composablePairMap S d) :
    quotientTransFromComposable S c =
      quotientTransFromComposable S d := by
  revert h
  refine Quotient.inductionOn₂ c d ?_
  intro c d h
  apply Quotient.sound
  exact totalEquivalent_totalTrans_of_composablePairMap_eq S h

noncomputable def quotientTransOnProduct
    (pq : ComposablePair S) : TotalHomotopyClass S :=
  quotientTransFromComposable S
    (Classical.choose (composablePairMap_surjective S pq))

theorem quotientTransOnProduct_composablePairMap
    (c : ComposableHomotopyClass S) :
    quotientTransOnProduct S (composablePairMap S c) =
      quotientTransFromComposable S c := by
  let d := Classical.choose
    (composablePairMap_surjective S (composablePairMap S c))
  have hd : composablePairMap S d = composablePairMap S c :=
    Classical.choose_spec
      (composablePairMap_surjective S (composablePairMap S c))
  exact quotientTransFromComposable_respects_composablePairMap S hd

/-- The exact extra condition needed for ordinary product-level composition. -/
structure ProductQuotientCompatibility
    (S : ContinuousGeometricStepSystem A Step) : Prop where
  composablePairMap_isQuotient :
    Topology.IsQuotientMap (composablePairMap S :
      ComposableHomotopyClass S → ComposablePair S)

theorem continuous_quotientTransOnProduct
    (H : ProductQuotientCompatibility S) :
    Continuous (quotientTransOnProduct S : ComposablePair S →
      TotalHomotopyClass S) := by
  apply (H.composablePairMap_isQuotient.continuous_iff).2
  have hfactor :
      quotientTransOnProduct S ∘ composablePairMap S =
        quotientTransFromComposable S := by
    funext c
    exact quotientTransOnProduct_composablePairMap S c
  rw [hfactor]
  exact continuous_quotientTransFromComposable S

/-! ## The canonical quotient-compatible composable topology -/

structure StrongComposablePair where
  val : ComposablePair S

noncomputable def strongPairMap
    (c : ComposableHomotopyClass S) : StrongComposablePair S :=
  ⟨composablePairMap S c⟩

noncomputable instance strongComposablePairTopology :
    TopologicalSpace (StrongComposablePair S) :=
  TopologicalSpace.coinduced (strongPairMap S) inferInstance

theorem strongPairMap_surjective :
    Function.Surjective (strongPairMap S :
      ComposableHomotopyClass S → StrongComposablePair S) := by
  intro p
  rcases p with ⟨p⟩
  rcases composablePairMap_surjective S p with ⟨c, hc⟩
  exact ⟨c, _root_.congrArg
    (fun q : ComposablePair S => (⟨q⟩ : StrongComposablePair S)) hc⟩

theorem strongPairMap_isQuotient :
    Topology.IsQuotientMap (strongPairMap S :
      ComposableHomotopyClass S → StrongComposablePair S) :=
  ⟨⟨rfl⟩, strongPairMap_surjective S⟩

noncomputable def strongPairToOrdinary :
    StrongComposablePair S → ComposablePair S :=
  fun p => p.val

theorem continuous_strongPairToOrdinary :
    Continuous (strongPairToOrdinary S :
      StrongComposablePair S → ComposablePair S) := by
  apply (strongPairMap_isQuotient S).continuous_iff.2
  exact continuous_composablePairMap S

noncomputable def quotientTransOnStrongPair
    (p : StrongComposablePair S) : TotalHomotopyClass S :=
  quotientTransOnProduct S p.val

theorem quotientTransOnStrongPair_strongPairMap
    (c : ComposableHomotopyClass S) :
    quotientTransOnStrongPair S (strongPairMap S c) =
      quotientTransFromComposable S c := by
  exact quotientTransOnProduct_composablePairMap S c

theorem continuous_quotientTransOnStrongPair :
    Continuous (quotientTransOnStrongPair S : StrongComposablePair S →
      TotalHomotopyClass S) := by
  apply (strongPairMap_isQuotient S).continuous_iff.2
  have hfactor :
      quotientTransOnStrongPair S ∘ strongPairMap S =
        quotientTransFromComposable S := by
    funext c
    exact quotientTransOnStrongPair_strongPairMap S c
  rw [hfactor]
  exact continuous_quotientTransFromComposable S

/-! ## Complete unconditional and conditional certificates -/

noncomputable def groupoidCompositionTracePath
    (c : TotalComposable A Step S) :
    ComputationalPaths.Path
      (GeometricTrace.traceLength (totalTrans S c).trace)
      (TotalComposable.leftTraceLength S c +
        TotalComposable.rightTraceLength S c) :=
  ComputationalPaths.Path.trans
    (GeometricTrace.traceLengthTransPath c.left.trace c.right.trace)
    (ComputationalPaths.Path.refl
      (TotalComposable.leftTraceLength S c +
        TotalComposable.rightTraceLength S c))

noncomputable def groupoidTraceUnitRewrite (n : Nat) :
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl n)
        (ComputationalPaths.Path.refl n))
      (ComputationalPaths.Path.refl n) :=
  ComputationalPaths.Path.RwEq.step
    (ComputationalPaths.Path.Step.trans_refl_right
      (ComputationalPaths.Path.refl n))

structure GroupoidInterfaceCertificate where
  left_continuous :
    Continuous (composableLeft S : ComposableHomotopyClass S →
      TotalHomotopyClass S)
  right_continuous :
    Continuous (composableRight S : ComposableHomotopyClass S →
      TotalHomotopyClass S)
  composable_pair_map_continuous :
    Continuous (composablePairMap S : ComposableHomotopyClass S →
      ComposablePair S)
  composable_pair_map_surjective :
    Function.Surjective (composablePairMap S :
      ComposableHomotopyClass S → ComposablePair S)
  strong_pair_map_quotient :
    Topology.IsQuotientMap (strongPairMap S :
      ComposableHomotopyClass S → StrongComposablePair S)
  strong_pair_to_ordinary_continuous :
    Continuous (strongPairToOrdinary S :
      StrongComposablePair S → ComposablePair S)
  quotient_domain_composition_continuous :
    Continuous (quotientTransFromComposable S)
  strong_composition_continuous :
    Continuous (quotientTransOnStrongPair S : StrongComposablePair S →
      TotalHomotopyClass S)
  product_composition_continuous :
    ∀ _ : ProductQuotientCompatibility S,
      Continuous (quotientTransOnProduct S : ComposablePair S →
        TotalHomotopyClass S)
  composition_trace_path : ∀ c : TotalComposable A Step S,
    ComputationalPaths.Path
      (GeometricTrace.traceLength (totalTrans S c).trace)
      (TotalComposable.leftTraceLength S c +
        TotalComposable.rightTraceLength S c)
  composition_trace_rewrite : ∀ n : Nat,
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl n)
        (ComputationalPaths.Path.refl n))
      (ComputationalPaths.Path.refl n)

noncomputable def groupoidInterfaceCertificate :
    GroupoidInterfaceCertificate S where
  left_continuous := continuous_composableLeft S
  right_continuous := continuous_composableRight S
  composable_pair_map_continuous := continuous_composablePairMap S
  composable_pair_map_surjective := composablePairMap_surjective S
  strong_pair_map_quotient := strongPairMap_isQuotient S
  strong_pair_to_ordinary_continuous := continuous_strongPairToOrdinary S
  quotient_domain_composition_continuous := continuous_quotientTransFromComposable S
  strong_composition_continuous := continuous_quotientTransOnStrongPair S
  product_composition_continuous := by
    intro H
    exact continuous_quotientTransOnProduct S H
  composition_trace_path := groupoidCompositionTracePath S
  composition_trace_rewrite := groupoidTraceUnitRewrite

end TotalOpenGeometricCompPath
end GeometricTopology
end Path
end ComputationalPaths
