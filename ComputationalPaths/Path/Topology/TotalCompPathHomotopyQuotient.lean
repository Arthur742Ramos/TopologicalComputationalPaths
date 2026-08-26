import ComputationalPaths.Path.Topology.UniversalCompPathHomotopyEquivalence
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# The total homotopy quotient and its topological groupoid interface

Endpointwise quotients identify geometric representatives with the same
endpoints.  This file performs the corresponding construction on the total
endpoint-varying carrier.  Endpoint maps descend continuously, reversal and
identity descend continuously, and composition is represented by a quotient
of the explicit composable-pair carrier.

The composable-pair quotient is intentional: arbitrary products of quotient
maps need not be quotient maps without additional hypotheses.  The quotient
of `TotalComposable` is therefore the canonical domain on which the
composition map is continuous in complete generality.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

attribute [local instance] _root_.Path.Homotopic.setoid

universe u v

namespace TotalOpenGeometricCompPath

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  (S : ContinuousGeometricStepSystem A Step)

/-! ## Codes for endpoint-varying homotopy classes -/

abbrev TotalPathCode (A : Type u) [TopologicalSpace A] :=
  Σ a : A, Σ b : A, _root_.Path.Homotopic.Quotient a b

abbrev ComposableCode (A : Type u) [TopologicalSpace A] :=
  Σ a : A, Σ b : A, Σ c : A,
    (_root_.Path.Homotopic.Quotient a b ×
      _root_.Path.Homotopic.Quotient b c)

noncomputable def totalCode
    (p : TotalOpenGeometricCompPath A Step S) : TotalPathCode A :=
  ⟨p.src, p.tgt, Quotient.mk' p.geometricPath⟩

noncomputable def composableCode
    (c : TotalComposable A Step S) : ComposableCode A :=
  ⟨c.src, c.mid, c.tgt,
    (Quotient.mk' c.left.geometric, Quotient.mk' c.right.geometric)⟩

noncomputable def codeSymm : TotalPathCode A → TotalPathCode A
  | ⟨a, b, p⟩ => ⟨b, a, pathQuotientSymm p⟩

noncomputable def codeTrans : ComposableCode A → TotalPathCode A
  | ⟨a, _, c, pq⟩ =>
      ⟨a, c, _root_.Path.Homotopic.Quotient.comp pq.1 pq.2⟩

noncomputable def totalTransTraceLengthPath
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

noncomputable def totalSymmTraceLengthPath
    (p : TotalOpenGeometricCompPath A Step S) :
    ComputationalPaths.Path
      (GeometricTrace.traceLength (totalSymm S p).trace)
      (GeometricTrace.traceLength p.trace) :=
  ComputationalPaths.Path.trans
    (GeometricTrace.traceLengthSymmPath p.trace)
    (ComputationalPaths.Path.refl (GeometricTrace.traceLength p.trace))

noncomputable def totalTraceUnitRewrite (n : Nat) :
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl n)
        (ComputationalPaths.Path.refl n))
      (ComputationalPaths.Path.refl n) :=
  ComputationalPaths.Path.RwEq.step
    (ComputationalPaths.Path.Step.trans_refl_right
      (ComputationalPaths.Path.refl n))

theorem totalCode_symm
    (p : TotalOpenGeometricCompPath A Step S) :
    totalCode S (totalSymm S p) = codeSymm (totalCode S p) := by
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  refine Quotient.inductionOn (Quotient.mk' p.geometricPath) ?_
  intro γ
  rfl

theorem totalCode_trans
    (c : TotalComposable A Step S) :
    totalCode S (totalTrans S c) = codeTrans (composableCode S c) := by
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  refine Quotient.inductionOn (Quotient.mk' c.left.geometric) ?_
  intro p
  refine Quotient.inductionOn (Quotient.mk' c.right.geometric) ?_
  intro q
  rfl

/-! ## The total quotient topology -/

def totalEquivalent
    (p q : TotalOpenGeometricCompPath A Step S) : Prop :=
  totalCode S p = totalCode S q

noncomputable instance totalHomotopySetoid :
    Setoid (TotalOpenGeometricCompPath A Step S) where
  r := totalEquivalent S
  iseqv :=
    { refl := fun _ => rfl
      symm := fun h => h.symm
      trans := fun h₁ h₂ => h₁.trans h₂ }

abbrev TotalHomotopyClass :=
  Quotient (totalHomotopySetoid S)

noncomputable def totalQuotientMk
    (p : TotalOpenGeometricCompPath A Step S) : TotalHomotopyClass S :=
  Quotient.mk' p

theorem continuous_totalQuotientMk :
    Continuous (totalQuotientMk S : TotalOpenGeometricCompPath A Step S →
      TotalHomotopyClass S) :=
  continuous_quotient_mk'

/-! ## Descended endpoint maps -/

noncomputable def quotientSrc : TotalHomotopyClass S → A :=
  Quotient.lift (fun p : TotalOpenGeometricCompPath A Step S => p.src)
    (by
      intro p q h
      change totalCode S p = totalCode S q at h
      exact _root_.congrArg Sigma.fst h)

noncomputable def quotientTgt : TotalHomotopyClass S → A :=
  Quotient.lift (fun p : TotalOpenGeometricCompPath A Step S => p.tgt)
    (by
      intro p q h
      change totalCode S p = totalCode S q at h
      exact _root_.congrArg (fun z : TotalPathCode A => z.2.1) h)

theorem quotientSrc_totalQuotientMk
    (p : TotalOpenGeometricCompPath A Step S) :
    quotientSrc S (totalQuotientMk S p) = p.src :=
  rfl

theorem quotientTgt_totalQuotientMk
    (p : TotalOpenGeometricCompPath A Step S) :
    quotientTgt S (totalQuotientMk S p) = p.tgt :=
  rfl

theorem continuous_quotientSrc : Continuous (quotientSrc S) := by
  apply Continuous.quotient_lift
  exact TotalOpenGeometricCompPath.continuous_src S

theorem continuous_quotientTgt : Continuous (quotientTgt S) := by
  apply Continuous.quotient_lift
  exact TotalOpenGeometricCompPath.continuous_tgt S

/-! ## Identity and reversal -/

noncomputable def totalQuotientRefl (a : A) : TotalHomotopyClass S :=
  totalQuotientMk S (totalRefl S a)

noncomputable def totalQuotientSymm (p : TotalHomotopyClass S) : TotalHomotopyClass S :=
  Quotient.lift
    (fun p => totalQuotientMk S (totalSymm S p))
    (by
      intro p q h
      apply Quotient.sound
      change totalCode S (totalSymm S p) = totalCode S (totalSymm S q)
      rw [totalCode_symm S p, totalCode_symm S q]
      change totalCode S p = totalCode S q at h
      exact _root_.congrArg (codeSymm (A := A)) h)
    p

theorem totalQuotientSymm_totalQuotientMk
    (p : TotalOpenGeometricCompPath A Step S) :
    totalQuotientSymm S (totalQuotientMk S p) =
      totalQuotientMk S (totalSymm S p) :=
  rfl

theorem continuous_totalQuotientRefl :
    Continuous (totalQuotientRefl S : A → TotalHomotopyClass S) := by
  exact continuous_totalQuotientMk S |>.comp (continuous_totalRefl S)

theorem continuous_totalQuotientSymm : Continuous (totalQuotientSymm S :
    TotalHomotopyClass S → TotalHomotopyClass S) := by
  apply Continuous.quotient_lift
  exact continuous_totalQuotientMk S |>.comp (continuous_totalSymm S)

/-! ## The composable-pair quotient -/

def composableEquivalent
    (c d : TotalComposable A Step S) : Prop :=
  composableCode S c = composableCode S d

noncomputable instance composableHomotopySetoid : Setoid (TotalComposable A Step S) where
  r := composableEquivalent S
  iseqv :=
    { refl := fun _ => rfl
      symm := fun h => h.symm
      trans := fun h₁ h₂ => h₁.trans h₂ }

abbrev ComposableHomotopyClass := Quotient (composableHomotopySetoid S)

noncomputable def composableQuotientMk (c : TotalComposable A Step S) :
    ComposableHomotopyClass S :=
  Quotient.mk' c

theorem continuous_composableQuotientMk :
    Continuous (composableQuotientMk S : TotalComposable A Step S →
      ComposableHomotopyClass S) :=
  continuous_quotient_mk'

/-! ## Composition as a continuous quotient-level map -/

theorem composableEquivalent_totalTrans
    {c d : TotalComposable A Step S}
    (h : composableEquivalent S c d) :
    totalEquivalent S (totalTrans S c) (totalTrans S d) := by
  change totalCode S (totalTrans S c) = totalCode S (totalTrans S d)
  rw [totalCode_trans S c, totalCode_trans S d]
  change composableCode S c = composableCode S d at h
  exact _root_.congrArg (codeTrans (A := A)) h

noncomputable def quotientTransFromComposable
    (c : ComposableHomotopyClass S) : TotalHomotopyClass S :=
  Quotient.lift
    (fun c => totalQuotientMk S (totalTrans S c))
    (by
      intro c d h
      apply Quotient.sound
      exact composableEquivalent_totalTrans S h)
    c

theorem quotientTransFromComposable_composableQuotientMk
    (c : TotalComposable A Step S) :
    quotientTransFromComposable S (composableQuotientMk S c) =
      totalQuotientMk S (totalTrans S c) :=
  rfl

theorem continuous_quotientTransFromComposable :
    Continuous (quotientTransFromComposable S :
      ComposableHomotopyClass S → TotalHomotopyClass S) := by
  apply Continuous.quotient_lift
  exact continuous_totalQuotientMk S |>.comp (continuous_totalTrans S)

/-! ## A compact phase-twelve certificate -/

structure Certificate where
  quotient_projection_continuous : Continuous (totalQuotientMk S)
  source_continuous : Continuous (quotientSrc S)
  target_continuous : Continuous (quotientTgt S)
  identity_continuous : Continuous (totalQuotientRefl S)
  reversal_continuous : Continuous (totalQuotientSymm S)
  composition_continuous : Continuous (quotientTransFromComposable S)
  composition_trace_path : ∀ c : TotalComposable A Step S,
    ComputationalPaths.Path
      (GeometricTrace.traceLength (totalTrans S c).trace)
      (TotalComposable.leftTraceLength S c +
        TotalComposable.rightTraceLength S c)
  reversal_trace_path : ∀ p : TotalOpenGeometricCompPath A Step S,
    ComputationalPaths.Path
      (GeometricTrace.traceLength (totalSymm S p).trace)
      (GeometricTrace.traceLength p.trace)
  trace_unit_rewrite : ∀ n : Nat,
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl n)
        (ComputationalPaths.Path.refl n))
      (ComputationalPaths.Path.refl n)
  source_of_refl : ∀ a, quotientSrc S (totalQuotientRefl S a) = a
  target_of_refl : ∀ a, quotientTgt S (totalQuotientRefl S a) = a

noncomputable def certificate : Certificate S where
  quotient_projection_continuous := continuous_totalQuotientMk S
  source_continuous := continuous_quotientSrc S
  target_continuous := continuous_quotientTgt S
  identity_continuous := continuous_totalQuotientRefl S
  reversal_continuous := continuous_totalQuotientSymm S
  composition_continuous := continuous_quotientTransFromComposable S
  composition_trace_path := totalTransTraceLengthPath S
  reversal_trace_path := totalSymmTraceLengthPath S
  trace_unit_rewrite := totalTraceUnitRewrite
  source_of_refl := by intro a; rfl
  target_of_refl := by intro a; rfl

end TotalOpenGeometricCompPath
end GeometricTopology
end Path
end ComputationalPaths
