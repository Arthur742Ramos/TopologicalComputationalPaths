import ComputationalPaths.Path.Topology.ContinuousGeometricStepSystemMap
import ComputationalPaths.Path.Rewrite.RwEq
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Endpointwise homotopy quotients of computational paths

The total carrier retains computational traces, while a topological
fundamental groupoid identifies geometric representatives up to homotopy.
This file makes that quotient explicit for every endpoint fibre.  The
quotient carries the canonical quotient topology, the quotient map is
continuous, and identity, composition, and reversal descend through the
homotopy relation.

Composition is presented in two forms: its algebraic descended operation on
quotient classes, and the continuous lift from the composable open-path
carrier.  The latter is the correct input for the total quotient groupoid in
the next phase; it does not silently assume that arbitrary products of
quotient maps are quotient maps.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open CategoryTheory
open scoped ContinuousMap FundamentalGroupoid Topology

attribute [local instance] _root_.Path.Homotopic.setoid

universe u v

namespace TotalOpenGeometricCompPath

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  (S : ContinuousGeometricStepSystem A Step)

/-! ## The endpointwise setoid and quotient topology -/

noncomputable instance openPathHomotopySetoid {a b : A} :
    Setoid (OpenGeometricCompPath S.toGeometricStepSystem a b) where
  r p q := _root_.Path.Homotopic p.geometric q.geometric
  iseqv :=
    { refl := fun p => _root_.Path.Homotopic.refl p.geometric
      symm := fun h => _root_.Path.Homotopic.symm h
      trans := fun h₁ h₂ => _root_.Path.Homotopic.trans h₁ h₂ }

/-- A computational-path homotopy class in a fixed endpoint fibre. -/
abbrev HomotopyClass {a b : A} :=
  Quotient (openPathHomotopySetoid S (a := a) (b := b))

/-- The quotient projection from coherent open paths to homotopy classes. -/
noncomputable def quotientMk {a b : A}
    (p : OpenGeometricCompPath S.toGeometricStepSystem a b) :
    HomotopyClass S (a := a) (b := b) :=
  Quotient.mk' p

theorem continuous_quotientMk {a b : A} :
    Continuous (quotientMk S : OpenGeometricCompPath
      S.toGeometricStepSystem a b → HomotopyClass S (a := a) (b := b)) :=
  continuous_quotient_mk'

theorem quotientMk_eq_iff {a b : A}
    (p q : OpenGeometricCompPath S.toGeometricStepSystem a b) :
    quotientMk S p = quotientMk S q ↔
      _root_.Path.Homotopic p.geometric q.geometric :=
  Quotient.eq

/-! ## Comparison with Mathlib's path-homotopy quotient -/

noncomputable def geometricClass {a b : A} :
    HomotopyClass S (a := a) (b := b) →
      _root_.Path.Homotopic.Quotient a b :=
  Quotient.lift
    (fun p => Quotient.mk' p.geometric)
    (by
      intro p q h
      exact Quotient.sound h)

theorem geometricClass_quotientMk {a b : A}
    (p : OpenGeometricCompPath S.toGeometricStepSystem a b) :
    geometricClass S (quotientMk S p) = Quotient.mk' p.geometric :=
  rfl

theorem geometricClass_injective {a b : A} :
    Function.Injective (geometricClass S : HomotopyClass S (a := a) (b := b) →
      _root_.Path.Homotopic.Quotient a b) := by
  intro p q h
  refine Quotient.inductionOn₂ p q ?_ h
  intro p q h
  apply Quotient.sound
  exact @Quotient.exact _ (_root_.Path.Homotopic.setoid a b)
    p.geometric q.geometric h

/-! ## Descended identity, composition, and reversal -/

noncomputable def pathQuotientRefl (a : A) :
    _root_.Path.Homotopic.Quotient a a :=
  Quotient.mk' (_root_.Path.refl a)

noncomputable def pathQuotientSymm {a b : A}
    (p : _root_.Path.Homotopic.Quotient a b) :
    _root_.Path.Homotopic.Quotient b a :=
  Quotient.lift
    (fun γ => Quotient.mk' γ.symm)
    (by
      intro γ₁ γ₂ h
      rcases h with ⟨h⟩
      exact Quotient.sound ⟨h.symm₂⟩)
    p

noncomputable def quotientRefl (a : A) : HomotopyClass S (a := a) (b := a) :=
  quotientMk S (openRefl S.toGeometricStepSystem a)

noncomputable def quotientTrans {a b c : A}
    (p : HomotopyClass S (a := a) (b := b))
    (q : HomotopyClass S (a := b) (b := c)) :
    HomotopyClass S (a := a) (b := c) :=
  Quotient.map₂
    (fun p q => openTrans S.toGeometricStepSystem p q)
    (by
      intro p₁ p₂ hp q₁ q₂ hq
      exact _root_.Path.Homotopic.hcomp hp hq)
    p q

noncomputable def quotientSymm {a b : A}
    (p : HomotopyClass S (a := a) (b := b)) :
    HomotopyClass S (a := b) (b := a) :=
  Quotient.map
    (fun p => openSymm S.toGeometricStepSystem p)
    (by
      intro p q h
      rcases h with ⟨h⟩
      exact ⟨h.symm₂⟩)
    p

theorem quotientTrans_quotientMk {a b c : A}
    (p : OpenGeometricCompPath S.toGeometricStepSystem a b)
    (q : OpenGeometricCompPath S.toGeometricStepSystem b c) :
    quotientTrans S (quotientMk S p) (quotientMk S q) =
      quotientMk S (openTrans S.toGeometricStepSystem p q) :=
  rfl

theorem quotientSymm_quotientMk {a b : A}
    (p : OpenGeometricCompPath S.toGeometricStepSystem a b) :
    quotientSymm S (quotientMk S p) =
      quotientMk S (openSymm S.toGeometricStepSystem p) :=
  rfl

theorem geometricClass_quotientRefl (a : A) :
    geometricClass S (quotientRefl S a) =
      pathQuotientRefl a := by
  rfl

theorem geometricClass_quotientTrans {a b c : A}
    (p : HomotopyClass S (a := a) (b := b))
    (q : HomotopyClass S (a := b) (b := c)) :
    geometricClass S (quotientTrans S p q) =
      _root_.Path.Homotopic.Quotient.comp (geometricClass S p)
        (geometricClass S q) := by
  refine Quotient.inductionOn₂ p q ?_
  intro p q
  rfl

theorem geometricClass_quotientSymm {a b : A}
    (p : HomotopyClass S (a := a) (b := b)) :
    geometricClass S (quotientSymm S p) =
      pathQuotientSymm (geometricClass S p) := by
  refine Quotient.inductionOn p ?_
  intro p
  rfl

/-! ## Continuous lifts from the explicit open-path carriers -/

noncomputable def quotientTransLift {a b c : A}
    (pq : OpenGeometricCompPath S.toGeometricStepSystem a b ×
      OpenGeometricCompPath S.toGeometricStepSystem b c) :
    HomotopyClass S (a := a) (b := c) :=
  quotientMk S (openTrans S.toGeometricStepSystem pq.1 pq.2)

theorem continuous_quotientTransLift {a b c : A} :
    Continuous (quotientTransLift S :
      OpenGeometricCompPath S.toGeometricStepSystem a b ×
        OpenGeometricCompPath S.toGeometricStepSystem b c →
      HomotopyClass S (a := a) (b := c)) := by
  exact continuous_quotientMk S |>.comp
    (continuous_openTrans S.toGeometricStepSystem)

noncomputable def quotientSymmLift {a b : A}
    (p : OpenGeometricCompPath S.toGeometricStepSystem a b) :
    HomotopyClass S (a := b) (b := a) :=
  quotientMk S (openSymm S.toGeometricStepSystem p)

theorem continuous_quotientSymmLift {a b : A} :
    Continuous (quotientSymmLift S :
      OpenGeometricCompPath S.toGeometricStepSystem a b →
      HomotopyClass S (a := b) (b := a)) := by
  exact continuous_quotientMk S |>.comp
    (continuous_openSymm S.toGeometricStepSystem)

/-! ## Computational trace witnesses at the quotient interface -/

noncomputable def quotientSymmTracePath {a b : A}
    (p : OpenGeometricCompPath S.toGeometricStepSystem a b) :
    ComputationalPaths.Path
      (GeometricTrace.traceLength
        (openSymm S.toGeometricStepSystem p).trace)
      (GeometricTrace.traceLength p.trace) :=
  ComputationalPaths.Path.trans
    (GeometricTrace.traceLengthSymmPath p.trace)
    (ComputationalPaths.Path.refl (GeometricTrace.traceLength p.trace))

noncomputable def quotientTraceUnitRewrite (n : Nat) :
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl n)
        (ComputationalPaths.Path.refl n))
      (ComputationalPaths.Path.refl n) :=
  ComputationalPaths.Path.RwEq.step
    (ComputationalPaths.Path.Step.trans_refl_right
      (ComputationalPaths.Path.refl n))

/-! ## A phase-ten certificate -/

structure TopologicalCompPathHomotopyQuotientCertificate where
  quotient_projection_continuous {a b : A} :
    Continuous (quotientMk S : OpenGeometricCompPath
      S.toGeometricStepSystem a b → HomotopyClass S (a := a) (b := b))
  geometric_comparison_injective {a b : A} :
    Function.Injective (geometricClass S : HomotopyClass S (a := a) (b := b) →
      _root_.Path.Homotopic.Quotient a b)
  composition_lift_continuous {a b c : A} :
    Continuous (quotientTransLift S :
      OpenGeometricCompPath S.toGeometricStepSystem a b ×
        OpenGeometricCompPath S.toGeometricStepSystem b c →
      HomotopyClass S (a := a) (b := c))
  reversal_lift_continuous {a b : A} :
    Continuous (quotientSymmLift S :
      OpenGeometricCompPath S.toGeometricStepSystem a b →
      HomotopyClass S (a := b) (b := a))
  reversal_trace_path {a b : A}
      (p : OpenGeometricCompPath S.toGeometricStepSystem a b) :
      ComputationalPaths.Path
        (GeometricTrace.traceLength
          (openSymm S.toGeometricStepSystem p).trace)
        (GeometricTrace.traceLength p.trace)
  trace_unit_rewrite : ∀ n : Nat,
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl n)
        (ComputationalPaths.Path.refl n))
      (ComputationalPaths.Path.refl n)

noncomputable def topologicalCompPathHomotopyQuotientCertificate :
    TopologicalCompPathHomotopyQuotientCertificate S where
  quotient_projection_continuous := continuous_quotientMk S
  geometric_comparison_injective := by
    intro a b
    exact geometricClass_injective S
  composition_lift_continuous := continuous_quotientTransLift S
  reversal_lift_continuous := continuous_quotientSymmLift S
  reversal_trace_path := quotientSymmTracePath S
  trace_unit_rewrite := quotientTraceUnitRewrite

end TotalOpenGeometricCompPath
end GeometricTopology
end Path
end ComputationalPaths
