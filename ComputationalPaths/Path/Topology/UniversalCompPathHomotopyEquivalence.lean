import ComputationalPaths.Path.Topology.TopologicalCompPathHomotopyQuotient
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# The universal endpointwise quotient equivalence

For the maximal continuous step system, every ordinary interval path is a
single coherent computational step.  After quotienting open computational
paths by geometric homotopy, this gives an actual endpointwise equivalence
with Mathlib's path-homotopy classes.

This is the precise universal statement available at the quotient level: the
computational trace is forgotten only after the explicit quotient, and the
remaining geometric class is neither lost nor duplicated.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

attribute [local instance] _root_.Path.Homotopic.setoid

universe u

namespace UniversalCompPathHomotopyEquivalence

variable {A : Type u} [TopologicalSpace A]

noncomputable abbrev UniversalSystem := continuousPathStepSystem A
abbrev UniversalOpen {a b : A} :=
  OpenGeometricCompPath UniversalSystem.toGeometricStepSystem a b
abbrev UniversalClass {a b : A} :=
  TotalOpenGeometricCompPath.HomotopyClass UniversalSystem (a := a) (b := b)

/-! ## The universal open-path section -/

noncomputable def universalOpenSection {a b : A} (γ : _root_.Path a b) :
    UniversalOpen (A := A) (a := a) (b := b) :=
  { trace :=
      ContinuousGeometricStepSystemMap.castTrace
        (S := UniversalSystem) γ.source.symm γ.target.symm
        (GeometricTrace.single
          (S := UniversalSystem.toGeometricStepSystem) γ.toContinuousMap)
    geometric := γ
    coherent := by
      have hrealize :
          GeometricTrace.realize
              (ContinuousGeometricStepSystemMap.castTrace
                (S := UniversalSystem) γ.source.symm γ.target.symm
                (GeometricTrace.single
                  (S := UniversalSystem.toGeometricStepSystem) γ.toContinuousMap)) =
            γ := by
        rw [ContinuousGeometricStepSystemMap.castTrace_realize]
        ext t
        rfl
      rw [hrealize]
      }

theorem universalOpenSection_geometric {a b : A} (γ : _root_.Path a b) :
    (universalOpenSection γ).geometric = γ :=
  rfl

/-! ## The two quotient maps -/

noncomputable def toPathClass {a b : A} :
    UniversalClass (A := A) (a := a) (b := b) →
      _root_.Path.Homotopic.Quotient a b :=
  TotalOpenGeometricCompPath.geometricClass UniversalSystem

noncomputable def fromPathClass {a b : A} :
    _root_.Path.Homotopic.Quotient a b →
      UniversalClass (A := A) (a := a) (b := b) :=
  Quotient.lift
    (fun γ => TotalOpenGeometricCompPath.quotientMk UniversalSystem
      (universalOpenSection γ))
    (by
      intro γ₁ γ₂ h
      exact Quotient.sound h)

theorem toPathClass_quotientMk {a b : A} (p : UniversalOpen (A := A) (a := a) (b := b)) :
    toPathClass (A := A)
        (TotalOpenGeometricCompPath.quotientMk UniversalSystem p) =
      Quotient.mk' p.geometric :=
  rfl

theorem fromPathClass_mk {a b : A} (γ : _root_.Path a b) :
    fromPathClass (A := A) (Quotient.mk' γ) =
      TotalOpenGeometricCompPath.quotientMk UniversalSystem
        (universalOpenSection γ) :=
  rfl

theorem from_toPathClass {a b : A}
    (p : UniversalClass (A := A) (a := a) (b := b)) :
    fromPathClass (A := A) (toPathClass (A := A) p) = p := by
  refine Quotient.inductionOn p ?_
  intro p
  apply Quotient.sound
  exact _root_.Path.Homotopic.refl p.geometric

theorem to_fromPathClass {a b : A}
    (γ : _root_.Path a b) :
    toPathClass (A := A) (fromPathClass (A := A) (Quotient.mk' γ)) =
      Quotient.mk' γ := by
  rfl

theorem universalOpenSection_traceLength {a b : A} (γ : _root_.Path a b) :
    GeometricTrace.traceLength (universalOpenSection γ).trace = 1 := by
  change GeometricTrace.traceLength
    (ContinuousGeometricStepSystemMap.castTrace
      (S := UniversalSystem) γ.source.symm γ.target.symm
      (GeometricTrace.single
        (S := UniversalSystem.toGeometricStepSystem) γ.toContinuousMap)) = 1
  rw [ContinuousGeometricStepSystemMap.castTrace_length]
  rfl

noncomputable def universalOpenSection_traceLengthPath
    {a b : A} (γ : _root_.Path a b) :
    ComputationalPaths.Path
      (GeometricTrace.traceLength (universalOpenSection γ).trace) 1 :=
  ComputationalPaths.Path.trans
    (ComputationalPaths.Path.ofEq (universalOpenSection_traceLength γ))
    (ComputationalPaths.Path.refl 1)

noncomputable def universalTraceUnitRewrite (n : Nat) :
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl n)
        (ComputationalPaths.Path.refl n))
      (ComputationalPaths.Path.refl n) :=
  ComputationalPaths.Path.RwEq.step
    (ComputationalPaths.Path.Step.trans_refl_right
      (ComputationalPaths.Path.refl n))

noncomputable def quotientEquiv {a b : A} :
    UniversalClass (A := A) (a := a) (b := b) ≃
      _root_.Path.Homotopic.Quotient a b where
  toFun := toPathClass (A := A)
  invFun := fromPathClass (A := A)
  left_inv := from_toPathClass (A := A)
  right_inv := by
    intro p
    refine Quotient.inductionOn p ?_
    intro γ
    exact to_fromPathClass (A := A) γ

theorem quotientEquiv_toFun {a b : A} :
    (quotientEquiv (A := A) (a := a) (b := b)).toFun =
      toPathClass (A := A) :=
  rfl

theorem quotientEquiv_surjective {a b : A} :
    Function.Surjective (toPathClass (A := A) :
      UniversalClass (A := A) (a := a) (b := b) →
        _root_.Path.Homotopic.Quotient a b) :=
  (quotientEquiv (A := A) (a := a) (b := b)).surjective

/-! ## A compact phase-eleven certificate -/

structure Certificate where
  quotient_equivalence {a b : A} :
    UniversalClass (A := A) (a := a) (b := b) ≃
      _root_.Path.Homotopic.Quotient a b
  endpointwise_surjective {a b : A} :
    Function.Surjective (toPathClass (A := A) :
      UniversalClass (A := A) (a := a) (b := b) →
        _root_.Path.Homotopic.Quotient a b)
  section_geometric {a b : A} (γ : _root_.Path a b) :
    (universalOpenSection γ).geometric = γ
  section_trace_length {a b : A} (γ : _root_.Path a b) :
    ComputationalPaths.Path
      (GeometricTrace.traceLength (universalOpenSection γ).trace) 1
  trace_unit_rewrite : ∀ n : Nat,
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl n)
        (ComputationalPaths.Path.refl n))
      (ComputationalPaths.Path.refl n)

noncomputable def certificate : Certificate (A := A) where
  quotient_equivalence := quotientEquiv
  endpointwise_surjective := quotientEquiv_surjective
  section_geometric := universalOpenSection_geometric
  section_trace_length := universalOpenSection_traceLengthPath
  trace_unit_rewrite := universalTraceUnitRewrite

end UniversalCompPathHomotopyEquivalence
end GeometricTopology
end Path
end ComputationalPaths
