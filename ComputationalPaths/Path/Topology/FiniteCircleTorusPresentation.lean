import ComputationalPaths.Path.Topology.ConcreteTorusWinding
import ComputationalPaths.Path.Topology.ScopedGeometricRewrite
import ComputationalPaths.Path.Rewrite.ScopedCompletion

/-!
# Finite-generator circle and torus presentation data

This module records the finite primitive-step carriers used by the manuscript.
The completed normal-form interfaces are kept separate from the integer-indexed
circle certificate and the ordinary loop quotient: the primitive alphabets here
are one circle generator and two torus generators.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

open ConcreteCircleWinding

universe u

namespace FiniteCircleTorusPresentation

/-! ## Finite circle alphabet -/

inductive CircleGenerator
  | a
deriving DecidableEq

noncomputable instance circleGeneratorTopologicalSpace :
    TopologicalSpace CircleGenerator := ⊥

noncomputable instance circleGeneratorDiscreteTopology :
    DiscreteTopology CircleGenerator := discreteTopology_bot CircleGenerator

noncomputable def circleStepSystem :
    ContinuousGeometricStepSystem TopologicalCircle CircleGenerator where
  src := fun _ => (0 : TopologicalCircle)
  tgt := fun _ => (0 : TopologicalCircle)
  realize := fun _ => standardLoop 1
  continuous_src := continuous_const
  continuous_tgt := continuous_const
  continuous_realize := by
    exact continuous_of_discreteTopology

abbrev CircleTrace :=
  GeometricTrace circleStepSystem.toGeometricStepSystem
    (0 : TopologicalCircle) (0 : TopologicalCircle)

def circleExponent :
    {a b : TopologicalCircle} →
      GeometricTrace circleStepSystem.toGeometricStepSystem a b → Int
  | _, _, .refl _ => 0
  | _, _, .single _ => 1
  | _, _, .trans p q => circleExponent p + circleExponent q
  | _, _, .symm p => -circleExponent p

def circlePower : Nat → CircleTrace
  | 0 => .refl 0
  | n + 1 => .trans (circlePower n) (.single CircleGenerator.a)

def circleCanonical : Int → CircleTrace
  | Int.ofNat n => circlePower n
  | Int.negSucc n => .symm (circlePower (n + 1))

@[simp] theorem circleExponent_power (n : Nat) :
    circleExponent (circlePower n) = (n : Int) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change circleExponent (GeometricTrace.trans (circlePower n)
        (.single CircleGenerator.a)) = (n + 1 : Nat)
      simp only [circleExponent]
      rw [ih]
      norm_num

@[simp] theorem circleExponent_canonical (z : Int) :
    circleExponent (circleCanonical z) = z := by
  cases z with
  | ofNat n => simp [circleCanonical]
  | negSucc n =>
      change -circleExponent (circlePower (n + 1)) = Int.negSucc n
      rw [circleExponent_power]
      rfl

noncomputable def circleCompletion :
    ScopedCompletion.Data CircleTrace Int where
  encode := circleExponent
  decode := circleCanonical
  encode_decode := circleExponent_canonical

noncomputable def circleFinitePresentation :
    ScopedGeometricRewritePresentation circleStepSystem where
  rule := fun {_} {_} _ _ => False
  sound_rule := by
    intro _ _ _ _ h
    exact False.elim h

noncomputable def circleCompletionEquivInt :
    SimpleEquiv (ScopedCompletion.Quotient circleCompletion) Int :=
  ScopedCompletion.equivNormal circleCompletion

theorem circleCompletion_normalizes (p : CircleTrace) :
    ScopedCompletion.RwEq circleCompletion p
      (circleCanonical (circleExponent p)) :=
  ScopedCompletion.RwEq.step (.normalize p)

/-! ## Finite torus alphabet -/

inductive TorusGenerator
  | a
  | b
deriving DecidableEq

noncomputable instance torusGeneratorTopologicalSpace :
    TopologicalSpace TorusGenerator := ⊥

noncomputable instance torusGeneratorDiscreteTopology :
    DiscreteTopology TorusGenerator := discreteTopology_bot TorusGenerator

abbrev TorusCarrier := TopologicalTorus.Carrier
noncomputable abbrev torusBase : TorusCarrier := TopologicalTorus.base

noncomputable def torusStepSystem :
    ContinuousGeometricStepSystem TorusCarrier TorusGenerator where
  src := fun _ => torusBase
  tgt := fun _ => torusBase
  realize := fun g =>
    match g with
    | TorusGenerator.a =>
        (standardLoop 1).prod (_root_.Path.refl (0 : TopologicalCircle))
    | TorusGenerator.b =>
        (_root_.Path.refl (0 : TopologicalCircle)).prod (standardLoop 1)
  continuous_src := continuous_const
  continuous_tgt := continuous_const
  continuous_realize := by
    exact continuous_of_discreteTopology

abbrev TorusTrace :=
  GeometricTrace torusStepSystem.toGeometricStepSystem torusBase torusBase

def torusCodeAdd (x y : Int × Int) : Int × Int :=
  (x.1 + y.1, x.2 + y.2)

def torusCodeNeg (x : Int × Int) : Int × Int :=
  (-x.1, -x.2)

def torusCode :
    {a b : TorusCarrier} →
      GeometricTrace torusStepSystem.toGeometricStepSystem a b → Int × Int
  | _, _, .refl _ => (0, 0)
  | _, _, .single TorusGenerator.a => (1, 0)
  | _, _, .single TorusGenerator.b => (0, 1)
  | _, _, .trans p q => torusCodeAdd (torusCode p) (torusCode q)
  | _, _, .symm p => torusCodeNeg (torusCode p)

noncomputable def torusPower (g : TorusGenerator) : Nat → TorusTrace
  | 0 => .refl torusBase
  | n + 1 => .trans (torusPower g n) (.single g)

noncomputable def torusZPower (g : TorusGenerator) : Int → TorusTrace
  | Int.ofNat n => torusPower g n
  | Int.negSucc n => .symm (torusPower g (n + 1))

noncomputable def torusCanonical (z : Int × Int) : TorusTrace :=
  .trans (torusZPower TorusGenerator.a z.1)
    (torusZPower TorusGenerator.b z.2)

@[simp] theorem torusCode_power_a (n : Nat) :
    torusCode (torusPower TorusGenerator.a n) = ((n : Int), 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change torusCode (GeometricTrace.trans
        (torusPower TorusGenerator.a n) (.single TorusGenerator.a)) = _
      simp only [torusCode, torusCodeAdd]
      rw [ih]
      norm_num

@[simp] theorem torusCode_power_b (n : Nat) :
    torusCode (torusPower TorusGenerator.b n) = (0, (n : Int)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change torusCode (GeometricTrace.trans
        (torusPower TorusGenerator.b n) (.single TorusGenerator.b)) = _
      simp only [torusCode, torusCodeAdd]
      rw [ih]
      norm_num

@[simp] theorem torusCode_zpower_a (z : Int) :
    torusCode (torusZPower TorusGenerator.a z) = (z, 0) := by
  cases z with
  | ofNat n =>
      change torusCode (torusPower TorusGenerator.a n) = ((n : Int), 0)
      exact torusCode_power_a n
  | negSucc n =>
      change torusCode (GeometricTrace.symm
        (torusPower TorusGenerator.a (n + 1))) = (Int.negSucc n, 0)
      simp only [torusCode, torusCodeNeg]
      rw [torusCode_power_a]
      rfl

@[simp] theorem torusCode_zpower_b (z : Int) :
    torusCode (torusZPower TorusGenerator.b z) = (0, z) := by
  cases z with
  | ofNat n =>
      change torusCode (torusPower TorusGenerator.b n) = (0, (n : Int))
      exact torusCode_power_b n
  | negSucc n =>
      change torusCode (GeometricTrace.symm
        (torusPower TorusGenerator.b (n + 1))) = (0, Int.negSucc n)
      simp only [torusCode, torusCodeNeg]
      rw [torusCode_power_b]
      rfl

@[simp] theorem torusCode_canonical (z : Int × Int) :
    torusCode (torusCanonical z) = z := by
  cases z with
  | mk m n =>
      change torusCode (GeometricTrace.trans
        (torusZPower TorusGenerator.a m)
        (torusZPower TorusGenerator.b n)) = (m, n)
      simp only [torusCode, torusCodeAdd, torusCode_zpower_a,
        torusCode_zpower_b]
      simp

noncomputable def torusCompletion :
    ScopedCompletion.Data TorusTrace (Int × Int) where
  encode := torusCode
  decode := torusCanonical
  encode_decode := torusCode_canonical

noncomputable def torusCompletionEquivIntProd :
    SimpleEquiv (ScopedCompletion.Quotient torusCompletion) (Int × Int) :=
  ScopedCompletion.equivNormal torusCompletion

theorem torusCompletion_normalizes (p : TorusTrace) :
    ScopedCompletion.RwEq torusCompletion p
      (torusCanonical (torusCode p)) :=
  ScopedCompletion.RwEq.step (.normalize p)

/-! ## The finite commuting square is geometrically sound -/

noncomputable def torusA : TorusTrace := .single TorusGenerator.a

noncomputable def torusB : TorusTrace := .single TorusGenerator.b

theorem torusFiniteCommutingSquare :
    _root_.Path.Homotopic
      (GeometricTrace.realize (.trans torusA torusB))
      (GeometricTrace.realize (.trans torusB torusA)) := by
  have hAB :=
    TopologicalTorus.standardLoop_homotopic_sequentialLoop (1 : Int) 1
  have hBA := TopologicalTorus.standardLoop_homotopic
    ((TopologicalTorus.secondFactorLoop 1).trans
      (TopologicalTorus.firstFactorLoop 1))
  have hBA' :
      (TopologicalTorus.standardLoop 1 1).Homotopic
        ((TopologicalTorus.secondFactorLoop 1).trans
          (TopologicalTorus.firstFactorLoop 1)) := by
    have hw :
        TopologicalTorus.winding
            ((TopologicalTorus.secondFactorLoop 1).trans
              (TopologicalTorus.firstFactorLoop 1)) = (1, 1) := by
      rw [TopologicalTorus.winding_trans,
        TopologicalTorus.winding_secondFactorLoop,
        TopologicalTorus.winding_firstFactorLoop]
      rfl
    simpa [hw] using hBA
  have hcomm := hAB.symm.trans hBA'
  simpa [torusA, torusB, torusStepSystem, GeometricTrace.realize,
    TopologicalTorus.sequentialLoop, TopologicalTorus.firstFactorLoop,
    TopologicalTorus.secondFactorLoop] using hcomm

def torusCommutationRule
    {a b : TorusCarrier}
    (p q : GeometricTrace torusStepSystem.toGeometricStepSystem a b) : Prop :=
  ∃ (ha : a = torusBase) (hb : b = torusBase),
    (by cases ha; cases hb; exact p : TorusTrace) =
        .trans torusA torusB ∧
    (by cases ha; cases hb; exact q : TorusTrace) =
        .trans torusB torusA

noncomputable def torusFinitePresentation :
    ScopedGeometricRewritePresentation torusStepSystem where
  rule := fun {a b} p q => torusCommutationRule p q
  sound_rule := by
    intro a b p q h
    rcases h with ⟨ha, hb, hp, hq⟩
    cases ha
    cases hb
    cases hp
    cases hq
    exact torusFiniteCommutingSquare

end FiniteCircleTorusPresentation
end GeometricTopology
end Path
end ComputationalPaths
