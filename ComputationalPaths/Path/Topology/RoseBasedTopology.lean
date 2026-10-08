import ComputationalPaths.Path.Topology.GeometricRose
import ComputationalPaths.Path.Topology.RoseReducedWords
import ComputationalPaths.Path.Topology.FlatObservableDiscreteness
import ComputationalPaths.Path.Topology.LiteralWordDiscrete

/-!
# Based computational quotient topologies of the actual rose

The two circle retractions distinguish all four oriented primitive paths by
their winding pairs. The flat observable based trace quotient is therefore
discrete. The full-word based quotient is also discrete, and the checked
algebraic free-group equivalence becomes a homeomorphism for each topology.

These are topologies on fixed-endpoint computational quotients. No assertion
about surjectivity onto all fundamental-group classes or topology inherited
from a global arrow quotient is made here.
-/

namespace ComputationalPaths.Path.GeometricTopology.RoseBasedTopology

open RoseReducedWords GeometricRose ConcreteCircleWinding
open unitInterval
open scoped Topology

noncomputable section

abbrev roseSystem := RoseReducedWords.system loopA loopB
abbrev rosePresentation := RoseReducedWords.presentation loopA loopB
abbrev RoseScopedGroup := RoseReducedWords.ScopedGroup loopA loopB

private theorem winding_symm (p : _root_.Path (0 : Circle) 0) :
    windingPath p.symm = -windingPath p := by
  have h := windingPath_eq_of_homotopic (_root_.Path.Homotopic.trans_symm p)
  rw [windingPath_trans, windingPath_refl] at h
  omega

def signedLoop (s : SignedStep Label) : _root_.Path base base :=
  Sum.elim roseSystem.realize (fun i => (roseSystem.realize i).symm) s

def windingPair (p : _root_.Path base base) : ℤ × ℤ :=
  (windingPath (p.map continuous_leftRetract), windingPath (p.map continuous_rightRetract))

private def windingCode : SignedStep Label → ℤ × ℤ
  | .inl .a => (1, 0)
  | .inl .b => (0, 1)
  | .inr .a => (-1, 0)
  | .inr .b => (0, -1)

theorem windingPair_signedLoop (s : SignedStep Label) :
    windingPair (signedLoop s) = windingCode s := by
  rcases s with s | s
  · cases s with
    | a =>
        change (windingPath (loopA.map continuous_leftRetract),
          windingPath (loopA.map continuous_rightRetract)) = (1, 0)
        rw [leftRetract_loopA, rightRetract_loopA, windingPath_standardLoop, windingPath_refl]
    | b =>
        change (windingPath (loopB.map continuous_leftRetract),
          windingPath (loopB.map continuous_rightRetract)) = (0, 1)
        rw [leftRetract_loopB, rightRetract_loopB, windingPath_standardLoop, windingPath_refl]
  · cases s with
    | a =>
        change (windingPath (loopA.symm.map continuous_leftRetract),
          windingPath (loopA.symm.map continuous_rightRetract)) = (-1, 0)
        rw [← _root_.Path.map_symm, ← _root_.Path.map_symm,
          leftRetract_loopA, rightRetract_loopA]
        change (windingPath (standardLoop 1).symm,
          windingPath (_root_.Path.refl (0 : Circle)).symm) = (-1, 0)
        rw [winding_symm, winding_symm, windingPath_standardLoop, windingPath_refl]
        norm_num
    | b =>
        change (windingPath (loopB.symm.map continuous_leftRetract),
          windingPath (loopB.symm.map continuous_rightRetract)) = (0, -1)
        rw [← _root_.Path.map_symm, ← _root_.Path.map_symm,
          leftRetract_loopB, rightRetract_loopB]
        change (windingPath (_root_.Path.refl (0 : Circle)).symm,
          windingPath (standardLoop 1).symm) = (0, -1)
        rw [winding_symm, winding_symm, windingPath_standardLoop, windingPath_refl]
        norm_num

theorem signedPrimitive_eq_signedLoop (s : SignedStep Label) (t : I) :
    FlatObservableDiscreteness.signedPrimitive roseSystem.toGeometricStepSystem s t =
      signedLoop s t := by
  cases s <;> exact _root_.Path.extend_extends' _ _

/-- This distinction uses actual geometric retractions, independently of the
Cayley covering and the later homotopy completeness theorem. -/
theorem signedPrimitive_injective :
    Function.Injective (FlatObservableDiscreteness.signedPrimitive roseSystem.toGeometricStepSystem) := by
  intro s t h
  have hp : signedLoop s = signedLoop t := by
    apply _root_.Path.ext
    funext u
    simpa only [signedPrimitive_eq_signedLoop] using _root_.congrFun h u
  have hc : windingCode s = windingCode t := by
    simpa only [windingPair_signedLoop] using _root_.congrArg windingPair hp
  rcases s with s | s <;> rcases t with t | t <;> cases s <;> cases t
  all_goals first | rfl | (exfalso; norm_num [windingCode] at hc)

/-- The actual algebraic based quotient, with the flat observable quotient topology. -/
@[reducible] def flatObservableTopology : TopologicalSpace RoseScopedGroup :=
  TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (BasedScopedTraceGroup.traceSetoid rosePresentation base)
    (EqualSlotTopology.traceObservableTopology (S := roseSystem.toGeometricStepSystem) base base)

/-- The same based quotient, with the equal-slot full-word refinement. -/
@[reducible] def flatSensitiveTopology : TopologicalSpace RoseScopedGroup :=
  TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (BasedScopedTraceGroup.traceSetoid rosePresentation base)
    (EqualSlotTopology.traceSensitiveTopology (S := roseSystem.toGeometricStepSystem) base base)

theorem flatObservable_discrete : @DiscreteTopology RoseScopedGroup flatObservableTopology := by
  exact FlatObservableDiscreteness.discrete_observable_traceQuotient
    rosePresentation signedPrimitive_injective base base

theorem flatSensitive_discrete : @DiscreteTopology RoseScopedGroup flatSensitiveTopology := by
  exact LiteralWord.discrete_traceSensitiveQuotient rosePresentation base base

@[reducible] def discreteFreeGroupTopology : TopologicalSpace (FreeGroup Label) := ⊥

/-- Continuity is derived from the proved discrete source and target topologies. -/
def flatObservableHomeomorph : @Homeomorph RoseScopedGroup (FreeGroup Label)
    flatObservableTopology discreteFreeGroupTopology := by
  letI := flatObservableTopology
  letI := flatObservable_discrete
  letI := discreteFreeGroupTopology
  letI : DiscreteTopology (FreeGroup Label) := discreteTopology_bot _
  exact { toEquiv := quotientEquiv loopA loopB
          continuous_toFun := continuous_of_discreteTopology
          continuous_invFun := continuous_of_discreteTopology }

def flatSensitiveHomeomorph : @Homeomorph RoseScopedGroup (FreeGroup Label)
    flatSensitiveTopology discreteFreeGroupTopology := by
  letI := flatSensitiveTopology
  letI := flatSensitive_discrete
  letI := discreteFreeGroupTopology
  letI : DiscreteTopology (FreeGroup Label) := discreteTopology_bot _
  exact { toEquiv := quotientEquiv loopA loopB
          continuous_toFun := continuous_of_discreteTopology
          continuous_invFun := continuous_of_discreteTopology }

end
end ComputationalPaths.Path.GeometricTopology.RoseBasedTopology
