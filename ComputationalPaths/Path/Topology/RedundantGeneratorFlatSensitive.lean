import ComputationalPaths.Path.Topology.VariableFlatGlobalInterpretation
import ComputationalPaths.Path.Topology.RedundantGeneratorObservable

/-!
# Full-word invariance for the conservative abbreviation example

The same actual substitutions that fail for the observable topology induce
homeomorphisms of the flat full-word quotients and their final pair domains.
-/

namespace ComputationalPaths.Path.GeometricTopology.RedundantGeneratorObservable

universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

private theorem old_primitive_roundtrip (α : _root_.Path x x) (s : OldLabel) :
    ScopedRwEq (oldPresentation α)
      ((eliminateNew α).substitution.mapTrace ((includeOld α).substitution.step s))
      (GeometricTrace.single s) := by
  cases s <;> exact ScopedRwEq.refl _

private theorem new_primitive_roundtrip (α : _root_.Path x x) (s : NewLabel) :
    ScopedRwEq (newPresentation α)
      ((includeOld α).substitution.mapTrace ((eliminateNew α).substitution.step s))
      (GeometricTrace.single s) := by
  cases s
  · exact ScopedRwEq.refl _
  · exact ScopedRwEq.refl _
  · exact (ScopedRwEq.generator (Abbreviation.define (α := α))).symm

noncomputable def flatSensitiveHomeomorph (α : _root_.Path x x) (a b : X) :=
  ScopedWordInterpretation.discreteFlatSensitiveQuotientHomeomorph
    (includeOld α) (eliminateNew α) (old_primitive_roundtrip α) (new_primitive_roundtrip α) a b

noncomputable def flatSensitiveGlobalHomeomorph (α : _root_.Path x x) :=
  ScopedWordInterpretation.flatSensitiveGlobalHomeomorph
    (includeOld α) (eliminateNew α) (old_primitive_roundtrip α) (new_primitive_roundtrip α)
    continuous_of_discreteTopology continuous_of_discreteTopology

noncomputable def flatSensitiveFinalPairHomeomorph (α : _root_.Path x x) :=
  ScopedWordInterpretation.flatSensitiveFinalPairHomeomorph
    (includeOld α) (eliminateNew α) (old_primitive_roundtrip α) (new_primitive_roundtrip α)
    continuous_of_discreteTopology continuous_of_discreteTopology

end ComputationalPaths.Path.GeometricTopology.RedundantGeneratorObservable
