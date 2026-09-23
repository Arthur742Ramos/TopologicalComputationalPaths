import ComputationalPaths.Path.Topology.TraceSensitiveTopologicalCompPath
import ComputationalPaths.Path.Topology.ConcreteCircleWinding

/-!
# A finite trace-sensitive separation certificate

This module records a finite code model of the two-label separation used in
the topological semantics manuscript. The trace code distinguishes the two one-letter
words, while the observable code intentionally forgets the generator name.
The discrete-to-indiscrete identity is continuous, but its reverse is not.
Thus the refinement comparison is a genuine continuous bijection which need
not be a homeomorphism.

The certificate is deliberately finite: it isolates the topological mechanism
without asserting that the code space formalizes the nonconstant circle
presentation or its scoped rewrite quotient. The manuscript proves that
quotient-level distinction with a signed-count invariant.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology
namespace TraceSensitiveSeparation

open Set
open scoped Topology

inductive Generator
  | e
  | f
  deriving DecidableEq

instance : Fintype Generator where
  elems := {Generator.e, Generator.f}
  complete := by
    intro g
    cases g <;> simp

/-- The one-letter signed word for a generator. -/
def oneLetter (g : Generator) : FlatWord Generator :=
  ⟨1, fun _ => Sum.inl g⟩

theorem oneLetter_e_ne_f : oneLetter Generator.e ≠ oneLetter Generator.f := by
  intro h
  have hfun : (fun _ : Fin 1 =>
      (Sum.inl Generator.e : SignedStep Generator)) =
      (fun _ : Fin 1 => (Sum.inl Generator.f : SignedStep Generator)) := by
    simpa [oneLetter] using h
  have hvalue := congrFun hfun (0 : Fin 1)
  cases hvalue

/-- The observable code keeps only the common one-letter length. -/
abbrev ObservableCode : Type := Nat × PUnit

def observableCode (_ : Generator) : ObservableCode :=
  (1, PUnit.unit)

theorem observableCode_e_eq_f :
    observableCode Generator.e = observableCode Generator.f := by
  rfl

def traceTopology : TopologicalSpace Generator := ⊥

def observableTopology : TopologicalSpace Generator := ⊤

instance : TopologicalSpace Generator := traceTopology

instance : DiscreteTopology Generator := discreteTopology_bot Generator

/-- Both labels execute the same nonconstant circle loop. -/
noncomputable def duplicateCircleSystem :
    ContinuousGeometricStepSystem
      ConcreteCircleWinding.TopologicalCircle Generator where
  src := fun _ => 0
  tgt := fun _ => 0
  realize := fun _ => ConcreteCircleWinding.standardLoop 1
  continuous_src := continuous_const
  continuous_tgt := continuous_const
  continuous_realize := continuous_of_discreteTopology

theorem duplicateCircle_realize_eq :
    GeometricTrace.realize
      (GeometricTrace.single (S := duplicateCircleSystem.toGeometricStepSystem)
        Generator.e) =
    GeometricTrace.realize
      (GeometricTrace.single (S := duplicateCircleSystem.toGeometricStepSystem)
        Generator.f) := rfl

theorem duplicateCircle_realize_nonconstant :
    ConcreteCircleWinding.standardLoop 1 ≠
      _root_.Path.refl (0 : ConcreteCircleWinding.TopologicalCircle) := by
  intro h
  have hw := _root_.congrArg ConcreteCircleWinding.windingPath h
  rw [ConcreteCircleWinding.windingPath_standardLoop,
    ConcreteCircleWinding.windingPath_refl] at hw
  omega

theorem continuous_trace_to_observable :
    @Continuous Generator Generator traceTopology observableTopology id := by
  change @Continuous Generator Generator ⊥ ⊤ id
  exact continuous_bot

theorem not_continuous_observable_to_trace :
    ¬ @Continuous Generator Generator observableTopology traceTopology id := by
  intro h
  letI : TopologicalSpace Generator := traceTopology
  letI : DiscreteTopology Generator := ⟨by rfl⟩
  let U : Set Generator := {Generator.e}
  have hopen : IsOpen[traceTopology] U := by
    exact isOpen_discrete U
  have hpre : IsOpen[observableTopology]
      ((id : Generator → Generator) ⁻¹' U) := by
    exact @IsOpen.preimage Generator Generator observableTopology traceTopology
      id h U hopen
  have hcases :
      ((id : Generator → Generator) ⁻¹' U) = ∅ ∨
        ((id : Generator → Generator) ⁻¹' U) = univ := by
    letI : TopologicalSpace Generator := observableTopology
    apply (TopologicalSpace.isOpen_top_iff _).mp
    exact hpre
  rcases hcases with hempty | huniv
  · have : Generator.e ∈ ((id : Generator → Generator) ⁻¹' U) := by
      simp [U]
    rw [hempty] at this
    exact this
  · have hf : Generator.f ∈ U := by
      have : Generator.f ∈ ((id : Generator → Generator) ⁻¹' U) := by
        rw [huniv]
        exact mem_univ _
      simpa using this
    simp [U] at hf

noncomputable def unitRewrite (n : Nat) :
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl n)
        (ComputationalPaths.Path.refl n))
      (ComputationalPaths.Path.refl n) :=
  ComputationalPaths.Path.RwEq.step
    (ComputationalPaths.Path.Step.trans_refl_right
      (ComputationalPaths.Path.refl n))

structure Certificate where
  trace_separates : oneLetter Generator.e ≠ oneLetter Generator.f
  observable_forgets : observableCode Generator.e = observableCode Generator.f
  forward_continuous :
    @Continuous Generator Generator traceTopology observableTopology id
  reverse_not_continuous :
    ¬ @Continuous Generator Generator observableTopology traceTopology id
  unit_coherence : ∀ n : Nat,
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl n)
        (ComputationalPaths.Path.refl n))
      (ComputationalPaths.Path.refl n)

noncomputable def certificate : Certificate where
  trace_separates := oneLetter_e_ne_f
  observable_forgets := observableCode_e_eq_f
  forward_continuous := continuous_trace_to_observable
  reverse_not_continuous := not_continuous_observable_to_trace
  unit_coherence := unitRewrite

end TraceSensitiveSeparation
end GeometricTopology
end Path
end ComputationalPaths
