import ComputationalPaths.Path.Topology.FlatWordSubstitution
import ComputationalPaths.Path.Topology.LiteralWordStrata
import ComputationalPaths.Path.Topology.ContinuousWordInterpretation
import ComputationalPaths.Path.Topology.FlatObservableTopology

/-!
# Variable-length invariance of the flat full-word quotient

A primitive interpretation is continuous into the coproduct of finite signed
words. This actual label-code condition permits locally varying image lengths.
Continuous execution on genuine composable word strata then derives realization
continuity. Primitive inverse rewrites yield the quotient inverse laws.
-/

namespace ComputationalPaths.Path.GeometricTopology

open scoped Topology
universe u v w
variable {A : Type u} [TopologicalSpace A] {Step : Type v} [TopologicalSpace Step]
  {Step' : Type w} [TopologicalSpace Step']
  {S : ContinuousGeometricStepSystem A Step} {T : ContinuousGeometricStepSystem A Step'}

namespace WordSubstitution

/-- Variable-length substitution is continuous for the actual equal-slot
full-word topology; no exact geometric compatibility or uniform length is input. -/
theorem continuous_flat_sensitive (M : WordSubstitution S.toGeometricStepSystem T.toGeometricStepSystem)
    (hprimitive : Continuous (FlatWordSubstitution.primitiveWord M)) (a b : A) :
    @Continuous _ _ (EqualSlotTopology.traceSensitiveTopology (S := S.toGeometricStepSystem) a b)
      (EqualSlotTopology.traceSensitiveTopology (S := T.toGeometricStepSystem) a b) M.mapTrace := by
  letI := EqualSlotTopology.traceSensitiveTopology (S := S.toGeometricStepSystem) a b
  have hcode : Continuous (fun p : GeometricTrace S.toGeometricStepSystem a b =>
      (GeometricTrace.flatWord p, EqualSlotTopology.traceCoordinates p)) := continuous_induced_dom
  have hword : Continuous (fun p : GeometricTrace S.toGeometricStepSystem a b =>
      GeometricTrace.flatWord (M.mapTrace p)) := by
    simpa only [Function.comp_def, FlatWordSubstitution.mapTrace_flatWord] using
      (FlatWordSubstitution.continuous_substitution M hprimitive).comp hcode.fst
  have hlength : Continuous (fun p : GeometricTrace S.toGeometricStepSystem a b =>
      GeometricTrace.traceLength (M.mapTrace p)) := by
    simpa only [Function.comp_def, GeometricTrace.flatWord_length] using
      continuous_flatWordLength.comp hword
  have hmap := LiteralWord.Strata.continuous_flatRealize_of_flatWord T
    (fun _ : GeometricTrace S.toGeometricStepSystem a b => a)
    (fun _ : GeometricTrace S.toGeometricStepSystem a b => b)
    M.mapTrace continuous_const continuous_const hword
  have hpath : Continuous (fun p : GeometricTrace S.toGeometricStepSystem a b =>
      GeometricTrace.flatRealize (M.mapTrace p)) := by
    apply continuous_induced_rng.mpr
    exact hmap
  apply continuous_induced_rng.mpr
  simpa only [Function.comp_def, EqualSlotTopology.traceCoordinates] using
    hword.prodMk (hlength.prodMk hpath)

/-- Geometric compatibility is a separate primitive condition. When supplied,
the induced flat interpretation preserves the actual geometric homotopy class. -/
theorem map_flat_homotopic
    (M : WordSubstitution S.toGeometricStepSystem T.toGeometricStepSystem)
    (hstep : ∀ s, _root_.Path.Homotopic (GeometricTrace.flatRealize (M.step s)) (S.realize s))
    {a b : A} (p : GeometricTrace S.toGeometricStepSystem a b) :
    _root_.Path.Homotopic (GeometricTrace.flatRealize (M.mapTrace p))
      (GeometricTrace.flatRealize p) :=
  (GeometricTrace.flatRealize_homotopic_binary _).trans
    ((M.realize_homotopic
      (fun s => (GeometricTrace.flatRealize_homotopic_binary (M.step s)).symm.trans (hstep s)) p).trans
      (GeometricTrace.flatRealize_homotopic_binary p).symm)

end WordSubstitution

namespace ScopedWordInterpretation

variable {P : ScopedGeometricRewritePresentation S} {Q : ScopedGeometricRewritePresentation T}

/-- Mutually inverse primitive interpretations induce flat full-word quotient
homeomorphisms. Both continuities are derived from primitive finite-word codes. -/
noncomputable def flatSensitiveQuotientHomeomorph
    (M : ScopedWordInterpretation P Q) (N : ScopedWordInterpretation Q P)
    (hS : ∀ s : Step, ScopedRwEq P (N.substitution.mapTrace (M.substitution.step s))
      (GeometricTrace.single s))
    (hT : ∀ t : Step', ScopedRwEq Q (M.substitution.mapTrace (N.substitution.step t))
      (GeometricTrace.single t))
    (hM : Continuous (FlatWordSubstitution.primitiveWord M.substitution))
    (hN : Continuous (FlatWordSubstitution.primitiveWord N.substitution)) (a b : A) :=
  quotientHomeomorph M N hS hT a b
    (EqualSlotTopology.traceSensitiveTopology (S := S.toGeometricStepSystem) a b)
    (EqualSlotTopology.traceSensitiveTopology (S := T.toGeometricStepSystem) a b)
    (M.substitution.continuous_flat_sensitive hM a b)
    (N.substitution.continuous_flat_sensitive hN a b)

/-- Discrete primitive alphabets satisfy the primitive continuity conditions
without any uniform expansion-length restriction. -/
noncomputable def discreteFlatSensitiveQuotientHomeomorph
    [DiscreteTopology Step] [DiscreteTopology Step']
    (M : ScopedWordInterpretation P Q) (N : ScopedWordInterpretation Q P)
    (hS : ∀ s : Step, ScopedRwEq P (N.substitution.mapTrace (M.substitution.step s))
      (GeometricTrace.single s))
    (hT : ∀ t : Step', ScopedRwEq Q (M.substitution.mapTrace (N.substitution.step t))
      (GeometricTrace.single t)) (a b : A) :=
  flatSensitiveQuotientHomeomorph M N hS hT
    continuous_of_discreteTopology continuous_of_discreteTopology a b

end ScopedWordInterpretation
end ComputationalPaths.Path.GeometricTopology
