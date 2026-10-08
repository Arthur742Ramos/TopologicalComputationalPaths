import ComputationalPaths.Path.Topology.LiteralWordRewrite
import ComputationalPaths.Path.Topology.FlatObservableTopology

/-!
# Matching equal-slot word and tree quotient topologies

The observable word topology observes length and canonical equal-slot
realization. Its full-word refinement additionally observes the signed word.
The comparison below derives continuity from exact coordinate identities and
structural normalization. Agreement of the refinement with the manuscript's
coproduct of composable word strata is a separate continuity obligation.
-/

namespace ComputationalPaths.Path.GeometricTopology.LiteralWord

open scoped Topology
universe u v

variable {A : Type u} [TopologicalSpace A] {Step : Type v}
  {S : GeometricStepSystem A Step}

namespace Word

/-- Structural word normalization also preserves the exact equal-slot path. -/
@[simp] theorem flatRealize_ofTrace {a b : A} (p : GeometricTrace S a b) :
    GeometricTrace.flatRealize (ofTrace p).toTrace = GeometricTrace.flatRealize p := by
  apply GeometricTrace.flatRealize_eq_of_flatWord
  rw [flatWord_toTrace, toFlatWord_ofTrace]

noncomputable def coordinates {a b : A} (w : Word S a b) :=
  (w.length, GeometricTrace.flatRealize w.toTrace)

@[reducible] noncomputable def observableTopology (a b : A) :
    TopologicalSpace (Word S a b) := TopologicalSpace.induced coordinates inferInstance

@[reducible] noncomputable def sensitiveTopology [TopologicalSpace Step] (a b : A) :
    TopologicalSpace (Word S a b) :=
  TopologicalSpace.induced (fun w : Word S a b => (w.toFlatWord, coordinates w)) inferInstance

@[simp] theorem coordinates_ofTrace {a b : A} (p : GeometricTrace S a b) :
    coordinates (ofTrace p) = EqualSlotTopology.traceCoordinates p := by
  simp only [coordinates, EqualSlotTopology.traceCoordinates, ofTrace_length, flatRealize_ofTrace]

@[simp] theorem traceCoordinates_toTrace {a b : A} (w : Word S a b) :
    EqualSlotTopology.traceCoordinates w.toTrace = coordinates w := by
  simp only [coordinates, EqualSlotTopology.traceCoordinates, toTrace_length]

theorem continuous_observable_ofTrace (a b : A) :
    @Continuous _ _ (EqualSlotTopology.traceObservableTopology (S := S) a b)
      (observableTopology (S := S) a b) ofTrace := by
  apply continuous_induced_rng.mpr
  simpa only [Function.comp_def, coordinates_ofTrace] using
    EqualSlotTopology.continuous_traceCoordinates (S := S) a b

theorem continuous_observable_toTrace (a b : A) :
    @Continuous _ _ (observableTopology (S := S) a b)
      (EqualSlotTopology.traceObservableTopology (S := S) a b) toTrace := by
  apply continuous_induced_rng.mpr
  simpa only [Function.comp_def, traceCoordinates_toTrace] using
    (continuous_induced_dom : @Continuous _ _ (observableTopology (S := S) a b)
      inferInstance coordinates)

theorem continuous_sensitive_ofTrace [TopologicalSpace Step] (a b : A) :
    @Continuous _ _ (EqualSlotTopology.traceSensitiveTopology (S := S) a b)
      (sensitiveTopology (S := S) a b) ofTrace := by
  apply continuous_induced_rng.mpr
  simpa only [Function.comp_def, toFlatWord_ofTrace, coordinates_ofTrace] using
    (continuous_induced_dom : @Continuous _ _
      (EqualSlotTopology.traceSensitiveTopology (S := S) a b) inferInstance
      (fun p : GeometricTrace S a b => (GeometricTrace.flatWord p, EqualSlotTopology.traceCoordinates p)))

theorem continuous_sensitive_toTrace [TopologicalSpace Step] (a b : A) :
    @Continuous _ _ (sensitiveTopology (S := S) a b)
      (EqualSlotTopology.traceSensitiveTopology (S := S) a b) toTrace := by
  apply continuous_induced_rng.mpr
  simpa only [Function.comp_def, flatWord_toTrace, traceCoordinates_toTrace] using
    (continuous_induced_dom : @Continuous _ _ (sensitiveTopology (S := S) a b) inferInstance
      (fun w : Word S a b => (w.toFlatWord, coordinates w)))

end Word

variable [TopologicalSpace Step] {C : ContinuousGeometricStepSystem A Step}

namespace WordRwEq

/-- General descent for the actual flatten/reconstruct maps. The specialized
results below derive these hypotheses from coordinate identities. -/
noncomputable def quotientHomeomorph (P : ScopedGeometricRewritePresentation C) (a b : A)
    (τ : TopologicalSpace (GeometricTrace C.toGeometricStepSystem a b))
    (ω : TopologicalSpace (Word C.toGeometricStepSystem a b))
    (hflat : @Continuous _ _ τ ω Word.ofTrace)
    (hrec : @Continuous _ _ ω τ Word.toTrace) :
    @Homeomorph (Quotient (CoherentRepresentativeElimination.traceSetoid P a b))
      (Quotient (setoid P a b))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (CoherentRepresentativeElimination.traceSetoid P a b) τ)
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology (setoid P a b) ω) := by
  letI := τ
  letI := ω
  letI := TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (CoherentRepresentativeElimination.traceSetoid P a b) τ
  letI := TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology (setoid P a b) ω
  refine { toEquiv := quotientEquiv P a b, continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientMk_isQuotient
      (CoherentRepresentativeElimination.traceSetoid P a b) τ).continuous_iff.2
    exact continuous_coinduced_rng.comp hflat
  · apply (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientMk_isQuotient
      (setoid P a b) ω).continuous_iff.2
    exact continuous_coinduced_rng.comp hrec

/-- Matching fixed-endpoint observable quotients have a checked homeomorphism. -/
noncomputable def observableQuotientHomeomorph
    (P : ScopedGeometricRewritePresentation C) (a b : A) :=
  quotientHomeomorph P a b
    (EqualSlotTopology.traceObservableTopology (S := C.toGeometricStepSystem) a b)
    (Word.observableTopology (S := C.toGeometricStepSystem) a b)
    (Word.continuous_observable_ofTrace a b) (Word.continuous_observable_toTrace a b)

/-- Matching full-word refinements have a checked homeomorphism. This statement
alone does not yet identify the word refinement with a coproduct topology. -/
noncomputable def sensitiveQuotientHomeomorph
    (P : ScopedGeometricRewritePresentation C) (a b : A) :=
  quotientHomeomorph P a b
    (EqualSlotTopology.traceSensitiveTopology (S := C.toGeometricStepSystem) a b)
    (Word.sensitiveTopology (S := C.toGeometricStepSystem) a b)
    (Word.continuous_sensitive_ofTrace a b) (Word.continuous_sensitive_toTrace a b)

end WordRwEq
end ComputationalPaths.Path.GeometricTopology.LiteralWord
