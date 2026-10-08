import ComputationalPaths.Path.Topology.LiteralWordQuotient

/-! # Discreteness of fixed-endpoint full-word quotients with discrete labels -/

namespace ComputationalPaths.Path.GeometricTopology.LiteralWord

open scoped Topology
universe u v
variable {A : Type u} [TopologicalSpace A] {Step : Type v} [TopologicalSpace Step]
  [DiscreteTopology Step] {S : GeometricStepSystem A Step}

/-- At fixed endpoints the exact signed tuple determines a literal word.
Thus discrete labels make the full-word topology discrete without a separation
assumption on the geometric space and without finiteness of the alphabet. -/
theorem discrete_words (a b : A) :
    @DiscreteTopology (Word S a b) (Word.sensitiveTopology (S := S) a b) := by
  letI := Word.sensitiveTopology (S := S) a b
  have h : Continuous (Word.toFlatWord : Word S a b → FlatWord Step) :=
    continuous_fst.comp (continuous_induced_dom :
      Continuous (fun w : Word S a b => (w.toFlatWord, Word.coordinates w)))
  exact DiscreteTopology.of_continuous_injective h (Word.toFlatWord_injective a b)

variable {C : ContinuousGeometricStepSystem A Step}

/-- A quotient of the discrete fixed-endpoint literal word carrier is discrete. -/
theorem discrete_wordQuotient (P : ScopedGeometricRewritePresentation C) (a b : A) :
    @DiscreteTopology (Quotient (WordRwEq.setoid P a b))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (WordRwEq.setoid P a b) (Word.sensitiveTopology (S := C.toGeometricStepSystem) a b)) := by
  letI := Word.sensitiveTopology (S := C.toGeometricStepSystem) a b
  letI := discrete_words (S := C.toGeometricStepSystem) a b
  letI := TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (WordRwEq.setoid P a b) (Word.sensitiveTopology (S := C.toGeometricStepSystem) a b)
  apply discreteTopology_iff_forall_isOpen.2
  intro U
  exact isOpen_coinduced.mpr (isOpen_discrete _)

/-- The matching equal-slot tree quotient is therefore discrete as well.
Tree parentheses are removed by structural normalization, not by an axiom. -/
theorem discrete_traceSensitiveQuotient (P : ScopedGeometricRewritePresentation C) (a b : A) :
    @DiscreteTopology (Quotient (CoherentRepresentativeElimination.traceSetoid P a b))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (CoherentRepresentativeElimination.traceSetoid P a b)
        (EqualSlotTopology.traceSensitiveTopology (S := C.toGeometricStepSystem) a b)) := by
  letI := TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (CoherentRepresentativeElimination.traceSetoid P a b)
    (EqualSlotTopology.traceSensitiveTopology (S := C.toGeometricStepSystem) a b)
  letI := TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (WordRwEq.setoid P a b) (Word.sensitiveTopology (S := C.toGeometricStepSystem) a b)
  letI := discrete_wordQuotient P a b
  exact DiscreteTopology.of_continuous_injective
    (WordRwEq.sensitiveQuotientHomeomorph P a b).continuous_toFun
    (WordRwEq.sensitiveQuotientHomeomorph P a b).injective

end ComputationalPaths.Path.GeometricTopology.LiteralWord
