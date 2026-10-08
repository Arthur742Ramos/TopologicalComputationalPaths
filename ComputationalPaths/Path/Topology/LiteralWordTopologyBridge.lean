import ComputationalPaths.Path.Topology.LiteralWordPairs
import ComputationalPaths.Path.Topology.LiteralWordStrata

/-!
# Identification with the genuine composable-word coproduct

The extra exact path coordinate in the full-word refinements is continuous
on the literal finite-word strata and therefore adds no opens. At length zero
the global source coordinate retains the basepoint.
-/

namespace ComputationalPaths.Path.GeometricTopology.LiteralWord

open scoped Topology ContinuousMap
universe u v
variable {A : Type u} [TopologicalSpace A] {Step : Type v} [TopologicalSpace Step]
  {S : ContinuousGeometricStepSystem A Step}

namespace Word

@[reducible] noncomputable def tupleTopology (a b : A) :
    TopologicalSpace (Word S.toGeometricStepSystem a b) :=
  TopologicalSpace.induced toFlatWord inferInstance

/-- On the literal fixed-endpoint word carrier, exact execution is continuous
for the finite-tuple topology itself. -/
theorem continuous_tuple_flatRealize (a b : A) :
    @Continuous _ _ (tupleTopology (S := S) a b) inferInstance
      (fun w : Word S.toGeometricStepSystem a b => GeometricTrace.flatRealize w.toTrace) := by
  letI := tupleTopology (S := S) a b
  have hf : Continuous (fun w : Word S.toGeometricStepSystem a b =>
      GeometricTrace.flatWord w.toTrace) := by
    simpa only [flatWord_toTrace] using (continuous_induced_dom : Continuous toFlatWord)
  have h := Strata.continuous_flatRealize_of_flatWord S
    (fun _ : Word S.toGeometricStepSystem a b => a)
    (fun _ : Word S.toGeometricStepSystem a b => b)
    toTrace continuous_const continuous_const hf
  apply continuous_induced_rng.mpr
  exact h

/-- The matching full-word refinement is exactly the literal tuple topology. -/
theorem sensitiveTopology_eq_tupleTopology (a b : A) :
    sensitiveTopology (S := S.toGeometricStepSystem) a b = tupleTopology (S := S) a b := by
  letI := tupleTopology (S := S) a b
  have hw : Continuous (toFlatWord : Word S.toGeometricStepSystem a b → FlatWord Step) :=
    continuous_induced_dom
  have hn : Continuous (fun w : Word S.toGeometricStepSystem a b => w.length) := by
    exact continuous_flatWordLength.comp hw
  have hcoords : Continuous (coordinates : Word S.toGeometricStepSystem a b → _) :=
    hn.prodMk (continuous_tuple_flatRealize (S := S) a b)
  have hfull := hw.prodMk hcoords
  have hi : Topology.IsInducing (toFlatWord : Word S.toGeometricStepSystem a b → FlatWord Step) := ⟨rfl⟩
  have h : Topology.IsInducing (fun w : Word S.toGeometricStepSystem a b =>
      (w.toFlatWord, coordinates w)) := Topology.IsInducing.of_comp hfull continuous_fst hi
  exact h.eq_induced.symm

end Word

namespace TotalWord

/-- Repackage endpoint indices without changing the literal word or basepoint. -/
def strataEquiv : TotalWord S ≃ Strata.TotalWord S where
  toFun w := ⟨w.src, w.tgt, w.word⟩
  invFun w := ⟨w.1, w.2.1, w.2.2⟩
  left_inv w := by cases w; rfl
  right_inv w := by rcases w with ⟨a, b, w⟩; rfl

/-- Transport of the genuine coproduct of compatible finite-tuple subspaces. -/
@[reducible] noncomputable def coproductTopology : TopologicalSpace (TotalWord S) :=
  @TopologicalSpace.induced _ _ (strataEquiv (S := S)) (Strata.totalWordTopology S)

def fullCode (w : TotalWord S) : A × FlatWord Step := (w.src, w.word.toFlatWord)

theorem coproductTopology_eq_induced_code :
    coproductTopology (S := S) = TopologicalSpace.induced fullCode inferInstance := by
  rw [coproductTopology, Strata.totalWordTopology_eq_induced_code, induced_compose]
  rfl

/-- The actual literal-stratum topology gives continuous exact execution. -/
theorem continuous_coproduct_flatRealize :
    @Continuous _ _ (coproductTopology (S := S)) inferInstance
      (fun w : TotalWord S => (GeometricTrace.flatRealize w.word.toTrace).toContinuousMap) := by
  letI := coproductTopology (S := S)
  letI := Strata.totalWordTopology S
  exact (Strata.continuous_totalWord_flatRealize S).comp
    (continuous_induced_dom : Continuous (strataEquiv (S := S)))

/-- The global full-word refinement equals the genuine composable coproduct.
The source coordinate is retained at zero length. -/
theorem sensitiveTopology_eq_coproductTopology :
    sensitiveTopology (S := S) = coproductTopology (S := S) := by
  letI := coproductTopology (S := S)
  have hinit : Topology.IsInducing (fullCode : TotalWord S → A × FlatWord Step) := ⟨coproductTopology_eq_induced_code⟩
  have hw := hinit.continuous
  have hs : Continuous (fun w : TotalWord S => w.src) := hw.fst
  have hword : Continuous (fun w : TotalWord S => w.word.toFlatWord) := hw.snd
  have hn : Continuous (fun w : TotalWord S => w.word.length) :=
    continuous_flatWordLength.comp hword
  have hpath := continuous_coproduct_flatRealize (S := S)
  have ht : Continuous (fun w : TotalWord S => w.tgt) := by
    have h := (continuous_eval_const (1 : unitInterval)).comp hpath
    simpa [Function.comp_def] using h
  have hobs : Continuous (observation : TotalWord S → Observation (A := A)) :=
    hs.prodMk (ht.prodMk (hn.prodMk hpath))
  have hfull := hword.prodMk hobs
  have hi : Topology.IsInducing (fullCode : TotalWord S → A × FlatWord Step) := by
    constructor
    exact coproductTopology_eq_induced_code
  have h : Topology.IsInducing (fun w : TotalWord S => (w.word.toFlatWord, observation w)) :=
    Topology.IsInducing.of_comp hfull (continuous_snd.fst.prodMk continuous_fst) hi
  exact h.eq_induced.symm

/-- Explicit homeomorphism from the manuscript's genuine finite-word coproduct
onto the implemented global literal-word carrier. -/
noncomputable def coproductHomeomorph :
    @Homeomorph (Strata.Total S) (TotalWord S) inferInstance (sensitiveTopology (S := S)) := by
  letI := Strata.totalWordTopology S
  letI := coproductTopology (S := S)
  have hpack : @Homeomorph (TotalWord S) (Strata.TotalWord S)
      (coproductTopology (S := S)) (Strata.totalWordTopology S) := by
    refine
      { toEquiv := strataEquiv
        continuous_toFun := continuous_induced_dom
        continuous_invFun := ?_ }
    apply continuous_induced_rng.mpr
    simpa using (continuous_id : Continuous (id : Strata.TotalWord S → Strata.TotalWord S))
  rw [sensitiveTopology_eq_coproductTopology]
  exact (Strata.totalWordHomeomorph S).trans hpack.symm

end TotalWord
namespace WordRwEq

/-- Fixed-endpoint tree/word comparison with the literal finite-tuple topology. -/
noncomputable def tupleQuotientHomeomorph (P : ScopedGeometricRewritePresentation S) (a b : A) :
    @Homeomorph (Quotient (CoherentRepresentativeElimination.traceSetoid P a b))
      (Quotient (setoid P a b))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (CoherentRepresentativeElimination.traceSetoid P a b)
        (EqualSlotTopology.traceSensitiveTopology (S := S.toGeometricStepSystem) a b))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (setoid P a b) (Word.tupleTopology (S := S) a b)) := by
  rw [← Word.sensitiveTopology_eq_tupleTopology]
  exact sensitiveQuotientHomeomorph P a b

end WordRwEq

namespace TotalWord

/-- Global coherent/tree quotient comparison with genuine literal-word strata. -/
noncomputable def coproductQuotientHomeomorph (P : ScopedGeometricRewritePresentation S) :
    @Homeomorph (ScopedClass P) (Quotient (setoid P))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (scopedSetoid P) (EqualSlotTopology.totalSensitiveTopology S))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (setoid P) (coproductTopology (S := S))) := by
  rw [← sensitiveTopology_eq_coproductTopology]
  exact sensitiveQuotientHomeomorph P

end TotalWord

namespace WordPair

/-- Matching final pair domains agree for genuine literal-word strata. -/
noncomputable def coproductQuotientHomeomorph (P : ScopedGeometricRewritePresentation S) :
    @Homeomorph (Quotient (rawSetoid P)) (Quotient (wordSetoid P))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (rawSetoid P) (rawTopology (EqualSlotTopology.totalSensitiveTopology S)))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (wordSetoid P) (wordTopology (TotalWord.coproductTopology (S := S)))) := by
  rw [← TotalWord.sensitiveTopology_eq_coproductTopology]
  exact sensitiveQuotientHomeomorph P

end WordPair

end ComputationalPaths.Path.GeometricTopology.LiteralWord
