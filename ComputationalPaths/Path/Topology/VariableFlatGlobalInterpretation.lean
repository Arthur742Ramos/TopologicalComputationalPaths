import ComputationalPaths.Path.Topology.VariableFlatWordInterpretation
import ComputationalPaths.Path.Topology.LiteralWordPairs

/-!
# Global and final-pair invariance under variable-length interpretation

Representative maps preserve endpoints and choose the equal-slot execution of
the substituted trace. Their continuity is derived from primitive word-code
continuity and execution on genuine finite word strata. Inverse laws follow
from the primitive roundtrip rewrites. Final pair domains use the quotient of
composable representatives, without an ordinary-product quotient assumption.
-/

namespace ComputationalPaths.Path.GeometricTopology.ScopedWordInterpretation

open scoped Topology
universe u v w
variable {A : Type u} [TopologicalSpace A] {Step : Type v} [TopologicalSpace Step]
  {Step' : Type w} [TopologicalSpace Step']
  {S : ContinuousGeometricStepSystem A Step} {T : ContinuousGeometricStepSystem A Step'}
  {P : ScopedGeometricRewritePresentation S} {Q : ScopedGeometricRewritePresentation T}

noncomputable def mapRaw (M : ScopedWordInterpretation P Q)
    (p : ScopedRawPath (S := S)) : ScopedRawPath (S := T) :=
  ⟨p.src, p.tgt, EqualSlotTopology.canonicalSection (M.substitution.mapTrace p.trace)⟩

theorem mapRaw_equivalent (M : ScopedWordInterpretation P Q)
    {p q : ScopedRawPath (S := S)} (h : scopedEquivalent P p q) :
    scopedEquivalent Q (M.mapRaw p) (M.mapRaw q) := by
  rcases p with ⟨a, b, p⟩
  rcases q with ⟨c, d, q⟩
  rcases h with ⟨hs, ht, h⟩
  cases hs
  cases ht
  exact ⟨rfl, rfl, M.map_scoped h⟩

/-- Global representative continuity follows from the actual primitive codes. -/
theorem continuous_flatSensitive_mapRaw (M : ScopedWordInterpretation P Q)
    (hprimitive : Continuous (FlatWordSubstitution.primitiveWord M.substitution)) :
    @Continuous _ _ (EqualSlotTopology.totalSensitiveTopology S)
      (EqualSlotTopology.totalSensitiveTopology T) M.mapRaw := by
  letI := EqualSlotTopology.totalSensitiveTopology S
  have hcode : Continuous (fun p : ScopedRawPath (S := S) =>
      (GeometricTrace.flatWord p.trace, EqualSlotTopology.totalObservation S p)) := continuous_induced_dom
  have hs : Continuous (fun p : ScopedRawPath (S := S) => p.src) := hcode.snd.fst
  have ht : Continuous (fun p : ScopedRawPath (S := S) => p.tgt) := hcode.snd.snd.fst
  have hword : Continuous (fun p : ScopedRawPath (S := S) =>
      GeometricTrace.flatWord (M.substitution.mapTrace p.trace)) := by
    simpa only [Function.comp_def, FlatWordSubstitution.mapTrace_flatWord] using
      (FlatWordSubstitution.continuous_substitution M.substitution hprimitive).comp hcode.fst
  have hlength : Continuous (fun p : ScopedRawPath (S := S) =>
      GeometricTrace.traceLength (M.substitution.mapTrace p.trace)) := by
    simpa only [Function.comp_def, GeometricTrace.flatWord_length] using
      continuous_flatWordLength.comp hword
  have hmap := LiteralWord.Strata.continuous_flatRealize_of_flatWord T
    (fun p : ScopedRawPath (S := S) => p.src) (fun p : ScopedRawPath (S := S) => p.tgt)
    (fun p => M.substitution.mapTrace p.trace) hs ht hword
  apply continuous_induced_rng.mpr
  simpa only [Function.comp_def, mapRaw, TotalOpenGeometricCompPath.trace,
    EqualSlotTopology.canonicalSection, EqualSlotTopology.totalObservation] using
    hword.prodMk (hs.prodMk (ht.prodMk (hlength.prodMk (hmap.prodMk hmap))))

noncomputable def globalQuotientMap (M : ScopedWordInterpretation P Q) : ScopedClass P → ScopedClass Q :=
  Quotient.map M.mapRaw (fun _ _ h => M.mapRaw_equivalent h)

theorem continuous_flatSensitive_globalQuotientMap (M : ScopedWordInterpretation P Q)
    (hprimitive : Continuous (FlatWordSubstitution.primitiveWord M.substitution)) :
    @Continuous _ _
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (scopedSetoid P) (EqualSlotTopology.totalSensitiveTopology S))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (scopedSetoid Q) (EqualSlotTopology.totalSensitiveTopology T)) M.globalQuotientMap := by
  letI := EqualSlotTopology.totalSensitiveTopology S
  letI := EqualSlotTopology.totalSensitiveTopology T
  letI := TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (scopedSetoid P) (EqualSlotTopology.totalSensitiveTopology S)
  letI := TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (scopedSetoid Q) (EqualSlotTopology.totalSensitiveTopology T)
  apply (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientMk_isQuotient
    (scopedSetoid P) (EqualSlotTopology.totalSensitiveTopology S)).continuous_iff.2
  have hq : @Continuous _ _ (EqualSlotTopology.totalSensitiveTopology T)
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (scopedSetoid Q) (EqualSlotTopology.totalSensitiveTopology T))
      (@Quotient.mk' _ (scopedSetoid Q)) := continuous_coinduced_rng
  exact @Continuous.comp _ _ _ (EqualSlotTopology.totalSensitiveTopology S)
    (EqualSlotTopology.totalSensitiveTopology T)
    (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
      (scopedSetoid Q) (EqualSlotTopology.totalSensitiveTopology T))
    _ _ hq (M.continuous_flatSensitive_mapRaw hprimitive)

/-- Global presentation equivalence is derived from primitive rewrites and
primitive-code continuity in both directions. -/
noncomputable def flatSensitiveGlobalHomeomorph
    (M : ScopedWordInterpretation P Q) (N : ScopedWordInterpretation Q P)
    (hS : ∀ s : Step, ScopedRwEq P (N.substitution.mapTrace (M.substitution.step s))
      (GeometricTrace.single s))
    (hT : ∀ t : Step', ScopedRwEq Q (M.substitution.mapTrace (N.substitution.step t))
      (GeometricTrace.single t))
    (hM : Continuous (FlatWordSubstitution.primitiveWord M.substitution))
    (hN : Continuous (FlatWordSubstitution.primitiveWord N.substitution)) :
    @Homeomorph (ScopedClass P) (ScopedClass Q)
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (scopedSetoid P) (EqualSlotTopology.totalSensitiveTopology S))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (scopedSetoid Q) (EqualSlotTopology.totalSensitiveTopology T)) := by
  letI := (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology (scopedSetoid P) (EqualSlotTopology.totalSensitiveTopology S))
  letI := (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology (scopedSetoid Q) (EqualSlotTopology.totalSensitiveTopology T))
  exact {
    toFun := M.globalQuotientMap
    invFun := N.globalQuotientMap
    left_inv x := by
      refine Quotient.inductionOn x ?_
      intro p
      exact Quotient.sound ⟨rfl, rfl, M.roundtrip N hS p.trace⟩
    right_inv x := by
      refine Quotient.inductionOn x ?_
      intro p
      exact Quotient.sound ⟨rfl, rfl, N.roundtrip M hT p.trace⟩
    continuous_toFun := M.continuous_flatSensitive_globalQuotientMap hM
    continuous_invFun := N.continuous_flatSensitive_globalQuotientMap hN }

noncomputable def mapRawPair (M : ScopedWordInterpretation P Q)
    (p : LiteralWord.WordPair.Raw (S := S)) : LiteralWord.WordPair.Raw (S := T) :=
  ⟨(M.mapRaw p.1.1, M.mapRaw p.1.2), p.2⟩

theorem continuous_flatSensitive_mapRawPair (M : ScopedWordInterpretation P Q)
    (hprimitive : Continuous (FlatWordSubstitution.primitiveWord M.substitution)) :
    @Continuous _ _
      (LiteralWord.WordPair.rawTopology (EqualSlotTopology.totalSensitiveTopology S))
      (LiteralWord.WordPair.rawTopology (EqualSlotTopology.totalSensitiveTopology T)) M.mapRawPair := by
  letI := EqualSlotTopology.totalSensitiveTopology S
  letI := EqualSlotTopology.totalSensitiveTopology T
  letI := LiteralWord.WordPair.rawTopology (EqualSlotTopology.totalSensitiveTopology S)
  letI := LiteralWord.WordPair.rawTopology (EqualSlotTopology.totalSensitiveTopology T)
  have h := M.continuous_flatSensitive_mapRaw hprimitive
  apply continuous_induced_rng.mpr
  exact (h.comp (continuous_fst.comp continuous_subtype_val)).prodMk
    (h.comp (continuous_snd.comp continuous_subtype_val))

noncomputable def finalPairMap (M : ScopedWordInterpretation P Q) :
    Quotient (LiteralWord.WordPair.rawSetoid P) → Quotient (LiteralWord.WordPair.rawSetoid Q) :=
  Quotient.map M.mapRawPair (fun _ _ h => ⟨M.mapRaw_equivalent h.1, M.mapRaw_equivalent h.2⟩)

/-- The two endpoint-matched arrow projections from the final domain. -/
noncomputable def finalLeft (P : ScopedGeometricRewritePresentation S) :
    Quotient (LiteralWord.WordPair.rawSetoid P) → ScopedClass P :=
  Quotient.lift (fun p => scopedQuotientMk P p.1.1) (fun _ _ h => Quotient.sound h.1)

noncomputable def finalRight (P : ScopedGeometricRewritePresentation S) :
    Quotient (LiteralWord.WordPair.rawSetoid P) → ScopedClass P :=
  Quotient.lift (fun p => scopedQuotientMk P p.1.2) (fun _ _ h => Quotient.sound h.2)

/-- Final pair transport commutes with the first arrow comparison. -/
theorem finalPairMap_left (M : ScopedWordInterpretation P Q)
    (p : Quotient (LiteralWord.WordPair.rawSetoid P)) :
    finalLeft Q (M.finalPairMap p) = M.globalQuotientMap (finalLeft P p) := by
  refine Quotient.inductionOn p ?_
  intro p
  rfl

/-- Final pair transport commutes with the second arrow comparison. -/
theorem finalPairMap_right (M : ScopedWordInterpretation P Q)
    (p : Quotient (LiteralWord.WordPair.rawSetoid P)) :
    finalRight Q (M.finalPairMap p) = M.globalQuotientMap (finalRight P p) := by
  refine Quotient.inductionOn p ?_
  intro p
  rfl

theorem continuous_flatSensitive_finalPairMap (M : ScopedWordInterpretation P Q)
    (hprimitive : Continuous (FlatWordSubstitution.primitiveWord M.substitution)) :
    @Continuous _ _
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (LiteralWord.WordPair.rawSetoid P)
        (LiteralWord.WordPair.rawTopology (EqualSlotTopology.totalSensitiveTopology S)))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (LiteralWord.WordPair.rawSetoid Q)
        (LiteralWord.WordPair.rawTopology (EqualSlotTopology.totalSensitiveTopology T))) M.finalPairMap := by
  letI := LiteralWord.WordPair.rawTopology (EqualSlotTopology.totalSensitiveTopology S)
  letI := LiteralWord.WordPair.rawTopology (EqualSlotTopology.totalSensitiveTopology T)
  letI := TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (LiteralWord.WordPair.rawSetoid P)
    (LiteralWord.WordPair.rawTopology (EqualSlotTopology.totalSensitiveTopology S))
  letI := TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (LiteralWord.WordPair.rawSetoid Q)
    (LiteralWord.WordPair.rawTopology (EqualSlotTopology.totalSensitiveTopology T))
  apply (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientMk_isQuotient
    (LiteralWord.WordPair.rawSetoid P)
    (LiteralWord.WordPair.rawTopology (EqualSlotTopology.totalSensitiveTopology S))).continuous_iff.2
  have hq : @Continuous _ _
      (LiteralWord.WordPair.rawTopology (EqualSlotTopology.totalSensitiveTopology T))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (LiteralWord.WordPair.rawSetoid Q)
        (LiteralWord.WordPair.rawTopology (EqualSlotTopology.totalSensitiveTopology T)))
      (@Quotient.mk' _ (LiteralWord.WordPair.rawSetoid Q)) := continuous_coinduced_rng
  exact @Continuous.comp _ _ _
    (LiteralWord.WordPair.rawTopology (EqualSlotTopology.totalSensitiveTopology S))
    (LiteralWord.WordPair.rawTopology (EqualSlotTopology.totalSensitiveTopology T))
    (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
      (LiteralWord.WordPair.rawSetoid Q)
      (LiteralWord.WordPair.rawTopology (EqualSlotTopology.totalSensitiveTopology T)))
    _ _ hq (M.continuous_flatSensitive_mapRawPair hprimitive)

/-- Compatible homeomorphisms of final composable-pair domains are obtained
without assuming products of arrow quotient maps are quotient. -/
noncomputable def flatSensitiveFinalPairHomeomorph
    (M : ScopedWordInterpretation P Q) (N : ScopedWordInterpretation Q P)
    (hS : ∀ s : Step, ScopedRwEq P (N.substitution.mapTrace (M.substitution.step s))
      (GeometricTrace.single s))
    (hT : ∀ t : Step', ScopedRwEq Q (M.substitution.mapTrace (N.substitution.step t))
      (GeometricTrace.single t))
    (hM : Continuous (FlatWordSubstitution.primitiveWord M.substitution))
    (hN : Continuous (FlatWordSubstitution.primitiveWord N.substitution)) :
    @Homeomorph (Quotient (LiteralWord.WordPair.rawSetoid P))
      (Quotient (LiteralWord.WordPair.rawSetoid Q))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (LiteralWord.WordPair.rawSetoid P)
        (LiteralWord.WordPair.rawTopology (EqualSlotTopology.totalSensitiveTopology S)))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (LiteralWord.WordPair.rawSetoid Q)
        (LiteralWord.WordPair.rawTopology (EqualSlotTopology.totalSensitiveTopology T))) := by
  letI := (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology (LiteralWord.WordPair.rawSetoid P) (LiteralWord.WordPair.rawTopology (EqualSlotTopology.totalSensitiveTopology S)))
  letI := (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology (LiteralWord.WordPair.rawSetoid Q) (LiteralWord.WordPair.rawTopology (EqualSlotTopology.totalSensitiveTopology T)))
  exact {
    toFun := M.finalPairMap
    invFun := N.finalPairMap
    left_inv x := by
      refine Quotient.inductionOn x ?_
      intro p
      exact Quotient.sound
        ⟨⟨rfl, rfl, M.roundtrip N hS p.1.1.trace⟩, ⟨rfl, rfl, M.roundtrip N hS p.1.2.trace⟩⟩
    right_inv x := by
      refine Quotient.inductionOn x ?_
      intro p
      exact Quotient.sound
        ⟨⟨rfl, rfl, N.roundtrip M hT p.1.1.trace⟩, ⟨rfl, rfl, N.roundtrip M hT p.1.2.trace⟩⟩
    continuous_toFun := M.continuous_flatSensitive_finalPairMap hM
    continuous_invFun := N.continuous_flatSensitive_finalPairMap hN }

end ComputationalPaths.Path.GeometricTopology.ScopedWordInterpretation
