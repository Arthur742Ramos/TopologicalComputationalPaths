import ComputationalPaths.Path.Topology.LiteralWordQuotient

/-!
# Global literal-word quotient comparison

Empty words retain their basepoint. Endpoints vary in the ambient space rather
than being given a disjoint-union topology. The observable code uses the exact
equal-slot realization; the full-word refinement adds the signed tuple.
-/

namespace ComputationalPaths.Path.GeometricTopology.LiteralWord

open scoped Topology ContinuousMap
universe u v

variable {A : Type u} [TopologicalSpace A] {Step : Type v} [TopologicalSpace Step]
  {S : ContinuousGeometricStepSystem A Step}

structure TotalWord (S : ContinuousGeometricStepSystem A Step) where
  src : A
  tgt : A
  word : Word S.toGeometricStepSystem src tgt

namespace TotalWord

noncomputable def castWord {p q : TotalWord S} (hs : q.src = p.src) (ht : q.tgt = p.tgt) :
    Word S.toGeometricStepSystem q.src q.tgt := hs.symm ▸ ht.symm ▸ p.word

def equivalent (P : ScopedGeometricRewritePresentation S) (p q : TotalWord S) : Prop :=
  ∃ hs : q.src = p.src, ∃ ht : q.tgt = p.tgt, WordRwEq P (castWord hs ht) q.word

noncomputable def setoid (P : ScopedGeometricRewritePresentation S) : Setoid (TotalWord S) where
  r := equivalent P
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact ⟨rfl, rfl, WordRwEq.refl p.word⟩
    · intro p q h
      rcases p with ⟨a, b, p⟩
      rcases q with ⟨c, d, q⟩
      rcases h with ⟨hs, ht, h⟩
      cases hs
      cases ht
      exact ⟨rfl, rfl, h.symm⟩
    · intro p q r h₁ h₂
      rcases p with ⟨a, b, p⟩
      rcases q with ⟨c, d, q⟩
      rcases r with ⟨e, f, r⟩
      rcases h₁ with ⟨hs₁, ht₁, h₁⟩
      rcases h₂ with ⟨hs₂, ht₂, h₂⟩
      cases hs₁
      cases ht₁
      cases hs₂
      cases ht₂
      exact ⟨rfl, rfl, h₁.trans h₂⟩

/-- Flatten the trace while retaining both endpoints and the empty basepoint. -/
def ofRaw (p : ScopedRawPath (S := S)) : TotalWord S :=
  ⟨p.src, p.tgt, Word.ofTrace p.trace⟩

/-- Reconstruct using the canonical equal-slot coherent representative. -/
noncomputable def toRaw (w : TotalWord S) : ScopedRawPath (S := S) :=
  ⟨w.src, w.tgt, EqualSlotTopology.canonicalSection w.word.toTrace⟩

@[simp] theorem ofRaw_toRaw (w : TotalWord S) : ofRaw w.toRaw = w := by
  cases w with
  | mk a b w => simp only [ofRaw, toRaw, TotalOpenGeometricCompPath.trace,
      EqualSlotTopology.canonicalSection, Word.ofTrace_toTrace]

theorem toRaw_ofRaw_equivalent (P : ScopedGeometricRewritePresentation S)
    (p : ScopedRawPath (S := S)) : scopedEquivalent P (ofRaw p).toRaw p :=
  ⟨rfl, rfl, (Word.normalization P p.trace).symm⟩

theorem ofRaw_equivalent (P : ScopedGeometricRewritePresentation S)
    {p q : ScopedRawPath (S := S)} (h : scopedEquivalent P p q) :
    equivalent P (ofRaw p) (ofRaw q) := by
  rcases p with ⟨a, b, p⟩
  rcases q with ⟨c, d, q⟩
  rcases h with ⟨hs, ht, h⟩
  cases hs
  cases ht
  exact ⟨rfl, rfl, WordRwEq.ofTrace P h⟩

theorem toRaw_equivalent (P : ScopedGeometricRewritePresentation S)
    {p q : TotalWord S} (h : equivalent P p q) :
    scopedEquivalent P p.toRaw q.toRaw := by
  rcases p with ⟨a, b, p⟩
  rcases q with ⟨c, d, q⟩
  rcases h with ⟨hs, ht, h⟩
  cases hs
  cases ht
  exact ⟨rfl, rfl, WordRwEq.toTrace P h⟩

abbrev Observation := A × (A × (Nat × C(unitInterval, A)))

noncomputable def observation (w : TotalWord S) : Observation (A := A) :=
  (w.src, (w.tgt, (w.word.length, (GeometricTrace.flatRealize w.word.toTrace).toContinuousMap)))

@[reducible] noncomputable def observableTopology : TopologicalSpace (TotalWord S) :=
  TopologicalSpace.induced observation inferInstance

@[reducible] noncomputable def sensitiveTopology : TopologicalSpace (TotalWord S) :=
  TopologicalSpace.induced (fun w : TotalWord S => (w.word.toFlatWord, observation w)) inferInstance

theorem continuous_observable_ofRaw :
    @Continuous _ _ (EqualSlotTopology.totalObservableTopology S)
      (observableTopology (S := S)) ofRaw := by
  letI := EqualSlotTopology.totalObservableTopology S
  apply continuous_induced_rng.mpr
  have h := EqualSlotTopology.continuous_totalObservation S
  have h' := h.fst.prodMk (h.snd.fst.prodMk (h.snd.snd.fst.prodMk h.snd.snd.snd.fst))
  simpa only [Function.comp_def, observation, ofRaw,
    Word.ofTrace_length, Word.flatRealize_ofTrace, EqualSlotTopology.totalObservation] using h'

theorem continuous_observable_toRaw :
    @Continuous _ _ (observableTopology (S := S))
      (EqualSlotTopology.totalObservableTopology S) toRaw := by
  letI := observableTopology (S := S)
  apply continuous_induced_rng.mpr
  have h : @Continuous _ _ (observableTopology (S := S)) inferInstance observation :=
    continuous_induced_dom
  have h' := h.fst.prodMk (h.snd.fst.prodMk
    (h.snd.snd.fst.prodMk (h.snd.snd.snd.prodMk h.snd.snd.snd)))
  simpa only [Function.comp_def, EqualSlotTopology.totalObservation, toRaw,
    EqualSlotTopology.canonicalSection, TotalOpenGeometricCompPath.trace,
    Word.toTrace_length, observation] using h'

theorem continuous_sensitive_ofRaw :
    @Continuous _ _ (EqualSlotTopology.totalSensitiveTopology S)
      (sensitiveTopology (S := S)) ofRaw := by
  letI := EqualSlotTopology.totalSensitiveTopology S
  apply continuous_induced_rng.mpr
  have h : @Continuous _ _ (EqualSlotTopology.totalSensitiveTopology S) inferInstance
      (fun p : ScopedRawPath (S := S) =>
        (GeometricTrace.flatWord p.trace, EqualSlotTopology.totalObservation S p)) :=
    continuous_induced_dom
  have hobs := h.snd
  have h' := h.fst.prodMk (hobs.fst.prodMk
    (hobs.snd.fst.prodMk (hobs.snd.snd.fst.prodMk hobs.snd.snd.snd.fst)))
  simpa only [Function.comp_def, observation, ofRaw, Word.toFlatWord_ofTrace,
    Word.ofTrace_length, Word.flatRealize_ofTrace, EqualSlotTopology.totalObservation] using h'

theorem continuous_sensitive_toRaw :
    @Continuous _ _ (sensitiveTopology (S := S))
      (EqualSlotTopology.totalSensitiveTopology S) toRaw := by
  letI := sensitiveTopology (S := S)
  apply continuous_induced_rng.mpr
  have h : @Continuous _ _ (sensitiveTopology (S := S)) inferInstance
      (fun w : TotalWord S => (w.word.toFlatWord, observation w)) := continuous_induced_dom
  have hobs := h.snd
  have h' := h.fst.prodMk (hobs.fst.prodMk (hobs.snd.fst.prodMk
    (hobs.snd.snd.fst.prodMk (hobs.snd.snd.snd.prodMk hobs.snd.snd.snd))))
  simpa only [Function.comp_def, EqualSlotTopology.totalObservation, toRaw,
    EqualSlotTopology.canonicalSection, TotalOpenGeometricCompPath.trace,
    Word.toTrace_length, Word.flatWord_toTrace, observation] using h'

noncomputable def quotientEquiv (P : ScopedGeometricRewritePresentation S) :
    ScopedClass P ≃ Quotient (setoid P) where
  toFun := Quotient.map ofRaw (fun _ _ h => ofRaw_equivalent P h)
  invFun := Quotient.map toRaw (fun _ _ h => toRaw_equivalent P h)
  left_inv x := by
    refine Quotient.inductionOn x ?_
    intro p
    exact Quotient.sound (toRaw_ofRaw_equivalent P p)
  right_inv x := by
    refine Quotient.inductionOn x ?_
    intro w
    simp only [Quotient.map_mk, ofRaw_toRaw]

/-- Eliminate coherent representatives and tree parentheses globally, using
matching equal-slot observations and independently generated word rewriting. -/
noncomputable def observableQuotientHomeomorph (P : ScopedGeometricRewritePresentation S) :
    @Homeomorph (ScopedClass P) (Quotient (setoid P))
      (EqualSlotTopology.totalQuotientTopology P)
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (setoid P) (observableTopology (S := S))) := by
  letI := EqualSlotTopology.totalObservableTopology S
  letI := observableTopology (S := S)
  letI := EqualSlotTopology.totalQuotientTopology P
  letI := TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (setoid P) (observableTopology (S := S))
  refine { toEquiv := quotientEquiv P, continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientMk_isQuotient
      (scopedSetoid P) (EqualSlotTopology.totalObservableTopology S)).continuous_iff.2
    exact continuous_coinduced_rng.comp continuous_observable_ofRaw
  · apply (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientMk_isQuotient
      (setoid P) (observableTopology (S := S))).continuous_iff.2
    exact continuous_coinduced_rng.comp continuous_observable_toRaw

/-- The global full-word refinement has the same reconstructed word quotient.
Its identification with genuine composable-word strata is established separately. -/
noncomputable def sensitiveQuotientHomeomorph (P : ScopedGeometricRewritePresentation S) :
    @Homeomorph (ScopedClass P) (Quotient (setoid P))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (scopedSetoid P) (EqualSlotTopology.totalSensitiveTopology S))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (setoid P) (sensitiveTopology (S := S))) := by
  letI := EqualSlotTopology.totalSensitiveTopology S
  letI := sensitiveTopology (S := S)
  letI := TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (scopedSetoid P) (EqualSlotTopology.totalSensitiveTopology S)
  letI := TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (setoid P) (sensitiveTopology (S := S))
  refine { toEquiv := quotientEquiv P, continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientMk_isQuotient
      (scopedSetoid P) (EqualSlotTopology.totalSensitiveTopology S)).continuous_iff.2
    exact continuous_coinduced_rng.comp continuous_sensitive_ofRaw
  · apply (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientMk_isQuotient
      (setoid P) (sensitiveTopology (S := S))).continuous_iff.2
    exact continuous_coinduced_rng.comp continuous_sensitive_toRaw

end TotalWord
end ComputationalPaths.Path.GeometricTopology.LiteralWord
