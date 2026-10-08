import ComputationalPaths.Path.Topology.LiteralWordGlobal

/-!
# Final composable-pair comparison for equal-slot words

Each final domain is the quotient of the actual composable-representative
subspace of a product. Continuity follows on representatives before quotienting;
no quotient-product stability or ordinary-pair topology is assumed.
-/

namespace ComputationalPaths.Path.GeometricTopology.LiteralWord

open scoped Topology
universe u v

variable {A : Type u} [TopologicalSpace A] {Step : Type v} [TopologicalSpace Step]
  {S : ContinuousGeometricStepSystem A Step}

namespace WordPair

abbrev Raw := {pq : ScopedRawPath (S := S) × ScopedRawPath (S := S) // pq.1.tgt = pq.2.src}
abbrev Words := {pq : TotalWord S × TotalWord S // pq.1.tgt = pq.2.src}

noncomputable def rawSetoid (P : ScopedGeometricRewritePresentation S) : Setoid (Raw (S := S)) :=
  Setoid.comap Subtype.val ((scopedSetoid P).prod (scopedSetoid P))

noncomputable def wordSetoid (P : ScopedGeometricRewritePresentation S) : Setoid (Words (S := S)) :=
  Setoid.comap Subtype.val ((TotalWord.setoid P).prod (TotalWord.setoid P))

def ofRaw (p : Raw (S := S)) : Words (S := S) :=
  ⟨(TotalWord.ofRaw p.1.1, TotalWord.ofRaw p.1.2), p.2⟩

noncomputable def toRaw (p : Words (S := S)) : Raw (S := S) :=
  ⟨(TotalWord.toRaw p.1.1, TotalWord.toRaw p.1.2), p.2⟩

@[simp] theorem ofRaw_toRaw (p : Words (S := S)) : ofRaw (toRaw p) = p := by
  apply Subtype.ext
  exact Prod.ext (TotalWord.ofRaw_toRaw _) (TotalWord.ofRaw_toRaw _)

/-- Product/subspace topology on the composable representative domain. -/
@[reducible] noncomputable def rawTopology
    (τ : TopologicalSpace (ScopedRawPath (S := S))) : TopologicalSpace (Raw (S := S)) :=
  @TopologicalSpace.induced _ _ Subtype.val (@instTopologicalSpaceProd _ _ τ τ)

@[reducible] noncomputable def wordTopology
    (ω : TopologicalSpace (TotalWord S)) : TopologicalSpace (Words (S := S)) :=
  @TopologicalSpace.induced _ _ Subtype.val (@instTopologicalSpaceProd _ _ ω ω)

theorem continuous_ofRaw
    (τ : TopologicalSpace (ScopedRawPath (S := S)))
    (ω : TopologicalSpace (TotalWord S))
    (h : @Continuous _ _ τ ω TotalWord.ofRaw) :
    @Continuous _ _ (rawTopology τ) (wordTopology ω) ofRaw := by
  letI := τ
  letI := ω
  letI := rawTopology τ
  letI := wordTopology ω
  apply continuous_induced_rng.mpr
  exact (h.comp (continuous_fst.comp continuous_subtype_val)).prodMk
    (h.comp (continuous_snd.comp continuous_subtype_val))

theorem continuous_toRaw
    (τ : TopologicalSpace (ScopedRawPath (S := S)))
    (ω : TopologicalSpace (TotalWord S))
    (h : @Continuous _ _ ω τ TotalWord.toRaw) :
    @Continuous _ _ (wordTopology ω) (rawTopology τ) toRaw := by
  letI := τ
  letI := ω
  letI := rawTopology τ
  letI := wordTopology ω
  apply continuous_induced_rng.mpr
  exact (h.comp (continuous_fst.comp continuous_subtype_val)).prodMk
    (h.comp (continuous_snd.comp continuous_subtype_val))

noncomputable def quotientEquiv (P : ScopedGeometricRewritePresentation S) :
    Quotient (rawSetoid P) ≃ Quotient (wordSetoid P) where
  toFun := Quotient.map ofRaw (fun _ _ h =>
    ⟨TotalWord.ofRaw_equivalent P h.1, TotalWord.ofRaw_equivalent P h.2⟩)
  invFun := Quotient.map toRaw (fun _ _ h =>
    ⟨TotalWord.toRaw_equivalent P h.1, TotalWord.toRaw_equivalent P h.2⟩)
  left_inv x := by
    refine Quotient.inductionOn x ?_
    intro p
    exact Quotient.sound
      ⟨TotalWord.toRaw_ofRaw_equivalent P p.1.1, TotalWord.toRaw_ofRaw_equivalent P p.1.2⟩
  right_inv x := by
    refine Quotient.inductionOn x ?_
    intro p
    simp only [Quotient.map_mk, ofRaw_toRaw]

/-- Both quotient continuities are obtained on composable representatives. -/
noncomputable def quotientHomeomorph (P : ScopedGeometricRewritePresentation S)
    (τ : TopologicalSpace (ScopedRawPath (S := S)))
    (ω : TopologicalSpace (TotalWord S))
    (hf : @Continuous _ _ τ ω TotalWord.ofRaw)
    (hr : @Continuous _ _ ω τ TotalWord.toRaw) :
    @Homeomorph (Quotient (rawSetoid P)) (Quotient (wordSetoid P))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (rawSetoid P) (rawTopology τ))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (wordSetoid P) (wordTopology ω)) := by
  letI := τ
  letI := ω
  letI := rawTopology τ
  letI := wordTopology ω
  letI := TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (rawSetoid P) (rawTopology τ)
  letI := TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (wordSetoid P) (wordTopology ω)
  refine { toEquiv := quotientEquiv P, continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientMk_isQuotient
      (rawSetoid P) (rawTopology τ)).continuous_iff.2
    exact continuous_coinduced_rng.comp (continuous_ofRaw τ ω hf)
  · apply (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientMk_isQuotient
      (wordSetoid P) (wordTopology ω)).continuous_iff.2
    exact continuous_coinduced_rng.comp (continuous_toRaw τ ω hr)

/-- Observable final composable-pair domains agree under canonical flattening. -/
noncomputable def observableQuotientHomeomorph (P : ScopedGeometricRewritePresentation S) :=
  quotientHomeomorph P (EqualSlotTopology.totalObservableTopology S)
    (TotalWord.observableTopology (S := S))
    TotalWord.continuous_observable_ofRaw TotalWord.continuous_observable_toRaw

/-- Full-word final composable-pair domains agree under canonical flattening. -/
noncomputable def sensitiveQuotientHomeomorph (P : ScopedGeometricRewritePresentation S) :=
  quotientHomeomorph P (EqualSlotTopology.totalSensitiveTopology S)
    (TotalWord.sensitiveTopology (S := S))
    TotalWord.continuous_sensitive_ofRaw TotalWord.continuous_sensitive_toRaw

end WordPair
end ComputationalPaths.Path.GeometricTopology.LiteralWord
