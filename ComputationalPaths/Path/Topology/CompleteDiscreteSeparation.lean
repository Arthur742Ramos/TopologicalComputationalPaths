import ComputationalPaths.Path.Topology.LiteralWordDiscrete
import ComputationalPaths.Path.Topology.QuotientFundamentalGroup

/-!
# Complete presentations with discrete labels for all paths

Every continuous interval path is a primitive label, with the discrete topology
on labels. Homotopy of parallel realized traces is declared as a named rule.
For fixed endpoints, the equal-slot observable quotient recovers the ordinary
compact-open path-homotopy quotient, while the full-word quotient is discrete.
Thus geometric completeness does not force the two topologies to agree.

The separation theorem takes nondiscreteness of the ordinary based quotient as
an explicit hypothesis. No facts about the harmonic archipelago are assumed
as axioms or established here. All observation coordinates use `flatRealize`.
-/

namespace ComputationalPaths.Path.GeometricTopology.CompleteDiscreteSeparation

open scoped Topology ContinuousMap
open CoherentRepresentativeElimination
attribute [local instance] _root_.Path.Homotopic.setoid

universe u
variable (A : Type u) [TopologicalSpace A]

/-- A distinct wrapper keeps the discrete label topology separate from the
compact-open topology on the underlying path space. -/
structure Label where
  path : C(unitInterval, A)

instance : TopologicalSpace (Label A) := ⊥
instance : DiscreteTopology (Label A) := discreteTopology_bot (Label A)

noncomputable def system : ContinuousGeometricStepSystem A (Label A) where
  src s := s.path 0
  tgt s := s.path 1
  realize s := { toContinuousMap := s.path, source' := rfl, target' := rfl }
  continuous_src := continuous_of_discreteTopology
  continuous_tgt := continuous_of_discreteTopology
  continuous_realize := continuous_of_discreteTopology

/-- Completeness is built into the actual declared rule, independently of any
topological claim. -/
noncomputable def presentation : ScopedGeometricRewritePresentation (system A) where
  rule := fun {_ _} p q =>
    _root_.Path.Homotopic (GeometricTrace.realize p) (GeometricTrace.realize q)
  sound_rule := by intro _ _ _ _ h; exact h

theorem complete :
    ∀ {p q : ScopedRawPath (S := system A)},
      TotalOpenGeometricCompPath.totalEquivalent (system A) p q →
        scopedEquivalent (presentation A) p q := by
  intro p q h
  rcases p with ⟨p_src, p_tgt, p_path⟩
  rcases q with ⟨q_src, q_tgt, q_path⟩
  change TotalOpenGeometricCompPath.totalCode (system A)
      { src := p_src, tgt := p_tgt, path := p_path } =
    TotalOpenGeometricCompPath.totalCode (system A)
      { src := q_src, tgt := q_tgt, path := q_path } at h
  have hs : p_src = q_src := _root_.congrArg Sigma.fst h
  cases hs
  have hrest :
      (⟨p_tgt, Quotient.mk' p_path.geometric⟩ :
        Σ y : A, _root_.Path.Homotopic.Quotient p_src y) =
      ⟨q_tgt, Quotient.mk' q_path.geometric⟩ :=
    eq_of_heq (Sigma.ext_iff.mp h).2
  have ht : p_tgt = q_tgt := _root_.congrArg Sigma.fst hrest
  cases ht
  have hclass : Quotient.mk' p_path.geometric = Quotient.mk' q_path.geometric :=
    eq_of_heq (Sigma.ext_iff.mp hrest).2
  have hg : _root_.Path.Homotopic p_path.geometric q_path.geometric :=
    Quotient.exact hclass
  exact ⟨rfl, rfl, ScopedRwEq.generator
    (p_path.coherent.symm.trans (hg.trans q_path.coherent))⟩

abbrev Trace (a b : A) := GeometricTrace (system A).toGeometricStepSystem a b
abbrev TraceClass (x : A) := Quotient (traceSetoid (presentation A) x x)

@[reducible] noncomputable def observableTopology (x : A) :
    TopologicalSpace (TraceClass A x) :=
  TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (traceSetoid (presentation A) x x)
    (EqualSlotTopology.traceObservableTopology (S := (system A).toGeometricStepSystem) x x)

@[reducible] noncomputable def sensitiveTopology (x : A) :
    TopologicalSpace (TraceClass A x) :=
  TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (traceSetoid (presentation A) x x)
    (EqualSlotTopology.traceSensitiveTopology (S := (system A).toGeometricStepSystem) x x)

private theorem castTrace_flat {a b a' b' : A} (ha : a' = a) (hb : b' = b)
    (p : Trace A a b) :
    GeometricTrace.flatRealize
        (ContinuousGeometricStepSystemMap.castTrace (S := system A) ha hb p) =
      (GeometricTrace.flatRealize p).cast ha hb := by
  cases ha
  cases hb
  rfl

/-- One letter representing an arbitrary path, with its endpoints retained. -/
noncomputable def sectionTrace {a b : A} (γ : _root_.Path a b) : Trace A a b :=
  ContinuousGeometricStepSystemMap.castTrace (S := system A)
    γ.source.symm γ.target.symm
    (.single (⟨γ.toContinuousMap⟩ : Label A))

@[simp] theorem sectionTrace_flat {a b : A} (γ : _root_.Path a b) :
    GeometricTrace.flatRealize (sectionTrace A γ) = γ := by
  rw [sectionTrace, castTrace_flat]
  ext t
  rfl

@[simp] theorem sectionTrace_binary {a b : A} (γ : _root_.Path a b) :
    GeometricTrace.realize (sectionTrace A γ) = γ := by
  rw [sectionTrace, ContinuousGeometricStepSystemMap.castTrace_realize]
  ext t
  rfl

@[simp] theorem sectionTrace_length {a b : A} (γ : _root_.Path a b) :
    GeometricTrace.traceLength (sectionTrace A γ) = 1 := by
  rw [sectionTrace, ContinuousGeometricStepSystemMap.castTrace_length]
  rfl

/-- The map into the observation topology is continuous even though the
underlying map into the discrete label space need not be continuous. -/
theorem continuous_sectionTrace {a b : A} :
    @Continuous (_root_.Path a b) (Trace A a b) inferInstance
      (EqualSlotTopology.traceObservableTopology (S := (system A).toGeometricStepSystem) a b)
      (sectionTrace A) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun γ : _root_.Path a b =>
    (GeometricTrace.traceLength (sectionTrace A γ),
      GeometricTrace.flatRealize (sectionTrace A γ)))
  simpa only [sectionTrace_length, sectionTrace_flat, id_eq] using
    (continuous_const.prodMk (continuous_id : Continuous (id : _root_.Path a b → _root_.Path a b)))

noncomputable def toLoopQuot (x : A) : TraceClass A x → QuotientFundamentalGroup.LoopQuot A x :=
  Quotient.lift (fun p => Quotient.mk' (GeometricTrace.flatRealize p))
    (fun _ _ h => Quotient.sound (EqualSlotTopology.scoped_sound h))

noncomputable def fromLoopQuot (x : A) : QuotientFundamentalGroup.LoopQuot A x → TraceClass A x :=
  Quotient.lift (fun γ => Quotient.mk (traceSetoid (presentation A) x x) (sectionTrace A γ))
    (by
      intro γ δ h
      change _root_.Path.Homotopic γ δ at h
      apply Quotient.sound
      apply ScopedRwEq.generator
      change _root_.Path.Homotopic (GeometricTrace.realize (sectionTrace A γ))
        (GeometricTrace.realize (sectionTrace A δ))
      simpa only [sectionTrace_binary] using h)

theorem continuous_toLoopQuot (x : A) :
    @Continuous _ _ (observableTopology A x) inferInstance (toLoopQuot A x) := by
  letI := EqualSlotTopology.traceObservableTopology (S := (system A).toGeometricStepSystem) x x
  letI := observableTopology A x
  apply Continuous.quotient_lift
  exact continuous_quotient_mk'.comp
    (EqualSlotTopology.continuous_flatRealize (S := (system A).toGeometricStepSystem) x x)

theorem continuous_fromLoopQuot (x : A) :
    @Continuous _ _ inferInstance (observableTopology A x) (fromLoopQuot A x) := by
  letI := EqualSlotTopology.traceObservableTopology (S := (system A).toGeometricStepSystem) x x
  letI := observableTopology A x
  apply Continuous.quotient_lift
  exact continuous_coinduced_rng.comp (continuous_sectionTrace A)

noncomputable def observableHomeomorph (x : A) :
    @Homeomorph (TraceClass A x) (QuotientFundamentalGroup.LoopQuot A x)
      (observableTopology A x) inferInstance := by
  letI := observableTopology A x
  exact {
    toFun := toLoopQuot A x
    invFun := fromLoopQuot A x
    left_inv := by
      intro p
      refine Quotient.inductionOn p ?_
      intro p
      apply Quotient.sound
      apply ScopedRwEq.generator
      change _root_.Path.Homotopic
        (GeometricTrace.realize (sectionTrace A (GeometricTrace.flatRealize p)))
        (GeometricTrace.realize p)
      rw [sectionTrace_binary]
      exact GeometricTrace.flatRealize_homotopic_binary p
    right_inv := by
      intro q
      refine Quotient.inductionOn q ?_
      intro γ
      change Quotient.mk' (GeometricTrace.flatRealize (sectionTrace A γ)) = Quotient.mk' γ
      rw [sectionTrace_flat]
    continuous_toFun := continuous_toLoopQuot A x
    continuous_invFun := continuous_fromLoopQuot A x }

theorem sensitive_discrete (x : A) :
    @DiscreteTopology (TraceClass A x) (sensitiveTopology A x) :=
  LiteralWord.discrete_traceSensitiveQuotient (presentation A) x x

theorem continuous_comparison (x : A) :
    @Continuous (TraceClass A x) (TraceClass A x)
      (sensitiveTopology A x) (observableTopology A x) id := by
  exact @continuous_of_discreteTopology (TraceClass A x) (sensitiveTopology A x)
    (sensitive_discrete A x) (TraceClass A x) (observableTopology A x) id

/-- The canonical inverse comparison would force the ordinary fundamental
quotient to be discrete, contrary to the explicit hypothesis. -/
theorem inverse_not_continuous (x : A)
    (h : ¬DiscreteTopology (QuotientFundamentalGroup.LoopQuot A x)) :
    ¬@Continuous (TraceClass A x) (TraceClass A x)
      (observableTopology A x) (sensitiveTopology A x) id := by
  intro hc
  let f := (@Homeomorph.toEquiv _ _ (observableTopology A x) inferInstance
    (observableHomeomorph A x)).symm
  have hf : @Continuous _ _ inferInstance (observableTopology A x) f :=
    @Homeomorph.continuous_invFun _ _ (observableTopology A x) inferInstance
      (observableHomeomorph A x)
  letI := sensitiveTopology A x
  letI := sensitive_discrete A x
  have hc' : Continuous (f : QuotientFundamentalGroup.LoopQuot A x → TraceClass A x) :=
    @Continuous.comp (QuotientFundamentalGroup.LoopQuot A x) (TraceClass A x) (TraceClass A x)
      inferInstance (observableTopology A x) (sensitiveTopology A x) f id hc hf
  exact h (DiscreteTopology.of_continuous_injective hc' f.injective)

/-- The distinction is intrinsic to the two spaces, not only to the
particular identity comparison. -/
theorem not_homeomorphic (x : A)
    (h : ¬DiscreteTopology (QuotientFundamentalGroup.LoopQuot A x)) :
    ¬Nonempty (@Homeomorph (TraceClass A x) (TraceClass A x)
      (sensitiveTopology A x) (observableTopology A x)) := by
  rintro ⟨e⟩
  let f := (@Homeomorph.toEquiv _ _ (sensitiveTopology A x) (observableTopology A x) e).symm
  let g := (@Homeomorph.toEquiv _ _ (observableTopology A x) inferInstance
    (observableHomeomorph A x)).symm
  have hf : @Continuous _ _ (observableTopology A x) (sensitiveTopology A x) f :=
    @Homeomorph.continuous_invFun _ _ (sensitiveTopology A x) (observableTopology A x) e
  have hg : @Continuous _ _ inferInstance (observableTopology A x) g :=
    @Homeomorph.continuous_invFun _ _ (observableTopology A x) inferInstance
      (observableHomeomorph A x)
  letI := sensitiveTopology A x
  letI := sensitive_discrete A x
  have hc : Continuous (fun q : QuotientFundamentalGroup.LoopQuot A x =>
      f (g q)) :=
    @Continuous.comp (QuotientFundamentalGroup.LoopQuot A x) (TraceClass A x) (TraceClass A x)
      inferInstance (observableTopology A x) (sensitiveTopology A x) g f hf hg
  exact h (DiscreteTopology.of_continuous_injective hc (f.injective.comp g.injective))

abbrev CoherentClass (x : A) := Quotient (coherentSetoid (presentation A) x x)

/-- Matching coherent representatives can be eliminated before making the
ordinary path quotient comparison. -/
noncomputable def coherentObservableHomeomorph (x : A) :=
  @Homeomorph.trans _ _ _
    (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
      (coherentSetoid (presentation A) x x)
      (EqualSlotTopology.coherentTopology
        (EqualSlotTopology.traceObservableTopology (S := (system A).toGeometricStepSystem) x x)))
    (observableTopology A x) inferInstance
    (EqualSlotTopology.observableQuotientHomeomorph (presentation A) x x)
    (observableHomeomorph A x)

theorem coherent_sensitive_discrete (x : A) :
    @DiscreteTopology (CoherentClass A x)
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (coherentSetoid (presentation A) x x)
        (EqualSlotTopology.coherentTopology
          (EqualSlotTopology.traceSensitiveTopology
            (S := (system A).toGeometricStepSystem) x x))) := by
  letI := sensitiveTopology A x
  letI := sensitive_discrete A x
  letI := TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
    (coherentSetoid (presentation A) x x)
    (EqualSlotTopology.coherentTopology
      (EqualSlotTopology.traceSensitiveTopology (S := (system A).toGeometricStepSystem) x x))
  exact DiscreteTopology.of_continuous_injective
    (EqualSlotTopology.traceSensitiveQuotientHomeomorph (presentation A) x x).continuous_toFun
    (EqualSlotTopology.traceSensitiveQuotientHomeomorph (presentation A) x x).injective

end ComputationalPaths.Path.GeometricTopology.CompleteDiscreteSeparation
