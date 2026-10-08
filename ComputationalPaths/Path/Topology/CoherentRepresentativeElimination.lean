import ComputationalPaths.Path.Topology.ScopedGeometricRewrite
import ComputationalPaths.Path.Topology.TraceSensitiveTopologicalCompPath

/-!
# Eliminating coherent representatives at fixed endpoints

The topology on a trace and the topology on its coherent enrichment must use
the same realization. This file concerns the existing binary realization.
It does not identify that topology with an equal-slot flat-word topology.

The forgetful map and its canonical continuous section induce inverse
homeomorphisms after quotienting by a relation depending only on traces.
The result applies both to the observable trace topology and its refinement
by the full signed word. No completeness hypothesis is used.
-/

namespace ComputationalPaths.Path.GeometricTopology

open scoped Topology

universe u v

namespace CoherentRepresentativeElimination

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  {S : ContinuousGeometricStepSystem A Step}

/-- Scoped rewriting on a fixed endpoint trace carrier. -/
def traceSetoid (P : ScopedGeometricRewritePresentation S) (a b : A) :
    Setoid (GeometricTrace S.toGeometricStepSystem a b) where
  r := ScopedRwEq P
  iseqv := ⟨ScopedRwEq.refl, ScopedRwEq.symm, ScopedRwEq.trans⟩

/-- Coherent representatives are related precisely when their traces are. -/
def coherentSetoid (P : ScopedGeometricRewritePresentation S) (a b : A) :
    Setoid (OpenGeometricCompPath S.toGeometricStepSystem a b) where
  r p q := ScopedRwEq P p.trace q.trace
  iseqv := ⟨fun p => ScopedRwEq.refl p.trace,
    fun h => ScopedRwEq.symm h, fun hpq hqr => ScopedRwEq.trans hpq hqr⟩

/-- Choose the realized trace itself as coherent representative. -/
noncomputable def canonicalSection {a b : A}
    (p : GeometricTrace S.toGeometricStepSystem a b) :
    OpenGeometricCompPath S.toGeometricStepSystem a b :=
  ⟨p, GeometricTrace.realize p, _root_.Path.Homotopic.refl _⟩

/-- Elimination for any trace topology for which realization is continuous.

The enriched topology is induced by `(trace, geometric)`. In particular this
allows the trace topology to observe the full word as well as binary timing.
-/
noncomputable def quotientHomeomorph
    (P : ScopedGeometricRewritePresentation S) (a b : A)
    (τ : TopologicalSpace (GeometricTrace S.toGeometricStepSystem a b))
    (hrealize : @Continuous _ _ τ inferInstance GeometricTrace.realize) :
    let τcoh := @TopologicalSpace.induced
      (OpenGeometricCompPath S.toGeometricStepSystem a b)
      (GeometricTrace S.toGeometricStepSystem a b × _root_.Path a b)
      (fun p => (p.trace, p.geometric)) (@instTopologicalSpaceProd _ _ τ inferInstance)
    @Homeomorph (Quotient (coherentSetoid P a b)) (Quotient (traceSetoid P a b))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (coherentSetoid P a b) τcoh)
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (traceSetoid P a b) τ) := by
  letI : TopologicalSpace (GeometricTrace S.toGeometricStepSystem a b) := τ
  letI : TopologicalSpace (OpenGeometricCompPath S.toGeometricStepSystem a b) :=
    TopologicalSpace.induced (fun p => (p.trace, p.geometric)) inferInstance
  letI : TopologicalSpace (Quotient (coherentSetoid P a b)) :=
    TopologicalSpace.coinduced (Quotient.mk (coherentSetoid P a b)) inferInstance
  letI : TopologicalSpace (Quotient (traceSetoid P a b)) :=
    TopologicalSpace.coinduced (Quotient.mk (traceSetoid P a b)) inferInstance
  let forget : Quotient (coherentSetoid P a b) → Quotient (traceSetoid P a b) :=
    Quotient.map (fun p => p.trace) (fun _ _ h => h)
  let choose : Quotient (traceSetoid P a b) → Quotient (coherentSetoid P a b) :=
    Quotient.map (canonicalSection (S := S) (a := a) (b := b)) (fun _ _ h => h)
  have hforget : Continuous forget := by
    apply (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientMk_isQuotient
      (coherentSetoid P a b) inferInstance).continuous_iff.2
    exact continuous_coinduced_rng.comp
      (continuous_fst.comp (continuous_induced_dom :
        Continuous (fun p : OpenGeometricCompPath S.toGeometricStepSystem a b =>
          (p.trace, p.geometric))))
  have hchoose : Continuous choose := by
    apply (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientMk_isQuotient
      (traceSetoid P a b) inferInstance).continuous_iff.2
    have hsection : Continuous (canonicalSection (S := S) (a := a) (b := b)) := by
      apply continuous_induced_rng.mpr
      exact continuous_id.prodMk hrealize
    exact continuous_coinduced_rng.comp hsection
  exact
    { toFun := forget
      invFun := choose
      left_inv := by
        intro p
        refine Quotient.inductionOn p ?_
        intro p
        exact Quotient.sound (ScopedRwEq.refl p.trace)
      right_inv := by
        intro p
        refine Quotient.inductionOn p ?_
        intro p
        rfl
      continuous_toFun := hforget
      continuous_invFun := hchoose }

/-- Elimination for the existing binary observable trace topology. -/
noncomputable def observableQuotientHomeomorph
    (P : ScopedGeometricRewritePresentation S) (a b : A) :=
  quotientHomeomorph P a b inferInstance (GeometricTrace.continuous_realize (S := S.toGeometricStepSystem))

/-- Full-word refinement of the fixed endpoint binary trace topology. -/
@[reducible] noncomputable def traceSensitiveTopology (a b : A) :
    TopologicalSpace (GeometricTrace S.toGeometricStepSystem a b) :=
  TopologicalSpace.induced
    (fun p => (GeometricTrace.flatWord p, GeometricTrace.coordinates p)) inferInstance

theorem continuous_traceSensitive_realize (a b : A) :
    @Continuous _ _ (traceSensitiveTopology (S := S) a b) inferInstance
      GeometricTrace.realize := by
  letI := traceSensitiveTopology (S := S) a b
  have hcode : Continuous (fun p : GeometricTrace S.toGeometricStepSystem a b =>
      (GeometricTrace.flatWord p, GeometricTrace.coordinates p)) := continuous_induced_dom
  exact hcode.snd.snd

/-- Elimination for the matching fixed endpoint full-word refinement. -/
noncomputable def traceSensitiveQuotientHomeomorph
    (P : ScopedGeometricRewritePresentation S) (a b : A) :=
  quotientHomeomorph P a b (traceSensitiveTopology (S := S) a b)
    (continuous_traceSensitive_realize (S := S) a b)

end CoherentRepresentativeElimination
end ComputationalPaths.Path.GeometricTopology
