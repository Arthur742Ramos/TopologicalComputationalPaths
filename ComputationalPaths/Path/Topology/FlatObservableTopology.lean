import ComputationalPaths.Path.Topology.FlatEqualSlotRealization
import ComputationalPaths.Path.Topology.CoherentRepresentativeElimination

/-!
# Observation topologies using exact equal-slot realization

These are separate topologies on the existing tree and coherent carriers.
The observation uses `flatRealize` throughout, without a binary-realization
coordinate. The homotopy bridge justifies reusing coherent representatives and
the same scoped rewrite relation. Fixed-endpoint representative elimination
is checked for this matching realization.

Identification with a literal carrier of composable flat words additionally
requires structural same-word equivalence and word-stratum continuity.
Neither those claims nor a binary/flat quotient homeomorphism is assumed here.
-/

namespace ComputationalPaths.Path.GeometricTopology

open scoped Topology ContinuousMap

universe u v

namespace EqualSlotTopology

variable {A : Type u} [TopologicalSpace A] {Step : Type v}
  {S : GeometricStepSystem A Step}

/-- Fixed-endpoint observable coordinates, using equal-slot timing. -/
noncomputable def traceCoordinates {a b : A} (p : GeometricTrace S a b) :=
  (GeometricTrace.traceLength p, GeometricTrace.flatRealize p)

@[reducible] noncomputable def traceObservableTopology (a b : A) :
    TopologicalSpace (GeometricTrace S a b) :=
  TopologicalSpace.induced (traceCoordinates (S := S)) inferInstance

theorem continuous_traceCoordinates (a b : A) :
    @Continuous _ _ (traceObservableTopology (S := S) a b) inferInstance
      (traceCoordinates (S := S)) := continuous_induced_dom

theorem continuous_flatRealize (a b : A) :
    @Continuous _ _ (traceObservableTopology (S := S) a b) inferInstance
      (GeometricTrace.flatRealize (S := S)) := by
  letI := traceObservableTopology (S := S) a b
  exact continuous_snd.comp (continuous_traceCoordinates (S := S) a b)

/-- The full-word refinement also observes only equal-slot realization. -/
@[reducible] noncomputable def traceSensitiveTopology [TopologicalSpace Step] (a b : A) :
    TopologicalSpace (GeometricTrace S a b) :=
  TopologicalSpace.induced
    (fun p : GeometricTrace S a b => (GeometricTrace.flatWord p, traceCoordinates p))
    inferInstance

theorem continuous_sensitive_flatRealize [TopologicalSpace Step] (a b : A) :
    @Continuous _ _ (traceSensitiveTopology (S := S) a b) inferInstance
      (GeometricTrace.flatRealize (S := S)) := by
  letI := traceSensitiveTopology (S := S) a b
  exact continuous_snd.comp (continuous_snd.comp (continuous_induced_dom :
    @Continuous _ _ (traceSensitiveTopology (S := S) a b) inferInstance
      (fun p : GeometricTrace S a b => (GeometricTrace.flatWord p, traceCoordinates p))))

/-- Binary coherence and equal-slot coherence are equivalent propositions. -/
theorem coherent_iff {a b : A} (p : GeometricTrace S a b) (γ : _root_.Path a b) :
    _root_.Path.Homotopic γ (GeometricTrace.realize p) ↔
      _root_.Path.Homotopic γ (GeometricTrace.flatRealize p) :=
  ⟨fun h => h.trans (GeometricTrace.flatRealize_homotopic_binary p).symm,
    fun h => h.trans (GeometricTrace.flatRealize_homotopic_binary p)⟩

/-- The canonical equal-slot representative belongs to the existing coherent
carrier by the checked homotopy bridge. -/
noncomputable def canonicalSection {a b : A} (p : GeometricTrace S a b) :
    OpenGeometricCompPath S a b :=
  ⟨p, GeometricTrace.flatRealize p, GeometricTrace.flatRealize_homotopic_binary p⟩

@[reducible] noncomputable def coherentTopology {a b : A}
    (τ : TopologicalSpace (GeometricTrace S a b)) :
    TopologicalSpace (OpenGeometricCompPath S a b) :=
  @TopologicalSpace.induced _ (GeometricTrace S a b × _root_.Path a b)
    (fun p => (p.trace, p.geometric)) (@instTopologicalSpaceProd _ _ τ inferInstance)

variable [TopologicalSpace Step] {C : ContinuousGeometricStepSystem A Step}

/-- Scoped rewrites remain geometrically sound for equal-slot realization. -/
theorem scoped_sound {a b : A} {P : ScopedGeometricRewritePresentation C}
    {p q : GeometricTrace C.toGeometricStepSystem a b} (h : ScopedRwEq P p q) :
    _root_.Path.Homotopic (GeometricTrace.flatRealize p) (GeometricTrace.flatRealize q) :=
  (GeometricTrace.flatRealize_homotopic_binary p).trans
    (h.sound.trans (GeometricTrace.flatRealize_homotopic_binary q).symm)

/-- Eliminate coherent representatives using the matching equal-slot section.
The assumptions concern realization continuity, not the desired homeomorphism. -/
noncomputable def quotientHomeomorph
    (P : ScopedGeometricRewritePresentation C) (a b : A)
    (τ : TopologicalSpace (GeometricTrace C.toGeometricStepSystem a b))
    (hflat : @Continuous _ _ τ inferInstance GeometricTrace.flatRealize) :
    @Homeomorph
      (Quotient (CoherentRepresentativeElimination.coherentSetoid P a b))
      (Quotient (CoherentRepresentativeElimination.traceSetoid P a b))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (CoherentRepresentativeElimination.coherentSetoid P a b) (coherentTopology τ))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (CoherentRepresentativeElimination.traceSetoid P a b) τ) := by
  letI : TopologicalSpace (GeometricTrace C.toGeometricStepSystem a b) := τ
  letI : TopologicalSpace (OpenGeometricCompPath C.toGeometricStepSystem a b) := coherentTopology τ
  letI : TopologicalSpace (Quotient (CoherentRepresentativeElimination.coherentSetoid P a b)) :=
    TopologicalSpace.coinduced
      (Quotient.mk (CoherentRepresentativeElimination.coherentSetoid P a b)) inferInstance
  letI : TopologicalSpace (Quotient (CoherentRepresentativeElimination.traceSetoid P a b)) :=
    TopologicalSpace.coinduced
      (Quotient.mk (CoherentRepresentativeElimination.traceSetoid P a b)) inferInstance
  let forget : Quotient (CoherentRepresentativeElimination.coherentSetoid P a b) →
      Quotient (CoherentRepresentativeElimination.traceSetoid P a b) :=
    Quotient.map (fun p => p.trace) (fun _ _ h => h)
  let choose : Quotient (CoherentRepresentativeElimination.traceSetoid P a b) →
      Quotient (CoherentRepresentativeElimination.coherentSetoid P a b) :=
    Quotient.map (canonicalSection (S := C.toGeometricStepSystem) (a := a) (b := b))
      (fun _ _ h => h)
  have hforget : Continuous forget := by
    apply (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientMk_isQuotient
      (CoherentRepresentativeElimination.coherentSetoid P a b) inferInstance).continuous_iff.2
    exact continuous_coinduced_rng.comp
      (continuous_fst.comp (continuous_induced_dom :
        Continuous (fun p : OpenGeometricCompPath C.toGeometricStepSystem a b =>
          (p.trace, p.geometric))))
  have hchoose : Continuous choose := by
    apply (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientMk_isQuotient
      (CoherentRepresentativeElimination.traceSetoid P a b) inferInstance).continuous_iff.2
    have hsection : Continuous
        (canonicalSection (S := C.toGeometricStepSystem) (a := a) (b := b)) := by
      apply continuous_induced_rng.mpr
      exact continuous_id.prodMk hflat
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

noncomputable def observableQuotientHomeomorph
    (P : ScopedGeometricRewritePresentation C) (a b : A) :=
  quotientHomeomorph P a b (traceObservableTopology (S := C.toGeometricStepSystem) a b)
    (continuous_flatRealize (S := C.toGeometricStepSystem) a b)

noncomputable def traceSensitiveQuotientHomeomorph
    (P : ScopedGeometricRewritePresentation C) (a b : A) :=
  quotientHomeomorph P a b (traceSensitiveTopology (S := C.toGeometricStepSystem) a b)
    (continuous_sensitive_flatRealize (S := C.toGeometricStepSystem) a b)

/-- Endpoint-varying observation with the exact equal-slot coordinate. -/
noncomputable def totalObservation (C : ContinuousGeometricStepSystem A Step)
    (p : TotalOpenGeometricCompPath A Step C) :
    TotalOpenGeometricCompPath.Observation (A := A) :=
  (p.src, (p.tgt, (GeometricTrace.traceLength p.trace,
    ((GeometricTrace.flatRealize p.trace).toContinuousMap, p.path.geometric.toContinuousMap))))

@[reducible] noncomputable def totalObservableTopology (C : ContinuousGeometricStepSystem A Step) :
    TopologicalSpace (TotalOpenGeometricCompPath A Step C) :=
  TopologicalSpace.induced (totalObservation C) inferInstance

@[reducible] noncomputable def totalSensitiveTopology (C : ContinuousGeometricStepSystem A Step) :
    TopologicalSpace (TotalOpenGeometricCompPath A Step C) :=
  TopologicalSpace.induced (fun p => (GeometricTrace.flatWord p.trace, totalObservation C p))
    inferInstance

theorem continuous_totalObservation (C : ContinuousGeometricStepSystem A Step) :
    @Continuous _ _ (totalObservableTopology C) inferInstance (totalObservation C) :=
  continuous_induced_dom

@[reducible] noncomputable def totalQuotientTopology (P : ScopedGeometricRewritePresentation C) :
    TopologicalSpace (ScopedClass P) :=
  @TopologicalSpace.coinduced _ _ (scopedQuotientMk P)
    (totalObservableTopology C)

theorem continuous_totalQuotientMk (P : ScopedGeometricRewritePresentation C) :
    @Continuous _ _ (totalObservableTopology C) (totalQuotientTopology P)
      (scopedQuotientMk P) := continuous_coinduced_rng

end EqualSlotTopology

end ComputationalPaths.Path.GeometricTopology
