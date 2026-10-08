import ComputationalPaths.Path.Topology.ScopedWordInterpretation

/-!
# Continuous fixed-endpoint word interpretations

This module descends continuity of actual recursive trace substitutions through
the scoped trace quotients. Together with primitive roundtrip rewrite witnesses
it gives a fixed-endpoint quotient homeomorphism for explicitly supplied trace
topologies. No continuity of a desired quotient map or homeomorphism is input.

For the binary observable trace topology, continuity is derived from two
primitive conditions: a uniform substituted length and exact binary geometric
realization compatibility. The length coordinate is multiplied by a fixed
natural number, and the realized-path coordinate is unchanged.

This is infrastructure rather than a general presentation-invariance theorem.
Primitive compatibility only up to homotopy does not imply this continuity
result. Variable-length substitutions, the flat equal-slot full-word topology,
endpoint-varying carriers, and composable-pair domains need separate arguments.
No equality of binary and flat quotient topologies is asserted here.
-/

namespace ComputationalPaths.Path.GeometricTopology

open scoped Topology

universe u v w

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} {Step' : Type w}

namespace WordSubstitution

variable {S : GeometricStepSystem A Step} {T : GeometricStepSystem A Step'}

/-- A uniform primitive expansion length multiplies the length of every trace.
No named rewrite rules or topological conditions are needed. -/
theorem mapTrace_length (M : WordSubstitution S T) (k : Nat)
    (hstep : ∀ s : Step, GeometricTrace.traceLength (M.step s) = k)
    {a b : A} (p : GeometricTrace S a b) :
    GeometricTrace.traceLength (M.mapTrace p) = k * GeometricTrace.traceLength p := by
  induction p with
  | refl a => simp [mapTrace, GeometricTrace.traceLength]
  | single s => simpa [mapTrace, GeometricTrace.traceLength] using hstep s
  | trans p q ihp ihq =>
      simp [mapTrace, GeometricTrace.traceLength, ihp, ihq, Nat.mul_add]
  | symm p ih => simpa [mapTrace, GeometricTrace.traceLength] using ih

/-- Exact compatibility at primitives propagates through binary composition
and reversal to exact parametrized-path equality for every trace. -/
theorem mapTrace_realize (M : WordSubstitution S T)
    (hstep : ∀ s : Step, GeometricTrace.realize (M.step s) = S.realize s)
    {a b : A} (p : GeometricTrace S a b) :
    GeometricTrace.realize (M.mapTrace p) = GeometricTrace.realize p := by
  induction p with
  | refl a => rfl
  | single s => exact hstep s
  | trans p q ihp ihq => simp only [mapTrace, GeometricTrace.realize, ihp, ihq]
  | symm p ih => simp only [mapTrace, GeometricTrace.realize, ih]

/-- These actual primitive conditions imply continuity for the existing binary
observable trace topology. They do not refer to the induced quotient map. -/
theorem continuous_binary (M : WordSubstitution S T) (k : Nat)
    (hlength : ∀ s : Step, GeometricTrace.traceLength (M.step s) = k)
    (hrealize : ∀ s : Step, GeometricTrace.realize (M.step s) = S.realize s)
    {a b : A} : Continuous (M.mapTrace : GeometricTrace S a b → GeometricTrace T a b) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : GeometricTrace S a b =>
    (GeometricTrace.traceLength (M.mapTrace p), GeometricTrace.realize (M.mapTrace p)))
  have hmul : Continuous (fun n : Nat => k * n) := continuous_of_discreteTopology
  have hcoordinate : Continuous (fun p : GeometricTrace S a b =>
      (k * GeometricTrace.traceLength p, GeometricTrace.realize p)) :=
    (hmul.comp GeometricTrace.continuous_traceLength).prodMk GeometricTrace.continuous_realize
  simpa only [M.mapTrace_length k hlength, M.mapTrace_realize hrealize] using hcoordinate

end WordSubstitution

variable [TopologicalSpace Step] [TopologicalSpace Step']
  {S : ContinuousGeometricStepSystem A Step}
  {T : ContinuousGeometricStepSystem A Step'}
  {P : ScopedGeometricRewritePresentation S}
  {Q : ScopedGeometricRewritePresentation T}

namespace ScopedWordInterpretation

/-- Continuity of the recursive substitution descends to the fixed-endpoint
scoped quotient, equipped with the coinduced topologies. -/
theorem continuous_quotientMap (M : ScopedWordInterpretation P Q) (a b : A)
    (τS : TopologicalSpace (GeometricTrace S.toGeometricStepSystem a b))
    (τT : TopologicalSpace (GeometricTrace T.toGeometricStepSystem a b))
    (hM : @Continuous _ _ τS τT M.substitution.mapTrace) :
    @Continuous _ _
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (CoherentRepresentativeElimination.traceSetoid P a b) τS)
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (CoherentRepresentativeElimination.traceSetoid Q a b) τT)
      (M.quotientMap a b) := by
  letI := τS
  letI := τT
  letI : TopologicalSpace (Quotient (CoherentRepresentativeElimination.traceSetoid P a b)) :=
    TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
      (CoherentRepresentativeElimination.traceSetoid P a b) τS
  letI : TopologicalSpace (Quotient (CoherentRepresentativeElimination.traceSetoid Q a b)) :=
    TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
      (CoherentRepresentativeElimination.traceSetoid Q a b) τT
  apply (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientMk_isQuotient
    (CoherentRepresentativeElimination.traceSetoid P a b) τS).continuous_iff.2
  exact continuous_coinduced_rng.comp hM

/-- Continuous actual substitutions with primitive roundtrip rewrites yield
a fixed-endpoint quotient homeomorphism. The algebraic inverse law and both
quotient-map continuity proofs are derived, not assumed. -/
noncomputable def quotientHomeomorph
    (M : ScopedWordInterpretation P Q) (N : ScopedWordInterpretation Q P)
    (hS : ∀ s : Step, ScopedRwEq P (N.substitution.mapTrace (M.substitution.step s))
      (GeometricTrace.single s))
    (hT : ∀ t : Step', ScopedRwEq Q (M.substitution.mapTrace (N.substitution.step t))
      (GeometricTrace.single t)) (a b : A)
    (τS : TopologicalSpace (GeometricTrace S.toGeometricStepSystem a b))
    (τT : TopologicalSpace (GeometricTrace T.toGeometricStepSystem a b))
    (hM : @Continuous _ _ τS τT M.substitution.mapTrace)
    (hN : @Continuous _ _ τT τS N.substitution.mapTrace) :
    @Homeomorph
      (Quotient (CoherentRepresentativeElimination.traceSetoid P a b))
      (Quotient (CoherentRepresentativeElimination.traceSetoid Q a b))
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (CoherentRepresentativeElimination.traceSetoid P a b) τS)
      (TotalOpenGeometricCompPath.TraceSensitiveQuotient.quotientTopology
        (CoherentRepresentativeElimination.traceSetoid Q a b) τT) :=
  { toEquiv := M.quotientEquiv N hS hT a b
    continuous_toFun := M.continuous_quotientMap a b τS τT hM
    continuous_invFun := N.continuous_quotientMap a b τT τS hN }

/-- Concrete binary-observable specialization: continuity in both directions
is obtained from uniform primitive lengths and exact realized paths. -/
noncomputable def binaryQuotientHomeomorph
    (M : ScopedWordInterpretation P Q) (N : ScopedWordInterpretation Q P)
    (hS : ∀ s : Step, ScopedRwEq P (N.substitution.mapTrace (M.substitution.step s))
      (GeometricTrace.single s))
    (hT : ∀ t : Step', ScopedRwEq Q (M.substitution.mapTrace (N.substitution.step t))
      (GeometricTrace.single t)) (k l : Nat)
    (hMLength : ∀ s : Step, GeometricTrace.traceLength (M.substitution.step s) = k)
    (hNLength : ∀ t : Step', GeometricTrace.traceLength (N.substitution.step t) = l)
    (hMRealize : ∀ s : Step,
      GeometricTrace.realize (M.substitution.step s) = S.toGeometricStepSystem.realize s)
    (hNRealize : ∀ t : Step',
      GeometricTrace.realize (N.substitution.step t) = T.toGeometricStepSystem.realize t)
    (a b : A) :=
  quotientHomeomorph M N hS hT a b inferInstance inferInstance
    (M.substitution.continuous_binary k hMLength hMRealize)
    (N.substitution.continuous_binary l hNLength hNRealize)

end ScopedWordInterpretation

end ComputationalPaths.Path.GeometricTopology
