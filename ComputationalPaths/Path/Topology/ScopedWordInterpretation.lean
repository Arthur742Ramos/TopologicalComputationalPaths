import ComputationalPaths.Path.Topology.CoherentRepresentativeElimination

/-!
# Primitive generators interpreted as finite traces

`WordSubstitution` maps a source primitive to an endpoint-typed target trace.
It can change length and retains the order of composition and reversal.
`ScopedWordInterpretation` requires only that images of named source rules
are derivable in the target presentation; preservation of the full scoped
relation follows by induction over the structural rules.

Primitive roundtrip rewrite witnesses for two interpretations extend to all
traces and yield an algebraic equivalence of fixed-endpoint trace quotients.
No quotient map, equivalence, continuity or geometric completeness is assumed.
Geometric compatibility is a separate theorem using primitive homotopies.

These statements do not assert topological presentation invariance. For the
observation topologies, continuity of a variable-length substitution requires
its own proof; exact binary and equal-slot timing can change under substitution.
Endpoint-varying quotient and composable-pair comparisons are also separate.
-/

namespace ComputationalPaths.Path.GeometricTopology

universe u v w

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} {Step' : Type w}

/-- A primitive may be interpreted as an arbitrary finite target trace with
the same source and target, including a zero-length trace when permitted by
its endpoint type. No length-preservation condition is imposed. -/
structure WordSubstitution (S : GeometricStepSystem A Step)
    (T : GeometricStepSystem A Step') where
  step : (s : Step) → GeometricTrace T (S.src s) (S.tgt s)

namespace WordSubstitution

variable {S : GeometricStepSystem A Step} {T : GeometricStepSystem A Step'}

/-- Interpret a tree of primitive generators by structural recursion. -/
def mapTrace (M : WordSubstitution S T) {a b : A} :
    GeometricTrace S a b → GeometricTrace T a b
  | .refl a => .refl a
  | .single s => M.step s
  | .trans p q => .trans (M.mapTrace p) (M.mapTrace q)
  | .symm p => .symm (M.mapTrace p)

@[simp] theorem mapTrace_refl (M : WordSubstitution S T) (a : A) :
    M.mapTrace (.refl a) = .refl a := rfl

@[simp] theorem mapTrace_single (M : WordSubstitution S T) (s : Step) :
    M.mapTrace (.single s) = M.step s := rfl

@[simp] theorem mapTrace_trans (M : WordSubstitution S T) {a b c : A}
    (p : GeometricTrace S a b) (q : GeometricTrace S b c) :
    M.mapTrace (.trans p q) = .trans (M.mapTrace p) (M.mapTrace q) := rfl

@[simp] theorem mapTrace_symm (M : WordSubstitution S T) {a b : A}
    (p : GeometricTrace S a b) :
    M.mapTrace (.symm p) = .symm (M.mapTrace p) := rfl

/-- Primitive endpoint-fixed homotopies imply geometric soundness of every
interpreted trace. Exact parametrized-path equality is not required. -/
theorem realize_homotopic (M : WordSubstitution S T)
    (hstep : ∀ s, _root_.Path.Homotopic (GeometricTrace.realize (M.step s)) (S.realize s))
    {a b : A} (p : GeometricTrace S a b) :
    _root_.Path.Homotopic (GeometricTrace.realize (M.mapTrace p)) (GeometricTrace.realize p) := by
  induction p with
  | refl a => exact _root_.Path.Homotopic.refl _
  | single s => exact hstep s
  | trans p q ihp ihq =>
      rcases ihp with ⟨hp⟩
      rcases ihq with ⟨hq⟩
      exact ⟨hp.hcomp hq⟩
  | symm p ih =>
      rcases ih with ⟨h⟩
      exact ⟨h.symm₂⟩

end WordSubstitution

variable [TopologicalSpace Step] [TopologicalSpace Step']
  {S : ContinuousGeometricStepSystem A Step}
  {T : ContinuousGeometricStepSystem A Step'}

/-- A finite-word interpretation respects the actual named rewrite generators.
Its target witnesses may use all target scoped rewrites. -/
structure ScopedWordInterpretation
    (P : ScopedGeometricRewritePresentation S) (Q : ScopedGeometricRewritePresentation T) where
  substitution : WordSubstitution S.toGeometricStepSystem T.toGeometricStepSystem
  named_rule : ∀ {a b : A} {p q : GeometricTrace S.toGeometricStepSystem a b},
    P.rule p q → ScopedRwEq Q (substitution.mapTrace p) (substitution.mapTrace q)

namespace ScopedWordInterpretation

variable {P : ScopedGeometricRewritePresentation S} {Q : ScopedGeometricRewritePresentation T}

/-- Named-rule preservation suffices for every scoped derivation, including
cancellation, associativity, reversal, identities and both congruences. -/
theorem map_scoped (M : ScopedWordInterpretation P Q) {a b : A}
    {p q : GeometricTrace S.toGeometricStepSystem a b} (h : ScopedRwEq P p q) :
    ScopedRwEq Q (M.substitution.mapTrace p) (M.substitution.mapTrace q) := by
  induction h with
  | refl p => exact ScopedRwEq.refl _
  | generator h => exact M.named_rule h
  | symm h ih => exact ScopedRwEq.symm ih
  | trans h₁ h₂ ih₁ ih₂ => exact ScopedRwEq.trans ih₁ ih₂
  | trans_congr h₁ h₂ ih₁ ih₂ => exact ScopedRwEq.trans_congr ih₁ ih₂
  | symm_congr h ih => exact ScopedRwEq.symm_congr ih
  | refl_trans p => exact ScopedRwEq.refl_trans _
  | trans_refl p => exact ScopedRwEq.trans_refl _
  | trans_assoc p q r => exact ScopedRwEq.trans_assoc _ _ _
  | symm_trans p => exact ScopedRwEq.symm_trans _
  | trans_symm p => exact ScopedRwEq.trans_symm _
  | symm_symm p => exact ScopedRwEq.symm_symm _
  | symm_refl a => exact ScopedRwEq.symm_refl _
  | symm_comp p q => exact ScopedRwEq.symm_comp _ _

/-- Proving the roundtrip relation just for primitive generators gives it for
all source traces. This is an algebraic derivation, independent of topology. -/
theorem roundtrip (M : ScopedWordInterpretation P Q) (N : ScopedWordInterpretation Q P)
    (hstep : ∀ s : Step, ScopedRwEq P (N.substitution.mapTrace (M.substitution.step s))
      (GeometricTrace.single s))
    {a b : A} (p : GeometricTrace S.toGeometricStepSystem a b) :
    ScopedRwEq P (N.substitution.mapTrace (M.substitution.mapTrace p)) p := by
  induction p with
  | refl a => exact ScopedRwEq.refl _
  | single s => exact hstep s
  | trans p q ihp ihq => exact ScopedRwEq.trans_congr ihp ihq
  | symm p ih => exact ScopedRwEq.symm_congr ih

/-- The descended fixed-endpoint quotient map. Preservation is established
from named generators by `map_scoped`, rather than assumed as a quotient law. -/
def quotientMap (M : ScopedWordInterpretation P Q) (a b : A) :
    Quotient (CoherentRepresentativeElimination.traceSetoid P a b) →
      Quotient (CoherentRepresentativeElimination.traceSetoid Q a b) :=
  Quotient.map M.substitution.mapTrace (fun _ _ h => M.map_scoped h)

/-- Two interpretations whose primitive roundtrips are scoped rewrites give
an algebraic equivalence. The hypotheses refer to finite trace substitutions
and primitive rewrite derivations; no desired quotient equivalence is input. -/
def quotientEquiv (M : ScopedWordInterpretation P Q) (N : ScopedWordInterpretation Q P)
    (hS : ∀ s : Step, ScopedRwEq P (N.substitution.mapTrace (M.substitution.step s))
      (GeometricTrace.single s))
    (hT : ∀ t : Step', ScopedRwEq Q (M.substitution.mapTrace (N.substitution.step t))
      (GeometricTrace.single t)) (a b : A) :
    Quotient (CoherentRepresentativeElimination.traceSetoid P a b) ≃
      Quotient (CoherentRepresentativeElimination.traceSetoid Q a b) where
  toFun := M.quotientMap a b
  invFun := N.quotientMap a b
  left_inv p := Quotient.inductionOn p (fun p => Quotient.sound (M.roundtrip N hS p))
  right_inv q := Quotient.inductionOn q (fun q => Quotient.sound (N.roundtrip M hT q))

end ScopedWordInterpretation

end ComputationalPaths.Path.GeometricTopology
