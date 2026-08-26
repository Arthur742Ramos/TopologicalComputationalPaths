import ComputationalPaths.Path.Topology.ComputationalPathTopology
import Mathlib.Topology.Path
import Mathlib.Topology.Homotopy.Path

/-!
# Geometric computational paths

The raw `ComputationalPaths.Path` type records a finite rewrite trace.  It is
not, by itself, a continuous map from an interval.  This file adds the
geometric layer without changing that raw API:

* a `RealizationModel` supplies a continuous topological path for each raw
  computational path;
* its coherence fields compare realization with `refl`, `trans`, and `symm`
  using topological path homotopies;
* `GeometricCompPath` packages the raw trace, its geometric path, and the
  realization coherence;
* the resulting space inherits the compact-open topology from Mathlib's
  interval-path space and the trace topology from the raw path space.

The realization model is deliberately explicit.  An arbitrary equality in a
topological space need not be represented by a continuous interval path, so
there is no sound canonical realization for every `A` without additional
hypotheses.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open TopologicalSpace

universe u

/-! ## Realization data -/

/-- A coherent geometric interpretation of raw computational paths.

The raw trace operations remain computational paths.  The geometric coherence
laws are homotopies because interval concatenation is naturally defined only
up to reparameterization, so demanding strict equality would be too strong.
-/
structure RealizationModel (A : Type u) [TopologicalSpace A] where
  realize {a b : A} : ComputationalPaths.Path a b → _root_.Path a b
  realize_refl (a : A) : _root_.Path.Homotopic
      (realize (ComputationalPaths.Path.refl a))
      (_root_.Path.refl a)
  realize_trans {a b c : A}
      (p : ComputationalPaths.Path a b) (q : ComputationalPaths.Path b c) :
    _root_.Path.Homotopic
      (realize (ComputationalPaths.Path.trans p q))
      (_root_.Path.trans (realize p) (realize q))
  realize_symm {a b : A} (p : ComputationalPaths.Path a b) :
    _root_.Path.Homotopic
      (realize (ComputationalPaths.Path.symm p))
      (_root_.Path.symm (realize p))
  realize_continuous {a b : A} :
    Continuous (realize : ComputationalPaths.Path a b → _root_.Path a b)

/-- The canonical realization forced by the equality semantics of raw
computational paths: every trace is sent to the constant interval path at its
source, cast to the target endpoint. -/
noncomputable def constantRealize {A : Type u} [TopologicalSpace A]
    {a b : A} (p : ComputationalPaths.Path a b) : _root_.Path a b :=
  (_root_.Path.refl a).cast rfl p.proof.symm

/-!
This model is intentionally degenerate geometrically.  It is canonical for
the present `Path` definition because a raw path carries `a = b`; nonconstant
geometric motion requires an additional path notion whose endpoints need not
be propositionally equal.
-/

/-- A proof-irrelevant realization model available for every topological space.
Its trace coordinate remains fully visible in `GeometricCompPath`, while the
geometric coordinate is the canonical constant path. -/
noncomputable def constantRealizationModel {A : Type u} [TopologicalSpace A] :
    RealizationModel A where
  realize := constantRealize
  realize_refl := by
    intro a
    exact ⟨by
      simpa [constantRealize] using (_root_.Path.Homotopy.refl (_root_.Path.refl a))⟩
  realize_trans := by
    intro a b c p q
    rcases p with ⟨psteps, hp⟩
    rcases q with ⟨qsteps, hq⟩
    cases hp
    cases hq
    exact ⟨by
      simpa [constantRealize] using (_root_.Path.Homotopy.refl (_root_.Path.refl a))⟩
  realize_symm := by
    intro a b p
    rcases p with ⟨steps, hp⟩
    cases hp
    exact ⟨by
      simpa [constantRealize] using (_root_.Path.Homotopy.refl (_root_.Path.refl a))⟩
  realize_continuous := by
    intro a b
    cases isEmpty_or_nonempty (ComputationalPaths.Path a b) with
    | inl h =>
        letI : IsEmpty (ComputationalPaths.Path a b) := h
        apply continuous_iff_continuousAt.mpr
        intro p
        exact isEmptyElim p
    | inr h =>
        let p₀ : ComputationalPaths.Path a b := Classical.choice h
        exact Continuous.congr
          (continuous_const :
            Continuous (fun _ : ComputationalPaths.Path a b => constantRealize p₀))
          (fun p => by
            cases p with
            | mk steps proof =>
                cases proof
                simp [constantRealize])

/-! ## Geometric paths carrying computational traces -/

/-- A continuous interval path equipped with a raw computational trace and a
homotopy witness identifying it with the model's realization of that trace. -/
structure GeometricCompPath {A : Type u} [TopologicalSpace A]
    (M : RealizationModel A) (a b : A) where
  trace : ComputationalPaths.Path a b
  geometric : _root_.Path a b
  coherent : _root_.Path.Homotopic geometric (M.realize trace)

/-!
The topology is induced by the pair consisting of the trace and geometric
coordinates.  The first coordinate uses the raw trace topology; the second
uses Mathlib's compact-open topology on `_root_.Path a b`.
-/
noncomputable instance instTopologicalSpace {A : Type u} [TopologicalSpace A]
    (M : RealizationModel A) {a b : A} :
    TopologicalSpace (GeometricCompPath M a b) :=
  TopologicalSpace.induced
    (fun p : GeometricCompPath M a b => (p.trace, p.geometric)) inferInstance

theorem continuous_trace {A : Type u} [TopologicalSpace A]
    (M : RealizationModel A) {a b : A} :
    Continuous (fun p : GeometricCompPath M a b => p.trace) :=
  continuous_fst.comp
    (continuous_induced_dom :
      Continuous (fun p : GeometricCompPath M a b => (p.trace, p.geometric)))

theorem continuous_geometric {A : Type u} [TopologicalSpace A]
    (M : RealizationModel A) {a b : A} :
    Continuous (fun p : GeometricCompPath M a b => p.geometric) :=
  continuous_snd.comp
    (continuous_induced_dom :
      Continuous (fun p : GeometricCompPath M a b => (p.trace, p.geometric)))

theorem continuous_realization {A : Type u} [TopologicalSpace A]
    (M : RealizationModel A) {a b : A} :
    Continuous (fun p : GeometricCompPath M a b => M.realize p.trace) :=
  M.realize_continuous.comp (continuous_trace M)

/-! ## Constructors and operations -/

/-- The constant geometric computational path. -/
noncomputable def refl {A : Type u} [TopologicalSpace A]
    (M : RealizationModel A) (a : A) : GeometricCompPath M a a :=
  { trace := ComputationalPaths.Path.refl a
    geometric := _root_.Path.refl a
    coherent := by
      rcases M.realize_refl a with ⟨h⟩
      exact ⟨h.symm⟩ }

/-- Geometric concatenation, with the raw traces concatenated in parallel. -/
noncomputable def trans {A : Type u} [TopologicalSpace A]
    {a b c : A} (M : RealizationModel A)
    (p : GeometricCompPath M a b) (q : GeometricCompPath M b c) :
    GeometricCompPath M a c :=
  { trace := ComputationalPaths.Path.trans p.trace q.trace
    geometric := _root_.Path.trans p.geometric q.geometric
    coherent := by
      rcases p.coherent with ⟨hp⟩
      rcases q.coherent with ⟨hq⟩
      rcases M.realize_trans p.trace q.trace with ⟨htrans⟩
      exact ⟨(hp.hcomp hq).trans htrans.symm⟩ }

/-- Geometric reversal, with the raw trace reversed in parallel. -/
noncomputable def symm {A : Type u} [TopologicalSpace A]
    {a b : A} (M : RealizationModel A) (p : GeometricCompPath M a b) :
    GeometricCompPath M b a :=
  { trace := ComputationalPaths.Path.symm p.trace
    geometric := _root_.Path.symm p.geometric
    coherent := by
      rcases p.coherent with ⟨hp⟩
      rcases M.realize_symm p.trace with ⟨hsymm⟩
      exact ⟨hp.symm₂.trans hsymm.symm⟩ }

/-! ## Continuity of the geometric operations -/

/-- Geometric concatenation is continuous for the induced compact-open/trace
topology. -/
theorem continuous_trans {A : Type u} [TopologicalSpace A]
    {a b c : A} (M : RealizationModel A) :
    Continuous
      (fun pq : GeometricCompPath M a b × GeometricCompPath M b c =>
        trans M pq.1 pq.2) := by
  apply continuous_induced_rng.mpr
  change Continuous
    (fun pq : GeometricCompPath M a b × GeometricCompPath M b c =>
      (ComputationalPaths.Path.trans pq.1.trace pq.2.trace,
        _root_.Path.trans pq.1.geometric pq.2.geometric))
  have htrace :
      Continuous (fun pq : GeometricCompPath M a b × GeometricCompPath M b c =>
        ComputationalPaths.Path.trans pq.1.trace pq.2.trace) :=
    RawTopology.continuous_path_trans.comp
      ((continuous_trace M |>.comp continuous_fst).prodMk
        (continuous_trace M |>.comp continuous_snd))
  have hgeometric :
      Continuous (fun pq : GeometricCompPath M a b × GeometricCompPath M b c =>
        _root_.Path.trans pq.1.geometric pq.2.geometric) :=
    _root_.Path.continuous_trans.comp
      ((continuous_geometric M |>.comp continuous_fst).prodMk
        (continuous_geometric M |>.comp continuous_snd))
  exact htrace.prodMk hgeometric

/-- Geometric reversal is continuous for the induced compact-open/trace
topology. -/
theorem continuous_symm {A : Type u} [TopologicalSpace A]
    {a b : A} (M : RealizationModel A) :
    Continuous (fun p : GeometricCompPath M a b => symm M p) := by
  apply continuous_induced_rng.mpr
  change Continuous
    (fun p : GeometricCompPath M a b =>
      (ComputationalPaths.Path.symm p.trace, _root_.Path.symm p.geometric))
  exact (RawTopology.continuous_path_symm.comp (continuous_trace M)).prodMk
    (_root_.Path.continuous_symm.comp (continuous_geometric M))

/-! ## A reusable certificate -/

/-- Summary of the geometric-path structure supplied by a realization model. -/
structure GeometricPathCertificate {A : Type u} [TopologicalSpace A]
    (M : RealizationModel A) where
  trace_continuous {a b : A} :
    Continuous (fun p : GeometricCompPath M a b => p.trace)
  geometric_continuous {a b : A} :
    Continuous (fun p : GeometricCompPath M a b => p.geometric)
  realization_continuous {a b : A} :
    Continuous (fun p : GeometricCompPath M a b => M.realize p.trace)
  trans_continuous {a b c : A} :
    Continuous
      (fun pq : GeometricCompPath M a b × GeometricCompPath M b c =>
        trans M pq.1 pq.2)
  symm_continuous {a b : A} :
    Continuous (fun p : GeometricCompPath M a b => symm M p)

noncomputable def geometricPathCertificate {A : Type u} [TopologicalSpace A]
    (M : RealizationModel A) : GeometricPathCertificate M where
  trace_continuous := continuous_trace M
  geometric_continuous := continuous_geometric M
  realization_continuous := continuous_realization M
  trans_continuous := continuous_trans M
  symm_continuous := continuous_symm M

end GeometricTopology
end Path
end ComputationalPaths
