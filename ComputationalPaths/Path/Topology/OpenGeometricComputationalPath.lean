import ComputationalPaths.Path.Topology.GeometricComputationalPath

/-!
# Open geometric computational paths

The raw `ComputationalPaths.Path a b` type is equality-indexed: a raw path
already contains a proof that `a = b`.  It therefore cannot be the path space
of a topological space when distinct points are joined by genuine motion.

This file supplies the strongest generic replacement that does not change that
existing API.  A `GeometricStepSystem` provides actual endpoint-changing
geometric steps, and `GeometricTrace` closes those steps under reflexivity,
composition, and reversal.  An `OpenGeometricCompPath` then records:

* a finite computational trace of admissible geometric steps;
* an arbitrary continuous interval path with the same endpoints; and
* a homotopy coherence witness between the two.

The trace topology observes both computational depth and its geometric
realization.  Consequently, trace realization, composition, and reversal are
continuous.  The universal step system, whose primitive steps are all
continuous paths, shows that this layer contains nonconstant paths between
distinct points; a domain can later replace it by a smaller primitive-step
system without changing the surrounding construction.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

universe u v

/-! ## Endpoint-changing geometric steps -/

/-- A primitive geometric computation system on a topological space. -/
structure GeometricStepSystem (A : Type u) [TopologicalSpace A] (Step : Type v) where
  src : Step → A
  tgt : Step → A
  realize : (s : Step) → _root_.Path (src s) (tgt s)

/-- A finite trace of endpoint-changing geometric computations. -/
inductive GeometricTrace {A : Type u} [TopologicalSpace A] {Step : Type v}
    (S : GeometricStepSystem A Step) : A → A → Type (max u v) where
  | refl (a : A) : GeometricTrace S a a
  | single (s : Step) : GeometricTrace S (S.src s) (S.tgt s)
  | trans {a b c : A} :
      GeometricTrace S a b → GeometricTrace S b c → GeometricTrace S a c
  | symm {a b : A} : GeometricTrace S a b → GeometricTrace S b a

namespace GeometricTrace

variable {A : Type u} [TopologicalSpace A] {Step : Type v}
  {S : GeometricStepSystem A Step}

/-- The continuous path obtained by executing a geometric trace. -/
noncomputable def realize {a b : A} : GeometricTrace S a b → _root_.Path a b
  | .refl a => _root_.Path.refl a
  | .single s => S.realize s
  | .trans p q => _root_.Path.trans (realize p) (realize q)
  | .symm p => _root_.Path.symm (realize p)

/-- Computational depth of a geometric trace. -/
def traceLength {a b : A} : GeometricTrace S a b → Nat
  | .refl _ => 0
  | .single _ => 1
  | .trans p q => traceLength p + traceLength q
  | .symm p => traceLength p

/-- The topological coordinates remembered by a geometric trace. -/
noncomputable def coordinates {a b : A} : GeometricTrace S a b → Nat × _root_.Path a b :=
  fun t => (traceLength t, realize t)

/-!
The induced topology is deliberately richer than the raw trace-length
topology: traces with the same length can still be separated by the geometric
path they execute.
-/
noncomputable instance instTopologicalSpace {a b : A} :
    TopologicalSpace (GeometricTrace S a b) :=
  TopologicalSpace.induced (coordinates : GeometricTrace S a b →
    Nat × _root_.Path a b) inferInstance

theorem continuous_coordinates {a b : A} :
    Continuous (coordinates : GeometricTrace S a b → Nat × _root_.Path a b) :=
  continuous_induced_dom

theorem continuous_traceLength {a b : A} :
    Continuous (traceLength : GeometricTrace S a b → Nat) :=
  continuous_fst.comp (continuous_coordinates (S := S))

theorem continuous_realize {a b : A} :
    Continuous (realize : GeometricTrace S a b → _root_.Path a b) :=
  continuous_snd.comp (continuous_coordinates (S := S))

theorem continuous_nat_add :
    Continuous (fun n : Nat × Nat => n.1 + n.2) :=
  continuous_of_discreteTopology

/-- Trace composition is continuous for the computational/geometric topology. -/
theorem continuous_trans {a b c : A} :
    Continuous
      (fun pq : GeometricTrace S a b × GeometricTrace S b c =>
        GeometricTrace.trans pq.1 pq.2) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun pq : GeometricTrace S a b × GeometricTrace S b c =>
    (traceLength (GeometricTrace.trans pq.1 pq.2),
      realize (GeometricTrace.trans pq.1 pq.2)))
  have hlength :
      Continuous (fun pq : GeometricTrace S a b × GeometricTrace S b c =>
        traceLength pq.1 + traceLength pq.2) :=
    continuous_nat_add.comp
      ((continuous_traceLength (S := S) |>.comp continuous_fst).prodMk
        (continuous_traceLength (S := S) |>.comp continuous_snd))
  have hrealize :
      Continuous (fun pq : GeometricTrace S a b × GeometricTrace S b c =>
        _root_.Path.trans (realize pq.1) (realize pq.2)) :=
    _root_.Path.continuous_trans.comp
      ((continuous_realize (S := S) |>.comp continuous_fst).prodMk
        (continuous_realize (S := S) |>.comp continuous_snd))
  have hlength' :
      Continuous (fun pq : GeometricTrace S a b × GeometricTrace S b c =>
        traceLength (GeometricTrace.trans pq.1 pq.2)) := by
    simpa [GeometricTrace.traceLength] using hlength
  have hrealize' :
      Continuous (fun pq : GeometricTrace S a b × GeometricTrace S b c =>
        realize (GeometricTrace.trans pq.1 pq.2)) := by
    simpa [GeometricTrace.realize] using hrealize
  exact hlength'.prodMk hrealize'

/-- Trace reversal is continuous for the computational/geometric topology. -/
theorem continuous_symm {a b : A} :
    Continuous (fun p : GeometricTrace S a b => GeometricTrace.symm p) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : GeometricTrace S a b =>
    (traceLength (GeometricTrace.symm p), _root_.Path.symm (realize p)))
  have hlength :
      Continuous (fun p : GeometricTrace S a b =>
        traceLength (GeometricTrace.symm p)) := by
    simpa [GeometricTrace.traceLength] using (continuous_traceLength (S := S))
  exact hlength.prodMk
    (_root_.Path.continuous_symm.comp (continuous_realize (S := S)))

/-!
These are computational-path certificates about the trace counter itself.
They keep the geometric layer connected to the repository's `Path` equality
calculus without pretending that an endpoint-changing trace is an equality
proof in `ComputationalPaths.Path a b`.
-/

noncomputable def traceLengthTransPath {a b c : A}
    (p : GeometricTrace S a b) (q : GeometricTrace S b c) :
    ComputationalPaths.Path
      (traceLength (GeometricTrace.trans p q))
      (traceLength p + traceLength q) := by
  change ComputationalPaths.Path (traceLength p + traceLength q)
    (traceLength p + traceLength q)
  exact ComputationalPaths.Path.refl _

noncomputable def traceLengthSymmPath {a b : A}
    (p : GeometricTrace S a b) :
    ComputationalPaths.Path
      (traceLength (GeometricTrace.symm p)) (traceLength p) := by
  change ComputationalPaths.Path (traceLength p) (traceLength p)
  exact ComputationalPaths.Path.refl _

noncomputable def traceLengthReassociationPath {a b c d : A}
    (p : GeometricTrace S a b) (q : GeometricTrace S b c)
    (r : GeometricTrace S c d) :
    ComputationalPaths.Path
      (traceLength (GeometricTrace.trans (GeometricTrace.trans p q) r))
      (traceLength p + (traceLength q + traceLength r)) :=
  ComputationalPaths.Path.trans
    (traceLengthTransPath (GeometricTrace.trans p q) r)
    (ComputationalPaths.Path.trans
      (ComputationalPaths.Path.ofEq rfl)
      (ComputationalPaths.Path.ofEq
        (Nat.add_assoc (traceLength p) (traceLength q) (traceLength r))))

end GeometricTrace

/-! ## Coherent open geometric computational paths -/

/-- A geometric path together with an endpoint-changing computational trace. -/
structure OpenGeometricCompPath {A : Type u} [TopologicalSpace A]
    {Step : Type v} (S : GeometricStepSystem A Step) (a b : A) where
  trace : GeometricTrace S a b
  geometric : _root_.Path a b
  coherent : _root_.Path.Homotopic geometric (GeometricTrace.realize trace)

noncomputable instance openCompPathTopologicalSpace
    {A : Type u} [TopologicalSpace A] {Step : Type v}
    (S : GeometricStepSystem A Step) {a b : A} :
    TopologicalSpace (OpenGeometricCompPath S a b) :=
  TopologicalSpace.induced
    (fun p : OpenGeometricCompPath S a b => (p.trace, p.geometric)) inferInstance

theorem continuous_open_trace {A : Type u} [TopologicalSpace A] {Step : Type v}
    (S : GeometricStepSystem A Step) {a b : A} :
    Continuous (fun p : OpenGeometricCompPath S a b => p.trace) :=
  continuous_fst.comp
    (continuous_induced_dom :
      Continuous (fun p : OpenGeometricCompPath S a b => (p.trace, p.geometric)))

theorem continuous_open_geometric {A : Type u} [TopologicalSpace A] {Step : Type v}
    (S : GeometricStepSystem A Step) {a b : A} :
    Continuous (fun p : OpenGeometricCompPath S a b => p.geometric) :=
  continuous_snd.comp
    (continuous_induced_dom :
      Continuous (fun p : OpenGeometricCompPath S a b => (p.trace, p.geometric)))

theorem continuous_open_realization {A : Type u} [TopologicalSpace A] {Step : Type v}
    (S : GeometricStepSystem A Step) {a b : A} :
    Continuous (fun p : OpenGeometricCompPath S a b => GeometricTrace.realize p.trace) :=
  GeometricTrace.continuous_realize.comp (continuous_open_trace S)

/-- The constant open geometric computational path. -/
noncomputable def openRefl {A : Type u} [TopologicalSpace A] {Step : Type v}
    (S : GeometricStepSystem A Step) (a : A) :
    OpenGeometricCompPath S a a :=
  { trace := GeometricTrace.refl a
    geometric := _root_.Path.refl a
    coherent := by
      change _root_.Path.Homotopic (_root_.Path.refl a) (_root_.Path.refl a)
      exact _root_.Path.Homotopic.refl _ }

/-- A primitive geometric step packaged as a coherent open path. -/
noncomputable def ofGeometricStep {A : Type u} [TopologicalSpace A] {Step : Type v}
    (S : GeometricStepSystem A Step) (s : Step) :
    OpenGeometricCompPath S (S.src s) (S.tgt s) :=
  { trace := GeometricTrace.single s
    geometric := S.realize s
    coherent := by
      change _root_.Path.Homotopic (S.realize s) (S.realize s)
      exact _root_.Path.Homotopic.refl _ }

/-- Concatenation preserves both the geometric path and its computational trace. -/
noncomputable def openTrans {A : Type u} [TopologicalSpace A] {Step : Type v}
    {a b c : A} (S : GeometricStepSystem A Step)
    (p : OpenGeometricCompPath S a b) (q : OpenGeometricCompPath S b c) :
    OpenGeometricCompPath S a c :=
  { trace := GeometricTrace.trans p.trace q.trace
    geometric := _root_.Path.trans p.geometric q.geometric
    coherent := by
      rcases p.coherent with ⟨hp⟩
      rcases q.coherent with ⟨hq⟩
      exact ⟨hp.hcomp hq⟩ }

/-- Reversal preserves both the geometric path and its computational trace. -/
noncomputable def openSymm {A : Type u} [TopologicalSpace A] {Step : Type v}
    {a b : A} (S : GeometricStepSystem A Step)
    (p : OpenGeometricCompPath S a b) :
    OpenGeometricCompPath S b a :=
  { trace := GeometricTrace.symm p.trace
    geometric := _root_.Path.symm p.geometric
    coherent := by
      rcases p.coherent with ⟨hp⟩
      exact ⟨hp.symm₂⟩ }

theorem continuous_openTrans {A : Type u} [TopologicalSpace A] {Step : Type v}
    {a b c : A} (S : GeometricStepSystem A Step) :
    Continuous
      (fun pq : OpenGeometricCompPath S a b × OpenGeometricCompPath S b c =>
        openTrans S pq.1 pq.2) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun pq : OpenGeometricCompPath S a b ×
      OpenGeometricCompPath S b c =>
      (GeometricTrace.trans pq.1.trace pq.2.trace,
        _root_.Path.trans pq.1.geometric pq.2.geometric))
  have htrace :
      Continuous (fun pq : OpenGeometricCompPath S a b ×
        OpenGeometricCompPath S b c =>
        GeometricTrace.trans pq.1.trace pq.2.trace) :=
    (GeometricTrace.continuous_trans (S := S) (a := a) (b := b) (c := c)).comp
      (((continuous_open_trace S (a := a) (b := b)).comp continuous_fst).prodMk
        ((continuous_open_trace S (a := b) (b := c)).comp continuous_snd))
  have hgeometric :
      Continuous (fun pq : OpenGeometricCompPath S a b ×
        OpenGeometricCompPath S b c =>
        _root_.Path.trans pq.1.geometric pq.2.geometric) :=
    (_root_.Path.continuous_trans (x := a) (y := b) (z := c)).comp
      (((continuous_open_geometric S (a := a) (b := b)).comp continuous_fst).prodMk
        ((continuous_open_geometric S (a := b) (b := c)).comp continuous_snd))
  exact htrace.prodMk hgeometric

theorem continuous_openSymm {A : Type u} [TopologicalSpace A] {Step : Type v}
    {a b : A} (S : GeometricStepSystem A Step) :
    Continuous (fun p : OpenGeometricCompPath S a b => openSymm S p) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : OpenGeometricCompPath S a b =>
    (GeometricTrace.symm p.trace, _root_.Path.symm p.geometric))
  exact
    (GeometricTrace.continuous_symm (S := S)).comp (continuous_open_trace S) |>.prodMk
      (_root_.Path.continuous_symm.comp (continuous_open_geometric S))

/-! ## A maximal generic model and a concrete nonconstant witness -/

/-- Every continuous interval path can be used as a primitive geometric step.

This is the maximal generic system.  Applications should normally replace it
with a smaller, domain-specific system whose primitive steps are actual
computational moves (for example, a triangulation, rewriting calculus, or
motion planner).
-/
noncomputable def universalGeometricStepSystem {A : Type u} [TopologicalSpace A] :
    GeometricStepSystem A (Σ x : A, Σ y : A, _root_.Path x y) where
  src s := s.1
  tgt s := s.2.1
  realize s := s.2.2

/-- A continuous path is represented exactly by a single universal step. -/
noncomputable def universalSingle {A : Type u} [TopologicalSpace A]
    {a b : A} (γ : _root_.Path a b) :
    OpenGeometricCompPath (universalGeometricStepSystem (A := A)) a b :=
  ofGeometricStep (universalGeometricStepSystem (A := A)) ⟨a, b, γ⟩

/-- The usual affine path on the real line, including the case of distinct endpoints. -/
noncomputable def realLineSegment (x y : ℝ) : _root_.Path x y :=
  _root_.Path.ofLine (f := fun t : ℝ => x + t * (y - x))
    (by fun_prop) (by ring) (by ring)

/-- A certified open geometric computational path from `0` to `1`. -/
noncomputable def zeroToOne :
    OpenGeometricCompPath
      (universalGeometricStepSystem (A := ℝ)) 0 1 :=
  universalSingle (realLineSegment 0 1)

theorem zeroToOne_exists :
    Nonempty (OpenGeometricCompPath
      (universalGeometricStepSystem (A := ℝ)) 0 1) :=
  ⟨zeroToOne⟩

/-- A compact certificate for the open geometric path construction. -/
structure OpenGeometricPathCertificate {A : Type u} [TopologicalSpace A]
    {Step : Type v} (S : GeometricStepSystem A Step) where
  trace_coordinates_continuous {a b : A} :
    Continuous (GeometricTrace.coordinates (S := S) :
      GeometricTrace S a b → Nat × _root_.Path a b)
  realization_continuous {a b : A} :
    Continuous (GeometricTrace.realize : GeometricTrace S a b → _root_.Path a b)
  trans_continuous {a b c : A} :
    Continuous
      (fun pq : GeometricTrace S a b × GeometricTrace S b c =>
        GeometricTrace.trans pq.1 pq.2)
  symm_continuous {a b : A} :
    Continuous (fun p : GeometricTrace S a b => GeometricTrace.symm p)
  reassociation_path {a b c d : A}
      (p : GeometricTrace S a b) (q : GeometricTrace S b c)
      (r : GeometricTrace S c d) :
      ComputationalPaths.Path
        (GeometricTrace.traceLength
          (GeometricTrace.trans (GeometricTrace.trans p q) r))
        (GeometricTrace.traceLength p +
          (GeometricTrace.traceLength q + GeometricTrace.traceLength r))

noncomputable def openGeometricPathCertificate
    {A : Type u} [TopologicalSpace A] {Step : Type v}
    (S : GeometricStepSystem A Step) : OpenGeometricPathCertificate S where
  trace_coordinates_continuous := GeometricTrace.continuous_coordinates
  realization_continuous := GeometricTrace.continuous_realize
  trans_continuous := GeometricTrace.continuous_trans
  symm_continuous := GeometricTrace.continuous_symm
  reassociation_path := GeometricTrace.traceLengthReassociationPath

end GeometricTopology
end Path
end ComputationalPaths
