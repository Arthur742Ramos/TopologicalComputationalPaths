import ComputationalPaths.Path.Topology.TopologicalCompPathOperations
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Functorial transport of continuous geometric step systems

The total computational-path space is useful only if continuous maps of
ambient spaces transport it functorially.  This file supplies that missing
layer.  A morphism records a continuous ambient map, a map of primitive
steps, endpoint compatibility, and exact compatibility of the chosen
primitive realizations.

The induced maps preserve trace length, map every realized trace by
postcomposition, and are continuous for the observation topologies from the
preceding phases.  They therefore transport identities, composition, and
reversal at the total-carrier level.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

universe u v u' v'

/-! ## Morphisms of continuous step systems -/

structure ContinuousGeometricStepSystemMap
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    {B : Type u'} [TopologicalSpace B]
    {Step' : Type v'} [TopologicalSpace Step']
    (S : ContinuousGeometricStepSystem A Step)
    (T : ContinuousGeometricStepSystem B Step') where
  map : C(A, B)
  stepMap : Step → Step'
  map_src : ∀ s, T.src (stepMap s) = map (S.src s)
  map_tgt : ∀ s, T.tgt (stepMap s) = map (S.tgt s)
  map_realize : ∀ s,
    (S.realize s).map map.continuous =
      (T.realize (stepMap s)).cast (map_src s).symm (map_tgt s).symm

namespace ContinuousGeometricStepSystemMap

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  {B : Type u'} [TopologicalSpace B]
  {Step' : Type v'} [TopologicalSpace Step']
  {S : ContinuousGeometricStepSystem A Step}
  {T : ContinuousGeometricStepSystem B Step'}

/-! Endpoint casts are kept explicit so trace transport does not discard the
endpoint equations supplied by a system morphism. -/

noncomputable def castTrace
    {a b a' b' : A} (ha : a' = a) (hb : b' = b)
    (t : GeometricTrace S.toGeometricStepSystem a b) :
    GeometricTrace S.toGeometricStepSystem a' b' :=
  Eq.mp (by cases ha; cases hb; rfl) t

theorem castTrace_length
    {a b a' b' : A} (ha : a' = a) (hb : b' = b)
    (t : GeometricTrace S.toGeometricStepSystem a b) :
    GeometricTrace.traceLength (castTrace ha hb t) =
      GeometricTrace.traceLength t := by
  cases ha
  cases hb
  rfl

theorem castTrace_realize
    {a b a' b' : A} (ha : a' = a) (hb : b' = b)
    (t : GeometricTrace S.toGeometricStepSystem a b) :
    GeometricTrace.realize (castTrace ha hb t) =
      (GeometricTrace.realize t).cast ha hb := by
  cases ha
  cases hb
  rfl

/-! ## Trace transport -/

noncomputable def mapTrace (M : ContinuousGeometricStepSystemMap S T)
    {a b : A} : GeometricTrace S.toGeometricStepSystem a b →
      GeometricTrace T.toGeometricStepSystem (M.map a) (M.map b)
  | .refl a => .refl (M.map a)
  | .single s =>
      castTrace (M.map_src s).symm (M.map_tgt s).symm
        (GeometricTrace.single (S := T.toGeometricStepSystem) (M.stepMap s))
  | .trans p q => .trans (mapTrace M p) (mapTrace M q)
  | .symm p => .symm (mapTrace M p)

theorem mapTrace_length (M : ContinuousGeometricStepSystemMap S T)
    {a b : A} (t : GeometricTrace S.toGeometricStepSystem a b) :
    GeometricTrace.traceLength (mapTrace M t) =
      GeometricTrace.traceLength t := by
  induction t with
  | refl a => rfl
  | single s =>
      change GeometricTrace.traceLength
          (castTrace (M.map_src s).symm (M.map_tgt s).symm
            (GeometricTrace.single (S := T.toGeometricStepSystem) (M.stepMap s))) =
        GeometricTrace.traceLength (GeometricTrace.single s)
      calc
        _ = GeometricTrace.traceLength
            (GeometricTrace.single (S := T.toGeometricStepSystem) (M.stepMap s)) :=
          castTrace_length (S := T) (M.map_src s).symm (M.map_tgt s).symm
            (GeometricTrace.single (S := T.toGeometricStepSystem) (M.stepMap s))
        _ = 1 := rfl
        _ = GeometricTrace.traceLength (GeometricTrace.single s) := rfl
  | trans p q ihp ihq => simp [mapTrace, GeometricTrace.traceLength, ihp, ihq]
  | symm p ih => simp [mapTrace, GeometricTrace.traceLength, ih]

/-- The preserved trace length is exposed as an actual computational path.

The equality is not left as a bare proposition: the first segment records the
map's length theorem and the second segment records the unchanged target.
This keeps functorial transport connected to the repository's explicit path
calculus.
-/
noncomputable def mapTrace_length_path (M : ContinuousGeometricStepSystemMap S T)
    {a b : A} (t : GeometricTrace S.toGeometricStepSystem a b) :
    ComputationalPaths.Path
      (GeometricTrace.traceLength (mapTrace M t))
      (GeometricTrace.traceLength t) :=
  ComputationalPaths.Path.trans
    (ComputationalPaths.Path.ofEq (mapTrace_length M t))
    (ComputationalPaths.Path.refl (GeometricTrace.traceLength t))

/-- A concrete rewrite step for the unit trace witness used by this map. -/
noncomputable def trace_unit_rewrite (n : Nat) :
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl n)
        (ComputationalPaths.Path.refl n))
      (ComputationalPaths.Path.refl n) :=
  ComputationalPaths.Path.RwEq.step
    (ComputationalPaths.Path.Step.trans_refl_right
      (ComputationalPaths.Path.refl n))

theorem mapTrace_realize (M : ContinuousGeometricStepSystemMap S T)
    {a b : A} (t : GeometricTrace S.toGeometricStepSystem a b) :
    GeometricTrace.realize (mapTrace M t) =
      (GeometricTrace.realize t).map M.map.continuous := by
  induction t with
  | refl a => rfl
  | single s =>
      rw [show GeometricTrace.realize (mapTrace M
          (GeometricTrace.single (S := S.toGeometricStepSystem) s)) =
          (T.realize (M.stepMap s)).cast
            (M.map_src s).symm (M.map_tgt s).symm by
        exact castTrace_realize (S := T) (M.map_src s).symm (M.map_tgt s).symm
          (GeometricTrace.single (S := T.toGeometricStepSystem) (M.stepMap s))]
      exact (M.map_realize s).symm
  | trans p q ihp ihq =>
      simp only [mapTrace, GeometricTrace.realize, Path.map_trans]
      rw [ihp, ihq]
  | symm p ih =>
      simp only [mapTrace, GeometricTrace.realize]
      rw [ih]
      exact _root_.Path.map_symm _ _

/-! ## Transport of open and total paths -/

noncomputable def mapOpen (M : ContinuousGeometricStepSystemMap S T)
    {a b : A} (p : OpenGeometricCompPath S.toGeometricStepSystem a b) :
    OpenGeometricCompPath T.toGeometricStepSystem (M.map a) (M.map b) :=
  { trace := mapTrace M p.trace
    geometric := p.geometric.map M.map.continuous
    coherent := by
      rcases p.coherent with ⟨hp⟩
      refine ⟨?_⟩
      rw [mapTrace_realize M p.trace]
      exact hp.map M.map }

theorem mapOpen_geometric (M : ContinuousGeometricStepSystemMap S T)
    {a b : A} (p : OpenGeometricCompPath S.toGeometricStepSystem a b) :
    (mapOpen M p).geometric = p.geometric.map M.map.continuous :=
  rfl

theorem continuous_mapTrace (M : ContinuousGeometricStepSystemMap S T)
    {a b : A} :
    Continuous
      (mapTrace M : GeometricTrace S.toGeometricStepSystem a b →
        GeometricTrace T.toGeometricStepSystem (M.map a) (M.map b)) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun t =>
    (GeometricTrace.traceLength (mapTrace M t),
      GeometricTrace.realize (mapTrace M t)))
  have hlength : Continuous (fun t : GeometricTrace S.toGeometricStepSystem a b =>
      GeometricTrace.traceLength (mapTrace M t)) := by
    simpa [mapTrace_length M] using
      (GeometricTrace.continuous_traceLength
        (S := S.toGeometricStepSystem) (a := a) (b := b))
  have hrealize : Continuous (fun t : GeometricTrace S.toGeometricStepSystem a b =>
      GeometricTrace.realize (mapTrace M t)) := by
    rw [show (fun t => GeometricTrace.realize (mapTrace M t)) =
      (fun t => (GeometricTrace.realize t).map M.map.continuous) by
        funext t; exact mapTrace_realize M t]
    apply continuous_induced_rng.mpr
    change Continuous (fun t =>
      M.map.comp (GeometricTrace.realize t).toContinuousMap)
    exact (ContinuousMap.continuous_postcomp M.map).comp
      (continuous_induced_dom.comp
        (GeometricTrace.continuous_realize
          (S := S.toGeometricStepSystem) (a := a) (b := b)))
  exact hlength.prodMk hrealize

theorem continuous_mapOpen (M : ContinuousGeometricStepSystemMap S T)
    {a b : A} :
    Continuous
      (mapOpen M : OpenGeometricCompPath S.toGeometricStepSystem a b →
        OpenGeometricCompPath T.toGeometricStepSystem (M.map a) (M.map b)) := by
  apply continuous_induced_rng.mpr
  unfold mapOpen
  change Continuous (fun p : OpenGeometricCompPath
    S.toGeometricStepSystem a b => (mapTrace M p.trace,
      p.geometric.map M.map.continuous))
  have htrace : Continuous (fun p : OpenGeometricCompPath
      S.toGeometricStepSystem a b => mapTrace M p.trace) :=
    (continuous_mapTrace (M := M) (a := a) (b := b)).comp
      (continuous_open_trace S.toGeometricStepSystem (a := a) (b := b))
  have hgeom : Continuous (fun p : OpenGeometricCompPath
      S.toGeometricStepSystem a b => p.geometric.map M.map.continuous) := by
    apply continuous_induced_rng.mpr
    change Continuous (fun p : OpenGeometricCompPath
      S.toGeometricStepSystem a b => M.map.comp p.geometric.toContinuousMap)
    exact (ContinuousMap.continuous_postcomp M.map).comp
      (continuous_induced_dom.comp
        (continuous_open_geometric S.toGeometricStepSystem))
  exact htrace.prodMk hgeom

noncomputable def mapTotal (M : ContinuousGeometricStepSystemMap S T)
    (p : TotalOpenGeometricCompPath A Step S) :
    TotalOpenGeometricCompPath B Step' T :=
  ⟨M.map p.src, M.map p.tgt, mapOpen M p.path⟩

theorem mapTotal_src (M : ContinuousGeometricStepSystemMap S T)
    (p : TotalOpenGeometricCompPath A Step S) :
    (mapTotal M p).src = M.map p.src :=
  rfl

theorem mapTotal_tgt (M : ContinuousGeometricStepSystemMap S T)
    (p : TotalOpenGeometricCompPath A Step S) :
    (mapTotal M p).tgt = M.map p.tgt :=
  rfl

theorem mapTotal_traceLength (M : ContinuousGeometricStepSystemMap S T)
    (p : TotalOpenGeometricCompPath A Step S) :
    GeometricTrace.traceLength (mapTotal M p).trace =
      GeometricTrace.traceLength p.trace :=
  mapTrace_length M p.trace

theorem mapTotal_traceMap (M : ContinuousGeometricStepSystemMap S T)
    (p : TotalOpenGeometricCompPath A Step S) :
    (mapTotal M p).traceMap T =
      M.map.comp (p.traceMap S) := by
  apply ContinuousMap.ext
  intro t
  change GeometricTrace.realize (mapTrace M p.trace) t =
    M.map (GeometricTrace.realize p.trace t)
  rw [mapTrace_realize M p.trace]
  rfl

theorem mapTotal_geometricMap (M : ContinuousGeometricStepSystemMap S T)
    (p : TotalOpenGeometricCompPath A Step S) :
    (mapTotal M p).geometricMap T = M.map.comp (p.geometricMap S) := by
  apply ContinuousMap.ext
  intro t
  rfl

theorem continuous_mapTotal (M : ContinuousGeometricStepSystemMap S T) :
    Continuous (mapTotal M :
      TotalOpenGeometricCompPath A Step S →
        TotalOpenGeometricCompPath B Step' T) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p =>
    (M.map p.src, (M.map p.tgt,
      (GeometricTrace.traceLength (mapTotal M p).trace,
        ((mapTotal M p).traceMap T, (mapTotal M p).geometricMap T)))))
  have hsrc : Continuous (fun p : TotalOpenGeometricCompPath A Step S =>
      M.map p.src) := M.map.continuous.comp (TotalOpenGeometricCompPath.continuous_src S)
  have htgt : Continuous (fun p : TotalOpenGeometricCompPath A Step S =>
      M.map p.tgt) := M.map.continuous.comp (TotalOpenGeometricCompPath.continuous_tgt S)
  have hlength : Continuous (fun p : TotalOpenGeometricCompPath A Step S =>
      GeometricTrace.traceLength (mapTotal M p).trace) := by
    simpa only [mapTotal_traceLength M] using
      (TotalOpenGeometricCompPath.continuous_traceLength S)
  have htrace : Continuous (fun p : TotalOpenGeometricCompPath A Step S =>
      (mapTotal M p).traceMap T) := by
    rw [show (fun p => (mapTotal M p).traceMap T) =
      (fun p => M.map.comp (p.traceMap S)) by
        funext p; exact mapTotal_traceMap M p]
    exact (ContinuousMap.continuous_postcomp M.map).comp
      (TotalOpenGeometricCompPath.continuous_traceMap S)
  have hgeom : Continuous (fun p : TotalOpenGeometricCompPath A Step S =>
      (mapTotal M p).geometricMap T) := by
    rw [show (fun p => (mapTotal M p).geometricMap T) =
      (fun p => M.map.comp (p.geometricMap S)) by
        funext p; exact mapTotal_geometricMap M p]
    exact (ContinuousMap.continuous_postcomp M.map).comp
      (TotalOpenGeometricCompPath.continuous_geometricMap S)
  exact hsrc.prodMk (htgt.prodMk (hlength.prodMk (htrace.prodMk hgeom)))

/-! ## Transported algebraic operations -/

theorem mapOpen_refl (M : ContinuousGeometricStepSystemMap S T) (a : A) :
    mapOpen M (openRefl S.toGeometricStepSystem a) =
      openRefl T.toGeometricStepSystem (M.map a) := by
  rfl

theorem openCompPath_ext
    {a b : A} {p q : OpenGeometricCompPath S.toGeometricStepSystem a b}
    (htrace : p.trace = q.trace) (hgeometric : p.geometric = q.geometric) :
    p = q := by
  cases p
  cases q
  cases htrace
  cases hgeometric
  rfl

theorem mapOpen_trans (M : ContinuousGeometricStepSystemMap S T)
    {a b c : A} (p : OpenGeometricCompPath S.toGeometricStepSystem a b)
    (q : OpenGeometricCompPath S.toGeometricStepSystem b c) :
    mapOpen M (openTrans S.toGeometricStepSystem p q) =
      openTrans T.toGeometricStepSystem (mapOpen M p) (mapOpen M q) := by
  apply openCompPath_ext
  · rfl
  · exact _root_.Path.map_trans p.geometric q.geometric M.map.continuous

theorem mapOpen_symm (M : ContinuousGeometricStepSystemMap S T)
    {a b : A} (p : OpenGeometricCompPath S.toGeometricStepSystem a b) :
    mapOpen M (openSymm S.toGeometricStepSystem p) =
      openSymm T.toGeometricStepSystem (mapOpen M p) := by
  apply openCompPath_ext
  · rfl
  · exact _root_.Path.map_symm p.geometric M.map.continuous

/-! ## A compact functoriality certificate -/

structure Certificate (M : ContinuousGeometricStepSystemMap S T) where
  total_continuous : Continuous (mapTotal M)
  trace_length_preserved : ∀ (p : TotalOpenGeometricCompPath A Step S),
    GeometricTrace.traceLength (mapTotal M p).trace =
      GeometricTrace.traceLength p.trace
  trace_length_path : ∀ (p : TotalOpenGeometricCompPath A Step S),
    ComputationalPaths.Path
      (GeometricTrace.traceLength (mapTotal M p).trace)
      (GeometricTrace.traceLength p.trace)
  trace_unit_rewrite : ∀ n : Nat,
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl n)
        (ComputationalPaths.Path.refl n))
      (ComputationalPaths.Path.refl n)
  identity_preserved : ∀ a, mapOpen M (openRefl S.toGeometricStepSystem a) =
    openRefl T.toGeometricStepSystem (M.map a)
  composition_preserved : ∀ {a b c} (p : OpenGeometricCompPath
    S.toGeometricStepSystem a b) (q : OpenGeometricCompPath
    S.toGeometricStepSystem b c),
    mapOpen M (openTrans S.toGeometricStepSystem p q) =
      openTrans T.toGeometricStepSystem (mapOpen M p) (mapOpen M q)
  reversal_preserved : ∀ {a b} (p : OpenGeometricCompPath
    S.toGeometricStepSystem a b),
    mapOpen M (openSymm S.toGeometricStepSystem p) =
      openSymm T.toGeometricStepSystem (mapOpen M p)

noncomputable def certificate (M : ContinuousGeometricStepSystemMap S T) :
    Certificate M where
  total_continuous := continuous_mapTotal M
  trace_length_preserved := mapTotal_traceLength M
  trace_length_path := fun p => mapTrace_length_path M p.trace
  trace_unit_rewrite := trace_unit_rewrite
  identity_preserved := by
    intro a
    simpa using mapOpen_refl M a
  composition_preserved := by
    intro a b c p q
    exact mapOpen_trans M p q
  reversal_preserved := by
    intro a b p
    exact mapOpen_symm M p

end ContinuousGeometricStepSystemMap
end GeometricTopology
end Path
end ComputationalPaths
