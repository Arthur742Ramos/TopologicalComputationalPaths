import ComputationalPaths.Path.Topology.TopologicalCompPathOperations
import ComputationalPaths.Path.Rewrite.RwEq
import Mathlib.Data.Fin.Rev
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Trace-sensitive topology for endpoint-varying computational paths

The standard total carrier in TotalGeometricComputationalPath is induced by
the observable semantic code: endpoints, trace length, trace realization, and
the chosen geometric representative.  That topology is intentionally useful
for the quotient semantics, but it does not expose the complete computational
word.

This file adds the complementary topology suggested by the flat-word model in
the topological semantics paper.  A parenthesized GeometricTrace is flattened
to a finite word in signed primitive steps.  The word carrier is the genuine
coproduct of finite coordinate spaces

Σ n, (Fin n → (Step ⊕ Step)).

The new topology is induced by the pair

(full signed word, observable semantic code).

Thus it is trace-sensitive while retaining all coordinates used by the
observable construction.  The identity from the trace-sensitive topology to
the observable topology is proved continuous.  Identity, composition, and
reversal are proved continuous for the new topology as well, and the
computation carries explicit Path/RwEq certificates for the length and
unit coherences.

Parenthesization is not made topological data: flattening identifies the
structural unit/associativity presentation with the flat-word strictification,
while signed leaves retain the actual primitive-step word and its orientation.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

universe u v

/-! ## Flat signed words -/

/-- A primitive step together with its orientation. -/
abbrev SignedStep (Step : Type v) := Step ⊕ Step

/-- The flat coproduct of finite signed words. -/
abbrev FlatWord (Step : Type v) := Σ n : Nat, Fin n → SignedStep Step

/-- Toggle the orientation of a signed primitive step. -/
def signedStepSymm {Step : Type v} : SignedStep Step → SignedStep Step
  | Sum.inl s => Sum.inr s
  | Sum.inr s => Sum.inl s

theorem continuous_signedStepSymm {Step : Type v} [TopologicalSpace Step] :
    Continuous (@signedStepSymm Step) := by
  have h : signedStepSymm =
      Sum.elim (Sum.inr : Step → SignedStep Step)
        (Sum.inl : Step → SignedStep Step) := by
    funext s
    cases s <;> rfl
  rw [h]
  exact continuous_sumElim.2 ⟨continuous_inr, continuous_inl⟩

/-- Concatenate two flat words.  Endpoint composability is imposed by the
composable carrier; the ambient operation is useful for continuity proofs. -/
def flatWordTrans {Step : Type v} (u v : FlatWord Step) : FlatWord Step :=
  ⟨u.1 + v.1, Fin.append u.2 v.2⟩

/-- Reverse a flat word and toggle every orientation. -/
def flatWordSymm {Step : Type v} (u : FlatWord Step) : FlatWord Step :=
  ⟨u.1, fun i => signedStepSymm (u.2 i.rev)⟩

/-- A map out of a product of two sigma spaces can be checked componentwise.
This is the finite-stratum argument used for flat word concatenation. -/
theorem continuous_prod_sigma
    {ι κ : Type*} {X : ι → Type*} {Y : κ → Type*}
    {Z : Type*} [∀ i, TopologicalSpace (X i)]
    [∀ j, TopologicalSpace (Y j)] [TopologicalSpace Z]
    {f : Sigma X × Sigma Y → Z}
    (hf : ∀ i j, Continuous (fun xy : X i × Y j =>
      f (⟨i, xy.1⟩, ⟨j, xy.2⟩))) :
    Continuous f := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨⟨i, x⟩, ⟨j, y⟩⟩
  have h : ContinuousAt (fun xy : X i × Y j =>
      f (⟨i, xy.1⟩, ⟨j, xy.2⟩)) (x, y) :=
    (hf i j).continuousAt
  rw [ContinuousAt, nhds_prod_eq] at h
  rw [ContinuousAt, nhds_prod_eq, Sigma.nhds_mk, Sigma.nhds_mk,
    Filter.prod_map_map_eq]
  rw [Filter.tendsto_map'_iff]
  exact h

theorem continuous_flatWordTrans {Step : Type v} [TopologicalSpace Step] :
    Continuous (fun uv : FlatWord Step × FlatWord Step =>
      flatWordTrans uv.1 uv.2) := by
  apply continuous_prod_sigma
  intro m n
  have hmk : Continuous (fun w : Fin (m + n) → SignedStep Step =>
      (⟨m + n, w⟩ : FlatWord Step)) :=
    (continuous_sigmaMk (ι := Nat)
      (σ := fun k => Fin k → SignedStep Step) (i := m + n))
  convert hmk.comp (Fin.continuous_append m n) using 1
  funext uv
  rfl

theorem continuous_flatWordSymm {Step : Type v} [TopologicalSpace Step] :
    Continuous (flatWordSymm : FlatWord Step → FlatWord Step) := by
  apply continuous_sigma
  intro n
  change Continuous (fun w : Fin n → SignedStep Step =>
    (⟨n, fun i => signedStepSymm (w i.rev)⟩ : FlatWord Step))
  apply continuous_sigmaMk.comp
  apply continuous_pi
  intro i
  exact continuous_signedStepSymm.comp (continuous_apply i.rev)

theorem continuous_flatWordLength {Step : Type v} [TopologicalSpace Step] :
    Continuous (fun w : FlatWord Step => w.1) := by
  apply continuous_sigma
  intro n
  exact continuous_const

/-! ## Flattening parenthesized traces -/

namespace GeometricTrace

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v}
  {S : GeometricStepSystem A Step}

/-- The flat signed-word image of a parenthesized geometric trace. -/
def flatWord {a b : A} : GeometricTrace S a b → FlatWord Step
  | .refl _ => ⟨0, fun i => Fin.elim0 i⟩
  | .single s => ⟨1, fun _ => Sum.inl s⟩
  | .trans p q =>
      let wp := flatWord p
      let wq := flatWord q
      ⟨wp.1 + wq.1, Fin.append wp.2 wq.2⟩
  | .symm p =>
      let w := flatWord p
      ⟨w.1, fun i => signedStepSymm (w.2 i.rev)⟩

@[simp] theorem flatWord_refl (a : A) :
    flatWord (GeometricTrace.refl a : GeometricTrace S a a) =
      (⟨0, fun i => Fin.elim0 i⟩ : FlatWord Step) :=
  rfl

@[simp] theorem flatWord_single (s : Step) :
    flatWord (GeometricTrace.single (S := S) s) =
      (⟨1, fun _ => Sum.inl s⟩ : FlatWord Step) :=
  rfl

@[simp] theorem flatWord_trans {a b c : A}
    (p : GeometricTrace S a b) (q : GeometricTrace S b c) :
    flatWord (GeometricTrace.trans p q) =
      flatWordTrans (flatWord p) (flatWord q) :=
  rfl

@[simp] theorem flatWord_symm {a b : A}
    (p : GeometricTrace S a b) :
    flatWord (GeometricTrace.symm p) = flatWordSymm (flatWord p) :=
  rfl

@[simp] theorem flatWord_length {a b : A}
    (p : GeometricTrace S a b) :
    (flatWord p).1 = GeometricTrace.traceLength p := by
  induction p with
  | refl a => rfl
  | single s => rfl
  | trans p q ihp ihq =>
      simp [flatWordTrans, GeometricTrace.traceLength, ihp, ihq]
  | symm p ih =>
      simp [flatWordSymm, GeometricTrace.traceLength, ih]

end GeometricTrace

/-! ## The two endpoint-varying topologies -/

namespace TotalOpenGeometricCompPath

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  (S : ContinuousGeometricStepSystem A Step)

/-- The trace-sensitive code contains the complete flat signed word and the
existing observable code.  The second coordinate is retained so that the
trace-sensitive topology is a refinement, rather than a replacement, of the
observable semantic topology. -/
abbrev TraceSensitiveObservation :=
  FlatWord Step × Observation (A := A)

noncomputable def traceSensitiveObservation
    (p : TotalOpenGeometricCompPath A Step S) :
    TraceSensitiveObservation (A := A) (Step := Step) :=
  (GeometricTrace.flatWord p.trace, observation S p)

noncomputable def traceSensitiveTopologicalSpace :
    TopologicalSpace (TotalOpenGeometricCompPath A Step S) :=
  TopologicalSpace.induced (traceSensitiveObservation S) inferInstance

theorem continuous_traceSensitiveObservation :
    @Continuous (TotalOpenGeometricCompPath A Step S)
      (TraceSensitiveObservation (A := A) (Step := Step))
      (traceSensitiveTopologicalSpace S) inferInstance
      (traceSensitiveObservation S) :=
  continuous_induced_dom

theorem continuous_traceSensitive_to_observable :
    @Continuous (TotalOpenGeometricCompPath A Step S)
      (TotalOpenGeometricCompPath A Step S)
      (traceSensitiveTopologicalSpace S) inferInstance
      id := by
  apply continuous_induced_rng.mpr
  have hcode :
      @Continuous (TotalOpenGeometricCompPath A Step S)
        (TraceSensitiveObservation (A := A) (Step := Step))
        (traceSensitiveTopologicalSpace S) inferInstance
        (traceSensitiveObservation S) :=
    continuous_traceSensitiveObservation S
  have hobs :
      Continuous (fun z : TraceSensitiveObservation
        (A := A) (Step := Step) => z.2) :=
    continuous_snd
  simpa [Function.comp_def, traceSensitiveObservation] using
    (@Continuous.comp _ _ _ (traceSensitiveTopologicalSpace S)
      inferInstance inferInstance _ _ hobs hcode)

theorem continuous_traceSensitive_from_observable
    {Y : Type*} [TopologicalSpace Y] {f : TotalOpenGeometricCompPath A Step S → Y}
    (hf : Continuous f) :
    @Continuous (TotalOpenGeometricCompPath A Step S) Y
      (traceSensitiveTopologicalSpace S) inferInstance f := by
  exact @Continuous.comp _ _ _ (traceSensitiveTopologicalSpace S)
    inferInstance inferInstance _ _ hf
      (continuous_traceSensitive_to_observable S)

theorem continuous_traceSensitive_src :
    @Continuous (TotalOpenGeometricCompPath A Step S) A
      (traceSensitiveTopologicalSpace S) inferInstance
      (fun p => p.src) := by
  exact continuous_traceSensitive_from_observable S
    (TotalOpenGeometricCompPath.continuous_src S)

theorem continuous_traceSensitive_tgt :
    @Continuous (TotalOpenGeometricCompPath A Step S) A
      (traceSensitiveTopologicalSpace S) inferInstance
      (fun p => p.tgt) := by
  exact continuous_traceSensitive_from_observable S
    (TotalOpenGeometricCompPath.continuous_tgt S)

theorem continuous_traceSensitive_flatWord :
    @Continuous (TotalOpenGeometricCompPath A Step S) (FlatWord Step)
      (traceSensitiveTopologicalSpace S) inferInstance
      (fun p => GeometricTrace.flatWord p.trace) := by
  exact @Continuous.comp _ _ _ (traceSensitiveTopologicalSpace S)
    inferInstance inferInstance _ _ continuous_fst
    (continuous_traceSensitiveObservation S)

theorem continuous_traceSensitiveLength :
    @Continuous (TotalOpenGeometricCompPath A Step S) Nat
      (traceSensitiveTopologicalSpace S) inferInstance
      (fun p => GeometricTrace.traceLength p.trace) := by
  have hflat :
      @Continuous (TotalOpenGeometricCompPath A Step S) Nat
        (traceSensitiveTopologicalSpace S) inferInstance
        (fun p => (GeometricTrace.flatWord p.trace).1) :=
    @Continuous.comp _ _ _ (traceSensitiveTopologicalSpace S)
      inferInstance inferInstance _ _ continuous_flatWordLength
      (continuous_traceSensitive_flatWord S)
  simpa only [Function.comp_apply, GeometricTrace.flatWord_length] using hflat

/-! ## Full trace realization bridge -/

/-- The complete trace realization remains continuous after the full signed
word is made a topological coordinate.  The codomain is the compact-open
continuous-map space, which is the non-dependent form of the interval-path
space used by the manuscript. -/
theorem continuous_fullTraceRealization :
    @Continuous (TotalOpenGeometricCompPath A Step S)
      (C(unitInterval, A))
      (traceSensitiveTopologicalSpace S) inferInstance
      (fun p => (GeometricTrace.realize p.trace).toContinuousMap) := by
  exact continuous_traceSensitive_from_observable S (continuous_traceMap S)

/-- The trace-sensitive family-level realization is continuous, so evaluation
at any interval parameter is continuous as well. -/
theorem continuous_fullTraceRealizationFamily :
    Continuous ↿(fun p : TotalOpenGeometricCompPath A Step S =>
      GeometricTrace.realize p.trace) := by
  exact continuous_traceFamily S

/-! ## Quotient comparison for the two representative topologies -/

namespace TraceSensitiveQuotient

/-- The quotient topology induced by an explicitly supplied representative
topology.  The explicit parameter is important: the same setoid can be
quotiented from both the observable and trace-sensitive carriers. -/
noncomputable def quotientTopology {α : Type*} (r : Setoid α)
    (τ : TopologicalSpace α) : TopologicalSpace (Quotient r) :=
  TopologicalSpace.coinduced (Quotient.mk r) τ

theorem quotientMk_isQuotient {α : Type*} (r : Setoid α)
    (τ : TopologicalSpace α) :
    @Topology.IsQuotientMap α (Quotient r) τ
      (quotientTopology r τ) (Quotient.mk r) := by
  exact ⟨⟨rfl⟩, Quotient.mk_surjective⟩

/-- A continuous refinement of representative topologies induces a continuous
map between the corresponding quotient topologies.  This is the abstract
quotient mechanism behind the map from the trace-sensitive scoped quotient to
the observable scoped quotient. -/
theorem continuous_quotientComparison {α : Type*} (r : Setoid α)
    {τtr τobs : TopologicalSpace α}
    (hcoarse : @Continuous α α τtr τobs id) :
    @Continuous (Quotient r) (Quotient r)
      (quotientTopology r τtr) (quotientTopology r τobs) id := by
  have hq : @Topology.IsQuotientMap α (Quotient r)
      τtr (quotientTopology r τtr) (Quotient.mk r) :=
    quotientMk_isQuotient r τtr
  apply (@Topology.IsQuotientMap.continuous_iff α (Quotient r)
    (Quotient r) (Quotient.mk r) id τtr
    (quotientTopology r τtr) (quotientTopology r τobs) hq).2
  have hqobs : @Continuous α (Quotient r) τobs
      (quotientTopology r τobs) (Quotient.mk r) :=
    continuous_coinduced_rng
  exact @Continuous.comp α α (Quotient r) τtr τobs
    (quotientTopology r τobs) id (Quotient.mk r) hqobs hcoarse

/-- A continuous representative section identifies the two quotient
topologies.  This is the abstract form of the universal-presentation
collapse: the coarse quotient can continuously choose a representative in the
trace-sensitive carrier, while the trace-sensitive topology continuously
coarsens to the observable one. -/
noncomputable def quotientComparisonHomeomorph_of_section
    {α : Type*} (r : Setoid α)
    {τtr τobs : TopologicalSpace α}
    (hcoarse : @Continuous α α τtr τobs id)
    (choose : Quotient r → α)
    (hsection : @Continuous (Quotient r) α
      (quotientTopology r τobs) τtr choose)
    (hsection_rightInverse : Function.RightInverse choose (Quotient.mk r)) :
    @Homeomorph (Quotient r) (Quotient r)
      (quotientTopology r τtr) (quotientTopology r τobs) := by
  have hforward :
      @Continuous (Quotient r) (Quotient r)
        (quotientTopology r τtr) (quotientTopology r τobs) id :=
    continuous_quotientComparison r hcoarse
  have hback_raw :
        @Continuous α (Quotient r) τobs (quotientTopology r τtr)
        (fun x => Quotient.mk r (choose (Quotient.mk r x))) := by
    have hqtr :
        @Continuous α (Quotient r) τtr (quotientTopology r τtr)
          (Quotient.mk r) := continuous_coinduced_rng
    have hqobs :
        @Continuous α (Quotient r) τobs (quotientTopology r τobs)
          (Quotient.mk r) := continuous_coinduced_rng
    have hchoose :
        @Continuous α α τobs τtr
          (fun x => choose (Quotient.mk r x)) := by
      exact @Continuous.comp α (Quotient r) α
        τobs (quotientTopology r τobs) τtr
        (Quotient.mk r) choose hsection hqobs
    exact @Continuous.comp α α (Quotient r)
      τobs τtr (quotientTopology r τtr)
      (fun x => choose (Quotient.mk r x)) (Quotient.mk r)
      hqtr hchoose
  have hback_raw_eq :
      @Continuous α (Quotient r) τobs (quotientTopology r τtr)
        (Quotient.mk r) := by
    convert hback_raw using 1
    funext x
    exact (hsection_rightInverse (Quotient.mk r x)).symm
  have hback :
      @Continuous (Quotient r) (Quotient r)
        (quotientTopology r τobs) (quotientTopology r τtr) id := by
    have hq : @Topology.IsQuotientMap α (Quotient r)
        τobs (quotientTopology r τobs) (Quotient.mk r) :=
      quotientMk_isQuotient r τobs
    apply (@Topology.IsQuotientMap.continuous_iff α (Quotient r)
      (Quotient r) (Quotient.mk r) id τobs
      (quotientTopology r τobs) (quotientTopology r τtr) hq).2
    exact hback_raw_eq
  exact @Homeomorph.mk (Quotient r) (Quotient r)
    (quotientTopology r τtr) (quotientTopology r τobs)
    (Equiv.refl _) hforward hback

/-- The same collapse criterion with an intermediate semantic space.  A
continuous realization map from the observable carrier and a continuous
representative section into the trace-sensitive carrier suffice when the
section represents each point in the same quotient class. -/
noncomputable def quotientComparisonHomeomorph_of_realization_section
    {α : Type*} (r : Setoid α)
    {τtr τobs : TopologicalSpace α}
    {C : Type*} {τC : TopologicalSpace C}
    (hcoarse : @Continuous α α τtr τobs id)
    (realize : α → C)
    (choose : C → α)
    (hrealize : @Continuous α C τobs τC realize)
    (hchoose : @Continuous C α τC τtr choose)
    (hfactor : ∀ x : α,
      Quotient.mk r (choose (realize x)) = Quotient.mk r x) :
    @Homeomorph (Quotient r) (Quotient r)
      (quotientTopology r τtr) (quotientTopology r τobs) := by
  have hforward :
      @Continuous (Quotient r) (Quotient r)
        (quotientTopology r τtr) (quotientTopology r τobs) id :=
    continuous_quotientComparison r hcoarse
  have hqtr :
      @Continuous α (Quotient r) τtr (quotientTopology r τtr)
        (Quotient.mk r) := continuous_coinduced_rng
  have hraw :
      @Continuous α (Quotient r) τobs (quotientTopology r τtr)
        (fun x => Quotient.mk r (choose (realize x))) := by
    have hchoose_realize :
        @Continuous α α τobs τtr (choose ∘ realize) :=
      @Continuous.comp α C α τobs τC τtr realize choose
        hchoose hrealize
    exact @Continuous.comp α α (Quotient r)
      τobs τtr (quotientTopology r τtr)
      (choose ∘ realize) (Quotient.mk r) hqtr hchoose_realize
  have hraw_eq :
      @Continuous α (Quotient r) τobs (quotientTopology r τtr)
        (Quotient.mk r) := by
    convert hraw using 1
    funext x
    exact (hfactor x).symm
  have hback :
      @Continuous (Quotient r) (Quotient r)
        (quotientTopology r τobs) (quotientTopology r τtr) id := by
    have hq : @Topology.IsQuotientMap α (Quotient r)
        τobs (quotientTopology r τobs) (Quotient.mk r) :=
      quotientMk_isQuotient r τobs
    apply (@Topology.IsQuotientMap.continuous_iff α (Quotient r)
      (Quotient r) (Quotient.mk r) id τobs
      (quotientTopology r τobs) (quotientTopology r τtr) hq).2
    exact hraw_eq
  exact @Homeomorph.mk (Quotient r) (Quotient r)
    (quotientTopology r τtr) (quotientTopology r τobs)
    (Equiv.refl _) hforward hback

end TraceSensitiveQuotient

/-! ## Trace-sensitive composable pairs -/

abbrev TraceSensitiveComposableObservation :=
  FlatWord Step × (FlatWord Step × TotalComposable.Observation (A := A))

noncomputable def traceSensitiveComposableObservation
    (c : TotalComposable A Step S) :
    TraceSensitiveComposableObservation (A := A) (Step := Step) :=
  (GeometricTrace.flatWord c.left.trace,
    (GeometricTrace.flatWord c.right.trace, TotalComposable.observation S c))

noncomputable def traceSensitiveComposableTopologicalSpace :
    TopologicalSpace (TotalComposable A Step S) :=
  TopologicalSpace.induced (traceSensitiveComposableObservation S) inferInstance

theorem continuous_traceSensitiveComposableObservation :
    @Continuous (TotalComposable A Step S)
      (TraceSensitiveComposableObservation (A := A) (Step := Step))
      (traceSensitiveComposableTopologicalSpace S) inferInstance
      (traceSensitiveComposableObservation S) :=
  continuous_induced_dom

theorem continuous_traceSensitiveComposable_to_observable :
    @Continuous (TotalComposable A Step S) (TotalComposable A Step S)
      (traceSensitiveComposableTopologicalSpace S) inferInstance
      id := by
  apply continuous_induced_rng.mpr
  have hcode := continuous_traceSensitiveComposableObservation S
  have hobs :
      Continuous (fun z : TraceSensitiveComposableObservation
        (A := A) (Step := Step) => z.2.2) := by
    exact continuous_snd.comp continuous_snd
  simpa [Function.comp_def, traceSensitiveComposableObservation] using
    (@Continuous.comp _ _ _ (traceSensitiveComposableTopologicalSpace S)
      inferInstance inferInstance _ _ hobs hcode)

theorem continuous_traceSensitiveComposable_from_observable
    {Y : Type*} [TopologicalSpace Y]
    {f : TotalComposable A Step S → Y} (hf : Continuous f) :
    @Continuous (TotalComposable A Step S) Y
      (traceSensitiveComposableTopologicalSpace S) inferInstance f := by
  exact @Continuous.comp _ _ _ (traceSensitiveComposableTopologicalSpace S)
    inferInstance inferInstance _ _ hf
    (continuous_traceSensitiveComposable_to_observable S)

theorem continuous_traceSensitiveComposable_leftFlat :
    @Continuous (TotalComposable A Step S) (FlatWord Step)
      (traceSensitiveComposableTopologicalSpace S) inferInstance
      (fun c => GeometricTrace.flatWord c.left.trace) := by
  exact @Continuous.comp _ _ _ (traceSensitiveComposableTopologicalSpace S)
    inferInstance inferInstance _ _ continuous_fst
    (continuous_traceSensitiveComposableObservation S)

theorem continuous_traceSensitiveComposable_rightFlat :
    @Continuous (TotalComposable A Step S) (FlatWord Step)
      (traceSensitiveComposableTopologicalSpace S) inferInstance
      (fun c => GeometricTrace.flatWord c.right.trace) := by
  exact @Continuous.comp _ _ _ (traceSensitiveComposableTopologicalSpace S)
    inferInstance inferInstance _ _ continuous_fst
    (@Continuous.comp _ _ _ (traceSensitiveComposableTopologicalSpace S)
      inferInstance inferInstance _ _ continuous_snd
      (continuous_traceSensitiveComposableObservation S))

/-! ## Operations for the trace-sensitive topology -/

theorem continuous_traceSensitive_totalRefl :
    @Continuous A (TotalOpenGeometricCompPath A Step S)
      inferInstance (traceSensitiveTopologicalSpace S)
      (totalRefl S) := by
  apply continuous_induced_rng.mpr
  have hobs :
      Continuous (fun a : A => observation S (totalRefl S a)) :=
    (TotalOpenGeometricCompPath.continuous_observation S).comp
      (TotalOpenGeometricCompPath.continuous_totalRefl S)
  change Continuous (fun a : A =>
    (GeometricTrace.flatWord (totalRefl S a).trace,
      observation S (totalRefl S a)))
  have hflat : Continuous (fun a : A =>
      GeometricTrace.flatWord (totalRefl S a).trace) := by
    have heq : (fun a : A =>
        GeometricTrace.flatWord (totalRefl S a).trace) =
        (fun _ : A => (⟨0, fun i => Fin.elim0 i⟩ : FlatWord Step)) := by
      funext a
      simp [totalRefl, TotalOpenGeometricCompPath.trace, openRefl]
    rw [heq]
    exact continuous_const
  exact hflat.prodMk hobs

theorem continuous_traceSensitive_totalSymm :
    @Continuous (TotalOpenGeometricCompPath A Step S)
      (TotalOpenGeometricCompPath A Step S)
      (traceSensitiveTopologicalSpace S) (traceSensitiveTopologicalSpace S)
      (totalSymm S) := by
  apply continuous_induced_rng.mpr
  have hsymmObs :
      @Continuous (TotalOpenGeometricCompPath A Step S)
        (TotalOpenGeometricCompPath A Step S)
        (traceSensitiveTopologicalSpace S) inferInstance
        (totalSymm S) :=
    continuous_traceSensitive_from_observable S
      (TotalOpenGeometricCompPath.continuous_totalSymm S)
  have hobs :
      @Continuous (TotalOpenGeometricCompPath A Step S)
        (Observation (A := A))
        (traceSensitiveTopologicalSpace S) inferInstance
        (fun p => observation S (totalSymm S p)) :=
    @Continuous.comp _ _ _ (traceSensitiveTopologicalSpace S)
      inferInstance inferInstance _ _
      (TotalOpenGeometricCompPath.continuous_observation S) hsymmObs
  have hflat :
      @Continuous (TotalOpenGeometricCompPath A Step S) (FlatWord Step)
        (traceSensitiveTopologicalSpace S) inferInstance
        (fun p => flatWordSymm (GeometricTrace.flatWord p.trace)) :=
    @Continuous.comp _ _ _ (traceSensitiveTopologicalSpace S)
      inferInstance inferInstance _ _ continuous_flatWordSymm
      (continuous_traceSensitive_flatWord S)
  convert (@Continuous.prodMk _ _ _ inferInstance inferInstance
      (traceSensitiveTopologicalSpace S) _ _ hflat hobs) using 1
  funext p
  simp [traceSensitiveObservation, totalSymm, openSymm,
    TotalOpenGeometricCompPath.trace,
    GeometricTrace.flatWord_symm]

theorem continuous_traceSensitive_totalTrans :
    @Continuous (TotalComposable A Step S)
      (TotalOpenGeometricCompPath A Step S)
      (traceSensitiveComposableTopologicalSpace S)
      (traceSensitiveTopologicalSpace S)
      (totalTrans S) := by
  apply continuous_induced_rng.mpr
  have htransObs :
      @Continuous (TotalComposable A Step S)
        (TotalOpenGeometricCompPath A Step S)
        (traceSensitiveComposableTopologicalSpace S) inferInstance
        (totalTrans S) :=
    continuous_traceSensitiveComposable_from_observable S
      (TotalOpenGeometricCompPath.continuous_totalTrans S)
  have hobs :
      @Continuous (TotalComposable A Step S)
        (Observation (A := A))
        (traceSensitiveComposableTopologicalSpace S) inferInstance
        (fun c => observation S (totalTrans S c)) :=
    @Continuous.comp _ _ _ (traceSensitiveComposableTopologicalSpace S)
      inferInstance inferInstance _ _
      (TotalOpenGeometricCompPath.continuous_observation S) htransObs
  have hpair :
      @Continuous (TotalComposable A Step S)
        (FlatWord Step × FlatWord Step)
        (traceSensitiveComposableTopologicalSpace S) inferInstance
        (fun c : TotalComposable A Step S =>
        (GeometricTrace.flatWord c.left.trace,
          GeometricTrace.flatWord c.right.trace)) :=
    @Continuous.prodMk _ _ _ inferInstance inferInstance
      (traceSensitiveComposableTopologicalSpace S) _ _
      (continuous_traceSensitiveComposable_leftFlat S)
      (continuous_traceSensitiveComposable_rightFlat S)
  have hflat :
      @Continuous (TotalComposable A Step S) (FlatWord Step)
        (traceSensitiveComposableTopologicalSpace S) inferInstance
        (fun c => flatWordTrans (GeometricTrace.flatWord c.left.trace)
          (GeometricTrace.flatWord c.right.trace)) :=
    @Continuous.comp _ _ _ (traceSensitiveComposableTopologicalSpace S)
      inferInstance inferInstance _ _ continuous_flatWordTrans hpair
  convert (@Continuous.prodMk _ _ _ inferInstance inferInstance
      (traceSensitiveComposableTopologicalSpace S) _ _ hflat hobs) using 1
  funext c
  simp [traceSensitiveObservation, totalTrans, openTrans,
    TotalOpenGeometricCompPath.trace,
    GeometricTrace.flatWord_trans]

/-! ## Explicit computational certificates -/

noncomputable def traceSensitiveTransLengthPath
    (c : TotalComposable A Step S) :
    ComputationalPaths.Path
      (GeometricTrace.traceLength (totalTrans S c).trace)
      (TotalComposable.leftTraceLength S c +
        TotalComposable.rightTraceLength S c) :=
  GeometricTrace.traceLengthTransPath c.left.trace c.right.trace

noncomputable def traceSensitiveUnitRewrite (n : Nat) :
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl n)
        (ComputationalPaths.Path.refl n))
      (ComputationalPaths.Path.refl n) :=
  ComputationalPaths.Path.RwEq.step
    (ComputationalPaths.Path.Step.trans_refl_right
      (ComputationalPaths.Path.refl n))

structure TraceSensitiveTopologyCertificate where
  full_code_continuous :
    @Continuous (TotalOpenGeometricCompPath A Step S)
      (TraceSensitiveObservation (A := A) (Step := Step))
      (traceSensitiveTopologicalSpace S) inferInstance
      (traceSensitiveObservation S)
  full_trace_realization_continuous :
    @Continuous (TotalOpenGeometricCompPath A Step S)
      (C(unitInterval, A))
      (traceSensitiveTopologicalSpace S) inferInstance
      (fun p => (GeometricTrace.realize p.trace).toContinuousMap)
  coarsening_continuous :
    @Continuous (TotalOpenGeometricCompPath A Step S)
      (TotalOpenGeometricCompPath A Step S)
      (traceSensitiveTopologicalSpace S) inferInstance id
  identity_continuous :
    @Continuous A (TotalOpenGeometricCompPath A Step S)
      inferInstance (traceSensitiveTopologicalSpace S) (totalRefl S)
  composition_continuous :
    @Continuous (TotalComposable A Step S)
      (TotalOpenGeometricCompPath A Step S)
      (traceSensitiveComposableTopologicalSpace S)
      (traceSensitiveTopologicalSpace S) (totalTrans S)
  reversal_continuous :
    @Continuous (TotalOpenGeometricCompPath A Step S)
      (TotalOpenGeometricCompPath A Step S)
      (traceSensitiveTopologicalSpace S) (traceSensitiveTopologicalSpace S)
      (totalSymm S)
  composition_length_path : ∀ c : TotalComposable A Step S,
    ComputationalPaths.Path
      (GeometricTrace.traceLength (totalTrans S c).trace)
      (TotalComposable.leftTraceLength S c +
        TotalComposable.rightTraceLength S c)
  unit_rewrite : ∀ n : Nat,
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl n)
        (ComputationalPaths.Path.refl n))
      (ComputationalPaths.Path.refl n)

noncomputable def traceSensitiveTopologyCertificate :
    TraceSensitiveTopologyCertificate S where
  full_code_continuous := continuous_traceSensitiveObservation S
  full_trace_realization_continuous := continuous_fullTraceRealization S
  coarsening_continuous := continuous_traceSensitive_to_observable S
  identity_continuous := continuous_traceSensitive_totalRefl S
  composition_continuous := continuous_traceSensitive_totalTrans S
  reversal_continuous := continuous_traceSensitive_totalSymm S
  composition_length_path := traceSensitiveTransLengthPath S
  unit_rewrite := traceSensitiveUnitRewrite

end TotalOpenGeometricCompPath

end GeometricTopology
end Path
end ComputationalPaths
