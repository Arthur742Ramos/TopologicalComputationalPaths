import Mathlib.Topology.Constructions
import ComputationalPaths

/-!
# Solution: topological semantics of computational paths

The selected theorem is the exact comparison between the canonical final
composable topology and the ordinary pullback topology.  It identifies the
quotient-map, homeomorphism, and induced-topology criteria; transfers
continuity to ordinary composition; and proves compact--Hausdorff and discrete
sufficient cases.  Its certificate also contains an explicit integer-labelled
one-object trace presentation with an inductive singleton normal form and a
finite trace-sensitive topology obstruction.  The generic final-domain
interface below remains supporting notation for the extraction adapter.
-/

namespace TopologicalComputationalPaths

universe u v w

open ComputationalPaths.Path.GeometricTopology
open ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite
open scoped Topology

/-! ## The ordinary/final topology comparison -/

noncomputable def finalToOrdinary
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    {S : ContinuousGeometricStepSystem A Step}
    (P : ScopedGeometricRewritePresentation S) :
    ScopedComposableClass P → ScopedComposablePair P :=
  fun c => (scopedPairMap P c).val

noncomputable def rawToOrdinary
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    {S : ContinuousGeometricStepSystem A Step}
    (P : ScopedGeometricRewritePresentation S) :
    ScopedComposableRaw (S := S) → ScopedComposablePair P :=
  fun c => finalToOrdinary P (scopedComposableMk P c)

noncomputable def ordinaryComposition
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    {S : ContinuousGeometricStepSystem A Step}
    (P : ScopedGeometricRewritePresentation S) :
    ScopedComposablePair P → ScopedClass P :=
  fun pq => scopedCompositionOnStrong P ⟨pq⟩

/-! ## A concrete exponent presentation

The comparison theorem is accompanied by a small but nontrivial instance.  A
one-object system has integer-labelled primitive computational loops, and its
local presentation contains explicit add, zero, and inverse normalization
rules.  Induction over the trace constructors proves a singleton normal form;
the quotient code is bijective with `Int`, and composition adds exponents.
-/

noncomputable def unitLoopStepSystem :
    ContinuousGeometricStepSystem Unit Int where
  src := fun _ => ()
  tgt := fun _ => ()
  realize := fun _ => _root_.Path.refl ()
  continuous_src := continuous_const
  continuous_tgt := continuous_const
  continuous_realize := by
    exact continuous_const

abbrev UnitLoopTrace :=
  GeometricTrace unitLoopStepSystem.toGeometricStepSystem () ()

def unitLoopDegree :
    {a b : Unit} →
      GeometricTrace unitLoopStepSystem.toGeometricStepSystem a b → Int
  | _, _, GeometricTrace.refl _ => 0
  | _, _, GeometricTrace.single n => n
  | _, _, GeometricTrace.trans p q => unitLoopDegree p + unitLoopDegree q
  | _, _, GeometricTrace.symm p => -unitLoopDegree p

def unitLoopPositiveTrace : Nat → UnitLoopTrace
  | 0 => GeometricTrace.refl ()
  | n + 1 => GeometricTrace.trans (unitLoopPositiveTrace n)
      (GeometricTrace.single (1 : Int))

def unitLoopTrace : Int → UnitLoopTrace
  | Int.ofNat n => unitLoopPositiveTrace n
  | Int.negSucc n => GeometricTrace.symm (unitLoopPositiveTrace (n + 1))

noncomputable def unitLoopTraceCast {a b : Unit}
    (ha : a = ()) (hb : b = ())
    (p : GeometricTrace unitLoopStepSystem.toGeometricStepSystem a b) :
    UnitLoopTrace := by
  cases ha
  cases hb
  exact p

def unitLoopRule {a b : Unit}
    (p q : GeometricTrace unitLoopStepSystem.toGeometricStepSystem a b) : Prop :=
  ∃ (ha : a = ()) (hb : b = ()),
    (∃ n m : Int,
        unitLoopTraceCast ha hb p =
          GeometricTrace.trans
            (GeometricTrace.single n : UnitLoopTrace)
            (GeometricTrace.single m : UnitLoopTrace) ∧
        unitLoopTraceCast ha hb q =
          (GeometricTrace.single (n + m) : UnitLoopTrace)) ∨
      (unitLoopTraceCast ha hb p =
          (GeometricTrace.refl () : UnitLoopTrace) ∧
        unitLoopTraceCast ha hb q =
          (GeometricTrace.single 0 : UnitLoopTrace)) ∨
      (∃ n : Int,
        unitLoopTraceCast ha hb p =
          GeometricTrace.symm (GeometricTrace.single n : UnitLoopTrace) ∧
        unitLoopTraceCast ha hb q =
          (GeometricTrace.single (-n) : UnitLoopTrace))

def unitLoopRule_add (n m : Int) :
    unitLoopRule
      (GeometricTrace.trans
        (GeometricTrace.single n : UnitLoopTrace)
        (GeometricTrace.single m : UnitLoopTrace))
      (GeometricTrace.single (n + m) : UnitLoopTrace) :=
  ⟨rfl, rfl, Or.inl ⟨n, m, rfl, rfl⟩⟩

def unitLoopRule_zero :
    unitLoopRule
      (GeometricTrace.refl () : UnitLoopTrace)
      (GeometricTrace.single 0 : UnitLoopTrace) :=
  ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

def unitLoopRule_neg (n : Int) :
    unitLoopRule
      (GeometricTrace.symm
        (GeometricTrace.single n : UnitLoopTrace))
      (GeometricTrace.single (-n) : UnitLoopTrace) :=
  ⟨rfl, rfl, Or.inr (Or.inr ⟨n, rfl, rfl⟩)⟩

def unitLoopRule_degree
    {a b : Unit}
    {p q : GeometricTrace unitLoopStepSystem.toGeometricStepSystem a b}
    (h : unitLoopRule p q) : unitLoopDegree p = unitLoopDegree q := by
  rcases h with ⟨ha, hb, h⟩
  cases ha
  cases hb
  rcases h with h | h | h
  · rcases h with ⟨n, m, hp, hq⟩
    cases hp
    cases hq
    simp [unitLoopDegree]
  · rcases h with ⟨hp, hq⟩
    cases hp
    cases hq
    simp [unitLoopDegree]
  · rcases h with ⟨n, hp, hq⟩
    cases hp
    cases hq
    simp [unitLoopDegree]

def unitPathHomotopy {a b : Unit} (p q : _root_.Path a b) :
    _root_.Path.Homotopic p q := by
  have h : p = q := by
    apply _root_.Path.ext
    funext t
    exact Subsingleton.elim _ _
  cases h
  exact _root_.Path.Homotopic.refl _

noncomputable def unitLoopPresentation :
    ScopedGeometricRewritePresentation unitLoopStepSystem where
  rule := fun {a b} p q => unitLoopRule p q
  sound_rule := by
    intro a b p q h
    exact unitPathHomotopy _ _

abbrev UnitLoopRaw := ScopedRawPath (S := unitLoopStepSystem)

noncomputable def unitLoopOpen (n : Int) :
    OpenGeometricCompPath
      unitLoopStepSystem.toGeometricStepSystem () () :=
  { trace := unitLoopTrace n
    geometric := _root_.Path.refl ()
    coherent := unitPathHomotopy _ _ }

noncomputable def unitLoopRepresentative (n : Int) : UnitLoopRaw :=
  ⟨(), (), unitLoopOpen n⟩

noncomputable def unitLoopComposable (m n : Int) :
    TotalComposable Unit Int unitLoopStepSystem :=
  ⟨(), (), (), unitLoopOpen m, unitLoopOpen n⟩

abbrev UnitLoopClass := ScopedClass unitLoopPresentation

noncomputable def unitLoopCode : UnitLoopClass → Int :=
  Quot.lift
    (fun p : UnitLoopRaw => unitLoopDegree p.path.trace)
    (by
      intro p q h
      rcases p with ⟨p_src, p_tgt, p_path⟩
      rcases q with ⟨q_src, q_tgt, q_path⟩
      rcases h with ⟨hs, ht, hr⟩
      cases p_src
      cases p_tgt
      cases q_src
      cases q_tgt
      have hs0 : hs = (rfl : () = ()) := Subsingleton.elim _ _
      have ht0 : ht = (rfl : () = ()) := Subsingleton.elim _ _
      cases hs0
      cases ht0
      change ScopedRwEq unitLoopPresentation p_path.trace q_path.trace at hr
      have hrewrites :
          ∀ {a b : Unit}
            {p q : GeometricTrace unitLoopStepSystem.toGeometricStepSystem a b},
            ScopedRwEq unitLoopPresentation p q →
              unitLoopDegree p = unitLoopDegree q := by
        intro a b p q hrewrite
        induction hrewrite with
        | refl => rfl
        | generator h => exact unitLoopRule_degree h
        | symm h ih => simpa [unitLoopDegree] using ih.symm
        | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
        | trans_congr h₁ h₂ ih₁ ih₂ =>
            simpa [unitLoopDegree, ih₁, ih₂, add_assoc]
        | symm_congr h ih => simpa [unitLoopDegree, ih]
        | refl_trans p => simp [unitLoopDegree]
        | trans_refl p => simp [unitLoopDegree]
        | trans_assoc p q r => simp [unitLoopDegree, add_assoc]
        | symm_trans p => simp [unitLoopDegree]
        | trans_symm p => simp [unitLoopDegree]
        | symm_symm p => simp [unitLoopDegree]
        | symm_refl a => simp [unitLoopDegree]
        | symm_comp p q => simp [unitLoopDegree, add_comm]
      exact hrewrites hr)

structure UnitLoopExponentCertificate : Prop where
  bijective : Function.Bijective unitLoopCode
  normal_form : ∀ p : UnitLoopTrace,
    ScopedRwEq unitLoopPresentation p
      (GeometricTrace.single (unitLoopDegree p) : UnitLoopTrace)
  raw_code : ∀ p : UnitLoopRaw,
    unitLoopCode (scopedQuotientMk unitLoopPresentation p) =
      unitLoopDegree p.path.trace
  representative_code : ∀ n,
    unitLoopCode
        (scopedQuotientMk unitLoopPresentation (unitLoopRepresentative n)) = n
  composition_additive : ∀ m n,
    unitLoopCode
        (scopedCompositionFromComposable unitLoopPresentation
          (scopedComposableMk unitLoopPresentation (unitLoopComposable m n))) =
      m + n

/-! ## A finite trace-sensitive obstruction

The selected result also records the smallest separation example: two
primitive computational labels are distinct in the trace carrier, while an
observable code forgets the label.  The identity from the indiscrete
observable topology to the discrete trace topology is not continuous in the
reverse direction.  This is the finite obstruction behind the warning that a
continuous bijection need not be a homeomorphism.
-/

inductive TraceLabel
  | left
  | right

noncomputable def finiteTraceStepSystem :
    GeometricStepSystem Unit TraceLabel where
  src := fun _ => ()
  tgt := fun _ => ()
  realize := fun _ => _root_.Path.refl ()

abbrev FiniteTrace :=
  GeometricTrace (A := Unit) (Step := TraceLabel) finiteTraceStepSystem () ()

def finiteTrace (g : TraceLabel) : FiniteTrace :=
  GeometricTrace.single g

abbrev ObservableTraceCode := Nat × Unit

def observableTraceCode (_ : TraceLabel) : ObservableTraceCode :=
  (1, Unit.unit)

def traceTopology : TopologicalSpace TraceLabel := ⊥

def observableTopology : TopologicalSpace TraceLabel := ⊤

inductive TraceUnitCoherence : Nat → Nat → Prop
  | trans_refl_right (n : Nat) : TraceUnitCoherence n n

noncomputable def traceUnitRewrite (n : Nat) :
    TraceUnitCoherence n n :=
  TraceUnitCoherence.trans_refl_right n

structure TraceTopologyObstructionCertificate : Prop where
  trace_separates : finiteTrace TraceLabel.left ≠ finiteTrace TraceLabel.right
  observable_forgets :
    observableTraceCode TraceLabel.left = observableTraceCode TraceLabel.right
  forward_continuous :
    @Continuous TraceLabel TraceLabel traceTopology observableTopology id
  reverse_not_continuous :
    ¬ @Continuous TraceLabel TraceLabel observableTopology traceTopology id
  unit_coherence : ∀ n : Nat, TraceUnitCoherence n n

noncomputable def traceTopologyObstructionCertificate :
    TraceTopologyObstructionCertificate where
  trace_separates := by
    intro h
    cases h
  observable_forgets := rfl
  forward_continuous := by
    change @Continuous TraceLabel TraceLabel
      (⊥ : TopologicalSpace TraceLabel)
      (⊤ : TopologicalSpace TraceLabel) id
    exact continuous_bot
  reverse_not_continuous := by
    intro h
    letI : TopologicalSpace TraceLabel := traceTopology
    letI : DiscreteTopology TraceLabel := ⟨by rfl⟩
    let U : Set TraceLabel := {TraceLabel.left}
    have hopen : IsOpen[traceTopology] U := by
      exact isOpen_discrete U
    have hpre : IsOpen[observableTopology]
        ((id : TraceLabel → TraceLabel) ⁻¹' U) := by
      exact @IsOpen.preimage TraceLabel TraceLabel
        observableTopology traceTopology id h U hopen
    have hcases :
        ((id : TraceLabel → TraceLabel) ⁻¹' U) = ∅ ∨
          ((id : TraceLabel → TraceLabel) ⁻¹' U) = Set.univ := by
      apply (TopologicalSpace.isOpen_top_iff _).mp
      change @IsOpen TraceLabel (⊤ : TopologicalSpace TraceLabel)
        ((id : TraceLabel → TraceLabel) ⁻¹' U)
      exact hpre
    rcases hcases with hempty | huniv
    · have hleft : TraceLabel.left ∈
          ((id : TraceLabel → TraceLabel) ⁻¹' U) := by
        simp [U]
      rw [hempty] at hleft
      exact hleft
    · have hright : TraceLabel.right ∈ U := by
        have hmem : TraceLabel.right ∈
            ((id : TraceLabel → TraceLabel) ⁻¹' U) := by
          rw [huniv]
          exact Set.mem_univ _
        simpa using hmem
      simp [U] at hright
  unit_coherence := traceUnitRewrite

noncomputable def unitLoopExponentCertificate : UnitLoopExponentCertificate := by
  have hpositive : ∀ n : Nat,
      unitLoopDegree (unitLoopPositiveTrace n) = (n : Int) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        simp [unitLoopPositiveTrace, unitLoopDegree, ih]
  have hdegree : ∀ n : Int, unitLoopDegree (unitLoopTrace n) = n := by
    intro n
    cases n with
    | ofNat n => simpa [unitLoopTrace] using hpositive n
    | negSucc n =>
        simp [unitLoopTrace, unitLoopDegree, hpositive, Int.negSucc_eq,
          add_comm, add_left_comm, add_assoc]
  have hraw (p : UnitLoopRaw) :
      unitLoopCode (scopedQuotientMk unitLoopPresentation p) =
        unitLoopDegree p.path.trace := by
    rfl
  have hnormal_aux :
      ∀ {a b : Unit}
        (p : GeometricTrace unitLoopStepSystem.toGeometricStepSystem a b),
        ∀ (ha : a = ()) (hb : b = ()),
          ScopedRwEq unitLoopPresentation (unitLoopTraceCast ha hb p)
            (GeometricTrace.single (unitLoopDegree p) : UnitLoopTrace) := by
    intro a b p
    induction p with
    | refl a =>
        intro ha hb
        cases ha
        cases hb
        simpa [unitLoopTraceCast, unitLoopDegree] using
          (ScopedRwEq.generator (P := unitLoopPresentation) unitLoopRule_zero)
    | single n =>
        intro ha hb
        cases ha
        cases hb
        exact ScopedRwEq.refl _
    | @trans a b c p q ihp ihq =>
        intro ha hb
        have hmid : b = () := Subsingleton.elim _ _
        cases ha
        cases hmid
        cases hb
        simpa [unitLoopTraceCast, unitLoopDegree] using
          (ScopedRwEq.trans
            (ScopedRwEq.trans_congr (ihp rfl rfl) (ihq rfl rfl))
            (ScopedRwEq.generator (P := unitLoopPresentation)
              (unitLoopRule_add (unitLoopDegree p) (unitLoopDegree q))))
    | symm p ih =>
        intro ha hb
        cases ha
        cases hb
        simpa [unitLoopTraceCast, unitLoopDegree] using
          (ScopedRwEq.trans
            (ScopedRwEq.symm_congr (ih rfl rfl))
            (ScopedRwEq.generator (P := unitLoopPresentation)
              (unitLoopRule_neg (unitLoopDegree p))))
  have hnormal : ∀ p : UnitLoopTrace,
      ScopedRwEq unitLoopPresentation p
        (GeometricTrace.single (unitLoopDegree p) : UnitLoopTrace) := by
    intro p
    simpa [unitLoopTraceCast] using hnormal_aux p rfl rfl
  have hequiv : ∀ (p q : UnitLoopRaw),
      unitLoopDegree p.path.trace = unitLoopDegree q.path.trace →
        scopedEquivalent unitLoopPresentation p q := by
    intro p q h
    rcases p with ⟨p_src, p_tgt, p_path⟩
    rcases q with ⟨q_src, q_tgt, q_path⟩
    have hs : q_src = p_src := Subsingleton.elim _ _
    have ht : q_tgt = p_tgt := Subsingleton.elim _ _
    cases p_src
    cases p_tgt
    cases q_src
    cases q_tgt
    have hs0 : hs = (rfl : () = ()) := Subsingleton.elim _ _
    have ht0 : ht = (rfl : () = ()) := Subsingleton.elim _ _
    cases hs0
    cases ht0
    change unitLoopDegree p_path.trace = unitLoopDegree q_path.trace at h
    have hmid : ScopedRwEq unitLoopPresentation
        (GeometricTrace.single (unitLoopDegree p_path.trace) : UnitLoopTrace)
        (GeometricTrace.single (unitLoopDegree q_path.trace) : UnitLoopTrace) := by
      rw [h]
      exact ScopedRwEq.refl _
    exact ⟨rfl, rfl,
      (hnormal p_path.trace).trans
        (hmid.trans (ScopedRwEq.symm (hnormal q_path.trace)))⟩
  refine
    { bijective := ?_
      normal_form := hnormal
      raw_code := hraw
      representative_code := ?_
      composition_additive := ?_ }
  · constructor
    · intro x y hxy
      revert y
      refine Quotient.inductionOn x ?_
      intro p y hxy
      revert hxy
      refine Quotient.inductionOn y ?_
      intro q hxy
      apply Quotient.sound
      apply hequiv p q
      exact hxy
    · intro n
      refine ⟨scopedQuotientMk unitLoopPresentation (unitLoopRepresentative n), ?_⟩
      change unitLoopDegree (unitLoopTrace n) = n
      exact hdegree n
  · intro n
    change unitLoopDegree (unitLoopTrace n) = n
    exact hdegree n
  · intro m n
    change unitLoopDegree
        (GeometricTrace.trans (unitLoopTrace m) (unitLoopTrace n)) = m + n
    simp [unitLoopDegree, hdegree]

structure OrdinaryTopologyComparisonCertificate
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    (S : ContinuousGeometricStepSystem A Step)
    (P : ScopedGeometricRewritePresentation S) : Prop where
  canonical_bijection : Function.Bijective (finalToOrdinary P)
  canonical_map_continuous : Continuous (finalToOrdinary P)
  raw_quotient_criterion :
    Topology.IsQuotientMap (finalToOrdinary P) ↔
      Topology.IsQuotientMap (rawToOrdinary P)
  homeomorphism_criterion :
    Topology.IsQuotientMap (finalToOrdinary P) ↔
      ∃ e : ScopedComposableClass P ≃ₜ ScopedComposablePair P,
        (e : ScopedComposableClass P → ScopedComposablePair P) =
          finalToOrdinary P
  topology_agreement_criterion :
    Topology.IsQuotientMap (finalToOrdinary P) ↔
      (inferInstance : TopologicalSpace (ScopedComposableClass P)) =
        TopologicalSpace.induced (finalToOrdinary P)
          (inferInstance : TopologicalSpace (ScopedComposablePair P))
  ordinary_composition_of_quotient :
    Topology.IsQuotientMap (finalToOrdinary P) →
      Continuous (ordinaryComposition P)
  discontinuity_obstructs_compatibility :
    ¬ Continuous (ordinaryComposition P) →
      ¬ Topology.IsQuotientMap (finalToOrdinary P)
  compact_hausdorff_recovers_ordinary :
    ∀ [CompactSpace (ScopedComposableClass P)]
      [T2Space (ScopedComposablePair P)],
      Topology.IsQuotientMap (finalToOrdinary P) ∧
        Continuous (ordinaryComposition P)
  discrete_recovers_ordinary :
    ∀ [DiscreteTopology (ScopedClass P)]
      [DiscreteTopology (ScopedComposableClass P)],
      Topology.IsQuotientMap (finalToOrdinary P) ∧
        Continuous (ordinaryComposition P)
  concrete_exponent_application : UnitLoopExponentCertificate
  trace_sensitive_obstruction : TraceTopologyObstructionCertificate

/-! The statement and solution use the same final topology on quotient domains. -/
noncomputable instance quotientFinalTopology
    {RawPair : Type u} [TopologicalSpace RawPair] (R : Setoid RawPair) :
    TopologicalSpace (Quotient R) :=
  TopologicalSpace.coinduced (Quotient.mk R) inferInstance

structure ScopedFinalPairData
    (RawPair : Type u) (OrdinaryPair : Type v)
    (Arrow : Type w)
    [TopologicalSpace RawPair]
    [TopologicalSpace OrdinaryPair] [TopologicalSpace Arrow] where
  relation : Setoid RawPair
  comparison : Quotient relation ≃ OrdinaryPair
  rawOperation : RawPair → Arrow
  ordinaryOperation : OrdinaryPair → Arrow
  operation_respects :
    ∀ {r s : RawPair}, relation.r r s → rawOperation r = rawOperation s
  comparison_continuous : Continuous comparison
  rawOperation_continuous : Continuous rawOperation
  ordinary_factor : ∀ r,
    ordinaryOperation (comparison (Quotient.mk relation r)) = rawOperation r

namespace ScopedFinalPairData

variable {RawPair : Type u} {OrdinaryPair : Type v} {Arrow : Type w}
  [TopologicalSpace RawPair]
  [TopologicalSpace OrdinaryPair] [TopologicalSpace Arrow]
  (D : ScopedFinalPairData RawPair OrdinaryPair Arrow)

def quotient : RawPair → Quotient D.relation := Quotient.mk D.relation

noncomputable def finalOperation : Quotient D.relation → Arrow :=
  Quotient.lift D.rawOperation (by
    intro r s h
    exact D.operation_respects h)

theorem quotient_is_quotient : Topology.IsQuotientMap D.quotient := by
  exact ⟨⟨rfl⟩, Quotient.mk_surjective⟩

def pairMap : RawPair → OrdinaryPair := D.comparison ∘ D.quotient

def topologyAgreement : Prop :=
  (inferInstance : TopologicalSpace (Quotient D.relation)) =
    TopologicalSpace.induced D.comparison
      (inferInstance : TopologicalSpace OrdinaryPair)

end ScopedFinalPairData

structure ScopedFinalSemanticsCertificate
    {RawPair : Type u} {OrdinaryPair : Type v} {Arrow : Type w}
    [TopologicalSpace RawPair]
    [TopologicalSpace OrdinaryPair] [TopologicalSpace Arrow]
    (D : ScopedFinalPairData RawPair OrdinaryPair Arrow) : Prop where
  final_operation_continuous : Continuous D.finalOperation
  pair_map_quotient_iff_comparison_quotient :
    Topology.IsQuotientMap (D.pairMap) ↔
      Topology.IsQuotientMap D.comparison
  comparison_quotient_iff_inverse_continuous :
    Topology.IsQuotientMap D.comparison ↔
      Continuous D.comparison.invFun
  inverse_continuous_iff_topology_agreement :
    Continuous D.comparison.invFun ↔ D.topologyAgreement
  ordinary_operation_continuous_of_inverse :
    Continuous D.comparison.invFun → Continuous D.ordinaryOperation

theorem main_result
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    (S : ContinuousGeometricStepSystem A Step)
    (P : ScopedGeometricRewritePresentation S) :
    OrdinaryTopologyComparisonCertificate S P := by
  have hBijective : Function.Bijective (finalToOrdinary P) :=
    ⟨scopedPairToOrdinary_injective P,
      scopedPairToOrdinary_surjective P⟩
  have hContinuous : Continuous (finalToOrdinary P) :=
    continuous_scopedPairToOrdinary P
  have hComposition :
      Topology.IsQuotientMap (finalToOrdinary P) →
        Continuous (ordinaryComposition P) := by
    intro h
    exact continuous_scopedCompositionOnProduct P ⟨h⟩
  exact
    { canonical_bijection := hBijective
      canonical_map_continuous := hContinuous
      raw_quotient_criterion := by
        constructor
        · intro h
          exact
            (scopedProductCompatibility_iff_raw_pair_map_quotient P).1 ⟨h⟩
        · intro h
          exact
            ((scopedProductCompatibility_iff_raw_pair_map_quotient P).2 h).pair_map_is_quotient
      homeomorphism_criterion := by
        constructor
        · intro h
          exact ⟨scopedFinalOrdinaryHomeomorph P ⟨h⟩, rfl⟩
        · rintro ⟨e, he⟩
          simpa [he] using e.isQuotientMap
      topology_agreement_criterion := by
        constructor
        · intro h
          exact
            (scopedProductCompatibility_iff_final_topology_agreement P).1 ⟨h⟩
        · intro h
          exact
            ((scopedProductCompatibility_iff_final_topology_agreement P).2 h).pair_map_is_quotient
      ordinary_composition_of_quotient := hComposition
      discontinuity_obstructs_compatibility := by
        intro hnot hquot
        exact hnot (hComposition hquot)
      compact_hausdorff_recovers_ordinary := by
        intro _ _
        let h := scopedProductCompatibility_of_compact_final_t2 P
        exact ⟨h.pair_map_is_quotient,
          continuous_scopedCompositionOnProduct P h⟩
      discrete_recovers_ordinary := by
        intro _ _
        let h :=
          scopedProductCompatibility_of_discrete_arrow_and_final_domain P
        exact ⟨h.pair_map_is_quotient,
          continuous_scopedCompositionOnProduct P h⟩
      concrete_exponent_application := unitLoopExponentCertificate
      trace_sensitive_obstruction := traceTopologyObstructionCertificate }

/-! The substantive repository contains the scoped quotient construction.  The
 following adapter makes the statement-side interface concrete: its raw
 operation is the actual quotient-level composition map, its final operation
 is the canonical descent of that raw map, and its comparison is the actual
 final-to-ordinary equivalence. -/

noncomputable def scopedFinalPairData
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    (S : _root_.ComputationalPaths.Path.GeometricTopology.ContinuousGeometricStepSystem A Step)
    (P : _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewritePresentation S) :
    ScopedFinalPairData
      (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedComposableRaw (S := S))
      (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedComposablePair P)
      (_root_.ComputationalPaths.Path.GeometricTopology.ScopedClass P) where
  relation := _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedComposableSetoid P
  comparison := _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedPairToOrdinaryEquiv P
  rawOperation := fun c =>
    _root_.ComputationalPaths.Path.GeometricTopology.scopedQuotientMk P
      (_root_.ComputationalPaths.Path.GeometricTopology.TotalOpenGeometricCompPath.totalTrans S c)
  ordinaryOperation := _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedCompositionOnProduct P
  operation_respects := by
    intro c d h
    exact Quotient.sound
      (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedEquivalent_totalTrans
        P h.1 h.2)
  comparison_continuous :=
    _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.continuous_scopedPairToOrdinary P
  rawOperation_continuous := by
    exact _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.continuous_scopedQuotientMk P |>.comp
      (_root_.ComputationalPaths.Path.GeometricTopology.TotalOpenGeometricCompPath.continuous_totalTrans S)
  ordinary_factor := by
    intro c
    change
      _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedCompositionOnProduct P
          (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedPairToOrdinary P
            (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedComposableMk P c)) =
        _root_.ComputationalPaths.Path.GeometricTopology.scopedQuotientMk P
          (_root_.ComputationalPaths.Path.GeometricTopology.TotalOpenGeometricCompPath.totalTrans S c)
    rw [_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedCompositionOnProduct_pairMap]
    rfl

theorem scoped_final_operation_agrees
    {A : Type u} [TopologicalSpace A]
    {Step : Type v} [TopologicalSpace Step]
    (S : _root_.ComputationalPaths.Path.GeometricTopology.ContinuousGeometricStepSystem A Step)
    (P : _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewritePresentation S)
    (c : _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedComposableClass P) :
    ScopedFinalPairData.finalOperation (scopedFinalPairData S P) c =
      _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedCompositionFromComposable P c := by
  refine Quotient.inductionOn c ?_
  intro c
  rfl

theorem scoped_groupoid_core_is_available :
    ∀ {A : Type u} [TopologicalSpace A]
      {Step : Type v} [TopologicalSpace Step]
      (S : _root_.ComputationalPaths.Path.GeometricTopology.ContinuousGeometricStepSystem A Step)
      (P : _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewritePresentation S),
      Nonempty (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedFinalTopologicalGroupoidCertificate P) := by
  intro A instA Step instStep S P
  exact ⟨_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.scopedFinalTopologicalGroupoidCertificate P⟩

theorem scoped_pair_data_is_well_formed :
    ∀ {A : Type u} [TopologicalSpace A]
      {Step : Type v} [TopologicalSpace Step]
      (S : _root_.ComputationalPaths.Path.GeometricTopology.ContinuousGeometricStepSystem A Step)
      (P : _root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewritePresentation S),
      Nonempty (ScopedFinalPairData
        (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedComposableRaw (S := S))
        (_root_.ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite.ScopedComposablePair P)
        (_root_.ComputationalPaths.Path.GeometricTopology.ScopedClass P)) := by
  intro A instA Step instStep S P
  exact ⟨scopedFinalPairData S P⟩

end TopologicalComputationalPaths
