import ComputationalPaths.Path.Topology.LiteralWord
import ComputationalPaths.Path.Topology.FlatWordContinuity

/-!
# Finite composable-word strata

The zero-letter stratum is the ambient space, retaining its basepoint. Positive
strata are subspaces of finite signed tuples with matching adjacent endpoints.
Canonical reconstruction uses endpoint-indexed literal words, and its equal-slot
realization varies continuously on every stratum.
-/

namespace ComputationalPaths.Path.GeometricTopology.LiteralWord.Strata

set_option backward.isDefEq.respectTransparency false

open unitInterval
open scoped Topology ContinuousMap

universe u v w

variable {A : Type u} [TopologicalSpace A] {Step : Type v}

/-- Endpoint compatibility of a literal finite list. -/
def Fits (S : GeometricStepSystem A Step) : A → List (SignedStep Step) → A → Prop
  | a, [], b => a = b
  | a, s :: l, b => a = signedSrc S s ∧ Fits S (signedTgt S s) l b

/-- Reconstruct a composable list without choosing a tree representative. -/
def fromList {S : GeometricStepSystem A Step} :
    {a b : A} → (l : List (SignedStep Step)) → Fits S a l b → Word S a b
  | a, b, [], h => by cases h; exact .nil a
  | a, b, s :: l, h => by
      rcases h with ⟨rfl, ht⟩
      exact .cons s (fromList l ht)

theorem fromList_toList {S : GeometricStepSystem A Step} {a b : A}
    (l : List (SignedStep Step)) (h : Fits S a l b) :
    (fromList l h).toList = l := by
  induction l generalizing a b with
  | nil => cases h; rfl
  | cons s l ih =>
      rcases h with ⟨rfl, ht⟩
      change s :: (fromList l ht).toList = s :: l
      rw [ih ht]

theorem fromList_length {S : GeometricStepSystem A Step} {a b : A}
    (l : List (SignedStep Step)) (h : Fits S a l b) :
    (fromList l h).length = l.length := by
  change (fromList l h).toList.length = _
  rw [fromList_toList]

theorem word_fits {S : GeometricStepSystem A Step} {a b : A} (p : Word S a b) :
    Fits S a p.toList b := by
  induction p with
  | nil a => rfl
  | cons s p ih => exact ⟨rfl, ih⟩

theorem fromList_word {S : GeometricStepSystem A Step} {a b : A} (p : Word S a b) :
    fromList p.toList (word_fits p) = p := by
  apply Word.toList_injective a b
  exact fromList_toList _ _

theorem fromList_congr {S : GeometricStepSystem A Step} {a b : A}
    {l k : List (SignedStep Step)} (hl : l = k)
    (h : Fits S a l b) (hk : Fits S a k b) : fromList l h = fromList k hk := by
  cases hl
  rfl

theorem weighted_counts_congr {a b c : A} {m n m' n' : Nat}
    (hmn : m = m') (hnn : n = n')
    (hm : m = 0 → a = b) (hn : n = 0 → b = c)
    (hm' : m' = 0 → a = b) (hn' : n' = 0 → b = c)
    (p : _root_.Path a b) (q : _root_.Path b c) :
    weightedConcatenation (GeometricTrace.equalSlotReparam m n) hm hn p q =
      weightedConcatenation (GeometricTrace.equalSlotReparam m' n') hm' hn' p q := by
  cases hmn
  cases hnn
  rfl

variable [TopologicalSpace Step] (S : ContinuousGeometricStepSystem A Step)

theorem continuous_signedSrc : Continuous (signedSrc S.toGeometricStepSystem) := by
  convert continuous_sumElim.2 ⟨S.continuous_src, S.continuous_tgt⟩ using 1
  funext s
  cases s <;> rfl

theorem continuous_signedTgt : Continuous (signedTgt S.toGeometricStepSystem) := by
  convert continuous_sumElim.2 ⟨S.continuous_tgt, S.continuous_src⟩ using 1
  funext s
  cases s <;> rfl

/-- The actual signed primitive path, with varying endpoints. -/
def signedPath (s : SignedStep Step) :
    _root_.Path (signedSrc S.toGeometricStepSystem s) (signedTgt S.toGeometricStepSystem s) :=
  match s with
  | .inl s => S.realize s
  | .inr s => (S.realize s).symm

theorem flatRealize_atomTrace (s : SignedStep Step) :
    GeometricTrace.flatRealize (atomTrace S.toGeometricStepSystem s) = signedPath S s := by
  cases s <;> rfl

theorem continuous_signedPath_map :
    Continuous (fun s => (signedPath S s).toContinuousMap) := by
  have hp : Continuous (fun st : Step × I => S.realize st.1 st.2) :=
    ContinuousMap.continuous_uncurry_of_continuous
      (⟨fun s => (S.realize s).toContinuousMap, S.continuous_realize⟩ : C(Step, C(I, A)))
  have hn : Continuous (fun s : Step => (S.realize s).symm.toContinuousMap) :=
    ContinuousMap.continuous_of_continuous_uncurry _
      (_root_.Path.symm_continuous_family _ hp)
  convert continuous_sumElim.2 ⟨S.continuous_realize, hn⟩ using 1
  funext s
  cases s <;> rfl

theorem continuous_signedPath_family :
    Continuous (fun st : SignedStep Step × I => signedPath S st.1 st.2) :=
  ContinuousMap.continuous_uncurry_of_continuous
    (⟨fun s => (signedPath S s).toContinuousMap, continuous_signedPath_map S⟩ :
      C(SignedStep Step, C(I, A)))

theorem fromList_nil_eval {a b : A}
    (h : Fits S.toGeometricStepSystem a [] b) (t : I) :
    GeometricTrace.flatRealize (fromList [] h).toTrace t = a := by
  cases h
  rfl

theorem fromList_cons_eval {a b : A} (s : SignedStep Step)
    (l : List (SignedStep Step)) (h : Fits S.toGeometricStepSystem a (s :: l) b) (t : I) :
    GeometricTrace.flatRealize (fromList (s :: l) h).toTrace t =
      weightedConcatenation (GeometricTrace.equalSlotReparam 1 l.length)
        (fun hzero => by omega)
        (fun hz => GeometricTrace.length_zero_endpoint (fromList l h.2).toTrace (by
          rw [Word.toTrace_length, fromList_length]; exact hz))
        (signedPath S s) (GeometricTrace.flatRealize (fromList l h.2).toTrace) t := by
  rcases h with ⟨rfl, ht⟩
  simp only [fromList, Word.toTrace, GeometricTrace.flatRealize]
  have hatom : GeometricTrace.traceLength (atomTrace S.toGeometricStepSystem s) = 1 := by
    cases s <;> rfl
  have hlen : GeometricTrace.traceLength (fromList l ht).toTrace = l.length := by
    rw [Word.toTrace_length, fromList_length]
  simp only [flatRealize_atomTrace]
  exact _root_.congrArg (fun p : _root_.Path (signedSrc S.toGeometricStepSystem s) b => p t)
    (weighted_counts_congr hatom hlen _ _ _ _ _ _)

/-- Fixed-length continuous letter families have continuous equal-slot execution.
The endpoint compatibility proof is not an extra topological coordinate. -/
theorem continuous_fromList_family
    {Z : Type w} [TopologicalSpace Z] (n : Nat)
    (a b : Z → A) (f : Z → Fin n → SignedStep Step)
    (h : ∀ z, Fits S.toGeometricStepSystem (a z) (List.ofFn (f z)) (b z))
    (ha : Continuous a) (hf : Continuous f) :
    Continuous (fun zt : Z × I =>
      GeometricTrace.flatRealize (fromList (List.ofFn (f zt.1)) (h zt.1)).toTrace zt.2) := by
  induction n generalizing a b with
  | zero =>
      have heq : (fun zt : Z × I =>
          GeometricTrace.flatRealize (fromList (List.ofFn (f zt.1)) (h zt.1)).toTrace zt.2) =
          fun zt => a zt.1 := by
        funext zt
        simpa only [List.ofFn_zero] using fromList_nil_eval S (h zt.1) zt.2
      rw [heq]
      exact ha.comp continuous_fst
  | succ n ih =>
      let head : Z → SignedStep Step := fun z => f z 0
      let tail : Z → Fin n → SignedStep Step := fun z i => f z i.succ
      have hh : Continuous head := (continuous_apply 0).comp hf
      have ht : Continuous tail := by
        apply continuous_pi
        intro i
        exact (continuous_apply i.succ).comp hf
      have hfits (z : Z) :
          Fits S.toGeometricStepSystem (a z) (head z :: List.ofFn (tail z)) (b z) := by
        simpa only [List.ofFn_succ] using h z
      let q (z : Z) :=
        (fromList (List.ofFn (tail z)) (hfits z).2).toTrace
      have hq : Continuous (fun zt : Z × I => GeometricTrace.flatRealize (q zt.1) zt.2) :=
        ih (fun z => signedTgt S.toGeometricStepSystem (head z)) b tail
          (fun z => (hfits z).2) ((continuous_signedTgt S).comp hh) ht
      have hp : Continuous (fun zt : Z × I => signedPath S (head zt.1) zt.2) :=
        (continuous_signedPath_family S).comp (hh.prodMap continuous_id)
      have hweighted := weightedConcatenation_continuous_family
        (GeometricTrace.equalSlotReparam 1 n)
        (fun _ hzero => by omega)
        (fun z hz => GeometricTrace.length_zero_endpoint (q z) (by
          rw [Word.toTrace_length, fromList_length, List.length_ofFn]
          exact hz))
        (fun z => signedPath S (head z))
        (fun z => GeometricTrace.flatRealize (q z)) hp hq
      have heq : (fun zt : Z × I =>
          GeometricTrace.flatRealize (fromList (List.ofFn (f zt.1)) (h zt.1)).toTrace zt.2) =
          fun zt => weightedConcatenation (GeometricTrace.equalSlotReparam 1 n)
            (fun hzero => by omega)
            (fun hz => GeometricTrace.length_zero_endpoint (q zt.1) (by
              rw [Word.toTrace_length, fromList_length, List.length_ofFn]; exact hz))
            (signedPath S (head zt.1)) (GeometricTrace.flatRealize (q zt.1)) zt.2 := by
        funext zt
        rw [fromList_congr (List.ofFn_succ (f := f zt.1)) (h zt.1) (hfits zt.1)]
        exact (fromList_cons_eval S (head zt.1) (List.ofFn (tail zt.1)) (hfits zt.1) zt.2).trans
          (_root_.congrArg (fun p : _root_.Path (signedSrc S.toGeometricStepSystem (head zt.1)) (b zt.1) => p zt.2)
            (weighted_counts_congr rfl (List.length_ofFn (f := tail zt.1)) _ _ _ _ _ _))
      rw [heq]
      exact hweighted

/-- Compatibility of consecutive letters in a nonempty finite tuple. -/
def Compatible (n : Nat) (f : Fin (n + 1) → SignedStep Step) : Prop :=
  ∀ i : Fin n, signedTgt S.toGeometricStepSystem (f i.castSucc) =
    signedSrc S.toGeometricStepSystem (f i.succ)

abbrev Positive (n : Nat) :=
  {f : Fin (n + 1) → SignedStep Step // Compatible S n f}

/-- The genuine finite-word strata: zero letters retain their basepoint. -/
def Stratum : Nat → Type (max u v)
  | 0 => ULift.{v} A
  | n + 1 => ULift.{u} (Positive S n)

instance stratumTopology (n : Nat) : TopologicalSpace (Stratum S n) := by
  cases n with
  | zero => exact inferInstanceAs (TopologicalSpace (ULift.{v} A))
  | succ n => exact inferInstanceAs (TopologicalSpace (ULift.{u} (Positive S n)))

def source : (n : Nat) → Stratum S n → A
  | 0, a => a.down
  | _ + 1, f => signedSrc S.toGeometricStepSystem (f.down.1 0)

def target : (n : Nat) → Stratum S n → A
  | 0, a => a.down
  | n + 1, f => signedTgt S.toGeometricStepSystem (f.down.1 (Fin.last n))

theorem compatible_fits (n : Nat) (f : Positive S n) :
    Fits S.toGeometricStepSystem (signedSrc S.toGeometricStepSystem (f.1 0))
      (List.ofFn f.1) (signedTgt S.toGeometricStepSystem (f.1 (Fin.last n))) := by
  induction n with
  | zero =>
      simp [List.ofFn_succ, Fits]
  | succ n ih =>
      let tail : Positive S n := ⟨fun i => f.1 i.succ, fun i => by
        simpa using f.2 i.succ⟩
      have ht := ih tail
      have hs := f.2 (0 : Fin (n + 1))
      have hs' : signedTgt S.toGeometricStepSystem (f.1 0) =
          signedSrc S.toGeometricStepSystem (f.1 1) := hs
      rw [List.ofFn_succ]
      refine ⟨rfl, ?_⟩
      rw [hs']
      simpa [tail] using ht

theorem fits_compatible {a b : A} (n : Nat) (f : Fin (n + 1) → SignedStep Step)
    (h : Fits S.toGeometricStepSystem a (List.ofFn f) b) : Compatible S n f := by
  induction n generalizing a b with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      have hh : Fits S.toGeometricStepSystem a
          (f 0 :: List.ofFn (fun i : Fin (n + 1) => f i.succ)) b := by
        simpa only [List.ofFn_succ] using h
      have ht : Fits S.toGeometricStepSystem (signedTgt S.toGeometricStepSystem (f 0))
          (List.ofFn (fun i : Fin (n + 1) => f i.succ)) b := by
        exact hh.2
      have hc := ih (fun i : Fin (n + 1) => f i.succ) ht
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · have hh' : Fits S.toGeometricStepSystem (signedTgt S.toGeometricStepSystem (f 0))
            (f (Fin.succ 0) :: List.ofFn (fun i : Fin n => f i.succ.succ)) b := by
          simpa only [List.ofFn_succ] using ht
        exact hh'.1
      · simpa using hc j

theorem fits_source {a b : A} (n : Nat) (f : Fin (n + 1) → SignedStep Step)
    (h : Fits S.toGeometricStepSystem a (List.ofFn f) b) :
    a = signedSrc S.toGeometricStepSystem (f 0) := by
  have hh : Fits S.toGeometricStepSystem a
      (f 0 :: List.ofFn (fun i : Fin n => f i.succ)) b := by
    simpa only [List.ofFn_succ] using h
  exact hh.1

theorem fits_target {a b : A} (n : Nat) (f : Fin (n + 1) → SignedStep Step)
    (h : Fits S.toGeometricStepSystem a (List.ofFn f) b) :
    signedTgt S.toGeometricStepSystem (f (Fin.last n)) = b := by
  induction n generalizing a b with
  | zero =>
      have hh : Fits S.toGeometricStepSystem a [f 0] b := by
        simpa only [List.ofFn_succ, List.ofFn_zero] using h
      simpa [Fits] using hh.2
  | succ n ih =>
      have hh : Fits S.toGeometricStepSystem a
          (f 0 :: List.ofFn (fun i : Fin (n + 1) => f i.succ)) b := by
        simpa only [List.ofFn_succ] using h
      have ht : Fits S.toGeometricStepSystem (signedTgt S.toGeometricStepSystem (f 0))
          (List.ofFn (fun i : Fin (n + 1) => f i.succ)) b := by
        exact hh.2
      simpa using ih (fun i : Fin (n + 1) => f i.succ) ht

def toWord : (n : Nat) → (x : Stratum S n) →
    Word S.toGeometricStepSystem (source S n x) (target S n x)
  | 0, a => .nil a.down
  | n + 1, f => fromList (List.ofFn f.down.1) (compatible_fits S n f.down)

theorem toWord_length (n : Nat) (x : Stratum S n) : (toWord S n x).length = n := by
  cases n with
  | zero => rfl
  | succ n => exact (fromList_length _ _).trans List.length_ofFn

theorem continuous_source (n : Nat) : Continuous (source S n) := by
  cases n with
  | zero => exact continuous_uliftDown
  | succ n =>
      exact (continuous_signedSrc S).comp
        ((continuous_apply 0).comp (continuous_subtype_val.comp continuous_uliftDown))

theorem continuous_target (n : Nat) : Continuous (target S n) := by
  cases n with
  | zero => exact continuous_uliftDown
  | succ n =>
      exact (continuous_signedTgt S).comp
        ((continuous_apply (Fin.last n)).comp (continuous_subtype_val.comp continuous_uliftDown))

/-- Equal-slot reconstruction is continuous on every genuine composable stratum. -/
theorem continuous_flatRealize_family (n : Nat) :
    Continuous (fun xt : Stratum S n × I =>
      GeometricTrace.flatRealize (toWord S n xt.1).toTrace xt.2) := by
  cases n with
  | zero => exact continuous_uliftDown.comp continuous_fst
  | succ n =>
      exact continuous_fromList_family S (n + 1) (source S (n + 1)) (target S (n + 1))
        (fun x => x.down.1) (fun x => compatible_fits S n x.down)
        (continuous_source S (n + 1)) (continuous_subtype_val.comp continuous_uliftDown)

theorem continuous_flatRealize_map (n : Nat) :
    Continuous (fun x : Stratum S n =>
      (GeometricTrace.flatRealize (toWord S n x).toTrace).toContinuousMap) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_flatRealize_family S n)

abbrev Total := Σ n, Stratum S n

theorem continuous_total_flatRealize :
    Continuous (fun x : Total S =>
      (GeometricTrace.flatRealize (toWord S x.1 x.2).toTrace).toContinuousMap) := by
  apply continuous_sigma
  exact continuous_flatRealize_map S

/-- All endpoint-indexed literal words, retaining their endpoints. -/
abbrev TotalWord := Σ a : A, Σ b : A, Word S.toGeometricStepSystem a b

def toTotalWord (x : Total S) : TotalWord S :=
  ⟨source S x.1 x.2, target S x.1 x.2, toWord S x.1 x.2⟩

theorem totalWord_ext {p q : TotalWord S} (hs : p.1 = q.1) (ht : p.2.1 = q.2.1)
    (hl : p.2.2.toList = q.2.2.toList) : p = q := by
  rcases p with ⟨a, b, p⟩
  rcases q with ⟨c, d, q⟩
  cases hs
  cases ht
  have hpq := Word.toList_injective a b hl
  cases hpq
  rfl

theorem toTotalWord_injective : Function.Injective (toTotalWord S) := by
  rintro ⟨n, x⟩ ⟨m, y⟩ h
  have hlen := _root_.congrArg (fun z : TotalWord S => z.2.2.length) h
  have hnm : n = m := by simpa only [toTotalWord, toWord_length] using hlen
  cases hnm
  cases n with
  | zero =>
      have hsrc := _root_.congrArg (fun z : TotalWord S => z.1) h
      have hxy : x = y := ULift.ext x y (by simpa only [toTotalWord, source] using hsrc)
      cases hxy
      rfl
  | succ n =>
      have hlist := _root_.congrArg (fun z : TotalWord S => z.2.2.toList) h
      have hf : x.down.1 = y.down.1 := List.ofFn_injective (by
        simpa only [toTotalWord, toWord, fromList_toList] using hlist)
      exact _root_.congrArg (Sigma.mk (n + 1)) (ULift.ext x y (Subtype.ext hf))

theorem toTotalWord_surjective : Function.Surjective (toTotalWord S) := by
  rintro ⟨a, b, p⟩
  cases hn : p.length with
  | zero =>
      cases p with
      | nil a => exact ⟨⟨0, ULift.up a⟩, rfl⟩
      | cons s p => simp [Word.length_cons] at hn
  | succ n =>
      let f : Fin (n + 1) → SignedStep Step := fun i => p.letters (Fin.cast hn.symm i)
      have hlist : List.ofFn f = p.toList := by
        change List.ofFn (fun i => p.letters (Fin.cast hn.symm i)) = p.toList
        rw [← List.ofFn_congr hn p.letters]
        exact List.ofFn_get _
      have hfits : Fits S.toGeometricStepSystem a (List.ofFn f) b := by
        rw [hlist]
        exact word_fits p
      let x : Positive S n := ⟨f, fits_compatible S n f hfits⟩
      have hs : source S (n + 1) (ULift.up x) = a := (fits_source S n f hfits).symm
      have ht : target S (n + 1) (ULift.up x) = b := fits_target S n f hfits
      refine ⟨⟨n + 1, ULift.up x⟩, ?_⟩
      exact totalWord_ext S hs ht ((fromList_toList _ _).trans hlist)

/-- The actual finite composable tuple carrier and total typed words agree. -/
noncomputable def totalWordEquiv : Total S ≃ TotalWord S :=
  Equiv.ofBijective (toTotalWord S) ⟨toTotalWord_injective S, toTotalWord_surjective S⟩

/-- Transport the genuine coproduct/subtype stratum topology to typed words. -/
@[reducible] noncomputable def totalWordTopology : TopologicalSpace (TotalWord S) :=
  TopologicalSpace.induced (totalWordEquiv S).symm inferInstance

noncomputable def totalWordHomeomorph :
    @Homeomorph (Total S) (TotalWord S) inferInstance (totalWordTopology S) := by
  letI := totalWordTopology S
  refine { toEquiv := totalWordEquiv S, continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply continuous_induced_rng.mpr
    simpa using (continuous_id : Continuous (id : Total S → Total S))
  · exact continuous_induced_dom

theorem continuous_totalWord_flatRealize :
    @Continuous (TotalWord S) C(I, A) (totalWordTopology S) inferInstance
      (fun p => (GeometricTrace.flatRealize p.2.2.toTrace).toContinuousMap) := by
  letI := totalWordTopology S
  have h := (continuous_total_flatRealize S).comp (totalWordHomeomorph S).continuous_invFun
  convert h using 1
  funext p
  have hp := (totalWordEquiv S).apply_symm_apply p
  have hp' : toTotalWord S ((totalWordEquiv S).symm p) = p := hp
  exact _root_.congrArg (fun p : TotalWord S =>
    (GeometricTrace.flatRealize p.2.2.toTrace).toContinuousMap) hp'.symm

def zeroHomeomorph : Stratum S 0 ≃ₜ A := Homeomorph.ulift

def positiveHomeomorph (n : Nat) : Stratum S (n + 1) ≃ₜ Positive S n := Homeomorph.ulift

theorem toWord_toFlatWord_positive (n : Nat) (x : Stratum S (n + 1)) :
    (toWord S (n + 1) x).toFlatWord = ⟨n + 1, x.down.1⟩ := by
  apply List.equivSigmaTuple.symm.injective
  change List.ofFn (toWord S (n + 1) x).letters = List.ofFn x.down.1
  rw [Word.letters, List.ofFn_get]
  exact fromList_toList _ _

/-- Full signed-word coordinates, retaining the empty word's point. -/
def totalCode (x : Total S) : A × FlatWord Step :=
  (source S x.1 x.2, (toWord S x.1 x.2).toFlatWord)

theorem continuous_totalCode_stratum (n : Nat) :
    Continuous (fun x : Stratum S n => totalCode S ⟨n, x⟩) := by
  cases n with
  | zero =>
      exact continuous_uliftDown.prodMk
        (continuous_const : Continuous (fun _ : ULift.{v} A =>
          (⟨0, ([] : List (SignedStep Step)).get⟩ : FlatWord Step)))
  | succ n =>
      have hw : Continuous (fun x : Stratum S (n + 1) =>
          (⟨n + 1, x.down.1⟩ : FlatWord Step)) :=
        continuous_sigmaMk.comp (continuous_subtype_val.comp continuous_uliftDown)
      convert (continuous_source S (n + 1)).prodMk hw using 1
      funext x
      exact Prod.ext rfl (toWord_toFlatWord_positive S n x)

theorem inducing_totalCode_stratum (n : Nat) :
    Topology.IsInducing (fun x : Stratum S n => totalCode S ⟨n, x⟩) := by
  cases n with
  | zero =>
      have hp : Topology.IsInducing
          (Prod.fst ∘ (fun x : Stratum S 0 => totalCode S ⟨0, x⟩)) :=
        (zeroHomeomorph S).isInducing
      exact Topology.IsInducing.of_comp (continuous_totalCode_stratum S 0) continuous_fst hp
  | succ n =>
      have hf : Topology.IsInducing (fun x : Stratum S (n + 1) => x.down.1) :=
        Topology.IsInducing.subtypeVal.comp (positiveHomeomorph S n).isInducing
      have hs := (@Topology.IsEmbedding.sigmaMk Nat (fun k => Fin k → SignedStep Step)
          (fun _ => inferInstance) (n + 1)).isInducing
      have hp : Topology.IsInducing
          (Prod.snd ∘ (fun x : Stratum S (n + 1) => totalCode S ⟨n + 1, x⟩)) := by
        convert hs.comp hf using 1
        funext x
        exact toWord_toFlatWord_positive S n x
      exact Topology.IsInducing.of_comp (continuous_totalCode_stratum S (n + 1)) continuous_snd hp

/-- The coproduct of genuine composable strata is initial in (source, signed word).
The source coordinate is essential at length zero and redundant at positive length. -/
theorem inducing_totalCode : Topology.IsInducing (totalCode S) := by
  apply inducing_sigma.mpr
  refine ⟨inducing_totalCode_stratum S, ?_⟩
  intro n
  let U : Set (A × FlatWord Step) := {x | x.2.1 = n}
  refine ⟨U, ?_, ?_⟩
  · exact (isOpen_discrete ({n} : Set Nat)).preimage
      (continuous_flatWordLength.comp continuous_snd)
  · intro x
    change (toWord S x.1 x.2).length = n ↔ x.1 = n
    rw [toWord_length]

def totalWordCode (p : TotalWord S) : A × FlatWord Step := (p.1, p.2.2.toFlatWord)

theorem inducing_totalWordCode :
    @Topology.IsInducing (TotalWord S) (A × FlatWord Step)
      (totalWordTopology S) inferInstance (totalWordCode S) := by
  letI := totalWordTopology S
  have h := (inducing_totalCode S).comp (totalWordHomeomorph S).symm.isInducing
  convert h using 1
  funext p
  have hp : toTotalWord S ((totalWordEquiv S).symm p) = p :=
    (totalWordEquiv S).apply_symm_apply p
  exact (_root_.congrArg (totalWordCode S) hp).symm

theorem totalWordTopology_eq_induced_code :
    totalWordTopology S = TopologicalSpace.induced (totalWordCode S) inferInstance := by
  letI := totalWordTopology S
  exact (inducing_totalWordCode S).eq_induced

/-- Continuous endpoints and signed words give continuous exact equal-slot
execution. No realization continuity or quotient comparison is assumed. -/
theorem continuous_flatRealize_of_flatWord
    {Z : Type w} [TopologicalSpace Z] (a b : Z → A)
    (p : ∀ z, GeometricTrace S.toGeometricStepSystem (a z) (b z))
    (ha : Continuous a) (_hb : Continuous b)
    (hf : Continuous (fun z => GeometricTrace.flatWord (p z))) :
    Continuous (fun z => (GeometricTrace.flatRealize (p z)).toContinuousMap) := by
  letI := totalWordTopology S
  let f : Z → TotalWord S := fun z => ⟨a z, b z, Word.ofTrace (p z)⟩
  have hcode : Continuous (totalWordCode S ∘ f) := by
    simpa only [f, totalWordCode, Word.toFlatWord_ofTrace, Function.comp_def] using ha.prodMk hf
  have hword : Continuous f := (inducing_totalWordCode S).continuous_iff.mpr hcode
  have hreal := (continuous_totalWord_flatRealize S).comp hword
  convert hreal using 1
  funext z
  exact _root_.congrArg _root_.Path.toContinuousMap
    (GeometricTrace.flatRealize_eq_of_flatWord _ _ (by
      rw [Word.flatWord_toTrace, Word.toFlatWord_ofTrace]))

end ComputationalPaths.Path.GeometricTopology.LiteralWord.Strata
