import ComputationalPaths.Path.Topology.FlatEqualSlotRealization

/-! # Continuity of equal-slot concatenation for endpoint-varying families -/

namespace ComputationalPaths.Path.GeometricTopology

open unitInterval
universe u v

/-- Fixed slot counts permit continuous concatenation even when endpoints vary.
The zero-slot cases omit the corresponding factor, as in the flat realization. -/
theorem weightedConcatenation_continuous_family
    {X : Type u} [TopologicalSpace X] {Z : Type v} [TopologicalSpace Z]
    {a b c : Z → X} {m n : Nat} (w : WeightedSlotReparam m n)
    (hm : ∀ z, m = 0 → a z = b z) (hn : ∀ z, n = 0 → b z = c z)
    (p : ∀ z, _root_.Path (a z) (b z))
    (q : ∀ z, _root_.Path (b z) (c z))
    (hp : Continuous (fun zt : Z × I => p zt.1 zt.2))
    (hq : Continuous (fun zt : Z × I => q zt.1 zt.2)) :
    Continuous (fun zt : Z × I =>
      weightedConcatenation w (hm zt.1) (hn zt.1) (p zt.1) (q zt.1) zt.2) := by
  cases m with
  | zero =>
      cases n with
      | zero =>
          have ha : Continuous a := by
            simpa [Function.comp_def] using hp.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : Z => (0 : I))))
          simpa [weightedConcatenation, Function.comp_def] using ha.comp continuous_fst
      | succ n => simpa [weightedConcatenation] using hq
  | succ m =>
      cases n with
      | zero => simpa [weightedConcatenation] using hp
      | succ n =>
          have htrans := _root_.Path.trans_continuous_family p hp q hq
          have hparam : Continuous (fun zt : Z × I => (zt.1, w.map zt.2)) :=
            continuous_fst.prodMk (w.continuous_map.comp continuous_snd)
          simpa [weightedConcatenation, _root_.Path.reparam, Function.comp_def, Function.HasUncurry.uncurry] using htrans.comp hparam

end ComputationalPaths.Path.GeometricTopology
