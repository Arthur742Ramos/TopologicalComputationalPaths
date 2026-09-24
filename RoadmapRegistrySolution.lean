import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Maps.OpenQuotient

namespace TopologicalComputationalPathsRoadmapRegistry

universe u v w

variable {A : Type u} {B : Type v} {X : Type w}
  [TopologicalSpace A] [TopologicalSpace B]

abbrev Composable (source target : B → X) :=
  {pair : B × B // target pair.1 = source pair.2}

abbrev RawComposable (q : A → B) (source target : B → X) :=
  {pair : A × A // target (q pair.1) = source (q pair.2)}

def pairProjection (q : A → B) (source target : B → X) :
    RawComposable q source target → Composable source target :=
  fun pair => ⟨(q pair.1.1, q pair.1.2), pair.2⟩

theorem open_arrow_pair_quotient
    (q : A → B) (source target : B → X)
    (hq : IsOpenQuotientMap q) :
    Topology.IsQuotientMap (pairProjection q source target) := by
  let admissible : Set (B × B) :=
    {pair | target pair.1 = source pair.2}
  have hprod : IsOpenQuotientMap (Prod.map q q) := hq.prodMap hq
  have hrestricted : Topology.IsQuotientMap
      (admissible.restrictPreimage (Prod.map q q)) :=
    (hprod.restrictPreimage admissible).isQuotientMap
  change Topology.IsQuotientMap (pairProjection q source target) at hrestricted
  exact hrestricted

theorem ordinary_composition_continuous
    {M : Type*} [TopologicalSpace M]
    (q : A → B) (source target : B → X)
    (hq : IsOpenQuotientMap q)
    (multiply : Composable source target → M)
    (hraw : Continuous (multiply ∘ pairProjection q source target)) :
    Continuous multiply :=
  (open_arrow_pair_quotient q source target hq).continuous_iff.mpr hraw

end TopologicalComputationalPathsRoadmapRegistry
