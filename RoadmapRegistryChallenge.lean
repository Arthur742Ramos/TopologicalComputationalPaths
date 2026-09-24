import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Maps.OpenQuotient

/-!
The ordinary composable-pair topology is a pullback of the product topology.
This statement isolates the open-quotient step used in the scoped-path paper.
It is independent of the project's implementation of paths and rewriting.
-/

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

/-- An open quotient on arrows gives a quotient on ordinary composable pairs.
The endpoint maps need no continuity assumption for this transfer. -/
theorem open_arrow_pair_quotient
    (q : A → B) (source target : B → X)
    (hq : IsOpenQuotientMap q) :
    Topology.IsQuotientMap (pairProjection q source target) := by
  sorry

/-- A multiplication law on ordinary composable pairs is continuous once
its pullback along the raw pair projection is continuous. -/
theorem ordinary_composition_continuous
    {M : Type*} [TopologicalSpace M]
    (q : A → B) (source target : B → X)
    (hq : IsOpenQuotientMap q)
    (multiply : Composable source target → M)
    (hraw : Continuous (multiply ∘ pairProjection q source target)) :
    Continuous multiply := by
  sorry

end TopologicalComputationalPathsRoadmapRegistry
