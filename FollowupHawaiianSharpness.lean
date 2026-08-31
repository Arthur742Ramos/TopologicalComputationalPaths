import FollowupSolution
import Solution

/-!
# Hawaiian-earring sharpness for the quotient-product theorem

This adapter deliberately lives outside the Comparator statement/solution
pair because the accepted baseline supplies a generic quotient-topology
instance.  Keeping it separate preserves an identical exported statement
surface while still checking the direct application to the accepted
Fabel-style Hawaiian-earring facts.
-/

namespace TopologicalComputationalPathsFollowup

open Topology

attribute [local instance] _root_.Path.Homotopic.setoid

/-- The accepted Fabel-style Hawaiian-earring facts instantiate the abstract
sharpness theorem: the square of the genuine based-loop quotient map is not
a quotient map. -/
theorem hawaiianEarring_loopQuotientProd_not_quotient
    (F : TopologicalComputationalPaths.FabelHawaiianEarringFacts) :
    ¬ IsQuotientMap
      (ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.loopQuotientProdMap
        TopologicalComputationalPaths.hawaiianBase
        TopologicalComputationalPaths.hawaiianBase) := by
  apply ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.not_isQuotientMap_loopQuotientProd_of_not_continuous
  exact TopologicalComputationalPaths.FabelHawaiianEarringFacts.multiplication_not_continuous F

end TopologicalComputationalPathsFollowup
