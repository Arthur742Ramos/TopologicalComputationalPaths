import ComputationalPaths.Path.Topology.TopologicalCompPathEvaluation
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# The fundamental-groupoid quotient of total computational paths

The geometric coordinate of a coherent open computational path determines an
arrow in Mathlib's fundamental groupoid.  Its coherence witness identifies
that arrow with the arrow obtained from the realized computational trace.
Composition and reversal descend to the quotient exactly as expected.

This is the quotient bridge after the topological evaluation phase.  It does
not identify the total carrier itself with a quotient: the carrier continues
to retain its explicit trace and geometric coordinates.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open CategoryTheory
open scoped ContinuousMap FundamentalGroupoid Topology

attribute [local instance] _root_.Path.Homotopic.setoid

universe u v

namespace TotalOpenGeometricCompPath

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  (S : ContinuousGeometricStepSystem A Step)

/-- The fundamental-groupoid arrow represented by a total path's geometric
representative. -/
noncomputable def fundamentalArrow (p : TotalPath S) :
    FundamentalGroupoid.fromTop (X := TopCat.of A) p.src ⟶
      FundamentalGroupoid.fromTop (X := TopCat.of A) p.tgt :=
  Quotient.mk' p.geometricPath

/-- The same arrow read from the realized computational trace. -/
noncomputable def traceArrow (p : TotalPath S) :
    FundamentalGroupoid.fromTop (X := TopCat.of A) p.src ⟶
      FundamentalGroupoid.fromTop (X := TopCat.of A) p.tgt :=
  Quotient.mk' (GeometricTrace.realize p.trace)

theorem traceArrow_eq_fundamentalArrow (p : TotalPath S) :
    traceArrow S p = fundamentalArrow S p := by
  exact Quotient.sound p.path.coherent.symm

theorem fundamentalArrow_totalRefl (a : A) :
    fundamentalArrow S (totalRefl S a) =
      𝟙 (FundamentalGroupoid.fromTop (X := TopCat.of A) a) := by
  rfl

theorem fundamentalArrow_totalTrans (c : TotalComposable A Step S) :
    fundamentalArrow S (totalTrans S c) =
      fundamentalArrow S (ofFiber S c.left) ≫
        fundamentalArrow S (ofFiber S c.right) := by
  rfl

theorem fundamentalArrow_totalSymm (p : TotalPath S) :
    fundamentalArrow S (totalSymm S p) =
      CategoryTheory.Groupoid.inv (fundamentalArrow S p) := by
  rfl

/-! ## A compact quotient-bridge certificate -/

structure TopologicalCompPathFundamentalGroupoidCertificate where
  trace_geometric_coherence :
    ∀ p : TotalPath S, traceArrow S p = fundamentalArrow S p
  identity_descends :
    ∀ a : A,
      fundamentalArrow S (totalRefl S a) =
        𝟙 (FundamentalGroupoid.fromTop (X := TopCat.of A) a)
  composition_descends :
    ∀ c : TotalComposable A Step S,
      fundamentalArrow S (totalTrans S c) =
        fundamentalArrow S (ofFiber S c.left) ≫
          fundamentalArrow S (ofFiber S c.right)
  reversal_descends :
    ∀ p : TotalPath S,
      fundamentalArrow S (totalSymm S p) =
        CategoryTheory.Groupoid.inv (fundamentalArrow S p)

noncomputable def topologicalCompPathFundamentalGroupoidCertificate :
    TopologicalCompPathFundamentalGroupoidCertificate S where
  trace_geometric_coherence := traceArrow_eq_fundamentalArrow S
  identity_descends := fundamentalArrow_totalRefl S
  composition_descends := fundamentalArrow_totalTrans S
  reversal_descends := fundamentalArrow_totalSymm S

/-! A direct computational loop remains available at the quotient interface. -/
noncomputable def fundamentalArrowLoopCertificate (p : TotalPath S) :
    ComputationalPaths.Path
      (GeometricTrace.traceLength p.trace)
      (GeometricTrace.traceLength p.trace) :=
  ComputationalPaths.Path.trans
    (ComputationalPaths.Path.refl (GeometricTrace.traceLength p.trace))
    (ComputationalPaths.Path.refl (GeometricTrace.traceLength p.trace))

end TotalOpenGeometricCompPath
end GeometricTopology
end Path
end ComputationalPaths
