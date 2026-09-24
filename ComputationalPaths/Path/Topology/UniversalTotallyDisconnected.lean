import ComputationalPaths.Path.Topology.UniversalQuotientTransfer
import ComputationalPaths.Path.Topology.UniversalGlobalBasedFiber
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The universal path-class quotient on totally disconnected spaces

Every continuous interval path in a totally disconnected space is constant.
The universal path-class projection is therefore a homeomorphism. This gives
an unconditional global open-quotient example, even without local path
connectedness.
-/

namespace ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite

open scoped ContinuousMap Topology

universe u
variable {A : Type u} [TopologicalSpace A] [TotallyDisconnectedSpace A]

/-- The class of a path determines the path itself when all interval paths are
constant. -/
theorem universalPathClassProjection_injective_of_totallyDisconnected :
    Function.Injective (universalPathClassProjection (A := A)) := by
  intro γ δ h
  have hsource : γ 0 = δ 0 := by
    have h' := _root_.congrArg
      (fun c : ScopedClass (universalPresentation (A := A)) =>
        scopedSrc (universalPresentation (A := A)) c) h
    simpa [universalPathClassProjection, universalTraceSensitiveChoice] using h'
  apply ContinuousMap.ext
  intro t
  calc
    γ t = γ 0 := TotallyDisconnectedSpace.eq_of_continuous γ γ.continuous t 0
    _ = δ 0 := hsource
    _ = δ t := TotallyDisconnectedSpace.eq_of_continuous δ δ.continuous 0 t

/-- The quotient projection is a homeomorphism on a totally disconnected
space, with no local path-connectedness assumption. -/
theorem universalPathClassProjection_isHomeomorph_of_totallyDisconnected :
    IsHomeomorph (universalPathClassProjection (A := A)) := by
  exact (isHomeomorph_iff_isQuotientMap_injective).2
    ⟨universalPathClassProjection_isQuotient (A := A),
      universalPathClassProjection_injective_of_totallyDisconnected (A := A)⟩

theorem universalPathClassProjection_isOpenMap_of_totallyDisconnected :
    IsOpenMap (universalPathClassProjection (A := A)) := by
  exact (universalPathClassProjection_isHomeomorph_of_totallyDisconnected
    (A := A)).isOpenMap

/-- Ordinary composable pairs carry the quotient topology in the totally
disconnected universal presentation. -/
theorem universalProductCompatibility_of_totallyDisconnected :
    ProductQuotientCompatibility (universalPresentation (A := A)) :=
  universalProductCompatibility_of_open_path_projection
    (universalPathClassProjection_isOpenMap_of_totallyDisconnected (A := A))

/-- Composition is continuous for the ordinary composable-pair subspace. -/
theorem continuous_universalComposition_of_totallyDisconnected :
    Continuous (scopedCompositionOnProduct (universalPresentation (A := A)) :
      ScopedComposablePair (universalPresentation (A := A)) →
        ScopedClass (universalPresentation (A := A))) :=
  continuous_universalComposition_of_open_path_projection
    (universalPathClassProjection_isOpenMap_of_totallyDisconnected (A := A))

/-- The ordinary based-loop quotient is the actual based-arrow subspace of
the global scoped quotient in this case. -/
noncomputable def universalBasedFiberHomeomorph_of_totallyDisconnected (x : A) :
    QuotientFundamentalGroup.LoopQuot A x ≃ₜ universalBasedArrowSet x :=
  basedGlobalFiberHomeomorph x
    (universalPathClassProjection_isOpenMap_of_totallyDisconnected (A := A))

end ComputationalPaths.Path.GeometricTopology.ScopedGeometricRewrite
