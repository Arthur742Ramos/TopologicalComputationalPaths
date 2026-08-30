import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Maps.OpenQuotient

/-!
# Continuous complete invariants of final quotients

This module isolates a reusable positive counterpart to product-quotient
obstructions.  If a quotient has its final topology and admits a continuous
complete invariant valued in a discrete space, then the quotient itself is
discrete.  Consequently its quotient map is open, its square is again a
quotient map, the classifier is a homeomorphism, and every finite-arity
operation on quotient classes is continuous for the ordinary product
topology.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open Topology

universe u v w

/-- A continuous invariant on representatives which completely classifies a
final quotient by a discrete type. -/
structure ContinuousCompleteInvariant
    (X : Type u) (Q : Type v) (I : Type w)
    [TopologicalSpace X] [TopologicalSpace Q] [TopologicalSpace I]
    [DiscreteTopology I] where
  quotient : X → Q
  quotient_isQuotientMap : IsQuotientMap quotient
  invariant : X → I
  classifier : Q ≃ I
  classifier_quotient : classifier ∘ quotient = invariant
  invariant_continuous : Continuous invariant

namespace ContinuousCompleteInvariant

variable {X : Type u} {Q : Type v} {I : Type w}
  [TopologicalSpace X] [TopologicalSpace Q] [TopologicalSpace I]
  [DiscreteTopology I]

variable (C : ContinuousCompleteInvariant X Q I)

/-- The complete classifier is continuous by the universal property of the
final quotient. -/
theorem classifier_continuous : Continuous C.classifier := by
  rw [C.quotient_isQuotientMap.continuous_iff]
  rw [C.classifier_quotient]
  exact C.invariant_continuous

/-- A continuous injective map into a discrete classifier forces the quotient
topology itself to be discrete. -/
theorem quotientDiscreteTopology
    (C : ContinuousCompleteInvariant X Q I) : DiscreteTopology Q :=
  DiscreteTopology.of_continuous_injective (classifier_continuous C)
    C.classifier.injective

/-- The complete invariant upgrades canonically from an equivalence to a
homeomorphism. -/
noncomputable def classifierHomeomorph : Q ≃ₜ I := by
  letI : DiscreteTopology Q := quotientDiscreteTopology C
  exact
    { toEquiv := C.classifier
      continuous_toFun := classifier_continuous C
      continuous_invFun := continuous_of_discreteTopology }

/-- Once classified by a continuous discrete invariant, the quotient map is
an open quotient map. -/
theorem quotient_isOpenQuotientMap : IsOpenQuotientMap C.quotient := by
  letI : DiscreteTopology Q := quotientDiscreteTopology C
  exact
    { surjective := C.quotient_isQuotientMap.surjective
      continuous := C.quotient_isQuotientMap.continuous
      isOpenMap := fun U _ => isOpen_discrete _ }

/-- Products preserve the quotient map in this classified discrete case. -/
theorem quotientProd_isQuotientMap :
    IsQuotientMap (Prod.map C.quotient C.quotient) :=
  ((quotient_isOpenQuotientMap C).prodMap
    (quotient_isOpenQuotientMap C)).isQuotientMap

/-- Every binary operation on the classified quotient is continuous for the
ordinary product topology. -/
theorem continuous_binary
    (C : ContinuousCompleteInvariant X Q I) (op : Q × Q → Q) :
    Continuous op := by
  letI : DiscreteTopology Q := quotientDiscreteTopology C
  exact continuous_of_discreteTopology

/-- Every unary operation on the classified quotient is continuous. -/
theorem continuous_unary
    (C : ContinuousCompleteInvariant X Q I) (op : Q → Q) :
    Continuous op := by
  letI : DiscreteTopology Q := quotientDiscreteTopology C
  exact continuous_of_discreteTopology

/-- Equality in the quotient is decided exactly by equality of invariants on
representatives. -/
theorem quotient_eq_iff_invariant_eq (x y : X) :
    C.quotient x = C.quotient y ↔ C.invariant x = C.invariant y := by
  have hx : C.classifier (C.quotient x) = C.invariant x :=
    congrFun C.classifier_quotient x
  have hy : C.classifier (C.quotient y) = C.invariant y :=
    congrFun C.classifier_quotient y
  constructor
  · intro h
    simpa only [hx, hy] using congrArg C.classifier h
  · intro h
    apply C.classifier.injective
    simpa only [hx, hy]

end ContinuousCompleteInvariant

end GeometricTopology
end Path
end ComputationalPaths
