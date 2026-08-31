import ComputationalPaths.Path.Topology.FiniteTorusWinding

/-!
# Topological Smith exactness and composition

This module packages the follow-up's substantive comparison theorem: every
finite-torus quotient fundamental group is explicitly homeomorphic to its
integer winding lattice; rectangular integer-matrix maps form a
winding-compatible short exact cokernel diagram with its first-isomorphism
quotient; and composition transports cardinality, finiteness, exponent, and
prime-support information through that diagram.  Every resulting topological
cokernel also has its arbitrary-rank Smith-factor decomposition, with a
prime-power refinement in the finite case.  The same package records the
free-factor/full-rank boundary and the square determinant-index
specialization.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open Set Topology
open scoped BigOperators

noncomputable section

namespace FiniteTorusWinding

/-! A single reusable topological--algebraic comparison certificate carried by
    integer matrix actions on finite-torus loop classes. -/
structure TopologicalSmithExactnessCertificate where
  topological_winding_homeomorph :
    ∀ (n : ℕ), Nonempty (LoopQuot n ≃ₜ (Fin n → ℤ))
  rectangular_winding_short_exact :
    ∀ {n m k : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ)
      (_hB : Function.Injective (matrixAction B)),
      Function.Injective
          (addCokernelCompMap (matrixMapQuotientAddHom A)
            (matrixMapQuotientAddHom B)) ∧
        (addCokernelCompProjection (matrixMapQuotientAddHom A)
            (matrixMapQuotientAddHom B)).ker =
          (addCokernelCompMap (matrixMapQuotientAddHom A)
            (matrixMapQuotientAddHom B)).range ∧
        Function.Surjective
          (addCokernelCompProjection (matrixMapQuotientAddHom A)
            (matrixMapQuotientAddHom B)) ∧
        Function.Injective
            (addCokernelCompMap (matrixAction A) (matrixAction B)) ∧
        (addCokernelCompProjection (matrixAction A) (matrixAction B)).ker =
          (addCokernelCompMap (matrixAction A) (matrixAction B)).range ∧
        Function.Surjective
          (addCokernelCompProjection (matrixAction A) (matrixAction B)) ∧
        (matrixMapQuotientAddHom_cokernel_windingEquiv_comp A B).toAddMonoidHom.comp
            (addCokernelCompMap (matrixMapQuotientAddHom A)
              (matrixMapQuotientAddHom B)) =
          (addCokernelCompMap (matrixAction A) (matrixAction B)).comp
            (matrixMapQuotientAddHom_cokernel_windingEquiv A).toAddMonoidHom ∧
        (matrixMapQuotientAddHom_cokernel_windingEquiv B).toAddMonoidHom.comp
            (addCokernelCompProjection (matrixMapQuotientAddHom A)
              (matrixMapQuotientAddHom B)) =
          (addCokernelCompProjection (matrixAction A) (matrixAction B)).comp
            (matrixMapQuotientAddHom_cokernel_windingEquiv_comp A B).toAddMonoidHom
  first_isomorphism_quotient :
    ∀ {n : ℕ} (A B : Fin n → Fin n → ℤ),
      Nonempty
        ((LoopQuot n ⧸
            (matrixMapQuotientAddHom (matrixCompose A B)).range) ⧸
          (matrixMapQuotientAddHom_cokernel_compProjection A B).ker ≃+
            LoopQuot n ⧸ (matrixMapQuotientAddHom B).range)
  rectangular_composition_profile :
    ∀ {n m k : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ)
      (_hB : Function.Injective (matrixAction B)),
      Nat.card (LoopQuot m ⧸ (matrixMapQuotientAddHom A).range) *
          Nat.card (LoopQuot k ⧸ (matrixMapQuotientAddHom B).range) =
        Nat.card
          (LoopQuot k ⧸ ((matrixMapQuotientAddHom B).comp
            (matrixMapQuotientAddHom A)).range) ∧
      ((Finite (LoopQuot m ⧸ (matrixMapQuotientAddHom A).range) ∧
          Finite (LoopQuot k ⧸ (matrixMapQuotientAddHom B).range)) ↔
        Finite
          (LoopQuot k ⧸ ((matrixMapQuotientAddHom B).comp
            (matrixMapQuotientAddHom A)).range)) ∧
      (∀ (p : ℕ) (_hp : Nat.Prime p),
        p ∣ AddMonoid.exponent
            (LoopQuot k ⧸ ((matrixMapQuotientAddHom B).comp
              (matrixMapQuotientAddHom A)).range) ↔
          p ∣ AddMonoid.exponent
              (LoopQuot m ⧸ (matrixMapQuotientAddHom A).range) ∨
            p ∣ AddMonoid.exponent
              (LoopQuot k ⧸ (matrixMapQuotientAddHom B).range)) ∧
      (∀ _hcop : Nat.Coprime
          (AddMonoid.exponent
            (LoopQuot m ⧸ (matrixMapQuotientAddHom A).range))
          (AddMonoid.exponent
            (LoopQuot k ⧸ (matrixMapQuotientAddHom B).range)),
        AddMonoid.exponent
            (LoopQuot k ⧸ ((matrixMapQuotientAddHom B).comp
              (matrixMapQuotientAddHom A)).range) =
          AddMonoid.exponent
              (LoopQuot m ⧸ (matrixMapQuotientAddHom A).range) *
            AddMonoid.exponent
              (LoopQuot k ⧸ (matrixMapQuotientAddHom B).range))
  smith_cokernel_profile :
    ∀ {n m : ℕ} (A : Fin m → Fin n → ℤ),
      Nonempty
          ((LoopQuot m ⧸ (matrixMapQuotientAddHom A).range) ≃+
            (∀ i : Fin m, ZMod (smithNormalFormFactor
              (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
                (matrixAction A).range.toIntSubmodule).2 i).natAbs)) ∧
      (Finite (LoopQuot m ⧸ (matrixMapQuotientAddHom A).range) ↔
        Module.finrank ℤ ((matrixAction A).range.toIntSubmodule) =
          Module.finrank ℤ (Fin m → ℤ)) ∧
      (AddMonoid.exponent
          (LoopQuot m ⧸ (matrixMapQuotientAddHom A).range) =
        Finset.univ.lcm (fun i : Fin m =>
          (smithNormalFormFactor
            (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
              (matrixAction A).range.toIntSubmodule).2 i).natAbs)) ∧
      (∀ (p : ℕ) (_hp : Nat.Prime p),
        p ∣ AddMonoid.exponent
            (LoopQuot m ⧸ (matrixMapQuotientAddHom A).range) ↔
          ∃ i : Fin m, p ∣ (smithNormalFormFactor
            (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
              (matrixAction A).range.toIntSubmodule).2 i).natAbs)
  determinant_index_compatibility :
    ∀ {n : ℕ} (A : Fin n → Fin n → ℤ) (hA : Matrix.det A ≠ 0),
      Nat.card (LoopQuot n ⧸ (matrixMapQuotientAddHom A).range) =
          Int.natAbs (Matrix.det A) ∧
      (∏ i : Fin n, (Submodule.smithNormalFormCoeffs
        (Pi.basisFun ℤ (Fin n)) (matrixAction_cokernel_full_rank A hA) i).natAbs) =
          Int.natAbs (Matrix.det A)
  prime_power_torsion_profile :
    ∀ {n m : ℕ} (A : Fin m → Fin n → ℤ)
      (_hA : ∀ i : Fin m, smithNormalFormFactor
        (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
          (matrixAction A).range.toIntSubmodule).2 i ≠ 0),
      Nonempty
          ((LoopQuot m ⧸ (matrixMapQuotientAddHom A).range) ≃+
            (∀ i : Fin m, ∀ p : (smithNormalFormFactor
              (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
                (matrixAction A).range.toIntSubmodule).2 i).natAbs.primeFactors,
              ZMod (p ^ ((smithNormalFormFactor
                (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
                  (matrixAction A).range.toIntSubmodule).2 i).natAbs.factorization p)))) ∧
        Nat.card (LoopQuot m ⧸ (matrixMapQuotientAddHom A).range) =
          ∏ i : Fin m, ∏ p : (smithNormalFormFactor
            (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
              (matrixAction A).range.toIntSubmodule).2 i).natAbs.primeFactors,
            (p : ℕ) ^ ((smithNormalFormFactor
              (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
                (matrixAction A).range.toIntSubmodule).2 i).natAbs.factorization p)

/-! The certificate is assembled entirely from the proved rectangular
    winding and Smith-normal-form theorems above; no evaluator escape or
    additional axiom is used. -/
theorem topologicalSmithExactnessCertificate :
    TopologicalSmithExactnessCertificate where
  topological_winding_homeomorph := by
    intro n
    exact ⟨loopQuotHomeomorphIntVector n⟩
  rectangular_winding_short_exact := by
    intro n m k A B hB
    exact matrixMapQuotientAddHom_rectangular_cokernel_winding_shortExact
      A B hB
  first_isomorphism_quotient := by
    intro n A B
    exact ⟨matrixMapQuotientAddHom_cokernel_compProjection_quotientKerEquiv A B⟩
  rectangular_composition_profile := by
    intro n m k A B hB
    constructor
    · exact matrixMapQuotientAddHom_rectangular_cokernel_card_mul_of_matrixAction_injective
        A B hB
    constructor
    · exact matrixMapQuotientAddHom_rectangular_cokernel_finite_iff_of_matrixAction_injective
        A B hB
    constructor
    · intro p hp
      exact matrixMapQuotientAddHom_rectangular_cokernel_exponent_prime_dvd_iff_of_matrixAction_injective
        A B hB p hp
    · intro hcop
      exact matrixMapQuotientAddHom_rectangular_cokernel_exponent_eq_mul_of_matrixAction_coprime_injective
        A B hB hcop
  smith_cokernel_profile := by
    intro n m A
    refine ⟨⟨matrixMapQuotientAddHom_cokernel_smithAddEquiv A⟩,
      matrixMapQuotientAddHom_cokernel_finite_iff_full_rank A,
      matrixMapQuotientAddHom_cokernel_exponent_eq_smithFactorLcm A, ?_⟩
    intro p hp
    exact matrixMapQuotientAddHom_cokernel_exponent_prime_dvd_iff_smithFactor
      A p hp
  determinant_index_compatibility := by
    intro n A hA
    exact ⟨matrixMapQuotientAddHom_cokernel_card_eq_natAbs_det A hA,
      matrixMapQuotientAddHom_smithNormalFormProduct_eq_natAbs_det A hA⟩
  prime_power_torsion_profile := by
    intro n m A hA
    exact ⟨⟨matrixMapQuotientAddHom_cokernel_smithPrimePowerEquiv A hA⟩,
      matrixMapQuotientAddHom_cokernel_smithPrimePowerEquiv_card_eq_primePowerProduct
        A hA⟩

end FiniteTorusWinding
end
end GeometricTopology
end Path
end ComputationalPaths
