import ComputationalPaths.Path.Topology.CertifiedTorusPreimage

namespace ComputationalPaths.Path.GeometricTopology.CertifiedTorusPreimage
open Matrix

/-- Any diagonal coordinate criterion for an integer image admits our finite
certificate format. This is an existence proof, not the executable producer. -/
theorem exists_certificate_of_criterion {m n : ℕ} (A : Mat m n)
    (e : Vec m ≃ₗ[ℤ] Vec m) (d : Vec m)
    (criterion : ∀ z, (∃ x, A.mulVec x = z) ↔ ∀ i, d i ∣ e z i) :
    ∃ c : Certificate m n, c.Valid A := by
  classical
  let L : Mat m m := LinearMap.toMatrix' e.toLinearMap
  let Li : Mat m m := LinearMap.toMatrix' e.symm.toLinearMap
  have hL (z : Vec m) : L.mulVec z = e z := LinearMap.toMatrix'_mulVec _ _
  have hLi (z : Vec m) : Li.mulVec z = e.symm z := LinearMap.toMatrix'_mulVec _ _
  have lift_exists (i : Fin m) : ∃ x, A.mulVec x = e.symm (Pi.single i (d i)) := by
    apply (criterion _).mpr
    intro j
    simp only [LinearEquiv.apply_symm_apply]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  choose lift hlift using lift_exists
  let R : Mat n m := fun j i => lift i j
  let T : Mat m n := fun i j => (L * A) i j / d i
  have hentry (i : Fin m) (j : Fin n) :
      (L * A) i j = e (A.mulVec (Pi.single j 1)) i := by
    rw [← hL, mulVec_mulVec, mulVec_single_one]
    rfl
  have hdiv (i : Fin m) (j : Fin n) : d i ∣ (L * A) i j := by
    rw [hentry]
    exact (criterion _).mp ⟨Pi.single j 1, rfl⟩ i
  refine ⟨⟨L, Li, R, T, d⟩, ?_, ?_, ?_, ?_⟩
  · apply Matrix.ext_of_mulVec_single
    intro j
    rw [← mulVec_mulVec, hL, hLi, LinearEquiv.symm_apply_apply, one_mulVec]
  · ext i j
    simp only [diagonal_mul, T]
    exact (Int.mul_ediv_cancel' (hdiv i j)).symm
  · apply Matrix.ext_of_mulVec_single
    intro j
    rw [← mulVec_mulVec, mulVec_single_one]
    change (L * A).mulVec (lift j) = (diagonal d).mulVec (Pi.single j 1)
    rw [← mulVec_mulVec, hlift, hL, LinearEquiv.apply_symm_apply]
    ext i
    by_cases hi : i = j <;> simp [mulVec_diagonal, hi]
  · intro i hi j
    change d i = 0 at hi
    simp [T, hi]

/-- The format is mathematically complete for every rectangular integer matrix,
including empty and rank-deficient cases. No producer termination claim follows. -/
theorem exists_valid_certificate {m n : ℕ} (A : Mat m n) :
    ∃ c : Certificate m n, c.Valid A := by
  classical
  let s := (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
    (FiniteTorusWinding.matrixAction A).range.toIntSubmodule).2
  apply exists_certificate_of_criterion A s.bM.equivFun
    (FiniteTorusWinding.smithNormalFormFactor s)
  intro z
  exact FiniteTorusWinding.matrixAction_mem_range_iff_smithNormalFormFactor_dvd A z

end ComputationalPaths.Path.GeometricTopology.CertifiedTorusPreimage
