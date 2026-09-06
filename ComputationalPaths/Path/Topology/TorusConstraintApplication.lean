import ComputationalPaths.Path.Topology.CertifiedTorusPreimage

/-! A worked simultaneous-constraint application. Four observed winding
channels depend on three source phases, with two redundant observations.
The exact solution family and both consistency equations are proved, not
inferred from a single numerical example. This is an application of classical
integer linear algebra, not a claim of new topology. -/

namespace ComputationalPaths.Path.GeometricTopology.CertifiedTorusPreimage.Coupled
open Matrix FiniteTorusWinding

def observations : Mat 4 3 := ![![2, 4, 0], ![0, 3, 3], ![2, 7, 3], ![4, 8, 0]]

theorem two_constraints (a b : ℤ) (x : Vec 3) :
    observations.mulVec x = ![a, b, a + b, 2 * a] ↔
      2 * x 0 + 4 * x 1 = a ∧ 3 * x 1 + 3 * x 2 = b := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [observations, mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
    omega
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i <;> simp [observations, mulVec, dotProduct, Fin.sum_univ_succ] <;> omega

theorem lattice_family (a b : ℤ) (ha : 2 ∣ a) (hb : 3 ∣ b) (x : Vec 3) :
    observations.mulVec x = ![a, b, a + b, 2 * a] ↔
      ∃ t : ℤ, x = ![a / 2 - 2 * t, t, b / 3 - t] := by
  have ha' : 2 * (a / 2) = a := Int.mul_ediv_cancel' ha
  have hb' : 3 * (b / 3) = b := Int.mul_ediv_cancel' hb
  rw [two_constraints]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨x 1, ?_⟩
    ext i
    fin_cases i <;> simp <;> omega
  · rintro ⟨t, rfl⟩
    simp
    omega

/-- All loop-class solutions of a parameterized simultaneous observation
problem, including its free integer parameter. -/
theorem topological_family (a b : ℤ) (ha : 2 ∣ a) (hb : 3 ∣ b) (q : LoopQuot 3) :
    matrixMapQuotientMap observations q = decode ![a, b, a + b, 2 * a] ↔
      ∃ t : ℤ, q = decode ![a / 2 - 2 * t, t, b / 3 - t] := by
  rw [Torus.preimage_iff, lattice_family a b ha hb]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, (decode_encode q).symm.trans (congrArg decode ht)⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, encode_decode _⟩

/-- Inconsistent redundant observations give a free (zero-modulus)
obstruction, regardless of any divisibility tests on the first two channels. -/
theorem inconsistent_observations (a b c d : ℤ) (h : c ≠ a + b ∨ d ≠ 2 * a) :
    ¬ ∃ q, matrixMapQuotientMap observations q = decode ![a, b, c, d] := by
  rw [Torus.exists_preimage_iff]
  rintro ⟨x, hx⟩
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  have h2 := congrFun hx 2
  have h3 := congrFun hx 3
  simp [observations, mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2 h3
  omega

end ComputationalPaths.Path.GeometricTopology.CertifiedTorusPreimage.Coupled
