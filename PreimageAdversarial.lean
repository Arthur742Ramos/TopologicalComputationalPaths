import PreimageTests

open ComputationalPaths.Path.GeometricTopology.CertifiedTorusPreimage
set_option maxRecDepth 100000

/- Each certificate law has an explicit tampering regression. Invalid data must
be rejected even for an otherwise soluble target. No native evaluator axiom. -/
example : solve Divisible.A { Divisible.cert with Linv := 0 } Divisible.z = .invalid := by decide
example : solve Divisible.A { Divisible.cert with R := 0 } Divisible.z = .invalid := by decide
example : solve Divisible.A { Divisible.cert with T := 0 } Divisible.z = .invalid := by decide
example : solve Divisible.A { Divisible.cert with d := 0 } Divisible.z = .invalid := by decide

/- Changing T in a zero-modulus row preserves the first three matrix identities,
but must fail the fourth condition: otherwise the claimed kernel generator can
lose actual solutions. -/
def badZeroRow : Certificate 2 2 := { SingularYes.cert with T := ![![1, 2], ![1, 0]] }
example : badZeroRow.Linv * badZeroRow.L = 1 ∧
    badZeroRow.L * SingularYes.A = Matrix.diagonal badZeroRow.d * badZeroRow.T ∧
    badZeroRow.L * SingularYes.A * badZeroRow.R = Matrix.diagonal badZeroRow.d := by decide
example : solve SingularYes.A badZeroRow SingularYes.z = .invalid := by decide

/- An all-zero map has an all-free source kernel and equality obstructions. -/
def zeroCert : Certificate 2 2 where
  L := 1
  Linv := 1
  R := 0
  T := 0
  d := 0
example : zeroCert.Valid 0 := by decide
example : solve (0 : Mat 2 2) zeroCert ![0, 1] = .obstructed ⟨1, by decide⟩ := by decide
example : zeroCert.kernelGenerator = (1 : Mat 2 2) := by decide
