import ComputationalPaths.Path.Topology.CertifiedTorusPreimageExistence

namespace TorusPreimageSubmission
open ComputationalPaths.Path.GeometricTopology.CertifiedTorusPreimage
theorem main_result {m n : ℕ} (A : Mat m n) :
    (∃ c : Certificate m n, c.Valid A) ∧
    ∀ (c : Certificate m n) (z : Vec m),
      Torus.TopologicallyCorrect A c z (solve A c z) :=
  ⟨exists_valid_certificate A, Torus.solve_topologically_correct A⟩
end TorusPreimageSubmission
