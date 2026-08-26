import ComputationalPaths.Path.Basic.Core
import Mathlib.Topology.Constructions
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Order

/-!
# Topology of raw computational paths

Raw computational paths are finite trace records rather than continuous maps
from an interval.  This file therefore equips them with the trace-length
topology: two paths are observed through the length of their rewrite trace.
The topology is non-discrete whenever a length fiber contains multiple raw
traces, while path composition, reversal, and reflexivity are continuous.

This is intentionally a topology on the raw record.  No `RwEq` quotient is
taken, so the construction does not erase the distinction between traces.
-/

open TopologicalSpace

namespace ComputationalPaths
namespace Path
namespace RawTopology

universe u

/-! ## The trace-length topology -/

/-- The observable computation depth of a raw path. -/
def traceLength {A : Type u} {a b : A} (p : Path a b) : Nat :=
  p.steps.length

/-- Rewrite steps inherit the topology of their ordered endpoint pair. -/
noncomputable instance stepTopologicalSpace {A : Type u} [TopologicalSpace A] :
    TopologicalSpace (Step A) :=
  TopologicalSpace.induced (fun s : Step A => (s.src, s.tgt)) inferInstance

/-- Raw paths are topologized by their trace length. -/
noncomputable instance pathTopologicalSpace {A : Type u} [TopologicalSpace A]
    {a b : A} : TopologicalSpace (Path a b) :=
  TopologicalSpace.induced (traceLength : Path a b → Nat) inferInstance

theorem continuous_traceLength {A : Type u} [TopologicalSpace A]
    {a b : A} : Continuous (traceLength : Path a b → Nat) :=
  continuous_induced_dom

theorem continuous_step_endpoints {A : Type u} [TopologicalSpace A] :
    Continuous (fun s : Step A => (s.src, s.tgt)) :=
  continuous_induced_dom

theorem continuous_step_src {A : Type u} [TopologicalSpace A] :
    Continuous (fun s : Step A => s.src) :=
  continuous_fst.comp continuous_step_endpoints

theorem continuous_step_tgt {A : Type u} [TopologicalSpace A] :
    Continuous (fun s : Step A => s.tgt) :=
  continuous_snd.comp continuous_step_endpoints

theorem traceLength_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    traceLength (Path.trans p q) = traceLength p + traceLength q := by
  simp [traceLength, Path.trans, List.length_append]

theorem traceLength_symm {A : Type u} {a b : A} (p : Path a b) :
    traceLength (Path.symm p) = traceLength p := by
  simp [traceLength, Path.symm]

theorem traceLength_refl {A : Type u} {a : A} :
    traceLength (Path.refl a) = 0 := by
  rfl

theorem continuous_nat_add :
    Continuous (fun n : Nat × Nat => n.1 + n.2) :=
  continuous_of_discreteTopology

theorem continuous_path_trans {A : Type u} [TopologicalSpace A]
    {a b c : A} :
    Continuous (fun pq : Path a b × Path b c => Path.trans pq.1 pq.2) := by
  apply continuous_induced_rng.mpr
  have hleft : Continuous (fun p : Path a b => traceLength p) :=
    continuous_traceLength
  have hright : Continuous (fun q : Path b c => traceLength q) :=
    continuous_traceLength
  have hcomp :
      (traceLength : Path a c → Nat) ∘
          (fun pq : Path a b × Path b c => Path.trans pq.1 pq.2) =
        (fun pq : Path a b × Path b c => traceLength pq.1 + traceLength pq.2) := by
    funext pq
    exact traceLength_trans pq.1 pq.2
  rw [hcomp]
  exact continuous_nat_add.comp
    ((hleft.comp continuous_fst).prodMk (hright.comp continuous_snd))

theorem continuous_path_symm {A : Type u} [TopologicalSpace A]
    {a b : A} : Continuous (Path.symm : Path a b → Path b a) := by
  apply continuous_induced_rng.mpr
  rw [show (traceLength : Path b a → Nat) ∘ Path.symm =
      (traceLength : Path a b → Nat) by
        funext p
        exact traceLength_symm p]
  exact continuous_traceLength

/-! ## What this topology remembers -/

/-- Equal trace lengths are topologically indistinguishable. -/
theorem inseparable_of_equal_traceLength {A : Type u} [TopologicalSpace A]
    {a b : A} {p q : Path a b}
    (h : traceLength p = traceLength q) : Inseparable p q := by
  simp only [Inseparable, nhds_induced]
  rw [h]

/-- The topology is a genuine trace filtration, not a discrete topology by
definition: its open information factors through `traceLength`. -/
theorem path_open_information_factors_through_traceLength
    {A : Type u} [TopologicalSpace A] {a b : A} :
    ∀ s : Set (Path a b), IsOpen s →
      ∀ p q, traceLength p = traceLength q → (p ∈ s ↔ q ∈ s) := by
  intro s hs p q h
  have hInsep := inseparable_of_equal_traceLength (p := p) (q := q) h
  exact (inseparable_iff_forall_isOpen.1 hInsep) s hs

/-! ## A reusable certificate -/

/-- The topological structure and continuous raw-path operations supplied by
the trace-length construction. -/
structure TopologicalPathCertificate (A : Type u) [TopologicalSpace A] where
  step_endpoints_continuous :
    Continuous (fun s : Step A => (s.src, s.tgt))
  traceLength_continuous {a b : A} : Continuous (traceLength : Path a b → Nat)
  trans_continuous {a b c : A} :
    Continuous (fun pq : Path a b × Path b c => Path.trans pq.1 pq.2)
  symm_continuous {a b : A} :
    Continuous (Path.symm : Path a b → Path b a)

noncomputable def topologicalPathCertificate {A : Type u} [TopologicalSpace A] :
    @TopologicalPathCertificate A ‹TopologicalSpace A› where
  step_endpoints_continuous := continuous_step_endpoints
  traceLength_continuous := continuous_traceLength
  trans_continuous := continuous_path_trans
  symm_continuous := continuous_path_symm

end RawTopology
end Path
end ComputationalPaths
