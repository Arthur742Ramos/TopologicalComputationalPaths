import ComputationalPaths.Path.Topology.CayleyRoseCovering
import ComputationalPaths.Path.Topology.FlatEqualSlotRealization

/-!
# Geometric completeness from actual lifts of rose words

Every signed word is lifted by explicit Cayley edges. Its endpoint records
the evaluated free-group word. Uniqueness of lifts and homotopy invariance of
their endpoints then prove completeness of the no-named-rule rose presentation.
The covering map used here is the concrete projection constructed separately;
neither a free-group homotopy invariant nor completeness is an assumption.

For arbitrary trace parentheses we first use the checked structural reduced-
word normalization and its geometric soundness. No contraction or general
classification of all paths in the covering space is needed for this result
about homotopies between realized finite traces.
-/

namespace ComputationalPaths.Path.GeometricTopology.RoseLiftedWords

open RoseReducedWords CayleyTreeGeometry
open unitInterval
open scoped Topology

noncomputable section

abbrev RoseTrace := Trace GeometricRose.loopA GeometricRose.loopB
abbrev rosePresentation := presentation GeometricRose.loopA GeometricRose.loopB

def letterValue (s : Label × Bool) : G :=
  cond s.2 (FreeGroup.of s.1) (FreeGroup.of s.1)⁻¹

theorem mk_cons (s : Label × Bool) (l : List (Label × Bool)) :
    FreeGroup.mk (s :: l) = letterValue s * FreeGroup.mk l := by
  rcases s with ⟨s, b⟩
  cases b <;> rfl

/-- A negative generator follows the preceding positively oriented edge back. -/
def liftLetter (g : G) : (s : Label × Bool) →
    _root_.Path (Tree.vertex g) (Tree.vertex (g * letterValue s))
  | (i, true) => edge g i
  | (i, false) => (edge (g * (FreeGroup.of i)⁻¹) i).symm.cast
      (by simp [mul_assoc]) rfl

/-- Actual concatenated edge paths, with group associativity used only to cast
the declared endpoint. Parenthesization matches the reconstructed trace. -/
def liftWord (g : G) : (l : List (Label × Bool)) →
    _root_.Path (Tree.vertex g) (Tree.vertex (g * FreeGroup.mk l))
  | [] => (_root_.Path.refl (Tree.vertex g)).cast rfl (by simp [← FreeGroup.one_eq_mk])
  | s :: l => ((liftLetter g s).trans (liftWord (g * letterValue s) l)).cast rfl
      (by simp only [mk_cons, mul_assoc])

theorem project_liftLetter (g : G) (s : Label × Bool) (t : I) :
    CayleyRoseCovering.project (liftLetter g s t) =
      GeometricTrace.realize (decodeLetter GeometricRose.loopA GeometricRose.loopB s) t := by
  rcases s with ⟨i, b⟩
  cases b with
  | true => exact CayleyRoseCovering.project_edge_apply g i t
  | false =>
      change CayleyRoseCovering.project (edge (g * (FreeGroup.of i)⁻¹) i (unitInterval.symm t)) =
        (system GeometricRose.loopA GeometricRose.loopB).realize i (unitInterval.symm t)
      exact CayleyRoseCovering.project_edge_apply _ i (unitInterval.symm t)

private theorem project_trans {a b c : Tree}
    (p : _root_.Path a b) (q : _root_.Path b c)
    (p' q' : _root_.Path GeometricRose.base GeometricRose.base)
    (hp : ∀ t, CayleyRoseCovering.project (p t) = p' t)
    (hq : ∀ t, CayleyRoseCovering.project (q t) = q' t) (t : I) :
    CayleyRoseCovering.project ((p.trans q) t) = (p'.trans q') t := by
  rw [_root_.Path.trans_apply, _root_.Path.trans_apply]
  split_ifs <;> first | exact hp _ | exact hq _

/-- Projection of the explicit lifted word is the actual binary realized path. -/
theorem project_liftWord (g : G) (l : List (Label × Bool)) (t : I) :
    CayleyRoseCovering.project (liftWord g l t) =
      GeometricTrace.realize (decode GeometricRose.loopA GeometricRose.loopB l) t := by
  induction l generalizing g t with
  | nil =>
      change CayleyRoseCovering.project (Tree.vertex g) = GeometricRose.base
      exact CayleyRoseCovering.project_vertex g
  | cons s l ih =>
      change CayleyRoseCovering.project
          (((liftLetter g s).trans (liftWord (g * letterValue s) l)) t) =
        ((GeometricTrace.realize (decodeLetter GeometricRose.loopA GeometricRose.loopB s)).trans
          (GeometricTrace.realize (decode GeometricRose.loopA GeometricRose.loopB l))) t
      exact project_trans _ _ _ _ (project_liftLetter g s) (ih _) t

theorem cover : IsCoveringMap CayleyRoseCovering.project := CayleyRoseCovering.covering.isCoveringMap

theorem start_eq_project_vertex (p : _root_.Path GeometricRose.base GeometricRose.base) (g : G) :
    p.toContinuousMap 0 = CayleyRoseCovering.project (Tree.vertex g) :=
  p.source.trans (CayleyRoseCovering.project_vertex g).symm

/-- The computed word path equals Mathlib's unique lift. -/
theorem liftPath_decode (g : G) (l : List (Label × Bool)) :
    cover.liftPath (GeometricTrace.realize
      (decode GeometricRose.loopA GeometricRose.loopB l)).toContinuousMap (Tree.vertex g)
      (start_eq_project_vertex _ g) = (liftWord g l).toContinuousMap := by
  apply Eq.symm
  apply (cover.eq_liftPath_iff' _).mpr
  exact ⟨funext (project_liftWord g l), (liftWord g l).source⟩

/-- A realized trace lifted from the identity vertex ends at its actual code.
Structural normalization is used before invoking geometric lifting. -/
theorem liftPath_trace_one (p : RoseTrace) :
    cover.liftPath (GeometricTrace.realize p).toContinuousMap (Tree.vertex 1)
      (start_eq_project_vertex _ 1) 1 =
      Tree.vertex (encode GeometricRose.loopA GeometricRose.loopB p) := by
  have hn := ScopedRwEq.sound rosePresentation
    (normalization GeometricRose.loopA GeometricRose.loopB p)
  have he := cover.liftPath_apply_one_eq_of_homotopicRel hn (Tree.vertex 1)
    (start_eq_project_vertex _ 1) (start_eq_project_vertex _ 1)
  rw [he, liftPath_decode]
  change (liftWord 1 (reducedWord GeometricRose.loopA GeometricRose.loopB p)) 1 = _
  rw [(liftWord 1 (reducedWord GeometricRose.loopA GeometricRose.loopB p)).target]
  rw [one_mul, reducedWord_eq_toWord, FreeGroup.mk_toWord]

/-- Geometric completeness for the actual finite rose presentation. -/
theorem trace_complete (p q : RoseTrace)
    (h : _root_.Path.Homotopic (GeometricTrace.realize p) (GeometricTrace.realize q)) :
    ScopedRwEq rosePresentation p q := by
  have he := cover.liftPath_apply_one_eq_of_homotopicRel h (Tree.vertex 1)
    (start_eq_project_vertex _ 1) (start_eq_project_vertex _ 1)
  rw [liftPath_trace_one, liftPath_trace_one] at he
  exact (scoped_iff_encode_eq GeometricRose.loopA GeometricRose.loopB p q).mpr
    (Tree.vertex.inj he)

theorem homotopic_iff_scoped (p q : RoseTrace) :
    _root_.Path.Homotopic (GeometricTrace.realize p) (GeometricTrace.realize q) ↔
      ScopedRwEq rosePresentation p q :=
  ⟨trace_complete p q, ScopedRwEq.sound rosePresentation⟩

/-- The order distinction is geometric for the genuine two-circle rose. -/
theorem ab_not_homotopic_ba :
    ¬ _root_.Path.Homotopic
      (GeometricTrace.realize (abTrace GeometricRose.loopA GeometricRose.loopB))
      (GeometricTrace.realize (baTrace GeometricRose.loopA GeometricRose.loopB)) := by
  intro h
  exact ab_not_scoped_ba GeometricRose.loopA GeometricRose.loopB (trace_complete _ _ h)

/-- Equal-slot completeness follows through the checked binary homotopy bridge. -/
theorem flat_trace_complete (p q : RoseTrace)
    (h : _root_.Path.Homotopic (GeometricTrace.flatRealize p) (GeometricTrace.flatRealize q)) :
    ScopedRwEq rosePresentation p q :=
  trace_complete p q ((GeometricTrace.flatRealize_homotopic_binary p).symm.trans
    (h.trans (GeometricTrace.flatRealize_homotopic_binary q)))

theorem flat_homotopic_iff_scoped (p q : RoseTrace) :
    _root_.Path.Homotopic (GeometricTrace.flatRealize p) (GeometricTrace.flatRealize q) ↔
      ScopedRwEq rosePresentation p q := by
  constructor
  · exact flat_trace_complete p q
  · intro h
    exact (GeometricTrace.flatRealize_homotopic_binary p).trans
      ((ScopedRwEq.sound rosePresentation h).trans
        (GeometricTrace.flatRealize_homotopic_binary q).symm)

end
end ComputationalPaths.Path.GeometricTopology.RoseLiftedWords
