import ComputationalPaths.Path.Topology.CayleyContraction
import ComputationalPaths.Path.Topology.RoseLiftedWords
import Mathlib.Algebra.Group.Equiv.Opposite

/-!
# Classification of all continuous based loops in the actual rose

The concrete Cayley covering, together with its constructed contraction,
classifies the full fundamental group. The value on a represented finite
trace is computed using its already checked lifted endpoint. Injectivity of
this classification then gives a reduced finite word representative for every
continuous based loop, rather than only completeness between finite traces.

Mathlib's fundamental-group multiplication composes the second path first.
Consequently the endpoint code is a group equivalence to the opposite free
group; the equivalence to the ordinary free group applies inversion. Both
conventions and the compatibility with the computational quotient are explicit.
-/

namespace ComputationalPaths.Path.GeometricTopology.RoseFundamentalGroup

open GeometricRose RoseReducedWords RoseLiftedWords CayleyTreeGeometry
open scoped Topology

noncomputable section

local instance : SimplyConnectedSpace Tree := CayleyContraction.simplyConnected

abbrev RosePiOne := FundamentalGroup Rose base
abbrev RoseScopedGroup := ScopedGroup loopA loopB

def fiberBase : CayleyRoseCovering.project ⁻¹' {base} :=
  ⟨Tree.vertex 1, CayleyRoseCovering.project_vertex 1⟩

/-- The opposite convention is the actual endpoint convention of this cover. -/
def fundamentalGroupEquiv : RosePiOne ≃* Gᵐᵒᵖ :=
  CayleyRoseCovering.covering.fundamentalGroupEquiv fiberBase

/-- Ordinary free-group multiplication is recovered by inversion. -/
def freeGroupEquiv : RosePiOne ≃* G :=
  fundamentalGroupEquiv.trans (MulEquiv.inv' G).symm

theorem fundamentalGroupEquiv_realize (p : RoseTrace) :
    fundamentalGroupEquiv (_root_.Path.Homotopic.Quotient.mk (GeometricTrace.realize p)) =
      MulOpposite.op (encode loopA loopB p) := by
  change CayleyRoseCovering.covering.fundamentalGroupToMulOpposite fiberBase
      (_root_.Path.Homotopic.Quotient.mk (GeometricTrace.realize p)) = _
  apply CayleyRoseCovering.covering.fundamentalGroupToMulOpposite_apply_eq_Iff.mpr
  change Tree.vertex (encode loopA loopB p * 1) =
    cover.liftPath (GeometricTrace.realize p).toContinuousMap (Tree.vertex 1)
      (start_eq_project_vertex _ 1) 1
  rw [mul_one, liftPath_trace_one]

theorem freeGroupEquiv_realize (p : RoseTrace) :
    freeGroupEquiv (_root_.Path.Homotopic.Quotient.mk (GeometricTrace.realize p)) =
      (encode loopA loopB p)⁻¹ := by
  change (MulEquiv.inv' G).symm
    (fundamentalGroupEquiv (_root_.Path.Homotopic.Quotient.mk (GeometricTrace.realize p))) = _
  rw [fundamentalGroupEquiv_realize]
  rfl

/-- The actual reduced finite word assigned to an arbitrary continuous loop. -/
def loopWord (p : _root_.Path base base) : List (Label × Bool) :=
  (fundamentalGroupEquiv (_root_.Path.Homotopic.Quotient.mk p)).unop.toWord

theorem loopWord_reduced (p : _root_.Path base base) : FreeGroup.IsReduced (loopWord p) :=
  FreeGroup.isReduced_toWord

theorem loopWord_realize (p : RoseTrace) :
    loopWord (GeometricTrace.realize p) = reducedWord loopA loopB p := by
  unfold loopWord
  rw [fundamentalGroupEquiv_realize, MulOpposite.unop_op, reducedWord_eq_toWord]

/-- Equality of the actual reduced codes classifies arbitrary loop homotopy. -/
theorem loopWord_eq_iff_homotopic (p q : _root_.Path base base) :
    loopWord p = loopWord q ↔ _root_.Path.Homotopic p q := by
  constructor
  · intro h
    apply _root_.Path.Homotopic.Quotient.exact
    apply fundamentalGroupEquiv.injective
    apply MulOpposite.unop_injective
    exact FreeGroup.toWord_inj.mp h
  · intro h
    exact _root_.congrArg
      (fun z : Gᵐᵒᵖ => z.unop.toWord)
      (_root_.congrArg fundamentalGroupEquiv (_root_.Quotient.sound h))

/-- All continuous based loops have a finite reduced-word representative. -/
theorem loop_homotopic_decode (p : _root_.Path base base) :
    _root_.Path.Homotopic p (GeometricTrace.realize (decode loopA loopB (loopWord p))) := by
  apply _root_.Path.Homotopic.Quotient.exact
  apply fundamentalGroupEquiv.injective
  rw [fundamentalGroupEquiv_realize, encode_decode]
  change fundamentalGroupEquiv (_root_.Path.Homotopic.Quotient.mk p) =
    MulOpposite.op (FreeGroup.mk
      (fundamentalGroupEquiv (_root_.Path.Homotopic.Quotient.mk p)).unop.toWord)
  rw [FreeGroup.mk_toWord, MulOpposite.op_unop]

theorem loop_homotopic_flat_decode (p : _root_.Path base base) :
    _root_.Path.Homotopic p (GeometricTrace.flatRealize (decode loopA loopB (loopWord p))) :=
  (loop_homotopic_decode p).trans
    (GeometricTrace.flatRealize_homotopic_binary _).symm

theorem every_loop_represented (p : _root_.Path base base) :
    ∃ q : RoseTrace, _root_.Path.Homotopic p (GeometricTrace.realize q) :=
  ⟨decode loopA loopB (loopWord p), loop_homotopic_decode p⟩

/-- The chosen geometric coordinate can be the arbitrary given loop itself. -/
def coherentRepresentative (p : _root_.Path base base) :
    OpenGeometricCompPath (system loopA loopB).toGeometricStepSystem base base :=
  ⟨decode loopA loopB (loopWord p), p, loop_homotopic_decode p⟩

@[simp] theorem coherentRepresentative_geometric (p : _root_.Path base base) :
    (coherentRepresentative p).geometric = p := rfl

/-- The underlying equivalence is the actual realization comparison.
Its reversal of multiplication is recorded separately below. -/
def traceQuotientEquiv : RoseScopedGroup ≃ RosePiOne :=
  (quotientEquiv loopA loopB).trans
    (MulOpposite.opEquiv.trans fundamentalGroupEquiv.symm.toEquiv)

theorem traceQuotientEquiv_mk (p : RoseTrace) :
    traceQuotientEquiv (BasedScopedTraceGroup.mk rosePresentation base p) =
      _root_.Path.Homotopic.Quotient.mk (GeometricTrace.realize p) := by
  apply fundamentalGroupEquiv.injective
  change fundamentalGroupEquiv
      (fundamentalGroupEquiv.symm (MulOpposite.op (encode loopA loopB p))) = _
  rw [fundamentalGroupEquiv.apply_symm_apply, fundamentalGroupEquiv_realize]

theorem traceQuotientEquiv_flat_mk (p : RoseTrace) :
    traceQuotientEquiv (BasedScopedTraceGroup.mk rosePresentation base p) =
      _root_.Path.Homotopic.Quotient.mk (GeometricTrace.flatRealize p) := by
  rw [traceQuotientEquiv_mk]
  exact _root_.Quotient.sound (GeometricTrace.flatRealize_homotopic_binary p).symm

theorem traceQuotientEquiv_mul (p q : RoseScopedGroup) :
    traceQuotientEquiv (p * q) = traceQuotientEquiv q * traceQuotientEquiv p := by
  refine _root_.Quotient.inductionOn p ?_
  intro p
  refine _root_.Quotient.inductionOn q ?_
  intro q
  change traceQuotientEquiv (BasedScopedTraceGroup.mk rosePresentation base (p.trans q)) =
    traceQuotientEquiv (BasedScopedTraceGroup.mk rosePresentation base q) *
      traceQuotientEquiv (BasedScopedTraceGroup.mk rosePresentation base p)
  rw [traceQuotientEquiv_mk, traceQuotientEquiv_mk, traceQuotientEquiv_mk]
  rfl

end
end ComputationalPaths.Path.GeometricTopology.RoseFundamentalGroup
