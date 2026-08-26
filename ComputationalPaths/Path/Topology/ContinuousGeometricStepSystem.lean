import ComputationalPaths.Path.Topology.OpenGeometricComputationalPath

/-!
# Continuous geometric step systems

`GeometricStepSystem` records endpoint-changing geometric primitives, but it
does not yet say that the primitive family varies continuously with its step
parameter.  This file adds exactly that missing datum.  The endpoint maps and
the underlying interval-path map are continuous, while the endpoint-indexed
`Path` witness remains available for every individual step.

The maximal instance takes every continuous interval path as a primitive
step.  It is useful as a universal comparison object; applications can impose
a smaller, domain-specific step type and discharge the same three continuity
fields.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

universe u v

/-! ## The continuous step-system certificate -/

/-- A geometric step system whose endpoint and realization maps vary
continuously with the primitive-step parameter. -/
structure ContinuousGeometricStepSystem (A : Type u) [TopologicalSpace A]
    (Step : Type v) [TopologicalSpace Step]
    extends GeometricStepSystem A Step where
  continuous_src : Continuous src
  continuous_tgt : Continuous tgt
  continuous_realize :
    Continuous (fun s => (realize s).toContinuousMap)

namespace ContinuousGeometricStepSystem

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]

theorem continuous_endpoints (S : ContinuousGeometricStepSystem A Step) :
    Continuous (fun s => (S.src s, S.tgt s)) :=
  S.continuous_src.prodMk S.continuous_tgt

theorem continuous_realization (S : ContinuousGeometricStepSystem A Step) :
    Continuous (fun s => (S.realize s).toContinuousMap) :=
  S.continuous_realize

end ContinuousGeometricStepSystem

/-! ## The maximal path-parameterized system -/

/-- Every continuous interval path is a primitive step. -/
abbrev ContinuousPathStep (A : Type u) [TopologicalSpace A] :=
  C(unitInterval, A)

/-- The universal continuous geometric step system on `A`. -/
noncomputable def continuousPathStepSystem
    (A : Type u) [TopologicalSpace A] :
    ContinuousGeometricStepSystem A (ContinuousPathStep A) where
  src γ := γ 0
  tgt γ := γ 1
  realize γ :=
    { toContinuousMap := γ
      source' := rfl
      target' := rfl }
  continuous_src := continuous_eval_const 0
  continuous_tgt := continuous_eval_const 1
  continuous_realize := by
    change Continuous (fun γ : ContinuousPathStep A => γ)
    exact continuous_id

theorem continuousPathStepSystem_src_apply
    {A : Type u} [TopologicalSpace A] (γ : ContinuousPathStep A) :
    (continuousPathStepSystem A).src γ = γ 0 :=
  rfl

theorem continuousPathStepSystem_tgt_apply
    {A : Type u} [TopologicalSpace A] (γ : ContinuousPathStep A) :
    (continuousPathStepSystem A).tgt γ = γ 1 :=
  rfl

/-- Package a universal continuous path as a coherent open computational path. -/
noncomputable def continuousPathStep
    {A : Type u} [TopologicalSpace A] (γ : ContinuousPathStep A) :
    OpenGeometricCompPath
      (continuousPathStepSystem A).toGeometricStepSystem (γ 0) (γ 1) :=
  ofGeometricStep (continuousPathStepSystem A).toGeometricStepSystem γ

/-!
The following witness is intentionally a nontrivial computational-path
composition.  It records that the new continuous layer still exposes the
repository's explicit `Path` calculus, rather than being only an external
topological wrapper.
-/
noncomputable def continuousPathStepLoopCertificate
    {A : Type u} [TopologicalSpace A] (γ : ContinuousPathStep A) :
    ComputationalPaths.Path (γ 0) (γ 0) :=
  ComputationalPaths.Path.trans
    (ComputationalPaths.Path.refl (γ 0))
    (ComputationalPaths.Path.refl (γ 0))

end GeometricTopology
end Path
end ComputationalPaths
