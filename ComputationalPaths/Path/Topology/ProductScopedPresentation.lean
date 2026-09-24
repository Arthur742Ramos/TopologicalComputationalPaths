import ComputationalPaths.Path.Topology.ProductGeometricStepSystem
import ComputationalPaths.Path.Topology.ScopedGeometricRewriteFunctor

/-!
# Scoped rules for a product presentation

Horizontal and vertical rules are transported from their factors.  The
primitive and whole-trace interchange generators swap horizontal and vertical
paths across rectangles. Their soundness follows from product path homotopy.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

universe u v w z

variable {X : Type u} [TopologicalSpace X]
  {Y : Type v} [TopologicalSpace Y]
  {StepX : Type w} [TopologicalSpace StepX]
  {StepY : Type z} [TopologicalSpace StepY]
  {S : ContinuousGeometricStepSystem X StepX}
  {T : ContinuousGeometricStepSystem Y StepY}

noncomputable abbrev ProductSystem (S : ContinuousGeometricStepSystem X StepX)
    (T : ContinuousGeometricStepSystem Y StepY) :=
  productGeometricStepSystem S T

inductive ProductRule
    (P : ScopedGeometricRewritePresentation S)
    (Q : ScopedGeometricRewritePresentation T) :
    {a b : X × Y} →
      GeometricTrace (ProductSystem S T).toGeometricStepSystem a b →
      GeometricTrace (ProductSystem S T).toGeometricStepSystem a b → Prop
  | horizontal {x₀ x₁ : X} (y : Y)
      {p q : GeometricTrace S.toGeometricStepSystem x₀ x₁}
      (h : P.rule p q) :
      ProductRule P Q
        ((horizontalSystemMap S T y).mapTrace p)
        ((horizontalSystemMap S T y).mapTrace q)
  | vertical (x : X) {y₀ y₁ : Y}
      {p q : GeometricTrace T.toGeometricStepSystem y₀ y₁}
      (h : Q.rule p q) :
      ProductRule P Q
        ((verticalSystemMap S T x).mapTrace p)
        ((verticalSystemMap S T x).mapTrace q)
  | interchange (e : StepX) (f : StepY) :
      ProductRule P Q
        (.trans (.single (Sum.inl (e, T.src f)))
          (.single (Sum.inr (S.tgt e, f))))
        (.trans (.single (Sum.inr (S.src e, f)))
          (.single (Sum.inl (e, T.tgt f))))
  | interchangeTrace {x₀ x₁ : X} {y₀ y₁ : Y}
      (p : GeometricTrace S.toGeometricStepSystem x₀ x₁)
      (q : GeometricTrace T.toGeometricStepSystem y₀ y₁) :
      ProductRule P Q
        (.trans ((horizontalSystemMap S T y₀).mapTrace p)
          ((verticalSystemMap S T x₁).mapTrace q))
        (.trans ((verticalSystemMap S T x₀).mapTrace q)
          ((horizontalSystemMap S T y₁).mapTrace p))

theorem ProductRule.sound
    {P : ScopedGeometricRewritePresentation S}
    {Q : ScopedGeometricRewritePresentation T}
    {a b : X × Y}
    {p q : GeometricTrace (ProductSystem S T).toGeometricStepSystem a b}
    (h : ProductRule P Q p q) :
    _root_.Path.Homotopic (GeometricTrace.realize p)
      (GeometricTrace.realize q) := by
  cases h with
  | horizontal y h =>
      rw [ContinuousGeometricStepSystemMap.mapTrace_realize,
        ContinuousGeometricStepSystemMap.mapTrace_realize]
      exact (P.sound_rule h).map (horizontalSystemMap S T y).map
  | vertical x h =>
      rw [ContinuousGeometricStepSystemMap.mapTrace_realize,
        ContinuousGeometricStepSystemMap.mapTrace_realize]
      exact (Q.sound_rule h).map (verticalSystemMap S T x).map
  | interchange e f =>
      simpa [GeometricTrace.realize, ProductSystem,
        productGeometricStepSystem] using
        (productInterchange_sound (S.realize e) (T.realize f))
  | interchangeTrace p q =>
      rename_i x0 x1 y0 y1
      have hh (y : Y) :
          GeometricTrace.realize
            ((horizontalSystemMap S T y).mapTrace p) =
            (GeometricTrace.realize p).prod (_root_.Path.refl y) := by
        rw [ContinuousGeometricStepSystemMap.mapTrace_realize]
        apply _root_.Path.ext
        funext t
        rfl
      have hv (x : X) :
          GeometricTrace.realize
            ((verticalSystemMap S T x).mapTrace q) =
            (_root_.Path.refl x).prod (GeometricTrace.realize q) := by
        rw [ContinuousGeometricStepSystemMap.mapTrace_realize]
        apply _root_.Path.ext
        funext t
        rfl
      change _root_.Path.Homotopic
        ((GeometricTrace.realize ((horizontalSystemMap S T _).mapTrace p)).trans
          (GeometricTrace.realize ((verticalSystemMap S T _).mapTrace q)))
        ((GeometricTrace.realize ((verticalSystemMap S T _).mapTrace q)).trans
          (GeometricTrace.realize ((horizontalSystemMap S T _).mapTrace p)))
      dsimp only [horizontalSystemMap, verticalSystemMap] at *
      rw [hh y0, hv x1, hv x0, hh y1]
      exact productInterchange_sound
        (GeometricTrace.realize p) (GeometricTrace.realize q)

noncomputable def productScopedPresentation
    (P : ScopedGeometricRewritePresentation S)
    (Q : ScopedGeometricRewritePresentation T) :
    ScopedGeometricRewritePresentation (ProductSystem S T) where
  rule := ProductRule P Q
  sound_rule := ProductRule.sound

noncomputable def horizontalPresentationMap
    (P : ScopedGeometricRewritePresentation S)
    (Q : ScopedGeometricRewritePresentation T) (y : Y) :
    ScopedGeometricRewrite.PresentationMap P
      (productScopedPresentation P Q) where
  systemMap := horizontalSystemMap S T y
  rule_map := by
    intro a b p q h
    exact ScopedRwEq.generator (ProductRule.horizontal y h)

noncomputable def verticalPresentationMap
    (P : ScopedGeometricRewritePresentation S)
    (Q : ScopedGeometricRewritePresentation T) (x : X) :
    ScopedGeometricRewrite.PresentationMap Q
      (productScopedPresentation P Q) where
  systemMap := verticalSystemMap S T x
  rule_map := by
    intro a b p q h
    exact ScopedRwEq.generator (ProductRule.vertical x h)

theorem liftHorizontalDerivation
    (P : ScopedGeometricRewritePresentation S)
    (Q : ScopedGeometricRewritePresentation T) (y : Y)
    {a b : X} {p q : GeometricTrace S.toGeometricStepSystem a b}
    (h : ScopedRwEq P p q) :
    ScopedRwEq (productScopedPresentation P Q)
      ((horizontalSystemMap S T y).mapTrace p)
      ((horizontalSystemMap S T y).mapTrace q) :=
  ScopedGeometricRewrite.mapScopedRwEq (horizontalPresentationMap P Q y) h

theorem liftVerticalDerivation
    (P : ScopedGeometricRewritePresentation S)
    (Q : ScopedGeometricRewritePresentation T) (x : X)
    {a b : Y} {p q : GeometricTrace T.toGeometricStepSystem a b}
    (h : ScopedRwEq Q p q) :
    ScopedRwEq (productScopedPresentation P Q)
      ((verticalSystemMap S T x).mapTrace p)
      ((verticalSystemMap S T x).mapTrace q) :=
  ScopedGeometricRewrite.mapScopedRwEq (verticalPresentationMap P Q x) h

end GeometricTopology
end Path
end ComputationalPaths
