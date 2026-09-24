import ComputationalPaths.Path.Topology.ProductScopedPresentation

/-!
# Coordinate traces for a scoped product

Horizontal letters project to steps in the first factor, vertical letters
to identity traces; the second projection is dual.  The sorted trace runs
the first projection at the initial second coordinate, then the second
projection at the final first coordinate.
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

noncomputable def productTraceLeft :
    {a b : X × Y} →
      GeometricTrace (ProductSystem S T).toGeometricStepSystem a b →
        GeometricTrace S.toGeometricStepSystem a.1 b.1
  | _, _, .refl a => .refl a.1
  | _, _, .single (Sum.inl (e, _)) => .single e
  | _, _, .single (Sum.inr (x, _)) => .refl x
  | _, _, .trans p q => .trans (productTraceLeft p) (productTraceLeft q)
  | _, _, .symm p => .symm (productTraceLeft p)

noncomputable def productTraceRight :
    {a b : X × Y} →
      GeometricTrace (ProductSystem S T).toGeometricStepSystem a b →
        GeometricTrace T.toGeometricStepSystem a.2 b.2
  | _, _, .refl a => .refl a.2
  | _, _, .single (Sum.inl (_, y)) => .refl y
  | _, _, .single (Sum.inr (_, f)) => .single f
  | _, _, .trans p q => .trans (productTraceRight p) (productTraceRight q)
  | _, _, .symm p => .symm (productTraceRight p)

noncomputable def productSortedTrace
    {a b : X × Y}
    (p : GeometricTrace (ProductSystem S T).toGeometricStepSystem a b) :
    GeometricTrace (ProductSystem S T).toGeometricStepSystem a b :=
  .trans
    ((horizontalSystemMap S T a.2).mapTrace (productTraceLeft p))
    ((verticalSystemMap S T b.1).mapTrace (productTraceRight p))

theorem productTraceLeft_realize
    {a b : X × Y}
    (p : GeometricTrace (ProductSystem S T).toGeometricStepSystem a b) :
    GeometricTrace.realize (productTraceLeft p) =
      (GeometricTrace.realize p).map continuous_fst := by
  induction p with
  | refl a => rfl
  | single step =>
      cases step with
      | inl ey =>
          rcases ey with ⟨e, y⟩
          rfl
      | inr xf =>
          rcases xf with ⟨x, f⟩
          rfl
  | trans p q ihp ihq =>
      simp only [productTraceLeft, GeometricTrace.realize, _root_.Path.map_trans]
      rw [ihp, ihq]
  | symm p ih =>
      simp only [productTraceLeft, GeometricTrace.realize]
      rw [ih]
      exact (_root_.Path.map_symm (GeometricTrace.realize p) continuous_fst).symm

theorem productTraceRight_realize
    {a b : X × Y}
    (p : GeometricTrace (ProductSystem S T).toGeometricStepSystem a b) :
    GeometricTrace.realize (productTraceRight p) =
      (GeometricTrace.realize p).map continuous_snd := by
  induction p with
  | refl a => rfl
  | single step =>
      cases step with
      | inl ey =>
          rcases ey with ⟨e, y⟩
          rfl
      | inr xf =>
          rcases xf with ⟨x, f⟩
          rfl
  | trans p q ihp ihq =>
      simp only [productTraceRight, GeometricTrace.realize, _root_.Path.map_trans]
      rw [ihp, ihq]
  | symm p ih =>
      simp only [productTraceRight, GeometricTrace.realize]
      rw [ih]
      exact (_root_.Path.map_symm (GeometricTrace.realize p) continuous_snd).symm

private theorem scopedSwapMiddle
    {A : Type*} [TopologicalSpace A]
    {Step : Type*} [TopologicalSpace Step]
    {U : ContinuousGeometricStepSystem A Step}
    (R : ScopedGeometricRewritePresentation U)
    {a b c d e f : A}
    (p : GeometricTrace U.toGeometricStepSystem a b)
    (v : GeometricTrace U.toGeometricStepSystem b c)
    (h : GeometricTrace U.toGeometricStepSystem c d)
    (w : GeometricTrace U.toGeometricStepSystem d e)
    (h' : GeometricTrace U.toGeometricStepSystem b f)
    (v' : GeometricTrace U.toGeometricStepSystem f d)
    (hswap : ScopedRwEq R (.trans v h) (.trans h' v')) :
    ScopedRwEq R
      (.trans (.trans p v) (.trans h w))
      (.trans (.trans p h') (.trans v' w)) := by
  have h1 := ScopedRwEq.trans_assoc (P := R) p v (.trans h w)
  have h2 := ScopedRwEq.trans_congr (ScopedRwEq.refl p)
    (ScopedRwEq.symm (ScopedRwEq.trans_assoc (P := R) v h w))
  have h3 := ScopedRwEq.trans_congr (ScopedRwEq.refl p)
    (ScopedRwEq.trans_congr hswap (ScopedRwEq.refl w))
  have h4 := ScopedRwEq.symm
    (ScopedRwEq.trans_assoc (P := R) p (.trans h' v') w)
  have h5 := ScopedRwEq.trans_congr
    (ScopedRwEq.symm (ScopedRwEq.trans_assoc (P := R) p h' v'))
    (ScopedRwEq.refl w)
  have h6 := ScopedRwEq.trans_assoc (P := R) (.trans p h') v' w
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

theorem productTrace_normalizes
    (P : ScopedGeometricRewritePresentation S)
    (Q : ScopedGeometricRewritePresentation T)
    {a b : X × Y}
    (p : GeometricTrace (ProductSystem S T).toGeometricStepSystem a b) :
    ScopedRwEq (productScopedPresentation P Q) p (productSortedTrace p) := by
  induction p with
  | refl a =>
      change ScopedRwEq (productScopedPresentation P Q)
        (.refl a) (.trans (.refl a) (.refl a))
      exact ScopedRwEq.symm (ScopedRwEq.refl_trans (P := productScopedPresentation P Q) (.refl a))
  | single step =>
      cases step with
      | inl ey =>
          rcases ey with ⟨e, y⟩
          simpa [productSortedTrace, productTraceLeft, productTraceRight,
            ProductSystem, productGeometricStepSystem,
            horizontalSystemMap, verticalSystemMap,
            ContinuousGeometricStepSystemMap.mapTrace,
            ContinuousGeometricStepSystemMap.castTrace] using
            (ScopedRwEq.symm (ScopedRwEq.trans_refl
              (P := productScopedPresentation P Q)
              (GeometricTrace.single (S := (ProductSystem S T).toGeometricStepSystem)
                (Sum.inl (e, y)))))
      | inr xf =>
          rcases xf with ⟨x, f⟩
          simpa [productSortedTrace, productTraceLeft, productTraceRight,
            ProductSystem, productGeometricStepSystem,
            horizontalSystemMap, verticalSystemMap,
            ContinuousGeometricStepSystemMap.mapTrace,
            ContinuousGeometricStepSystemMap.castTrace] using
            (ScopedRwEq.symm (ScopedRwEq.refl_trans
              (P := productScopedPresentation P Q)
              (GeometricTrace.single (S := (ProductSystem S T).toGeometricStepSystem)
                (Sum.inr (x, f)))))
  | trans p q ihp ihq =>
      have hpre := ScopedRwEq.trans_congr ihp ihq
      have hswap : ScopedRwEq (productScopedPresentation P Q)
          (.trans
            ((verticalSystemMap S T _).mapTrace (productTraceRight p))
            ((horizontalSystemMap S T _).mapTrace (productTraceLeft q)))
          (.trans
            ((horizontalSystemMap S T _).mapTrace (productTraceLeft q))
            ((verticalSystemMap S T _).mapTrace (productTraceRight p))) :=
        ScopedRwEq.symm (ScopedRwEq.generator
          (ProductRule.interchangeTrace (productTraceLeft q)
            (productTraceRight p)))
      exact hpre.trans (scopedSwapMiddle (productScopedPresentation P Q)
        _ _ _ _ _ _ hswap)
  | symm p ih =>
      have hpre := ScopedRwEq.symm_congr ih
      have hcomp := ScopedRwEq.symm_comp
        (P := productScopedPresentation P Q)
        ((horizontalSystemMap S T _).mapTrace (productTraceLeft p))
        ((verticalSystemMap S T _).mapTrace (productTraceRight p))
      have hswap := ScopedRwEq.symm (ScopedRwEq.generator
        (P := productScopedPresentation P Q)
        (ProductRule.interchangeTrace
          (GeometricTrace.symm (productTraceLeft p))
          (GeometricTrace.symm (productTraceRight p))))
      exact hpre.trans (hcomp.trans hswap)

/-- Completeness of the two based trace calculi passes to their scoped product. -/
theorem productBasedTraceCompleteness
    (P : ScopedGeometricRewritePresentation S)
    (Q : ScopedGeometricRewritePresentation T)
    (x : X) (y : Y)
    (hP : ∀ {p q : GeometricTrace S.toGeometricStepSystem x x},
      _root_.Path.Homotopic (GeometricTrace.realize p)
        (GeometricTrace.realize q) → ScopedRwEq P p q)
    (hQ : ∀ {p q : GeometricTrace T.toGeometricStepSystem y y},
      _root_.Path.Homotopic (GeometricTrace.realize p)
        (GeometricTrace.realize q) → ScopedRwEq Q p q)
    {p q : GeometricTrace (ProductSystem S T).toGeometricStepSystem
      (x, y) (x, y)}
    (h : _root_.Path.Homotopic (GeometricTrace.realize p)
      (GeometricTrace.realize q)) :
    ScopedRwEq (productScopedPresentation P Q) p q := by
  have hleft : ScopedRwEq P (productTraceLeft p) (productTraceLeft q) := by
    apply hP
    rw [productTraceLeft_realize, productTraceLeft_realize]
    exact h.map ⟨_, continuous_fst⟩
  have hright : ScopedRwEq Q (productTraceRight p) (productTraceRight q) := by
    apply hQ
    rw [productTraceRight_realize, productTraceRight_realize]
    exact h.map ⟨_, continuous_snd⟩
  have hsorted : ScopedRwEq (productScopedPresentation P Q)
      (productSortedTrace p) (productSortedTrace q) :=
    ScopedRwEq.trans_congr
      (liftHorizontalDerivation P Q y hleft)
      (liftVerticalDerivation P Q x hright)
  exact (productTrace_normalizes P Q p).trans
    (hsorted.trans (ScopedRwEq.symm (productTrace_normalizes P Q q)))

theorem productBasedCoherentCompleteness
    (P : ScopedGeometricRewritePresentation S)
    (Q : ScopedGeometricRewritePresentation T)
    (x : X) (y : Y)
    (hP : ∀ {p q : GeometricTrace S.toGeometricStepSystem x x},
      _root_.Path.Homotopic (GeometricTrace.realize p)
        (GeometricTrace.realize q) → ScopedRwEq P p q)
    (hQ : ∀ {p q : GeometricTrace T.toGeometricStepSystem y y},
      _root_.Path.Homotopic (GeometricTrace.realize p)
        (GeometricTrace.realize q) → ScopedRwEq Q p q)
    (p q : OpenGeometricCompPath
      (ProductSystem S T).toGeometricStepSystem (x, y) (x, y))
    (h : _root_.Path.Homotopic p.geometric q.geometric) :
    ScopedRwEq (productScopedPresentation P Q) p.trace q.trace := by
  apply productBasedTraceCompleteness P Q x y hP hQ
  exact p.coherent.symm.trans (h.trans q.coherent)

end GeometricTopology
end Path
end ComputationalPaths
