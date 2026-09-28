import ComputationalPaths.Path.Topology.ProductScopedSorting

/-!
# Product completeness from primitive interchange

The product presentation with lifted factor rules and primitive rectangle
swaps already derives interchange for arbitrary signed traces. The resulting
scoped rewrite relation agrees with the presentation that names whole-trace
interchange. Based trace completeness therefore needs only primitive squares.
-/

namespace ComputationalPaths.Path.GeometricTopology

open scoped ContinuousMap Topology

private theorem squareInverseLeft
    {A : Type*} [TopologicalSpace A]
    {Step : Type*} [TopologicalSpace Step]
    {S : ContinuousGeometricStepSystem A Step}
    (R : ScopedGeometricRewritePresentation S)
    {a b c d : A}
    (p : GeometricTrace S.toGeometricStepSystem a b)
    (v : GeometricTrace S.toGeometricStepSystem b c)
    (w : GeometricTrace S.toGeometricStepSystem a d)
    (q : GeometricTrace S.toGeometricStepSystem d c)
    (h : ScopedRwEq R (.trans p v) (.trans w q)) :
    ScopedRwEq R (.trans (.symm p) w) (.trans v (.symm q)) := by
  have h1 : ScopedRwEq R
      (.trans (.symm p) w)
      (.trans (.trans (.symm p) w) (.trans q (.symm q))) := by
    exact (ScopedRwEq.trans_refl (P := R) _).symm.trans
      (ScopedRwEq.trans_congr (ScopedRwEq.refl _)
        (ScopedRwEq.trans_symm (P := R) q).symm)
  have h2 : ScopedRwEq R
      (.trans (.trans (.symm p) w) (.trans q (.symm q)))
      (.trans (.symm p) (.trans (.trans w q) (.symm q))) := by
    exact (ScopedRwEq.trans_assoc (P := R) (.symm p) w _).trans
      (ScopedRwEq.trans_congr (ScopedRwEq.refl (.symm p))
        (ScopedRwEq.trans_assoc (P := R) w q (.symm q)).symm)
  have h3 : ScopedRwEq R
      (.trans (.symm p) (.trans (.trans w q) (.symm q)))
      (.trans (.symm p) (.trans (.trans p v) (.symm q))) := by
    exact ScopedRwEq.trans_congr (ScopedRwEq.refl _) <|
      ScopedRwEq.trans_congr h.symm (ScopedRwEq.refl _)
  have h4 : ScopedRwEq R
      (.trans (.symm p) (.trans (.trans p v) (.symm q)))
      (.trans (.trans (.trans (.symm p) p) v) (.symm q)) := by
    exact (ScopedRwEq.trans_congr (ScopedRwEq.refl (.symm p))
      (ScopedRwEq.trans_assoc (P := R) p v (.symm q))).trans <|
      ((ScopedRwEq.trans_assoc (P := R) (.symm p) p
        (.trans v (.symm q))).symm.trans
        (ScopedRwEq.trans_assoc (P := R) (.trans (.symm p) p) v (.symm q)).symm)
  have h5 : ScopedRwEq R
      (.trans (.trans (.trans (.symm p) p) v) (.symm q))
      (.trans v (.symm q)) := by
    exact (ScopedRwEq.trans_congr
      (ScopedRwEq.trans_congr (ScopedRwEq.symm_trans (P := R) p)
        (ScopedRwEq.refl v)) (ScopedRwEq.refl _)).trans
      (ScopedRwEq.trans_congr (ScopedRwEq.refl_trans (P := R) v)
        (ScopedRwEq.refl _))
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

private theorem squareInverseRight
    {A : Type*} [TopologicalSpace A]
    {Step : Type*} [TopologicalSpace Step]
    {S : ContinuousGeometricStepSystem A Step}
    (R : ScopedGeometricRewritePresentation S)
    {a b c d : A}
    (p : GeometricTrace S.toGeometricStepSystem a b)
    (v : GeometricTrace S.toGeometricStepSystem b c)
    (w : GeometricTrace S.toGeometricStepSystem a d)
    (q : GeometricTrace S.toGeometricStepSystem d c)
    (h : ScopedRwEq R (.trans p v) (.trans w q)) :
    ScopedRwEq R (.trans q (.symm v)) (.trans (.symm w) p) :=
  (squareInverseLeft R w q p v h.symm).symm

private theorem squareVerticalPaste
    {A : Type*} [TopologicalSpace A]
    {Step : Type*} [TopologicalSpace Step]
    {S : ContinuousGeometricStepSystem A Step}
    (R : ScopedGeometricRewritePresentation S)
    {a b c d e f : A}
    (p0 : GeometricTrace S.toGeometricStepSystem a b)
    (v1 : GeometricTrace S.toGeometricStepSystem b c)
    (w1 : GeometricTrace S.toGeometricStepSystem a d)
    (p1 : GeometricTrace S.toGeometricStepSystem d c)
    (v2 : GeometricTrace S.toGeometricStepSystem c e)
    (w2 : GeometricTrace S.toGeometricStepSystem d f)
    (p2 : GeometricTrace S.toGeometricStepSystem f e)
    (h1 : ScopedRwEq R (.trans p0 v1) (.trans w1 p1))
    (h2 : ScopedRwEq R (.trans p1 v2) (.trans w2 p2)) :
    ScopedRwEq R (.trans p0 (.trans v1 v2))
      (.trans (.trans w1 w2) p2) := by
  have hA := (ScopedRwEq.trans_assoc (P := R) p0 v1 v2).symm
  have hB := ScopedRwEq.trans_congr h1 (ScopedRwEq.refl v2)
  have hC := ScopedRwEq.trans_assoc (P := R) w1 p1 v2
  have hD := ScopedRwEq.trans_congr (ScopedRwEq.refl w1) h2
  have hE := (ScopedRwEq.trans_assoc (P := R) w1 w2 p2).symm
  exact hA.trans (hB.trans (hC.trans (hD.trans hE)))

private theorem squareHorizontalPaste
    {A : Type*} [TopologicalSpace A]
    {Step : Type*} [TopologicalSpace Step]
    {S : ContinuousGeometricStepSystem A Step}
    (R : ScopedGeometricRewritePresentation S)
    {a b c d e f : A}
    (p0 : GeometricTrace S.toGeometricStepSystem a b)
    (v1 : GeometricTrace S.toGeometricStepSystem b c)
    (w0 : GeometricTrace S.toGeometricStepSystem a d)
    (q0 : GeometricTrace S.toGeometricStepSystem d c)
    (p1 : GeometricTrace S.toGeometricStepSystem b e)
    (v2 : GeometricTrace S.toGeometricStepSystem e f)
    (q1 : GeometricTrace S.toGeometricStepSystem c f)
    (h1 : ScopedRwEq R (.trans p0 v1) (.trans w0 q0))
    (h2 : ScopedRwEq R (.trans p1 v2) (.trans v1 q1)) :
    ScopedRwEq R (.trans (.trans p0 p1) v2)
      (.trans w0 (.trans q0 q1)) := by
  have hA := ScopedRwEq.trans_assoc (P := R) p0 p1 v2
  have hB := ScopedRwEq.trans_congr (ScopedRwEq.refl p0) h2
  have hC := (ScopedRwEq.trans_assoc (P := R) p0 v1 q1).symm
  have hD := ScopedRwEq.trans_congr h1 (ScopedRwEq.refl q1)
  have hE := ScopedRwEq.trans_assoc (P := R) w0 q0 q1
  exact hA.trans (hB.trans (hC.trans (hD.trans hE)))

universe u v w z

variable {X : Type u} [TopologicalSpace X]
  {Y : Type v} [TopologicalSpace Y]
  {StepX : Type w} [TopologicalSpace StepX]
  {StepY : Type z} [TopologicalSpace StepY]
  {S : ContinuousGeometricStepSystem X StepX}
  {T : ContinuousGeometricStepSystem Y StepY}

/-- Product rules with no whole-trace interchange generator. -/
inductive PrimitiveProductRule
    (P : ScopedGeometricRewritePresentation S)
    (Q : ScopedGeometricRewritePresentation T) :
    {a b : X × Y} →
      GeometricTrace (ProductSystem S T).toGeometricStepSystem a b →
      GeometricTrace (ProductSystem S T).toGeometricStepSystem a b → Prop
  | horizontal {x₀ x₁ : X} (y : Y)
      {p q : GeometricTrace S.toGeometricStepSystem x₀ x₁}
      (h : P.rule p q) :
      PrimitiveProductRule P Q
        ((horizontalSystemMap S T y).mapTrace p)
        ((horizontalSystemMap S T y).mapTrace q)
  | vertical (x : X) {y₀ y₁ : Y}
      {p q : GeometricTrace T.toGeometricStepSystem y₀ y₁}
      (h : Q.rule p q) :
      PrimitiveProductRule P Q
        ((verticalSystemMap S T x).mapTrace p)
        ((verticalSystemMap S T x).mapTrace q)
  | interchange (e : StepX) (f : StepY) :
      PrimitiveProductRule P Q
        (.trans (.single (Sum.inl (e, T.src f)))
          (.single (Sum.inr (S.tgt e, f))))
        (.trans (.single (Sum.inr (S.src e, f)))
          (.single (Sum.inl (e, T.tgt f))))

private theorem PrimitiveProductRule.sound
    {P : ScopedGeometricRewritePresentation S}
    {Q : ScopedGeometricRewritePresentation T}
    {a b : X × Y}
    {p q : GeometricTrace (ProductSystem S T).toGeometricStepSystem a b}
    (h : PrimitiveProductRule P Q p q) :
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

noncomputable def primitiveProductPresentation
    (P : ScopedGeometricRewritePresentation S)
    (Q : ScopedGeometricRewritePresentation T) :
    ScopedGeometricRewritePresentation (ProductSystem S T) where
  rule := PrimitiveProductRule P Q
  sound_rule := PrimitiveProductRule.sound

private theorem primitiveSwapSingleSingle
    (P : ScopedGeometricRewritePresentation S)
    (Q : ScopedGeometricRewritePresentation T)
    (e : StepX) (f : StepY) :
    ScopedRwEq (primitiveProductPresentation P Q)
      (.trans
        ((horizontalSystemMap S T (T.src f)).mapTrace (.single e))
        ((verticalSystemMap S T (S.tgt e)).mapTrace (.single f)))
      (.trans
        ((verticalSystemMap S T (S.src e)).mapTrace (.single f))
        ((horizontalSystemMap S T (T.tgt f)).mapTrace (.single e))) := by
  simpa [horizontalSystemMap, verticalSystemMap,
    ProductSystem, productGeometricStepSystem,
    ContinuousGeometricStepSystemMap.mapTrace,
    ContinuousGeometricStepSystemMap.castTrace] using
    (ScopedRwEq.generator (P := primitiveProductPresentation P Q)
      (PrimitiveProductRule.interchange e f))

private theorem primitiveSwapLeftTrace
    (P : ScopedGeometricRewritePresentation S)
    (Q : ScopedGeometricRewritePresentation T)
    {x₀ x₁ : X}
    (p : GeometricTrace S.toGeometricStepSystem x₀ x₁)
    (f : StepY) :
    ScopedRwEq (primitiveProductPresentation P Q)
      (.trans
        ((horizontalSystemMap S T (T.src f)).mapTrace p)
        ((verticalSystemMap S T x₁).mapTrace (.single f)))
      (.trans
        ((verticalSystemMap S T x₀).mapTrace (.single f))
        ((horizontalSystemMap S T (T.tgt f)).mapTrace p)) := by
  induction p with
  | refl x =>
      exact (ScopedRwEq.refl_trans (P := primitiveProductPresentation P Q)
        ((verticalSystemMap S T x).mapTrace (.single f))).trans
        (ScopedRwEq.trans_refl (P := primitiveProductPresentation P Q)
          ((verticalSystemMap S T x).mapTrace (.single f))).symm
  | single e =>
      exact primitiveSwapSingleSingle P Q e f
  | trans p q ihp ihq =>
      exact squareHorizontalPaste (primitiveProductPresentation P Q)
        _ _ _ _ _ _ _ ihp ihq
  | symm p ih =>
      exact squareInverseLeft (primitiveProductPresentation P Q)
        _ _ _ _ ih

/-- The interchange rule for arbitrary factor traces follows from primitive
rectangle swaps and the scoped groupoid laws. -/
theorem primitiveInterchangeTrace
    (P : ScopedGeometricRewritePresentation S)
    (Q : ScopedGeometricRewritePresentation T)
    {x₀ x₁ : X} {y₀ y₁ : Y}
    (p : GeometricTrace S.toGeometricStepSystem x₀ x₁)
    (q : GeometricTrace T.toGeometricStepSystem y₀ y₁) :
    ScopedRwEq (primitiveProductPresentation P Q)
      (.trans ((horizontalSystemMap S T y₀).mapTrace p)
        ((verticalSystemMap S T x₁).mapTrace q))
      (.trans ((verticalSystemMap S T x₀).mapTrace q)
        ((horizontalSystemMap S T y₁).mapTrace p)) := by
  induction q with
  | refl y =>
      exact (ScopedRwEq.trans_refl (P := primitiveProductPresentation P Q)
        ((horizontalSystemMap S T y).mapTrace p)).trans
        (ScopedRwEq.refl_trans (P := primitiveProductPresentation P Q)
          ((horizontalSystemMap S T y).mapTrace p)).symm
  | single f =>
      exact primitiveSwapLeftTrace P Q p f
  | trans q r ihq ihr =>
      exact squareVerticalPaste (primitiveProductPresentation P Q)
        _ _ _ _ _ _ _ ihq ihr
  | symm q ih =>
      exact squareInverseRight (primitiveProductPresentation P Q)
        _ _ _ _ ih

noncomputable def fullToPrimitivePresentationMap
    (P : ScopedGeometricRewritePresentation S)
    (Q : ScopedGeometricRewritePresentation T) :
    ScopedGeometricRewrite.PresentationMap
      (productScopedPresentation P Q) (primitiveProductPresentation P Q) where
  systemMap := ScopedGeometricRewrite.identitySystemMap (ProductSystem S T)
  rule_map := by
    intro a b p q h
    rw [ScopedGeometricRewrite.identitySystemMap_mapTrace,
      ScopedGeometricRewrite.identitySystemMap_mapTrace]
    cases h with
    | horizontal y h =>
        exact ScopedRwEq.generator (PrimitiveProductRule.horizontal y h)
    | vertical x h =>
        exact ScopedRwEq.generator (PrimitiveProductRule.vertical x h)
    | interchange e f =>
        exact ScopedRwEq.generator (PrimitiveProductRule.interchange e f)
    | interchangeTrace p q =>
        exact primitiveInterchangeTrace P Q p q

noncomputable def primitiveToFullPresentationMap
    (P : ScopedGeometricRewritePresentation S)
    (Q : ScopedGeometricRewritePresentation T) :
    ScopedGeometricRewrite.PresentationMap
      (primitiveProductPresentation P Q) (productScopedPresentation P Q) where
  systemMap := ScopedGeometricRewrite.identitySystemMap (ProductSystem S T)
  rule_map := by
    intro a b p q h
    rw [ScopedGeometricRewrite.identitySystemMap_mapTrace,
      ScopedGeometricRewrite.identitySystemMap_mapTrace]
    cases h with
    | horizontal y h =>
        exact ScopedRwEq.generator (ProductRule.horizontal y h)
    | vertical x h =>
        exact ScopedRwEq.generator (ProductRule.vertical x h)
    | interchange e f =>
        exact ScopedRwEq.generator (ProductRule.interchange e f)

theorem primitiveProduct_rwEq_iff_full
    (P : ScopedGeometricRewritePresentation S)
    (Q : ScopedGeometricRewritePresentation T)
    {a b : X × Y}
    {p q : GeometricTrace (ProductSystem S T).toGeometricStepSystem a b} :
    ScopedRwEq (primitiveProductPresentation P Q) p q ↔
      ScopedRwEq (productScopedPresentation P Q) p q := by
  constructor
  · intro h
    have h' := ScopedGeometricRewrite.mapScopedRwEq
      (primitiveToFullPresentationMap P Q) h
    change ScopedRwEq (productScopedPresentation P Q)
      ((ScopedGeometricRewrite.identitySystemMap (ProductSystem S T)).mapTrace p)
      ((ScopedGeometricRewrite.identitySystemMap (ProductSystem S T)).mapTrace q) at h'
    rw [ScopedGeometricRewrite.identitySystemMap_mapTrace,
      ScopedGeometricRewrite.identitySystemMap_mapTrace] at h'
    exact h'
  · intro h
    have h' := ScopedGeometricRewrite.mapScopedRwEq
      (fullToPrimitivePresentationMap P Q) h
    change ScopedRwEq (primitiveProductPresentation P Q)
      ((ScopedGeometricRewrite.identitySystemMap (ProductSystem S T)).mapTrace p)
      ((ScopedGeometricRewrite.identitySystemMap (ProductSystem S T)).mapTrace q) at h'
    rw [ScopedGeometricRewrite.identitySystemMap_mapTrace,
      ScopedGeometricRewrite.identitySystemMap_mapTrace] at h'
    exact h'

theorem primitiveProductBasedTraceCompleteness
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
    ScopedRwEq (primitiveProductPresentation P Q) p q :=
  (primitiveProduct_rwEq_iff_full P Q).2
    (productBasedTraceCompleteness P Q x y hP hQ h)

end ComputationalPaths.Path.GeometricTopology
