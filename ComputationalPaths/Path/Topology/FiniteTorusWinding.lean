import ComputationalPaths.Path.Topology.TopologicalWindingHomeomorph
import ComputationalPaths.Path.Topology.QuotientFundamentalGroup
import ComputationalPaths.Path.Topology.SemilocallySimplyConnected
import Mathlib.Topology.Homotopy.Product
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-!
# Finite-dimensional topological torus winding

For every `n`, genuine based loops in the finite product `(S¹)ⁿ`, modulo
endpoint-fixed homotopy, are classified by `Fin n → ℤ`.  The classification
is first proved algebraically by coordinate winding and explicit standard
loops, then upgraded to a homeomorphism for the compact-open/final quotient
topology.  In particular, the quotient is discrete, its quotient square is a
quotient map, and loop-class composition and reversal are continuous for the
ordinary product topology.  The classifier is also a continuous
multiplicative equivalence to the integer lattice (viewed through
`Multiplicative`), so quotient concatenation is commutative at the zero
basepoint and, by continuous basepoint transport, at every torus point.
The abelian target transport theorem further shows that the resulting
path-based lattice classifier at each point is independent of the explicit
path used to transport it.  Coordinate-selection maps between finite tori
act on winding vectors by the corresponding reindexing map, both before and
after passage to the quotient, and the maps themselves satisfy explicit
identity and composition laws.  The continuous multiplicative lattice
classifier satisfies the same reindexing equation, including maps between
different dimensions.  The standard-loop representatives and the quotient
decoder satisfy the same reindexing equations.  The lattice reindexings are
also packaged as continuous additive morphisms with the corresponding
identity and composition laws.  When the index map is an equivalence,
the torus coordinate map and lattice reindexing are upgraded to continuous
homeomorphisms and additive equivalences, with matching coherence laws.
Surjective and injective index maps additionally give the exact injectivity
and surjectivity behavior of the torus map, lattice reindexing, and typed
quotient map, including converses.  The typed quotient maps compose
contravariantly and are additive homomorphisms for the transported winding
groups (continuously for the discrete quotient topologies); their kernels are
exactly the classes whose winding vanishes on the image of the index map.  At
arbitrary torus basepoints, the same coordinate maps are exposed as continuous
multiplicative homomorphisms with explicit identity/composition laws, and the
canonical basepoint classifiers factor their action through the lattice
reindexing.  The same classifiers transport the exact fiber-constant image,
injectivity/surjectivity converses, and kernel characterization to every
torus basepoint.  Finally, arbitrary integer matrices (not only coordinate
selections) define continuous torus maps whose winding actions, standard
representatives, typed quotient maps, images, kernels, injectivity and
surjectivity, and additive quotient homomorphisms all satisfy matching
matrix-composition and identity laws.
At arbitrary basepoints, the induced continuous multiplicative homomorphisms
commute with explicit basepoint transport, and both the path-based and
canonical winding classifiers satisfy the corresponding matrix naturality
square, with the endpoint cast made explicit.
The canonical classifier also transports exact matrix image, kernel,
injectivity, and surjectivity criteria to arbitrary basepoints.
The arbitrary-basepoint matrix homomorphisms satisfy typed composition and
identity laws as well, with the endpoint equalities induced by matrix-map
coherence transported explicitly.
An explicit two-sided integer-matrix inverse is upgraded at every level to an
additive lattice equivalence, a torus homeomorphism, and a quotient
homeomorphism and continuous additive equivalence for the transported loop
groups at the canonical basepoint.  At every arbitrary torus basepoint, the
corresponding quotient homomorphism is likewise upgraded to a continuous
multiplicative equivalence, with explicit injectivity and surjectivity
corollaries.
For square matrices, the lattice and canonical quotient actions satisfy the
sharp determinant criteria: injectivity is equivalent to a nonzero determinant,
while surjectivity is equivalent to a unit determinant.  A unimodular matrix's
canonical nonsingular inverse then supplies the preceding equivalences without
requiring an inverse as an extra hypothesis, including at arbitrary
basepoints.
For every nonzero determinant, the winding-lattice cokernel is finite with
cardinality `Int.natAbs (Matrix.det A)`.  The canonical quotient image has the
same finite index, and its quotient cardinality and finiteness are exposed
explicitly as well.
For composable non-singular square matrices, the determinant index is
multiplicative, and composition is refined to a short exact sequence of
cokernels: the induced composition embedding is injective and the canonical
projection onto the second cokernel is surjective with that image as kernel,
on both the winding and topological quotient sides.
The lattice cokernel is additionally presented, via Smith normal form, as a
coordinatewise product of `ZMod` factors for arbitrary rank: zero factors
retain the free part, while nonzero factors are the finite cyclic torsion
factors.  The full-rank image theorem and exact product cardinality are made
available as finite specializations.  The same arbitrary-rank presentation is
transported through the winding equivalence to the canonical quotient
cokernel of the induced torus homomorphism, now as an explicit additive
equivalence.  Finally, the quotient of the
composition cokernel by the projection kernel is identified with the second
cokernel by an explicit first-isomorphism additive equivalence, whose action
on quotient representatives is proved directly.
The underlying cokernel construction is also factored through a general
first-isomorphism package for arbitrary composable additive homomorphisms.
The induced map and projection have direct quotient-representative formulas,
so the package can be used without unfolding the underlying quotient maps.
Consequently, rectangular integer matrices in any composable dimensions
inherit the same short-exact sequence whenever the second matrix action is
injective, and the corresponding finite-torus quotient maps satisfy the same
statement.
The induced cokernel map also has the exact converse criterion that its
composite-image preimage equals the first image.
The rectangular composite ranges are additionally identified with the ranges
of `matrixAction (matrixCompose A B)` and
`matrixMapQuotientAddHom (matrixCompose A B)`.  The short-exact statements
and converse criteria are exposed in these canonical matrix-composition forms
as well, so clients need not unfold the homomorphism composition.
Finally, the winding equivalence lifts from image subgroups to an explicit
additive equivalence between every rectangular finite-torus cokernel and its
integer-lattice cokernel.  In the composite form, this equivalence is proved
natural for both the cokernel embedding and projection, so the topological and
lattice exact sequences are related by a checked commutative diagram.  The
named square-matrix `matrixCompose` maps expose the same naturality laws
directly at their canonical target types.  A single rectangular certificate
packages both short-exact sequences and both commuting squares under the
shared injectivity hypothesis.  The equivalence also transports cardinality
and finiteness for individual matrices and explicit composites, without a
square-dimension or finiteness assumption.
The Smith-normal-form product is generalized to rectangular maps with full
target rank and transported to their finite-torus cokernels as well.  The
lattice finite-cokernel condition is characterized exactly by full target
rank, and the arbitrary-rank factorization identifies this condition with the
absence of zero Smith factors on both the lattice and finite-torus sides.
In the square nonsingular specialization, the Smith-modulus product is proved
to equal the determinant index `Int.natAbs (Matrix.det A)` on both sides.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open Set Topology
open scoped ContinuousMap Topology BigOperators

noncomputable section

namespace FiniteTorusWinding

open ConcreteCircleWinding

attribute [local instance] _root_.Path.Homotopic.setoid

/-! The functorial quotient module keeps the fundamental-group instance local.
We reuse that exact instance here so the multiplicative certificate below is
definitionally the usual fundamental-group multiplication. -/
noncomputable local instance functorialLoopQuotGroup
    (X : Type*) [TopologicalSpace X] (x : X) :
    Group (QuotientFundamentalGroup.LoopQuot X x) :=
  QuotientFundamentalGroup.functorialLoopQuotGroup X x

/-- The `n`-dimensional torus as a finite product of additive circles. -/
abbrev Carrier (n : ℕ) : Type := Fin n → TopologicalCircle

/-- The all-zero basepoint of the finite torus. -/
noncomputable abbrev base (n : ℕ) : Carrier n := fun _ => 0

/-- Genuine compact-open based loops in the finite torus. -/
abbrev Loop (n : ℕ) : Type := _root_.Path (base n) (base n)

/-- Projection of a finite-torus loop to one circle coordinate. -/
noncomputable def coordinate {n : ℕ} (i : Fin n) (γ : Loop n) :
    ConcreteCircleWinding.TopologicalLoop :=
  γ.map (continuous_apply i)

/-- Coordinatewise winding vector. -/
noncomputable def winding {n : ℕ} (γ : Loop n) : Fin n → ℤ :=
  fun i => windingPath (coordinate i γ)

/-- A map of finite index sets induces the corresponding coordinate-selection
map between finite tori. -/
noncomputable def coordinateProjection {n m : ℕ} (f : Fin m → Fin n) :
    C(Carrier n, Carrier m) :=
  ⟨fun x j => x (f j), continuous_pi (fun j => continuous_apply (f j))⟩

/-- Reindexing of integer winding vectors induced by a coordinate map. -/
noncomputable def coordinateReindex {n m : ℕ} (f : Fin m → Fin n) :
    (Fin n → ℤ) →+ (Fin m → ℤ) where
  toFun z j := z (f j)
  map_zero' := by ext j; rfl
  map_add' z w := by ext j; rfl

/-- Reindexing is a continuous additive morphism for the product topologies
on the integer lattices. -/
noncomputable def coordinateReindexContinuous {n m : ℕ} (f : Fin m → Fin n) :
    (Fin n → ℤ) →ₜ+ (Fin m → ℤ) where
  toAddMonoidHom := coordinateReindex f
  continuous_toFun := by
    apply continuous_pi
    intro j
    exact continuous_apply (f j)

@[simp] theorem coordinateReindexContinuous_apply {n m : ℕ}
    (f : Fin m → Fin n) (z : Fin n → ℤ) :
    coordinateReindexContinuous f z = coordinateReindex f z :=
  rfl

/-- Lattice reindexing is contravariantly functorial. -/
theorem coordinateReindex_comp {n m k : ℕ} (f : Fin m → Fin n)
    (g : Fin k → Fin m) :
    coordinateReindex (f ∘ g) =
      (coordinateReindex g).comp (coordinateReindex f) := by
  ext z j
  rfl

/-- Reindexing along the identity index map is the identity additive homomorphism. -/
theorem coordinateReindex_id (n : ℕ) :
    coordinateReindex (id : Fin n → Fin n) = AddMonoidHom.id (Fin n → ℤ) := by
  ext z j
  rfl

/-- Continuous lattice reindexing is contravariantly functorial. -/
theorem coordinateReindexContinuous_comp {n m k : ℕ} (f : Fin m → Fin n)
    (g : Fin k → Fin m) :
    coordinateReindexContinuous (f ∘ g) =
      (coordinateReindexContinuous g).comp (coordinateReindexContinuous f) := by
  ext z j
  rfl

/-- Continuous reindexing along the identity index map is the identity. -/
theorem coordinateReindexContinuous_id (n : ℕ) :
    coordinateReindexContinuous (id : Fin n → Fin n) =
      ContinuousAddMonoidHom.id (Fin n → ℤ) := by
  ext z j
  rfl

/-- A coordinate relabeling is a homeomorphism of finite tori. -/
noncomputable def coordinateProjectionHomeomorph {n m : ℕ} (e : Fin m ≃ Fin n) :
    Carrier n ≃ₜ Carrier m where
  toFun := coordinateProjection e
  invFun := coordinateProjection e.symm
  left_inv x := by
    ext j
    simp [coordinateProjection]
  right_inv x := by
    ext j
    simp [coordinateProjection]
  continuous_toFun := (coordinateProjection e).continuous_toFun
  continuous_invFun := (coordinateProjection e.symm).continuous_toFun

/-- Coordinate relabeling homeomorphisms compose contravariantly. -/
theorem coordinateProjectionHomeomorph_comp {n m k : ℕ} (e : Fin m ≃ Fin n)
    (g : Fin k ≃ Fin m) :
    coordinateProjectionHomeomorph (g.trans e) =
      (coordinateProjectionHomeomorph e).trans
        (coordinateProjectionHomeomorph g) := by
  ext x j
  rfl

/-- Relabeling along the identity equivalence is the identity homeomorphism. -/
theorem coordinateProjectionHomeomorph_refl (n : ℕ) :
    coordinateProjectionHomeomorph (Equiv.refl (Fin n)) =
      Homeomorph.refl (Carrier n) := by
  ext x j
  rfl

/-- A bijective coordinate relabeling is a continuous additive equivalence of
integer lattices. -/
noncomputable def coordinateReindexContinuousEquiv {n m : ℕ} (e : Fin m ≃ Fin n) :
    (Fin n → ℤ) ≃ₜ+ (Fin m → ℤ) where
  toFun := coordinateReindex e
  invFun := coordinateReindex e.symm
  left_inv z := by
    ext i
    simp [coordinateReindex]
  right_inv z := by
    ext i
    simp [coordinateReindex]
  map_add' z w := by
    ext i
    rfl
  continuous_toFun := (coordinateReindexContinuous e).continuous_toFun
  continuous_invFun := (coordinateReindexContinuous e.symm).continuous_toFun

/-- Continuous additive reindexing equivalences compose contravariantly. -/
theorem coordinateReindexContinuousEquiv_comp {n m k : ℕ}
    (e : Fin m ≃ Fin n) (g : Fin k ≃ Fin m) :
    coordinateReindexContinuousEquiv (g.trans e) =
      (coordinateReindexContinuousEquiv e).trans
        (coordinateReindexContinuousEquiv g) := by
  ext z j
  rfl

/-- Reindexing along the identity equivalence is the identity continuous
additive equivalence. -/
theorem coordinateReindexContinuousEquiv_refl (n : ℕ) :
    coordinateReindexContinuousEquiv (Equiv.refl (Fin n)) =
      ContinuousAddEquiv.refl (Fin n → ℤ) := by
  ext z j
  rfl

/-- A surjective index map gives an injective reindexing of integer lattices. -/
theorem coordinateReindex_injective_of_surjective {n m : ℕ}
    (f : Fin m → Fin n) (hf : Function.Surjective f) :
    Function.Injective (coordinateReindex f) := by
  intro z w h
  funext i
  obtain ⟨j, rfl⟩ := hf i
  exact congrFun h j

/-- An injective index map gives a surjective reindexing of integer lattices;
the missing coordinates are filled with zero. -/
theorem coordinateReindex_surjective_of_injective {n m : ℕ}
    (f : Fin m → Fin n) (hf : Function.Injective f) :
    Function.Surjective (coordinateReindex f) := by
  intro w
  let z : Fin n → ℤ := Function.extend f w (fun _ => 0)
  refine ⟨z, ?_⟩
  funext j
  exact Function.Injective.extend_apply hf w (fun _ => 0) j

/-- Reindexing is injective exactly when the index map is surjective. -/
theorem coordinateReindex_injective_iff_surjective {n m : ℕ}
    (f : Fin m → Fin n) :
    Function.Injective (coordinateReindex f) ↔ Function.Surjective f := by
  constructor
  · intro hinj
    by_contra hsurj
    simp only [Function.Surjective, not_forall, not_exists] at hsurj
    obtain ⟨i, hi⟩ := hsurj
    let z : Fin n → ℤ := fun l => if l = i then 1 else 0
    have hz : coordinateReindex f z = coordinateReindex f 0 := by
      funext j
      have hne : f j ≠ i := hi j
      simp [coordinateReindex, z, hne]
    have hz' := hinj hz
    have hi0 := congrFun hz' i
    simp [z] at hi0
  · exact coordinateReindex_injective_of_surjective f

/-- Reindexing is surjective exactly when the index map is injective. -/
theorem coordinateReindex_surjective_iff_injective {n m : ℕ}
    (f : Fin m → Fin n) :
    Function.Surjective (coordinateReindex f) ↔ Function.Injective f := by
  constructor
  · intro hsurj j k hfjk
    by_contra hne
    let w : Fin m → ℤ := fun l => if l = k then 1 else 0
    obtain ⟨z, hz⟩ := hsurj w
    have hzw : w j = w k := by
      calc
        w j = z (f j) := by
          simpa [coordinateReindex] using (congrFun hz j).symm
        _ = z (f k) := by rw [hfjk]
        _ = w k := by simpa [coordinateReindex] using congrFun hz k
    have hjw : w j = 0 := by simp [w, hne]
    have hkw : w k = 1 := by simp [w]
    rw [hjw, hkw] at hzw
    norm_num at hzw
  · exact coordinateReindex_surjective_of_injective f

/-- The image of a lattice reindexing consists exactly of vectors constant on
the fibers of its index map. -/
theorem coordinateReindex_mem_range_iff {n m : ℕ} (f : Fin m → Fin n)
    (w : Fin m → ℤ) :
    w ∈ Set.range (coordinateReindex f) ↔
      ∀ ⦃j k : Fin m⦄, f j = f k → w j = w k := by
  constructor
  · rintro ⟨z, rfl⟩ j k h
    simp [coordinateReindex, h]
  · intro h
    let z : Fin n → ℤ := Function.extend f w (fun _ => 0)
    refine ⟨z, ?_⟩
    funext j
    have hfactor : Function.FactorsThrough w f := by
      intro a b hab
      exact h hab
    exact hfactor.extend_apply (fun _ => 0) j

/-- A lattice vector lies in the kernel of reindexing exactly when it
vanishes on the image of the index map. -/
theorem coordinateReindex_eq_zero_iff {n m : ℕ} (f : Fin m → Fin n)
    (z : Fin n → ℤ) :
    coordinateReindex f z = 0 ↔
      ∀ i ∈ Set.range f, z i = 0 := by
  constructor
  · intro h i hi
    obtain ⟨j, rfl⟩ := hi
    have hj := congrFun h j
    simpa [coordinateReindex] using hj
  · intro h
    funext j
    exact h (f j) ⟨j, rfl⟩

/-- Coordinate-selection maps respect composition of index maps. -/
theorem coordinateProjection_comp {n m k : ℕ} (f : Fin m → Fin n)
    (g : Fin k → Fin m) :
    (coordinateProjection (n := m) (m := k) g).comp
        (coordinateProjection (n := n) (m := m) f) =
      coordinateProjection (n := n) (m := k) (f ∘ g) := by
  ext x j
  rfl

/-- Selecting coordinates along the identity index map is the identity map. -/
theorem coordinateProjection_id (n : ℕ) :
    coordinateProjection (id : Fin n → Fin n) = ContinuousMap.id (Carrier n) := by
  ext x j
  rfl

/-- A surjective index map gives an injective coordinate map of finite tori. -/
theorem coordinateProjection_injective_of_surjective {n m : ℕ}
    (f : Fin m → Fin n) (hf : Function.Surjective f) :
    Function.Injective (coordinateProjection f) := by
  intro x y h
  funext i
  obtain ⟨j, rfl⟩ := hf i
  exact congrFun h j

/-- An injective index map gives a surjective coordinate map of finite tori;
the missing coordinates can be filled with the zero circle point. -/
theorem coordinateProjection_surjective_of_injective {n m : ℕ}
    (f : Fin m → Fin n) (hf : Function.Injective f) :
    Function.Surjective (coordinateProjection f) := by
  intro x
  let z : Carrier n := fun i => Function.extend f x (fun _ => 0) i
  refine ⟨z, ?_⟩
  funext j
  exact Function.Injective.extend_apply hf x (fun _ => 0) j

/-- A coordinate map of finite tori is injective exactly when its index map is
surjective. -/
theorem coordinateProjection_injective_iff_surjective {n m : ℕ}
    (f : Fin m → Fin n) :
    Function.Injective (coordinateProjection f) ↔ Function.Surjective f := by
  constructor
  · intro hinj
    by_contra hsurj
    simp only [Function.Surjective, not_forall, not_exists] at hsurj
    obtain ⟨i, hi⟩ := hsurj
    let a : TopologicalCircle := circleCover 0
    let b : TopologicalCircle := circleCover (cut 0)
    have hab : a ≠ b := by
      change circleCover 0 ≠ circleCover (cut 0)
      exact circleCover_ne_cut 0
    let x : Carrier n := fun l => if l = i then a else b
    let y : Carrier n := fun _ => b
    have hxy : coordinateProjection f x = coordinateProjection f y := by
      funext j
      have hne : f j ≠ i := hi j
      simp [coordinateProjection, x, y, hne]
    have hxy' := hinj hxy
    have hi0 := congrFun hxy' i
    have hab' : a = b := by simpa [x, y] using hi0
    exact hab hab'
  · exact coordinateProjection_injective_of_surjective f

/-- A coordinate map of finite tori is surjective exactly when its index map
is injective. -/
theorem coordinateProjection_surjective_iff_injective {n m : ℕ}
    (f : Fin m → Fin n) :
    Function.Surjective (coordinateProjection f) ↔ Function.Injective f := by
  constructor
  · intro hsurj j k hfjk
    by_contra hne
    let a : TopologicalCircle := circleCover 0
    let b : TopologicalCircle := circleCover (cut 0)
    have hab : a ≠ b := by
      change circleCover 0 ≠ circleCover (cut 0)
      exact circleCover_ne_cut 0
    let x : Carrier m := fun l => if l = k then a else b
    obtain ⟨z, hz⟩ := hsurj x
    have hxjk : x j = x k := by
      calc
        x j = z (f j) := by
          simpa [coordinateProjection] using (congrFun hz j).symm
        _ = z (f k) := by rw [hfjk]
        _ = x k := by simpa [coordinateProjection] using congrFun hz k
    have hjx : x j = b := by simp [x, hne]
    have hkx : x k = a := by simp [x]
    rw [hjx, hkx] at hxjk
    exact hab hxjk.symm
  · exact coordinateProjection_surjective_of_injective f

/-- Winding vectors are natural under coordinate selection: the induced loop
map simply reindexes the vector. -/
theorem winding_coordinateProjection {n m : ℕ} (f : Fin m → Fin n)
    (γ : Loop n) :
    winding (γ.map (coordinateProjection f).continuous) =
      fun j => winding γ (f j) := by
  funext j
  change windingPath
      (coordinate j (γ.map (coordinateProjection f).continuous)) =
    windingPath (coordinate (f j) γ)
  congr 1

/-- The standard loop with a prescribed integer winding in each coordinate. -/
noncomputable def standardLoop {n : ℕ} (z : Fin n → ℤ) : Loop n :=
  _root_.Path.pi (fun i => ConcreteCircleWinding.standardLoop (z i))

@[simp] theorem coordinate_standardLoop {n : ℕ} (z : Fin n → ℤ) (i : Fin n) :
    coordinate i (standardLoop z) = ConcreteCircleWinding.standardLoop (z i) := by
  apply _root_.Path.ext
  funext t
  rfl

/-- Standard representatives are preserved by coordinate selection. -/
theorem standardLoop_coordinateProjection {n m : ℕ} (f : Fin m → Fin n)
    (z : Fin n → ℤ) :
    (standardLoop z).map (coordinateProjection f).continuous =
      standardLoop (fun j => z (f j)) := by
  apply _root_.Path.ext
  funext t
  funext j
  rfl

@[simp] theorem winding_standardLoop {n : ℕ} (z : Fin n → ℤ) :
    winding (standardLoop z) = z := by
  funext i
  simp [winding]

theorem winding_eq_of_homotopic {n : ℕ} {γ δ : Loop n}
    (h : γ.Homotopic δ) : winding γ = winding δ := by
  funext i
  exact windingPath_eq_of_homotopic (h.map ⟨_, continuous_apply i⟩)

theorem coordinate_pi_eq (γ : Loop n) :
    _root_.Path.pi (fun i => coordinate i γ) = γ := by
  apply _root_.Path.ext
  funext t
  funext i
  rfl

/-- Every finite-torus loop is endpoint-fixed homotopic to the coordinatewise
standard loop selected by its winding vector. -/
theorem standardLoop_homotopic {n : ℕ} (γ : Loop n) :
    (standardLoop (winding γ)).Homotopic γ := by
  have hcoord : ∀ i, (ConcreteCircleWinding.standardLoop (winding γ i)).Homotopic
      (coordinate i γ) := fun i => ConcreteCircleWinding.standardLoop_homotopic _
  have hpi :
      (_root_.Path.pi
        (fun i => ConcreteCircleWinding.standardLoop (winding γ i))).Homotopic
        (_root_.Path.pi (fun i => coordinate i γ)) := by
    refine ⟨_root_.Path.Homotopic.piHomotopy _ _ (fun i => ?_)⟩
    exact Classical.choice (hcoord i)
  simpa only [standardLoop, coordinate_pi_eq] using hpi

/-- Coordinate winding is a complete invariant of based finite-torus loops. -/
theorem homotopic_iff_winding_eq {n : ℕ} (γ δ : Loop n) :
    γ.Homotopic δ ↔ winding γ = winding δ := by
  constructor
  · exact winding_eq_of_homotopic
  · intro h
    exact (standardLoop_homotopic γ).symm.trans (h ▸ standardLoop_homotopic δ)

theorem coordinate_trans {n : ℕ} (i : Fin n) (γ δ : Loop n) :
    coordinate i (γ.trans δ) = (coordinate i γ).trans (coordinate i δ) := by
  exact _root_.Path.map_trans γ δ (continuous_apply i)

theorem winding_trans {n : ℕ} (γ δ : Loop n) :
    winding (γ.trans δ) = winding γ + winding δ := by
  funext i
  change windingPath (coordinate i (γ.trans δ)) = _
  rw [coordinate_trans, windingPath_trans]
  rfl

theorem winding_identity {n : ℕ} :
    winding (_root_.Path.refl (base n)) = 0 := by
  funext i
  change windingPath (coordinate i (_root_.Path.refl (base n))) = 0
  rw [show coordinate i (_root_.Path.refl (base n)) =
      _root_.Path.refl (0 : TopologicalCircle) by
    apply _root_.Path.ext
    funext t
    rfl]
  exact windingPath_refl

/-- Based finite-torus loop classes. -/
abbrev LoopQuot (n : ℕ) : Type :=
  _root_.Path.Homotopic.Quotient (base n) (base n)

/-- Coordinate selection on based loop classes, with the target basepoint
cast made explicit.  The cast is definitionally along the zero basepoint. -/
noncomputable def coordinateProjectionQuotientMap {n m : ℕ}
    (f : Fin m → Fin n) : LoopQuot n → LoopQuot m :=
  fun q =>
    (_root_.Path.Homotopic.Quotient.map q (coordinateProjection f)).cast
      (by rfl) (by rfl)

/-- Winding descended to loop homotopy classes. -/
noncomputable def encode {n : ℕ} : LoopQuot n → Fin n → ℤ :=
  Quotient.lift winding (fun _ _ h => winding_eq_of_homotopic h)

/-- The quotient winding classifier commutes with every coordinate-selection
map of finite tori. -/
theorem encode_coordinateProjection {n m : ℕ} (f : Fin m → Fin n)
    (q : LoopQuot n) :
    encode
        (_root_.Path.Homotopic.Quotient.map q (coordinateProjection f)) =
      fun j => encode q (f j) := by
  induction q using _root_.Path.Homotopic.Quotient.ind with
  | mk γ =>
    change winding (γ.map (coordinateProjection f).continuous) =
      fun j => winding γ (f j)
    exact winding_coordinateProjection f γ

/-- The typed quotient map is classified by the same lattice reindexing. -/
theorem encode_coordinateProjectionQuotientMap {n m : ℕ}
    (f : Fin m → Fin n) (q : LoopQuot n) :
    encode (coordinateProjectionQuotientMap f q) =
      coordinateReindex f (encode q) := by
  induction q using _root_.Path.Homotopic.Quotient.ind with
  | mk γ =>
    change winding (γ.map (coordinateProjection f).continuous) =
      coordinateReindex f (winding γ)
    exact winding_coordinateProjection f γ

/-- Standard loop class for an integer vector. -/
noncomputable def decode {n : ℕ} (z : Fin n → ℤ) : LoopQuot n :=
  Quotient.mk' (standardLoop z)

/-- The explicit quotient representatives are natural in the same way as the
    winding classifier: selecting coordinates reindexes the lattice vector. -/
theorem decode_coordinateProjection {n m : ℕ} (f : Fin m → Fin n)
    (z : Fin n → ℤ) :
    _root_.Path.Homotopic.Quotient.map (decode z) (coordinateProjection f) =
      decode (fun j => z (f j)) := by
  change Quotient.mk'
      ((standardLoop z).map (coordinateProjection f).continuous) =
    Quotient.mk' (standardLoop (fun j => z (f j)))
  rw [standardLoop_coordinateProjection]
  rfl

@[simp] theorem encode_decode {n : ℕ} (z : Fin n → ℤ) :
    encode (decode z) = z :=
  winding_standardLoop z

theorem decode_encode {n : ℕ} (x : LoopQuot n) : decode (encode x) = x := by
  refine Quotient.inductionOn x ?_
  intro γ
  exact Quotient.sound (standardLoop_homotopic γ)

/-- Algebraic classification of finite-torus loop classes. -/
noncomputable def equivIntVector (n : ℕ) : LoopQuot n ≃ (Fin n → ℤ) where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

/-- Typed quotient coordinate maps compose contravariantly. -/
theorem coordinateProjectionQuotientMap_comp {n m k : ℕ}
    (f : Fin m → Fin n) (g : Fin k → Fin m) (q : LoopQuot n) :
    coordinateProjectionQuotientMap g (coordinateProjectionQuotientMap f q) =
      coordinateProjectionQuotientMap (f ∘ g) q := by
  apply (equivIntVector k).injective
  change encode (coordinateProjectionQuotientMap g
      (coordinateProjectionQuotientMap f q)) =
    encode (coordinateProjectionQuotientMap (f ∘ g) q)
  rw [encode_coordinateProjectionQuotientMap,
    encode_coordinateProjectionQuotientMap,
    encode_coordinateProjectionQuotientMap]
  rfl

/-- Typed quotient coordinate selection along the identity is the identity. -/
theorem coordinateProjectionQuotientMap_id {n : ℕ} (q : LoopQuot n) :
    coordinateProjectionQuotientMap (id : Fin n → Fin n) q = q := by
  apply (equivIntVector n).injective
  change encode (coordinateProjectionQuotientMap (id : Fin n → Fin n) q) =
    encode q
  rw [encode_coordinateProjectionQuotientMap]
  rw [coordinateReindex_id]
  rfl

/-- A surjective index map induces an injective map on finite-torus loop
classes. -/
theorem coordinateProjectionQuotientMap_injective_of_surjective
    {n m : ℕ} (f : Fin m → Fin n) (hf : Function.Surjective f) :
    Function.Injective (coordinateProjectionQuotientMap f) := by
  intro q r hqr
  apply (equivIntVector n).injective
  apply coordinateReindex_injective_of_surjective f hf
  change coordinateReindex f (encode q) = coordinateReindex f (encode r)
  rw [← encode_coordinateProjectionQuotientMap,
    ← encode_coordinateProjectionQuotientMap, hqr]

/-- An injective index map induces a surjective map on finite-torus loop
classes. -/
theorem coordinateProjectionQuotientMap_surjective_of_injective
    {n m : ℕ} (f : Fin m → Fin n) (hf : Function.Injective f) :
    Function.Surjective (coordinateProjectionQuotientMap f) := by
  intro q
  obtain ⟨z, hz⟩ := coordinateReindex_surjective_of_injective f hf (encode q)
  refine ⟨decode z, ?_⟩
  apply (equivIntVector m).injective
  change encode (coordinateProjectionQuotientMap f (decode z)) = encode q
  rw [encode_coordinateProjectionQuotientMap, encode_decode, hz]

/-- A typed quotient coordinate map is injective exactly when its index map is
surjective. -/
theorem coordinateProjectionQuotientMap_injective_iff_surjective
    {n m : ℕ} (f : Fin m → Fin n) :
    Function.Injective (coordinateProjectionQuotientMap f) ↔
      Function.Surjective f := by
  constructor
  · intro h
    apply (coordinateReindex_injective_iff_surjective f).mp
    intro z w hzw
    have hmap : coordinateProjectionQuotientMap f (decode z) =
        coordinateProjectionQuotientMap f (decode w) := by
      apply (equivIntVector m).injective
      change encode (coordinateProjectionQuotientMap f (decode z)) =
        encode (coordinateProjectionQuotientMap f (decode w))
      rw [encode_coordinateProjectionQuotientMap,
        encode_coordinateProjectionQuotientMap, encode_decode,
        encode_decode, hzw]
    have hdec := h hmap
    have henc := congrArg (fun q => encode q) hdec
    simpa only [encode_decode] using henc
  · exact coordinateProjectionQuotientMap_injective_of_surjective f

/-- A typed quotient coordinate map is surjective exactly when its index map
is injective. -/
theorem coordinateProjectionQuotientMap_surjective_iff_injective
    {n m : ℕ} (f : Fin m → Fin n) :
    Function.Surjective (coordinateProjectionQuotientMap f) ↔
      Function.Injective f := by
  constructor
  · intro h
    apply (coordinateReindex_surjective_iff_injective f).mp
    intro w
    obtain ⟨q, hq⟩ := h (decode w)
    have henc := congrArg (fun q => encode q) hq
    rw [encode_coordinateProjectionQuotientMap, encode_decode] at henc
    exact ⟨encode q, henc⟩
  · exact coordinateProjectionQuotientMap_surjective_of_injective f

/-- The image of the typed quotient map is exactly the set of classes whose
winding vectors are constant on the fibers of the index map. -/
theorem coordinateProjectionQuotientMap_mem_range_iff
    {n m : ℕ} (f : Fin m → Fin n) (q : LoopQuot m) :
    q ∈ Set.range (coordinateProjectionQuotientMap f) ↔
      ∀ ⦃j k : Fin m⦄, f j = f k → encode q j = encode q k := by
  constructor
  · rintro ⟨p, rfl⟩ j k h
    rw [encode_coordinateProjectionQuotientMap]
    simp [coordinateReindex, h]
  · intro h
    obtain ⟨z, hz⟩ := (coordinateReindex_mem_range_iff f (encode q)).mpr h
    refine ⟨decode z, ?_⟩
    apply (equivIntVector m).injective
    change encode (coordinateProjectionQuotientMap f (decode z)) = encode q
    rw [encode_coordinateProjectionQuotientMap, encode_decode, hz]

/-- The additive-group structure transported from the integer winding lattice. -/
noncomputable instance loopQuotAddGroup (n : ℕ) : AddGroup (LoopQuot n) :=
  (equivIntVector n).addGroup

/-- Winding as an additive equivalence. -/
noncomputable def loopQuotAddEquivIntVector (n : ℕ) :
    LoopQuot n ≃+ (Fin n → ℤ) where
  toEquiv := equivIntVector n
  map_add' x y := by
    change encode (decode (encode x + encode y)) = encode x + encode y
    exact encode_decode _

theorem encode_trans {n : ℕ} (x y : LoopQuot n) :
    encode (_root_.Path.Homotopic.Quotient.trans x y) = encode x + encode y := by
  induction x using Quotient.ind with
  | _ γ =>
      induction y using Quotient.ind with
      | _ δ => exact winding_trans γ δ

/-- Under the transported additive structure, addition is exactly
concatenation of loop homotopy classes. -/
theorem quotientTrans_eq_add {n : ℕ} (x y : LoopQuot n) :
    _root_.Path.Homotopic.Quotient.trans x y = x + y := by
  apply (equivIntVector n).injective
  change encode (_root_.Path.Homotopic.Quotient.trans x y) = encode (x + y)
  rw [encode_trans]
  exact (loopQuotAddEquivIntVector n).map_add x y |>.symm

/-- Typed quotient coordinate selection preserves the zero loop class. -/
theorem coordinateProjectionQuotientMap_map_zero {n m : ℕ}
    (f : Fin m → Fin n) :
    coordinateProjectionQuotientMap f (0 : LoopQuot n) = (0 : LoopQuot m) := by
  apply (equivIntVector m).injective
  change encode (coordinateProjectionQuotientMap f (0 : LoopQuot n)) =
    encode (0 : LoopQuot m)
  rw [encode_coordinateProjectionQuotientMap]
  have hn : encode (0 : LoopQuot n) = 0 :=
    (loopQuotAddEquivIntVector n).map_zero
  have hm : encode (0 : LoopQuot m) = 0 :=
    (loopQuotAddEquivIntVector m).map_zero
  rw [hn, hm]
  rfl

/-- Typed quotient coordinate selection preserves concatenation/addition. -/
theorem coordinateProjectionQuotientMap_map_add {n m : ℕ}
    (f : Fin m → Fin n) (x y : LoopQuot n) :
    coordinateProjectionQuotientMap f (x + y) =
      coordinateProjectionQuotientMap f x + coordinateProjectionQuotientMap f y := by
  apply (equivIntVector m).injective
  change encode (coordinateProjectionQuotientMap f (x + y)) =
    encode (coordinateProjectionQuotientMap f x + coordinateProjectionQuotientMap f y)
  rw [encode_coordinateProjectionQuotientMap]
  have hxy : encode (x + y) = encode x + encode y :=
    (loopQuotAddEquivIntVector n).map_add x y
  have hmap :
      encode (coordinateProjectionQuotientMap f x +
        coordinateProjectionQuotientMap f y) =
        encode (coordinateProjectionQuotientMap f x) +
          encode (coordinateProjectionQuotientMap f y) :=
    (loopQuotAddEquivIntVector m).map_add _ _
  rw [hxy, hmap, encode_coordinateProjectionQuotientMap,
    encode_coordinateProjectionQuotientMap]
  rfl

/-- The typed quotient coordinate map is a homomorphism of the transported
integer-winding additive groups. -/
noncomputable def coordinateProjectionQuotientAddHom {n m : ℕ}
    (f : Fin m → Fin n) : LoopQuot n →+ LoopQuot m where
  toFun := coordinateProjectionQuotientMap f
  map_zero' := coordinateProjectionQuotientMap_map_zero f
  map_add' := coordinateProjectionQuotientMap_map_add f

@[simp] theorem coordinateProjectionQuotientAddHom_apply {n m : ℕ}
    (f : Fin m → Fin n) (q : LoopQuot n) :
    coordinateProjectionQuotientAddHom f q =
      coordinateProjectionQuotientMap f q :=
  rfl

/-- The quotient additive maps satisfy the same contravariant composition law. -/
theorem coordinateProjectionQuotientAddHom_comp {n m k : ℕ}
    (f : Fin m → Fin n) (g : Fin k → Fin m) :
    coordinateProjectionQuotientAddHom (f ∘ g) =
      (coordinateProjectionQuotientAddHom g).comp
        (coordinateProjectionQuotientAddHom f) := by
  ext q
  exact (coordinateProjectionQuotientMap_comp f g q).symm

/-- The quotient additive map associated to the identity index map is the
identity homomorphism. -/
theorem coordinateProjectionQuotientAddHom_id (n : ℕ) :
    coordinateProjectionQuotientAddHom (id : Fin n → Fin n) =
      AddMonoidHom.id (LoopQuot n) := by
  ext q
  exact coordinateProjectionQuotientMap_id q

/-- The quotient coordinate map has the same exact kernel description as its
lattice classifier. -/
theorem coordinateProjectionQuotientMap_eq_zero_iff {n m : ℕ}
    (f : Fin m → Fin n) (q : LoopQuot n) :
    coordinateProjectionQuotientMap f q = (0 : LoopQuot m) ↔
      ∀ i ∈ Set.range f, encode q i = 0 := by
  constructor
  · intro h i hi
    obtain ⟨j, rfl⟩ := hi
    have hm : encode (0 : LoopQuot m) = 0 :=
      (loopQuotAddEquivIntVector m).map_zero
    have henc := congrArg (fun q => encode q) h
    rw [hm] at henc
    have hj := congrFun henc j
    rw [encode_coordinateProjectionQuotientMap] at hj
    change encode q (f j) = 0 at hj
    exact hj
  · intro h
    apply (equivIntVector m).injective
    change encode (coordinateProjectionQuotientMap f q) = encode (0 : LoopQuot m)
    rw [encode_coordinateProjectionQuotientMap]
    have hm : encode (0 : LoopQuot m) = 0 :=
      (loopQuotAddEquivIntVector m).map_zero
    rw [hm]
    exact (coordinateReindex_eq_zero_iff f (encode q)).mpr h

/-- Membership in the additive kernel is equivalent to the exact vanishing
condition on the image coordinates. -/
theorem coordinateProjectionQuotientAddHom_mem_ker_iff {n m : ℕ}
    (f : Fin m → Fin n) (q : LoopQuot n) :
    q ∈ (coordinateProjectionQuotientAddHom f).ker ↔
      ∀ i ∈ Set.range f, encode q i = 0 := by
  change coordinateProjectionQuotientMap f q = (0 : LoopQuot m) ↔ _
  exact coordinateProjectionQuotientMap_eq_zero_iff f q

/-- The ordinary final quotient topology on finite-torus loop classes. -/
noncomputable instance loopQuotTopologicalSpace (n : ℕ) :
    TopologicalSpace (LoopQuot n) :=
  TopologicalSpace.coinduced (Quotient.mk' : Loop n → LoopQuot n) inferInstance

theorem continuous_coordinate {n : ℕ} (i : Fin n) :
    Continuous (coordinate i : Loop n → ConcreteCircleWinding.TopologicalLoop) := by
  apply continuous_induced_rng.2
  exact (ContinuousMap.continuous_postcomp ⟨_, continuous_apply i⟩).comp
    continuous_induced_dom

/-- Coordinate winding is continuous into the discrete integer-vector space. -/
theorem continuous_winding {n : ℕ} :
    Continuous (winding : Loop n → Fin n → ℤ) := by
  apply continuous_pi
  intro i
  exact ConcreteCircleWinding.continuous_windingPath.comp (continuous_coordinate i)

theorem continuous_encode {n : ℕ} :
    Continuous (encode : LoopQuot n → Fin n → ℤ) := by
  apply Continuous.quotient_lift
  exact continuous_winding

/-- The null-homotopy class is open in the compact-open finite-torus loop
space.  This is the exact hypothesis in the general quotient-topological
fundamental-group discreteness criterion. -/
theorem isOpen_nullHomotopyClass (n : ℕ) :
    IsOpen
      (QuotientFundamentalGroup.nullHomotopyClass (Carrier n) (base n)) := by
  have hopen :
      IsOpen (winding ⁻¹' ({0} : Set (Fin n → ℤ))) :=
    (isOpen_discrete _).preimage continuous_winding
  convert hopen using 1
  ext γ
  change γ.Homotopic (_root_.Path.refl (base n)) ↔ winding γ = 0
  rw [homotopic_iff_winding_eq, winding_identity]

/-- Finite-torus winding as a continuous complete invariant. -/
noncomputable def windingCompleteInvariant (n : ℕ) :
    ContinuousCompleteInvariant (Loop n) (LoopQuot n) (Fin n → ℤ) where
  quotient := Quotient.mk'
  quotient_isQuotientMap := isQuotientMap_quotient_mk'
  invariant := winding
  classifier := equivIntVector n
  classifier_quotient := rfl
  invariant_continuous := continuous_winding

/-- The finite-torus loop quotient is discrete. -/
noncomputable instance loopQuotDiscreteTopology (n : ℕ) :
    DiscreteTopology (LoopQuot n) :=
  QuotientFundamentalGroup.quotientDiscreteTopology
    (Carrier n) (base n) (isOpen_nullHomotopyClass n)

/-- Typed quotient coordinate selection is a continuous additive map for the
discrete quotient topologies. -/
noncomputable def coordinateProjectionQuotientContinuousAddHom {n m : ℕ}
    (f : Fin m → Fin n) : LoopQuot n →ₜ+ LoopQuot m where
  toAddMonoidHom := coordinateProjectionQuotientAddHom f
  continuous_toFun := continuous_of_discreteTopology

@[simp] theorem coordinateProjectionQuotientContinuousAddHom_apply
    {n m : ℕ} (f : Fin m → Fin n) (q : LoopQuot n) :
    coordinateProjectionQuotientContinuousAddHom f q =
      coordinateProjectionQuotientMap f q :=
  rfl

/-- The continuous quotient additive maps inherit contravariant composition. -/
theorem coordinateProjectionQuotientContinuousAddHom_comp
    {n m k : ℕ} (f : Fin m → Fin n) (g : Fin k → Fin m) :
    coordinateProjectionQuotientContinuousAddHom (f ∘ g) =
      (coordinateProjectionQuotientContinuousAddHom g).comp
        (coordinateProjectionQuotientContinuousAddHom f) := by
  ext q
  exact (coordinateProjectionQuotientMap_comp f g q).symm

/-- The continuous quotient additive map associated to the identity is the
identity continuous homomorphism. -/
theorem coordinateProjectionQuotientContinuousAddHom_id (n : ℕ) :
    coordinateProjectionQuotientContinuousAddHom (id : Fin n → Fin n) =
      ContinuousAddMonoidHom.id (LoopQuot n) := by
  ext q
  exact coordinateProjectionQuotientMap_id q

/-- Every based quotient fundamental group of a finite torus is discrete.
The zero-basepoint classification is transported to an arbitrary point along
the explicit path supplied by path-connectedness of the indexed product. -/
theorem loopQuotDiscreteTopology_at (n : ℕ) (x : Carrier n) :
    DiscreteTopology
      (QuotientFundamentalGroup.LoopQuot (Carrier n) x) := by
  let p : _root_.Path (base n) x := PathConnectedSpace.somePath (base n) x
  have hbase : DiscreteTopology (LoopQuot n) := loopQuotDiscreteTopology n
  have hpath := QuotientFundamentalGroup.quotientDiscreteTopology_iff_of_path p
  exact hpath.mp hbase

/-- Finite-dimensional tori are semilocally simply connected at every point,
as witnessed by the discrete quotient criterion. -/
theorem semilocallySimplyConnected (n : ℕ) :
    QuotientFundamentalGroup.SemilocallySimplyConnected (Carrier n) := by
  intro x
  letI : DiscreteTopology
      (QuotientFundamentalGroup.LoopQuot (Carrier n) x) :=
    loopQuotDiscreteTopology_at n x
  exact QuotientFundamentalGroup.semilocallySimplyConnectedAt_of_discreteTopology
    (Carrier n) x

/-- The quotient-topological fundamental group of `(S¹)ⁿ` is homeomorphic to
the discrete integer lattice `ℤⁿ`. -/
noncomputable def loopQuotHomeomorphIntVector (n : ℕ) :
    LoopQuot n ≃ₜ (Fin n → ℤ) :=
  (windingCompleteInvariant n).classifierHomeomorph

/-- Every based quotient fundamental group of a finite torus has the same
integer-lattice model.  The model at the all-zero basepoint is transported
along a path supplied by path-connectedness. -/
noncomputable def loopQuotHomeomorphIntVector_at (n : ℕ) (x : Carrier n) :
    QuotientFundamentalGroup.LoopQuot (Carrier n) x ≃ₜ (Fin n → ℤ) :=
  by
    letI : Group
        (QuotientFundamentalGroup.LoopQuot (Carrier n) (base n)) :=
      inferInstanceAs (Group (FundamentalGroup (Carrier n) (base n)))
    letI : Group
        (QuotientFundamentalGroup.LoopQuot (Carrier n) x) :=
      inferInstanceAs (Group (FundamentalGroup (Carrier n) x))
    exact
      ((QuotientFundamentalGroup.pathConnectedBasepointContinuousMulEquiv
          (X := Carrier n) (base n) x).toHomeomorph.symm).trans
        (loopQuotHomeomorphIntVector n)

/-- Winding is simultaneously an additive equivalence and a homeomorphism. -/
noncomputable def loopQuotContinuousAddEquivIntVector (n : ℕ) :
    LoopQuot n ≃ₜ+ (Fin n → ℤ) where
  __ := loopQuotAddEquivIntVector n
  continuous_toFun := continuous_encode
  continuous_invFun := continuous_of_discreteTopology

/-! The additive classifier above is also a classifier for the actual
fundamental-group multiplication.  `Multiplicative` is only a type synonym;
its multiplication is the addition of the integer lattice. -/

/-- The finite-torus quotient fundamental group is continuously isomorphic,
as a multiplicative group, to the integer lattice. -/
noncomputable def loopQuotContinuousMulEquivIntVector (n : ℕ) :
    LoopQuot n ≃ₜ* Multiplicative (Fin n → ℤ) :=
  ContinuousMulEquiv.mk' (loopQuotHomeomorphIntVector n) <| by
    intro x y
    change encode (x * y) = encode x + encode y
    change encode (_root_.Path.Homotopic.Quotient.trans y x) =
      encode x + encode y
    simpa [add_comm] using encode_trans y x

/-- The multiplicative lattice classifier is natural under coordinate
selection, including maps between different finite dimensions. -/
theorem loopQuotContinuousMulEquivIntVector_coordinateProjection
    {n m : ℕ} (f : Fin m → Fin n) (q : LoopQuot n) :
    Multiplicative.ofAdd
        (coordinateReindex f (encode q)) =
      (loopQuotContinuousMulEquivIntVector m)
        (_root_.Path.Homotopic.Quotient.map q (coordinateProjection f)) := by
  apply Multiplicative.ext
  change coordinateReindex f (encode q) =
    encode (_root_.Path.Homotopic.Quotient.map q (coordinateProjection f))
  funext j
  exact (encode_coordinateProjection f q).symm ▸ rfl

/-- The classifier naturality equation can be read through the continuous
additive lattice morphism itself. -/
theorem loopQuotContinuousMulEquivIntVector_coordinateProjection_continuousReindex
    {n m : ℕ} (f : Fin m → Fin n) (q : LoopQuot n) :
    Multiplicative.ofAdd
        (coordinateReindexContinuous f (encode q)) =
      (loopQuotContinuousMulEquivIntVector m)
        (_root_.Path.Homotopic.Quotient.map q (coordinateProjection f)) := by
  simpa only [coordinateReindexContinuous_apply] using
    (loopQuotContinuousMulEquivIntVector_coordinateProjection f q)

/-- The same integer-lattice model works at every torus basepoint, and the
basepoint transport is a continuous multiplicative equivalence. -/
noncomputable def loopQuotContinuousMulEquivIntVector_at
    (n : ℕ) (x : Carrier n) :
    QuotientFundamentalGroup.LoopQuot (Carrier n) x ≃ₜ*
      Multiplicative (Fin n → ℤ) := by
  exact
    (QuotientFundamentalGroup.pathConnectedBasepointContinuousMulEquiv
      (X := Carrier n) (base n) x).symm.trans
      (loopQuotContinuousMulEquivIntVector n)

/-- Concatenation of finite-torus loop classes is commutative. -/
theorem quotientTrans_comm {n : ℕ} (x y : LoopQuot n) :
    _root_.Path.Homotopic.Quotient.trans x y =
      _root_.Path.Homotopic.Quotient.trans y x := by
  apply (loopQuotHomeomorphIntVector n).injective
  change encode (_root_.Path.Homotopic.Quotient.trans x y) =
    encode (_root_.Path.Homotopic.Quotient.trans y x)
  rw [encode_trans, encode_trans, add_comm]

/-- The transported winding addition on a finite-torus quotient is
commutative.  This packages the preceding classifier theorem as the
`AddCommGroup` structure needed by additive cokernel constructions. -/
noncomputable instance loopQuotAddCommGroup (n : ℕ) : AddCommGroup (LoopQuot n) :=
  { loopQuotAddGroup n with
    add_comm := by
      intro x y
      rw [← quotientTrans_eq_add, ← quotientTrans_eq_add]
      exact quotientTrans_comm x y }

/-- The fundamental group of every finite torus is abelian, at every chosen
basepoint. -/
theorem quotientMul_comm_at (n : ℕ) (x : Carrier n)
    (p q : QuotientFundamentalGroup.LoopQuot (Carrier n) x) :
    p * q = q * p := by
  let e := loopQuotContinuousMulEquivIntVector_at n x
  apply e.injective
  calc
    e (p * q) = e p * e q := e.map_mul p q
    _ = e q * e p := mul_comm _ _
    _ = e (q * p) := (e.map_mul q p).symm

/-! A classifier may be built using any explicit path from the canonical
basepoint.  The abelian target theorem in the functorial quotient module
shows that this extra path choice is immaterial. -/

/-- Classifier at a chosen torus basepoint along an explicit path. -/
noncomputable def loopQuotContinuousMulEquivIntVector_at_path
    (n : ℕ) (x : Carrier n)
    (p : _root_.Path (base n) x) :
    QuotientFundamentalGroup.LoopQuot (Carrier n) x ≃ₜ*
      Multiplicative (Fin n → ℤ) :=
  (QuotientFundamentalGroup.basepointChangeContinuousMulEquiv p).symm.trans
    (loopQuotContinuousMulEquivIntVector n)

/-- Path-based lattice classifiers are natural under coordinate selection.
Transporting a basepoint path and then applying the target classifier agrees
with reindexing the source lattice classifier, including arbitrary source and
target dimensions. -/
theorem loopQuotContinuousMulEquivIntVector_at_path_coordinateProjection
    {n m : ℕ} (f : Fin m → Fin n) (x : Carrier n)
    (p : _root_.Path (base n) x)
    (q : QuotientFundamentalGroup.LoopQuot (Carrier n) x) :
    (loopQuotContinuousMulEquivIntVector_at_path m
      (coordinateProjection f x)
      (p.map (coordinateProjection f).continuous))
        (_root_.Path.Homotopic.Quotient.map q (coordinateProjection f)) =
      Multiplicative.ofAdd
        (coordinateReindex f
          (Multiplicative.toAdd
            (loopQuotContinuousMulEquivIntVector_at_path n x p q))) := by
  let r : LoopQuot n :=
    (QuotientFundamentalGroup.basepointChangeContinuousMulEquiv p).symm q
  have hr :
      _root_.Path.Homotopic.Quotient.map q (coordinateProjection f) =
        QuotientFundamentalGroup.basepointChangeContinuousMulEquiv
          (p.map (coordinateProjection f).continuous)
          (_root_.Path.Homotopic.Quotient.map r (coordinateProjection f)) := by
    have hnat :=
      QuotientFundamentalGroup.basepointChange_quotientMap_naturality
        p (coordinateProjection f) r
    have hpr :
        QuotientFundamentalGroup.basepointChangeContinuousMulEquiv p
            ((QuotientFundamentalGroup.basepointChangeContinuousMulEquiv p).symm q) = q :=
      (QuotientFundamentalGroup.basepointChangeContinuousMulEquiv p).apply_symm_apply q
    rw [hpr] at hnat
    exact hnat
  rw [loopQuotContinuousMulEquivIntVector_at_path,
    loopQuotContinuousMulEquivIntVector_at_path]
  change
    (loopQuotContinuousMulEquivIntVector m)
      ((QuotientFundamentalGroup.basepointChangeContinuousMulEquiv
        (p.map (coordinateProjection f).continuous)).symm
        (_root_.Path.Homotopic.Quotient.map q (coordinateProjection f))) =
      Multiplicative.ofAdd
        (coordinateReindex f
          (Multiplicative.toAdd
            ((QuotientFundamentalGroup.basepointChangeContinuousMulEquiv p).symm.trans
              (loopQuotContinuousMulEquivIntVector n)) q))
  rw [hr]
  rw [(QuotientFundamentalGroup.basepointChangeContinuousMulEquiv
    (p.map (coordinateProjection f).continuous)).symm_apply_apply]
  exact (loopQuotContinuousMulEquivIntVector_coordinateProjection f r).symm

/-- The path-based arbitrary-basepoint naturality square can be read through
the continuous additive lattice morphism itself. -/
theorem loopQuotContinuousMulEquivIntVector_at_path_coordinateProjection_continuousReindex
    {n m : ℕ} (f : Fin m → Fin n) (x : Carrier n)
    (p : _root_.Path (base n) x)
    (q : QuotientFundamentalGroup.LoopQuot (Carrier n) x) :
    (loopQuotContinuousMulEquivIntVector_at_path m
      (coordinateProjection f x)
      (p.map (coordinateProjection f).continuous))
        (_root_.Path.Homotopic.Quotient.map q (coordinateProjection f)) =
      Multiplicative.ofAdd
        (coordinateReindexContinuous f
          (Multiplicative.toAdd
            (loopQuotContinuousMulEquivIntVector_at_path n x p q))) := by
  simpa only [coordinateReindexContinuous_apply] using
    (loopQuotContinuousMulEquivIntVector_at_path_coordinateProjection f x p q)

/-- The explicit-path lattice classifier is independent of the chosen path. -/
theorem loopQuotContinuousMulEquivIntVector_at_path_eq
    (n : ℕ) (x : Carrier n)
    (p q : _root_.Path (base n) x) :
    loopQuotContinuousMulEquivIntVector_at_path n x p =
      loopQuotContinuousMulEquivIntVector_at_path n x q := by
  have hpq :=
    QuotientFundamentalGroup.basepointChangeContinuousMulEquiv_eq_of_target_comm
      p q (quotientMul_comm_at n x)
  simp only [loopQuotContinuousMulEquivIntVector_at_path]
  rw [hpq]

/-- The canonical arbitrary-basepoint lattice classifiers are natural under
coordinate selection.  The path used by the definition is immaterial by the
abelian-target transport theorem, so no path choice appears in this statement.
-/
theorem loopQuotContinuousMulEquivIntVector_at_coordinateProjection
    {n m : ℕ} (f : Fin m → Fin n) (x : Carrier n)
    (q : QuotientFundamentalGroup.LoopQuot (Carrier n) x) :
    (loopQuotContinuousMulEquivIntVector_at m
      (coordinateProjection f x))
        (_root_.Path.Homotopic.Quotient.map q (coordinateProjection f)) =
      Multiplicative.ofAdd
        (coordinateReindex f
          (Multiplicative.toAdd
            (loopQuotContinuousMulEquivIntVector_at n x q))) := by
  let p : _root_.Path (base n) x := PathConnectedSpace.somePath (base n) x
  let p' : _root_.Path (base m) (coordinateProjection f x) :=
    PathConnectedSpace.somePath (base m) (coordinateProjection f x)
  have h := loopQuotContinuousMulEquivIntVector_at_path_coordinateProjection
    f x p q
  have ht := loopQuotContinuousMulEquivIntVector_at_path_eq m
    (coordinateProjection f x) (p.map (coordinateProjection f).continuous) p'
  have htq := congrArg
    (fun E => E (_root_.Path.Homotopic.Quotient.map q (coordinateProjection f))) ht
  have hs := loopQuotContinuousMulEquivIntVector_at_path_eq n x p
    (PathConnectedSpace.somePath (base n) x)
  have hsq := congrArg (fun E => E q) hs
  rw [htq] at h
  rw [← hsq] at h
  simpa [p, p', loopQuotContinuousMulEquivIntVector_at,
    loopQuotContinuousMulEquivIntVector_at_path,
    QuotientFundamentalGroup.pathConnectedBasepointContinuousMulEquiv] using h

/-- The canonical arbitrary-basepoint naturality square can likewise be read
through the continuous additive lattice morphism. -/
theorem loopQuotContinuousMulEquivIntVector_at_coordinateProjection_continuousReindex
    {n m : ℕ} (f : Fin m → Fin n) (x : Carrier n)
    (q : QuotientFundamentalGroup.LoopQuot (Carrier n) x) :
    (loopQuotContinuousMulEquivIntVector_at m
      (coordinateProjection f x))
        (_root_.Path.Homotopic.Quotient.map q (coordinateProjection f)) =
      Multiplicative.ofAdd
        (coordinateReindexContinuous f
          (Multiplicative.toAdd
            (loopQuotContinuousMulEquivIntVector_at n x q))) := by
  simpa only [coordinateReindexContinuous_apply] using
    (loopQuotContinuousMulEquivIntVector_at_coordinateProjection f x q)

/-! The coordinate map is itself a named morphism of quotient fundamental
groups at arbitrary basepoints.  The zero-basepoint additive map above is
the lattice-level specialization; this multiplicative version exposes the
full functorial map before choosing a classifier. -/

/-- Coordinate selection induces a continuous homomorphism between the
quotient fundamental groups at the corresponding basepoints. -/
noncomputable def coordinateProjectionQuotientContinuousMulHom
    {n m : ℕ} (f : Fin m → Fin n) (x : Carrier n) :
    QuotientFundamentalGroup.LoopQuot (Carrier n) x →ₜ*
      QuotientFundamentalGroup.LoopQuot
        (Carrier m) (coordinateProjection f x) :=
  QuotientFundamentalGroup.inducedContinuousMonoidHom
    (coordinateProjection f) x

@[simp] theorem coordinateProjectionQuotientContinuousMulHom_apply
    {n m : ℕ} (f : Fin m → Fin n) (x : Carrier n)
    (q : QuotientFundamentalGroup.LoopQuot (Carrier n) x) :
    coordinateProjectionQuotientContinuousMulHom f x q =
      _root_.Path.Homotopic.Quotient.map q (coordinateProjection f) :=
  rfl

/-- Arbitrary-basepoint coordinate maps compose contravariantly as continuous
monoid homomorphisms. -/
theorem coordinateProjectionQuotientContinuousMulHom_comp
    {n m k : ℕ} (f : Fin m → Fin n) (g : Fin k → Fin m)
    (x : Carrier n) :
    coordinateProjectionQuotientContinuousMulHom (f ∘ g) x =
      (coordinateProjectionQuotientContinuousMulHom g
        (coordinateProjection f x)).comp
        (coordinateProjectionQuotientContinuousMulHom f x) := by
  ext q
  change _root_.Path.Homotopic.Quotient.map q
      (coordinateProjection (f ∘ g)) =
    _root_.Path.Homotopic.Quotient.map
      (_root_.Path.Homotopic.Quotient.map q (coordinateProjection f))
      (coordinateProjection g)
  have hcomp := coordinateProjection_comp f g
  cases hcomp
  exact (QuotientFundamentalGroup.quotientMap_comp
    (coordinateProjection f) (coordinateProjection g) x q).symm

/-- The arbitrary-basepoint coordinate map for the identity index map is the
identity continuous monoid homomorphism. -/
theorem coordinateProjectionQuotientContinuousMulHom_id (n : ℕ)
    (x : Carrier n) :
    coordinateProjectionQuotientContinuousMulHom
        (id : Fin n → Fin n) x =
      ContinuousMonoidHom.id
        (QuotientFundamentalGroup.LoopQuot (Carrier n) x) := by
  ext q
  change _root_.Path.Homotopic.Quotient.map q
      (coordinateProjection (id : Fin n → Fin n)) = q
  have hid := coordinateProjection_id n
  cases hid
  exact QuotientFundamentalGroup.quotientMap_id x q

/-- Coordinate selection commutes with basepoint transport along every explicit
path from the canonical torus basepoint. -/
theorem coordinateProjectionQuotientContinuousMulHom_basepointChange
    {n m : ℕ} (f : Fin m → Fin n) (x : Carrier n)
    (p : _root_.Path (base n) x) (q : LoopQuot n) :
    coordinateProjectionQuotientContinuousMulHom f x
        (QuotientFundamentalGroup.basepointChangeContinuousMulEquiv p q) =
      QuotientFundamentalGroup.basepointChangeContinuousMulEquiv
        (p.map (coordinateProjection f).continuous)
        (coordinateProjectionQuotientContinuousMulHom f (base n) q) := by
  change _root_.Path.Homotopic.Quotient.map
      (QuotientFundamentalGroup.basepointChangeContinuousMulEquiv p q)
        (coordinateProjection f) =
    QuotientFundamentalGroup.basepointChangeContinuousMulEquiv
      (p.map (coordinateProjection f).continuous)
      (_root_.Path.Homotopic.Quotient.map q (coordinateProjection f))
  exact QuotientFundamentalGroup.basepointChange_quotientMap_naturality
    p (coordinateProjection f) q

/-- The arbitrary-basepoint classifier naturality theorem can be stated
directly through the induced continuous monoid homomorphism. -/
theorem loopQuotContinuousMulEquivIntVector_at_coordinateProjection_hom
    {n m : ℕ} (f : Fin m → Fin n) (x : Carrier n)
    (q : QuotientFundamentalGroup.LoopQuot (Carrier n) x) :
    (loopQuotContinuousMulEquivIntVector_at m
      (coordinateProjection f x))
        (coordinateProjectionQuotientContinuousMulHom f x q) =
      Multiplicative.ofAdd
        (coordinateReindex f
          (Multiplicative.toAdd
            (loopQuotContinuousMulEquivIntVector_at n x q))) := by
  simpa only [coordinateProjectionQuotientContinuousMulHom_apply] using
    (loopQuotContinuousMulEquivIntVector_at_coordinateProjection f x q)

/-- At arbitrary basepoints, the image of coordinate selection is exactly the
fiber-constant part of the target lattice under the canonical classifier. -/
theorem coordinateProjectionQuotientContinuousMulHom_mem_range_iff
    {n m : ℕ} (f : Fin m → Fin n) (x : Carrier n)
    (q : QuotientFundamentalGroup.LoopQuot
      (Carrier m) (coordinateProjection f x)) :
    q ∈ Set.range (coordinateProjectionQuotientContinuousMulHom f x) ↔
      ∀ ⦃j k : Fin m⦄, f j = f k →
        Multiplicative.toAdd
            ((loopQuotContinuousMulEquivIntVector_at m
              (coordinateProjection f x)) q) j =
          Multiplicative.toAdd
            ((loopQuotContinuousMulEquivIntVector_at m
              (coordinateProjection f x)) q) k := by
  let eₙ := loopQuotContinuousMulEquivIntVector_at n x
  let eₘ := loopQuotContinuousMulEquivIntVector_at m (coordinateProjection f x)
  constructor
  · rintro ⟨p, rfl⟩ j k h
    have hnat := loopQuotContinuousMulEquivIntVector_at_coordinateProjection_hom
      f x p
    have hvec :
        Multiplicative.toAdd (eₘ
            (coordinateProjectionQuotientContinuousMulHom f x p)) =
          coordinateReindex f (Multiplicative.toAdd (eₙ p)) := by
      rw [hnat]
      rfl
    rw [hvec]
    simp [coordinateReindex, h]
  · intro h
    have hrange :=
      (coordinateReindex_mem_range_iff f
        (Multiplicative.toAdd (eₘ q))).mpr h
    obtain ⟨z, hz⟩ := hrange
    refine ⟨eₙ.symm (Multiplicative.ofAdd z), ?_⟩
    apply eₘ.injective
    have hnat :=
      loopQuotContinuousMulEquivIntVector_at_coordinateProjection_hom
        f x (eₙ.symm (Multiplicative.ofAdd z))
    rw [hnat]
    apply Multiplicative.ext
    change coordinateReindex f
        (Multiplicative.toAdd (eₙ (eₙ.symm (Multiplicative.ofAdd z)))) =
      Multiplicative.toAdd (eₘ q)
    rw [eₙ.apply_symm_apply]
    exact hz

/-- The arbitrary-basepoint quotient homomorphism is injective exactly when
the index map is surjective. -/
theorem coordinateProjectionQuotientContinuousMulHom_injective_iff_surjective
    {n m : ℕ} (f : Fin m → Fin n) (x : Carrier n) :
    Function.Injective (coordinateProjectionQuotientContinuousMulHom f x) ↔
      Function.Surjective f := by
  let eₙ := loopQuotContinuousMulEquivIntVector_at n x
  let eₘ := loopQuotContinuousMulEquivIntVector_at m (coordinateProjection f x)
  constructor
  · intro hinj
    apply (coordinateReindex_injective_iff_surjective f).mp
    intro z w hzw
    let p := eₙ.symm (Multiplicative.ofAdd z)
    let q := eₙ.symm (Multiplicative.ofAdd w)
    have hmap :
        coordinateProjectionQuotientContinuousMulHom f x p =
          coordinateProjectionQuotientContinuousMulHom f x q := by
      apply eₘ.injective
      have hp :=
        loopQuotContinuousMulEquivIntVector_at_coordinateProjection_hom
          f x p
      have hq :=
        loopQuotContinuousMulEquivIntVector_at_coordinateProjection_hom
          f x q
      rw [hp, hq]
      apply Multiplicative.ext
      change coordinateReindex f (Multiplicative.toAdd (eₙ p)) =
        coordinateReindex f (Multiplicative.toAdd (eₙ q))
      simp [p, q, hzw]
    have hpq := hinj hmap
    have heq := congrArg (fun r => eₙ r) hpq
    have hvec := congrArg Multiplicative.toAdd heq
    simpa [p, q] using hvec
  · intro hf p q hmap
    apply eₙ.injective
    apply Multiplicative.ext
    apply coordinateReindex_injective_of_surjective f hf
    have hmap' := congrArg (fun r => eₘ r) hmap
    have hp :=
      loopQuotContinuousMulEquivIntVector_at_coordinateProjection_hom
        f x p
    have hq :=
      loopQuotContinuousMulEquivIntVector_at_coordinateProjection_hom
        f x q
    rw [hp, hq] at hmap'
    exact Multiplicative.ofAdd.injective hmap'

/-- The arbitrary-basepoint quotient homomorphism is surjective exactly when
the index map is injective. -/
theorem coordinateProjectionQuotientContinuousMulHom_surjective_iff_injective
    {n m : ℕ} (f : Fin m → Fin n) (x : Carrier n) :
    Function.Surjective (coordinateProjectionQuotientContinuousMulHom f x) ↔
      Function.Injective f := by
  let eₙ := loopQuotContinuousMulEquivIntVector_at n x
  let eₘ := loopQuotContinuousMulEquivIntVector_at m (coordinateProjection f x)
  constructor
  · intro hsurj
    apply (coordinateReindex_surjective_iff_injective f).mp
    intro w
    obtain ⟨q, hq⟩ := hsurj (eₘ.symm (Multiplicative.ofAdd w))
    have hq' := congrArg (fun r => eₘ r) hq
    have hnat :=
      loopQuotContinuousMulEquivIntVector_at_coordinateProjection_hom
        f x q
    rw [hnat] at hq'
    rw [eₘ.apply_symm_apply] at hq'
    refine ⟨Multiplicative.toAdd (eₙ q), ?_⟩
    exact Multiplicative.ofAdd.injective hq'
  · intro hf q
    obtain ⟨z, hz⟩ :=
      coordinateReindex_surjective_of_injective f hf
        (Multiplicative.toAdd (eₘ q))
    refine ⟨eₙ.symm (Multiplicative.ofAdd z), ?_⟩
    apply eₘ.injective
    have hnat :=
      loopQuotContinuousMulEquivIntVector_at_coordinateProjection_hom
        f x (eₙ.symm (Multiplicative.ofAdd z))
    rw [hnat]
    apply Multiplicative.ext
    change coordinateReindex f
        (Multiplicative.toAdd (eₙ (eₙ.symm (Multiplicative.ofAdd z)))) =
      Multiplicative.toAdd (eₘ q)
    rw [eₙ.apply_symm_apply]
    exact hz

/-- The kernel of an arbitrary-basepoint coordinate homomorphism is exactly
the set of classes whose canonical winding vector vanishes on the image of
the index map. -/
theorem coordinateProjectionQuotientContinuousMulHom_eq_one_iff
    {n m : ℕ} (f : Fin m → Fin n) (x : Carrier n)
    (q : QuotientFundamentalGroup.LoopQuot (Carrier n) x) :
    coordinateProjectionQuotientContinuousMulHom f x q = 1 ↔
      ∀ i ∈ Set.range f,
        Multiplicative.toAdd
            ((loopQuotContinuousMulEquivIntVector_at n x) q) i = 0 := by
  let eₙ := loopQuotContinuousMulEquivIntVector_at n x
  let eₘ := loopQuotContinuousMulEquivIntVector_at m (coordinateProjection f x)
  constructor
  · intro h i hi
    have hq := congrArg (fun r => eₘ r) h
    have hnat :=
      loopQuotContinuousMulEquivIntVector_at_coordinateProjection_hom
        f x q
    rw [hnat] at hq
    have h_one : eₘ (1 : QuotientFundamentalGroup.LoopQuot
        (Carrier m) (coordinateProjection f x)) = 1 := eₘ.map_one
    rw [h_one] at hq
    have hvec : coordinateReindex f (Multiplicative.toAdd (eₙ q)) = 0 := by
      simpa using hq
    exact (coordinateReindex_eq_zero_iff f
      (Multiplicative.toAdd (eₙ q))).mp hvec i hi
  · intro h
    apply eₘ.injective
    have hnat :=
      loopQuotContinuousMulEquivIntVector_at_coordinateProjection_hom
        f x q
    rw [hnat]
    have h_one : eₘ (1 : QuotientFundamentalGroup.LoopQuot
        (Carrier m) (coordinateProjection f x)) = 1 := eₘ.map_one
    rw [h_one]
    apply Multiplicative.ext
    change coordinateReindex f (Multiplicative.toAdd (eₙ q)) = 0
    exact (coordinateReindex_eq_zero_iff f
      (Multiplicative.toAdd (eₙ q))).mpr h

/-- Membership in the kernel of the arbitrary-basepoint coordinate
homomorphism has the same exact winding characterization. -/
theorem coordinateProjectionQuotientContinuousMulHom_mem_ker_iff
    {n m : ℕ} (f : Fin m → Fin n) (x : Carrier n)
    (q : QuotientFundamentalGroup.LoopQuot (Carrier n) x) :
    q ∈ (coordinateProjectionQuotientContinuousMulHom f x).ker ↔
      ∀ i ∈ Set.range f,
        Multiplicative.toAdd
            ((loopQuotContinuousMulEquivIntVector_at n x) q) i = 0 := by
  change coordinateProjectionQuotientContinuousMulHom f x q = 1 ↔ _
  exact coordinateProjectionQuotientContinuousMulHom_eq_one_iff f x q

/-! Integer matrices give a genuinely larger class of torus maps than
coordinate selections.  The rows of a matrix describe the target
coordinates, and the induced map on the winding lattice is ordinary matrix
multiplication over `ℤ`.  The endpoint cast in the quotient construction is
kept explicit because a matrix map sends the canonical zero basepoint to the
canonical zero basepoint only propositionally. -/

/-- The torus map associated to an integer matrix. -/
noncomputable def matrixMap {n m : ℕ} (A : Fin m → Fin n → ℤ) :
    C(Carrier n, Carrier m) :=
  ⟨fun x j => ∑ i : Fin n, A j i • x i,
    continuous_pi (fun j =>
      continuous_finsetSum Finset.univ (fun i _ =>
        (continuous_apply i).zsmul (A j i)))⟩

/-- The induced action of an integer matrix on winding vectors. -/
noncomputable def matrixAction {n m : ℕ} (A : Fin m → Fin n → ℤ) :
    (Fin n → ℤ) →+ (Fin m → ℤ) where
  toFun z j := ∑ i : Fin n, A j i * z i
  map_zero' := by
    ext j
    simp
  map_add' z w := by
    ext j
    simp [mul_add, Finset.sum_add_distrib]

/-- Matrix multiplication in the row-by-column convention used by
`matrixMap`. -/
def matrixCompose {n m k : ℕ}
    (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ) :
    Fin k → Fin n → ℤ :=
  fun l i => ∑ j : Fin m, B l j * A j i

/-- For square matrices, the determinant follows the row-by-column
`matrixCompose` convention (the standard product is `B * A`). -/
theorem matrixCompose_det {n : ℕ} (A B : Fin n → Fin n → ℤ) :
    Matrix.det (matrixCompose A B) = Matrix.det B * Matrix.det A := by
  let AM : Matrix (Fin n) (Fin n) ℤ := A
  let BM : Matrix (Fin n) (Fin n) ℤ := B
  have hmul : matrixCompose A B = BM * AM := by
    ext i j
    simp [matrixCompose, AM, BM, Matrix.mul_apply]
  rw [hmul]
  change Matrix.det (BM * AM) = Matrix.det BM * Matrix.det AM
  exact Matrix.det_mul BM AM

/-- The identity matrix in the same row-by-column convention. -/
def matrixIdentity (n : ℕ) : Fin n → Fin n → ℤ :=
  fun i j => if i = j then 1 else 0

/-- Matrix actions compose by ordinary integer matrix multiplication. -/
lemma matrixAction_comp {n m k : ℕ}
    (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ) (z : Fin n → ℤ) :
    matrixAction B (matrixAction A z) =
      matrixAction (matrixCompose A B) z := by
  ext l
  change (∑ i : Fin m, B l i * (∑ j : Fin n, A i j * z j)) =
    ∑ x : Fin n, (∑ j : Fin m, B l j * A j x) * z x
  rw [show (∑ i : Fin m, B l i * (∑ j : Fin n, A i j * z j)) =
      ∑ i : Fin m, ∑ j : Fin n, B l i * (A i j * z j) by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The matrix-action composition law as an equality of additive homomorphisms. -/
theorem matrixAction_comp_hom {n m k : ℕ}
    (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ) :
    matrixAction (matrixCompose A B) =
      (matrixAction B).comp (matrixAction A) := by
  apply AddMonoidHom.ext
  intro z
  exact (matrixAction_comp A B z).symm

/-- The image of a rectangular composite is independent of whether the
composition is written as an explicit homomorphism composition or as the
row-by-column `matrixCompose` operation. -/
theorem matrixAction_comp_range_eq_matrixCompose_range
    {n m k : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ) :
    ((matrixAction B).comp (matrixAction A)).range =
      (matrixAction (matrixCompose A B)).range := by
  rw [← matrixAction_comp_hom A B]

/-- The identity matrix acts as the identity on the winding lattice. -/
lemma matrixAction_id (n : ℕ) (z : Fin n → ℤ) :
    matrixAction (matrixIdentity n) z = z := by
  ext i
  simp [matrixAction, matrixIdentity]

/-- The identity-action law as an equality of additive homomorphisms. -/
theorem matrixAction_id_hom (n : ℕ) :
    matrixAction (matrixIdentity n) = AddMonoidHom.id (Fin n → ℤ) := by
  apply AddMonoidHom.ext
  intro z
  change matrixAction (matrixIdentity n) z = z
  exact matrixAction_id n z

/-! The cokernel argument is independent of matrices.  We first package it
for arbitrary composable additive homomorphisms; the rectangular matrix and
finite-torus statements below then become direct specializations. -/

/-- The map on additive cokernels induced by the second map in a composable
pair of additive homomorphisms. -/
noncomputable def addCokernelCompMap
    {U V W : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    (f : U →+ V) (g : V →+ W) :
    V ⧸ f.range →+ W ⧸ (g.comp f).range := by
  let N : AddSubgroup V := f.range
  let M : AddSubgroup W := (g.comp f).range
  have hNM : N ≤ AddSubgroup.comap g M := by
    intro z hz
    rw [AddSubgroup.mem_comap]
    rcases (AddMonoidHom.mem_range).mp hz with ⟨w, hw⟩
    rw [AddMonoidHom.mem_range]
    refine ⟨w, ?_⟩
    rw [← hw]
    rfl
  exact QuotientAddGroup.map N M g hNM

/-- Representative formula for the induced map on additive cokernels. -/
@[simp] theorem addCokernelCompMap_apply_mk
    {U V W : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    (f : U →+ V) (g : V →+ W) (v : V) :
    addCokernelCompMap f g (QuotientAddGroup.mk' f.range v) =
      QuotientAddGroup.mk' (g.comp f).range (g v) := by
  rfl

/-- The canonical projection from the cokernel of a composite onto the
cokernel of its second map. -/
noncomputable def addCokernelCompProjection
    {U V W : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    (f : U →+ V) (g : V →+ W) :
    W ⧸ (g.comp f).range →+ W ⧸ g.range := by
  let N : AddSubgroup W := (g.comp f).range
  let M : AddSubgroup W := g.range
  have hNM : N ≤ AddSubgroup.comap (AddMonoidHom.id W) M := by
    intro z hz
    rw [AddSubgroup.mem_comap]
    rcases (AddMonoidHom.mem_range).mp hz with ⟨w, hw⟩
    rw [AddMonoidHom.mem_range]
    refine ⟨f w, ?_⟩
    simpa only [AddMonoidHom.id_apply, AddMonoidHom.comp_apply] using hw
  exact QuotientAddGroup.map N M (AddMonoidHom.id W) hNM

/-- Representative formula for the canonical projection on additive
cokernels. -/
@[simp] theorem addCokernelCompProjection_apply_mk
    {U V W : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    (f : U →+ V) (g : V →+ W) (w : W) :
    addCokernelCompProjection f g
        (QuotientAddGroup.mk' (g.comp f).range w) =
      QuotientAddGroup.mk' g.range w := by
  rfl

/-- The cokernel projection of a composite is always surjective. -/
theorem addCokernelCompProjection_surjective
    {U V W : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    (f : U →+ V) (g : V →+ W) :
    Function.Surjective (addCokernelCompProjection f g) := by
  let N : AddSubgroup W := (g.comp f).range
  let M : AddSubgroup W := g.range
  have hNM : N ≤ AddSubgroup.comap (AddMonoidHom.id W) M := by
    intro z hz
    rw [AddSubgroup.mem_comap]
    rcases (AddMonoidHom.mem_range).mp hz with ⟨w, hw⟩
    rw [AddMonoidHom.mem_range]
    refine ⟨f w, ?_⟩
    simpa only [AddMonoidHom.id_apply, AddMonoidHom.comp_apply] using hw
  intro y
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective M y
  refine ⟨(QuotientAddGroup.mk' N) v, ?_⟩
  change (QuotientAddGroup.map N M (AddMonoidHom.id W) hNM)
      ((QuotientAddGroup.mk' N) v) = (QuotientAddGroup.mk' M) v
  rw [QuotientAddGroup.map_mk' N M (AddMonoidHom.id W) hNM v]
  rfl

/-- If the second homomorphism is injective, the induced map on cokernels is
injective. -/
theorem addCokernelCompMap_injective_of_injective
    {U V W : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    (f : U →+ V) (g : V →+ W)
    (hg : Function.Injective g) :
    Function.Injective (addCokernelCompMap f g) := by
  let N : AddSubgroup V := f.range
  let M : AddSubgroup W := (g.comp f).range
  have hNM : N ≤ AddSubgroup.comap g M := by
    intro z hz
    rw [AddSubgroup.mem_comap]
    rcases (AddMonoidHom.mem_range).mp hz with ⟨w, hw⟩
    rw [AddMonoidHom.mem_range]
    refine ⟨w, ?_⟩
    rw [← hw]
    rfl
  intro x y hxy
  obtain ⟨x', rfl⟩ := QuotientAddGroup.mk'_surjective N x
  obtain ⟨y', rfl⟩ := QuotientAddGroup.mk'_surjective N y
  change (QuotientAddGroup.map N M g hNM)
      ((QuotientAddGroup.mk' N) x') =
    (QuotientAddGroup.map N M g hNM)
      ((QuotientAddGroup.mk' N) y') at hxy
  rw [QuotientAddGroup.map_mk' N M g hNM x',
    QuotientAddGroup.map_mk' N M g hNM y'] at hxy
  change (x' : V ⧸ N) = (y' : V ⧸ N)
  rw [QuotientAddGroup.eq_iff_sub_mem] at hxy ⊢
  rcases hxy with ⟨z, hz⟩
  rw [AddMonoidHom.mem_range]
  refine ⟨z, ?_⟩
  have hzero : g (x' - y' - f z) = 0 := by
    rw [map_sub, map_sub]
    change g (f z) = g x' - g y' at hz
    rw [hz]
    simp
  have hEq : x' - y' - f z = 0 := by
    apply hg
    simpa using hzero
  have hrel : x' - y' = f z := by
    exact sub_eq_zero.mp hEq
  rw [hrel]

/-- The induced map on cokernels is injective exactly when the second map
creates no additional relations beyond the first map's image. -/
theorem addCokernelCompMap_injective_iff
    {U V W : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    (f : U →+ V) (g : V →+ W) :
    Function.Injective (addCokernelCompMap f g) ↔
      AddSubgroup.comap g (g.comp f).range = f.range := by
  let N : AddSubgroup V := f.range
  let M : AddSubgroup W := (g.comp f).range
  have hNM : N ≤ AddSubgroup.comap g M := by
    intro z hz
    rw [AddSubgroup.mem_comap]
    rcases (AddMonoidHom.mem_range).mp hz with ⟨w, hw⟩
    rw [AddMonoidHom.mem_range]
    refine ⟨w, ?_⟩
    rw [← hw]
    rfl
  constructor
  · intro hinj
    change AddSubgroup.comap g M = N
    apply le_antisymm
    · intro v hv
      rw [AddSubgroup.mem_comap] at hv
      have hq :
          (addCokernelCompMap f g) (QuotientAddGroup.mk' N v) =
            (addCokernelCompMap f g) (QuotientAddGroup.mk' N (0 : V)) := by
        change (QuotientAddGroup.map N M g hNM)
            ((QuotientAddGroup.mk' N) v) =
          (QuotientAddGroup.map N M g hNM)
            ((QuotientAddGroup.mk' N) (0 : V))
        rw [QuotientAddGroup.map_mk' N M g hNM v,
          QuotientAddGroup.map_mk' N M g hNM (0 : V)]
        change ((g v : W) : W ⧸ M) = ((g (0 : V) : W) : W ⧸ M)
        rw [QuotientAddGroup.eq_iff_sub_mem]
        simpa only [map_zero, sub_zero] using hv
      have hq0 := hinj hq
      change ((v : V) : V ⧸ N) = (((0 : V) : V) : V ⧸ N) at hq0
      have hvN := (QuotientAddGroup.eq_iff_sub_mem).mp hq0
      simpa only [sub_zero] using hvN
    · exact hNM
  · intro hN
    intro x y hxy
    obtain ⟨x', rfl⟩ := QuotientAddGroup.mk'_surjective N x
    obtain ⟨y', rfl⟩ := QuotientAddGroup.mk'_surjective N y
    change (QuotientAddGroup.map N M g hNM)
        ((QuotientAddGroup.mk' N) x') =
      (QuotientAddGroup.map N M g hNM)
        ((QuotientAddGroup.mk' N) y') at hxy
    rw [QuotientAddGroup.map_mk' N M g hNM x',
      QuotientAddGroup.map_mk' N M g hNM y'] at hxy
    change ((g x' : W) : W ⧸ M) = ((g y' : W) : W ⧸ M) at hxy
    rw [QuotientAddGroup.eq_iff_sub_mem] at hxy
    change ((x' : V) : V ⧸ N) = ((y' : V) : V ⧸ N)
    rw [QuotientAddGroup.eq_iff_sub_mem]
    change x' - y' ∈ f.range
    rw [← hN]
    rw [AddSubgroup.mem_comap]
    simpa only [map_sub] using hxy

/-- The kernel of the cokernel projection is exactly the range of the
induced composite map, with no injectivity hypothesis. -/
theorem addCokernelCompProjection_ker_eq_range
    {U V W : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    (f : U →+ V) (g : V →+ W) :
    (addCokernelCompProjection f g).ker =
      (addCokernelCompMap f g).range := by
  let N₀ : AddSubgroup V := f.range
  let N : AddSubgroup W := (g.comp f).range
  let M : AddSubgroup W := g.range
  have hNM : N₀ ≤ AddSubgroup.comap g N := by
    intro z hz
    rw [AddSubgroup.mem_comap]
    rcases (AddMonoidHom.mem_range).mp hz with ⟨w, hw⟩
    rw [AddMonoidHom.mem_range]
    refine ⟨w, ?_⟩
    rw [← hw]
    rfl
  have hNP : N ≤ AddSubgroup.comap (AddMonoidHom.id W) M := by
    intro z hz
    rw [AddSubgroup.mem_comap]
    rcases (AddMonoidHom.mem_range).mp hz with ⟨w, hw⟩
    rw [AddMonoidHom.mem_range]
    refine ⟨f w, ?_⟩
    simpa only [AddMonoidHom.id_apply, AddMonoidHom.comp_apply] using hw
  have hcomp :
      (addCokernelCompProjection f g).comp
          (addCokernelCompMap f g) = 0 := by
    apply AddMonoidHom.ext
    intro q
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective N₀ q
    change (QuotientAddGroup.map N M (AddMonoidHom.id W) hNP)
        ((QuotientAddGroup.map N₀ N g hNM)
          ((QuotientAddGroup.mk' N₀) z)) = 0
    rw [QuotientAddGroup.map_mk' N₀ N g hNM z]
    change (QuotientAddGroup.map N M (AddMonoidHom.id W) hNP)
      ((QuotientAddGroup.mk' N) (g z)) = 0
    rw [QuotientAddGroup.map_mk' N M (AddMonoidHom.id W) hNP]
    change (QuotientAddGroup.mk' M) (g z) = 0
    change ((g z : W) : W ⧸ M) = ((0 : W) : W ⧸ M)
    rw [QuotientAddGroup.eq_iff_sub_mem]
    simp only [sub_zero]
    exact (AddMonoidHom.mem_range).mpr ⟨z, rfl⟩
  ext q
  constructor
  · intro hq
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective N q
    change (QuotientAddGroup.map N M (AddMonoidHom.id W) hNP)
        ((QuotientAddGroup.mk' N) x) = 0 at hq
    rw [QuotientAddGroup.map_mk' N M (AddMonoidHom.id W) hNP] at hq
    change (x : W ⧸ M) = 0 at hq
    have hx : x ∈ M := by
      have := (QuotientAddGroup.eq_iff_sub_mem).mp hq
      simpa only [sub_zero] using this
    rcases (AddMonoidHom.mem_range).mp hx with ⟨z, hz⟩
    refine ⟨(QuotientAddGroup.mk' N₀) z, ?_⟩
    change (QuotientAddGroup.map N₀ N g hNM)
        ((QuotientAddGroup.mk' N₀) z) = (QuotientAddGroup.mk' N) x
    rw [QuotientAddGroup.map_mk' N₀ N g hNM z]
    exact congrArg (QuotientAddGroup.mk' N) hz
  · intro hq
    rcases hq with ⟨qA, rfl⟩
    change (addCokernelCompProjection f g)
        ((addCokernelCompMap f g) qA) = 0
    have hcomp_q := congrArg
      (fun F : (V ⧸ N₀) →+ (W ⧸ M) => F qA) hcomp
    simpa only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply] using hcomp_q

/-- The first-isomorphism equivalence associated with the cokernel
projection. -/
noncomputable def addCokernelCompProjection_quotientKerEquiv
    {U V W : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    (f : U →+ V) (g : V →+ W) :
    (W ⧸ (g.comp f).range) ⧸ (addCokernelCompProjection f g).ker ≃+
      W ⧸ g.range :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    (addCokernelCompProjection f g)
    (addCokernelCompProjection_surjective f g)

@[simp] theorem addCokernelCompProjection_quotientKerEquiv_apply_mk
    {U V W : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    (f : U →+ V) (g : V →+ W)
    (q : W ⧸ (g.comp f).range) :
    addCokernelCompProjection_quotientKerEquiv f g
        (QuotientAddGroup.mk'
          (addCokernelCompProjection f g).ker q) =
      addCokernelCompProjection f g q := by
  exact QuotientAddGroup.kerLift_mk
    (addCokernelCompProjection f g) q

/-- The additive cokernel sequence is short exact whenever the second map is
injective. -/
theorem addCokernelComp_shortExact_of_injective
    {U V W : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    (f : U →+ V) (g : V →+ W) (hg : Function.Injective g) :
    Function.Injective (addCokernelCompMap f g) ∧
      (addCokernelCompProjection f g).ker =
        (addCokernelCompMap f g).range ∧
      Function.Surjective (addCokernelCompProjection f g) :=
  ⟨addCokernelCompMap_injective_of_injective f g hg,
    addCokernelCompProjection_ker_eq_range f g,
    addCokernelCompProjection_surjective f g⟩

/-- Rectangular integer matrices inherit the additive cokernel sequence for
any composable dimensions.  The only hypothesis is injectivity of the second
matrix action; no square determinant is needed. -/
theorem matrixAction_rectangular_cokernel_shortExact_of_injective
    {n m k : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ)
    (hB : Function.Injective (matrixAction B)) :
    ∃ f : (Fin m → ℤ) ⧸ (matrixAction A).range →+
          (Fin k → ℤ) ⧸ ((matrixAction B).comp (matrixAction A)).range,
    ∃ g : (Fin k → ℤ) ⧸ ((matrixAction B).comp (matrixAction A)).range →+
          (Fin k → ℤ) ⧸ (matrixAction B).range,
    ∃ e : (((Fin k → ℤ) ⧸
          ((matrixAction B).comp (matrixAction A)).range) ⧸ g.ker) ≃+
          (Fin k → ℤ) ⧸ (matrixAction B).range,
      Function.Injective f ∧ g.ker = f.range ∧ Function.Surjective g := by
  refine ⟨addCokernelCompMap (matrixAction A) (matrixAction B),
    addCokernelCompProjection (matrixAction A) (matrixAction B),
    addCokernelCompProjection_quotientKerEquiv
      (matrixAction A) (matrixAction B), ?_⟩
  exact addCokernelComp_shortExact_of_injective
    (matrixAction A) (matrixAction B) hB

/-- The rectangular exact sequence can be consumed directly through the
matrix-composition notation, without exposing the underlying homomorphism
composition in the target cokernel. -/
theorem matrixAction_rectangular_cokernel_shortExact_of_matrixCompose_injective
    {n m k : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ)
    (hB : Function.Injective (matrixAction B)) :
    ∃ f : (Fin m → ℤ) ⧸ (matrixAction A).range →+
          (Fin k → ℤ) ⧸ (matrixAction (matrixCompose A B)).range,
    ∃ g : (Fin k → ℤ) ⧸ (matrixAction (matrixCompose A B)).range →+
          (Fin k → ℤ) ⧸ (matrixAction B).range,
    ∃ e : (((Fin k → ℤ) ⧸
          (matrixAction (matrixCompose A B)).range) ⧸ g.ker) ≃+
          (Fin k → ℤ) ⧸ (matrixAction B).range,
      Function.Injective f ∧ g.ker = f.range ∧ Function.Surjective g := by
  rw [← matrixAction_comp_range_eq_matrixCompose_range A B]
  exact matrixAction_rectangular_cokernel_shortExact_of_injective A B hB

/-- The rectangular matrix cokernel embedding has the exact preimage-of-image
criterion inherited from the abstract additive construction. -/
theorem matrixAction_rectangular_cokernel_compMap_injective_iff
    {n m k : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ) :
    Function.Injective
        (addCokernelCompMap (matrixAction A) (matrixAction B)) ↔
      AddSubgroup.comap (matrixAction B)
          ((matrixAction B).comp (matrixAction A)).range =
        (matrixAction A).range := by
  exact addCokernelCompMap_injective_iff
    (matrixAction A) (matrixAction B)

/-- The exact preimage-of-image criterion also has a canonical matrix-compose
presentation. -/
theorem matrixAction_rectangular_cokernel_compMap_injective_iff_matrixCompose
    {n m k : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ) :
    Function.Injective
        (addCokernelCompMap (matrixAction A) (matrixAction B)) ↔
      AddSubgroup.comap (matrixAction B)
          (matrixAction (matrixCompose A B)).range =
        (matrixAction A).range := by
  rw [← matrixAction_comp_range_eq_matrixCompose_range A B]
  exact matrixAction_rectangular_cokernel_compMap_injective_iff A B

/-! For square matrices, the winding-lattice action has a sharp determinant
criterion.  Injectivity only asks for a nonzero determinant, whereas
surjectivity over `ℤ` is equivalent to unimodularity of that determinant. -/

/-- A square integer matrix acts injectively on the winding lattice exactly
when its determinant is nonzero. -/
theorem matrixAction_injective_iff_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℤ) :
    Function.Injective (matrixAction A) ↔ Matrix.det A ≠ 0 := by
  change Function.Injective (Matrix.mulVec A) ↔ Matrix.det A ≠ 0
  constructor
  · intro hinj hdet
    obtain ⟨v, hv, hz⟩ :=
      (Matrix.exists_mulVec_eq_zero_iff (M := A)).mpr hdet
    have hEq : Matrix.mulVec A v = Matrix.mulVec A 0 := by
      simpa using hz
    have hv0 := hinj hEq
    exact hv (by simpa using hv0)
  · intro hdet v w hvw
    have hz : Matrix.mulVec A (v - w) = 0 := by
      rw [Matrix.mulVec_sub, hvw]
      simp
    have hzero := Matrix.eq_zero_of_mulVec_eq_zero hdet hz
    exact sub_eq_zero.mp hzero

/-- A square integer matrix acts surjectively on the winding lattice exactly
when its determinant is a unit in `ℤ` (equivalently, `±1`). -/
theorem matrixAction_surjective_iff_isUnit_det {n : ℕ}
    (A : Fin n → Fin n → ℤ) :
    Function.Surjective (matrixAction A) ↔ IsUnit (Matrix.det A) := by
  change Function.Surjective (Matrix.mulVec A) ↔ IsUnit (Matrix.det A)
  rw [← Matrix.isUnit_iff_isUnit_det]
  exact Matrix.mulVec_surjective_iff_isUnit (m := Fin n) (R := ℤ)

/-- If a square integer matrix has nonzero determinant, its winding-lattice
cokernel is finite and has cardinality `natAbs (det A)`. -/
theorem matrixAction_cokernel_card_eq_natAbs_det {n : ℕ}
    (A : Fin n → Fin n → ℤ) (hA : Matrix.det A ≠ 0) :
    Nat.card ((Fin n → ℤ) ⧸ ((matrixAction A).range.toIntSubmodule)) =
      Int.natAbs (Matrix.det A) := by
  let f := matrixAction A
  have hf : Function.Injective f :=
    (matrixAction_injective_iff_det_ne_zero A).mpr hA
  let r : (Fin n → ℤ) ≃+ f.range := AddMonoidHom.ofInjective hf
  let s : f.range ≃+ f.range.toIntSubmodule :=
    { toFun := fun z =>
        ⟨z.1, by
          change z.1 ∈ (f.range : Set (Fin n → ℤ))
          exact z.2⟩
      invFun := fun y =>
        ⟨y.1, by
          change y.1 ∈ (f.range : Set (Fin n → ℤ))
          exact y.2⟩
      left_inv := by
        intro z
        apply Subtype.ext
        rfl
      right_inv := by
        intro y
        apply Subtype.ext
        rfl
      map_add' := by
        intro z w
        apply Subtype.ext
        rfl }
  let e : (Fin n → ℤ) ≃+ f.range.toIntSubmodule := r.trans s
  have hcard := Submodule.natAbs_det_equiv f.range.toIntSubmodule e
  have hlin :
      (f.range.toIntSubmodule).subtype ∘ₗ
        (e : (Fin n → ℤ) →+ f.range.toIntSubmodule).toIntLinearMap =
        Matrix.toLin' A := by
    ext z j
    rfl
  rw [hlin, LinearMap.det_toLin'] at hcard
  simpa [f] using hcard.symm

/-- The exact finite index is multiplicative under composition of
non-singular square matrix actions. -/
theorem matrixAction_cokernel_card_comp {n : ℕ}
    (A B : Fin n → Fin n → ℤ)
    (hA : Matrix.det A ≠ 0) (hB : Matrix.det B ≠ 0) :
    Nat.card ((Fin n → ℤ) ⧸
        ((matrixAction (matrixCompose A B)).range.toIntSubmodule)) =
      Int.natAbs (Matrix.det A) * Int.natAbs (Matrix.det B) := by
  rw [matrixAction_cokernel_card_eq_natAbs_det (matrixCompose A B)]
  · rw [matrixCompose_det, Int.natAbs_mul]
    exact Nat.mul_comm _ _
  · rw [matrixCompose_det]
    exact mul_ne_zero hB hA

/-- Composition induces the canonical additive map from the cokernel of `A`
to the cokernel of `B ∘ A`.  The target uses the same row-by-column
`matrixCompose` convention as the torus maps. -/
noncomputable def matrixAction_cokernel_compMap {n : ℕ}
    (A B : Fin n → Fin n → ℤ) :
    (Fin n → ℤ) ⧸ (matrixAction A).range →+
      (Fin n → ℤ) ⧸ (matrixAction (matrixCompose A B)).range := by
  let N : AddSubgroup (Fin n → ℤ) := (matrixAction A).range
  let M : AddSubgroup (Fin n → ℤ) :=
    (matrixAction (matrixCompose A B)).range
  have hNM : N ≤ AddSubgroup.comap (matrixAction B) M := by
    intro z hz
    rw [AddSubgroup.mem_comap]
    rcases (AddMonoidHom.mem_range).mp hz with ⟨w, hw⟩
    rw [AddMonoidHom.mem_range]
    refine ⟨w, ?_⟩
    rw [← hw]
    exact congrArg (fun F : (Fin n → ℤ) →+ (Fin n → ℤ) => F w)
      (matrixAction_comp_hom A B)
  exact QuotientAddGroup.map N M (matrixAction B) hNM

/-- If `B` has nonzero determinant, the composition map on additive
cokernels is injective.  This is the algebraic embedding behind the
multiplicative determinant-index law. -/
theorem matrixAction_cokernel_compMap_injective_of_det_ne_zero
    {n : ℕ} (A B : Fin n → Fin n → ℤ) (hB : Matrix.det B ≠ 0) :
    Function.Injective (matrixAction_cokernel_compMap A B) := by
  let N : AddSubgroup (Fin n → ℤ) := (matrixAction A).range
  let M : AddSubgroup (Fin n → ℤ) :=
    (matrixAction (matrixCompose A B)).range
  have hNM : N ≤ AddSubgroup.comap (matrixAction B) M := by
    intro z hz
    rw [AddSubgroup.mem_comap]
    rcases (AddMonoidHom.mem_range).mp hz with ⟨w, hw⟩
    rw [AddMonoidHom.mem_range]
    refine ⟨w, ?_⟩
    rw [← hw]
    exact congrArg (fun F : (Fin n → ℤ) →+ (Fin n → ℤ) => F w)
      (matrixAction_comp_hom A B)
  intro x y hxy
  obtain ⟨x', rfl⟩ := QuotientAddGroup.mk'_surjective N x
  obtain ⟨y', rfl⟩ := QuotientAddGroup.mk'_surjective N y
  change (QuotientAddGroup.map N M (matrixAction B) hNM)
      ((QuotientAddGroup.mk' N) x') =
    (QuotientAddGroup.map N M (matrixAction B) hNM)
      ((QuotientAddGroup.mk' N) y') at hxy
  rw [QuotientAddGroup.map_mk' N M (matrixAction B) hNM x',
    QuotientAddGroup.map_mk' N M (matrixAction B) hNM y'] at hxy
  change (x' : (Fin n → ℤ) ⧸ N) = (y' : (Fin n → ℤ) ⧸ N)
  rw [QuotientAddGroup.eq_iff_sub_mem] at hxy ⊢
  rcases hxy with ⟨z, hz⟩
  rw [AddMonoidHom.mem_range]
  refine ⟨z, ?_⟩
  have hB_inj : Function.Injective (matrixAction B) :=
    (matrixAction_injective_iff_det_ne_zero B).mpr hB
  have hzero : matrixAction B (x' - y' - matrixAction A z) = 0 := by
    rw [map_sub, map_sub]
    rw [matrixAction_comp A B z, hz]
    simp
  have hEq : x' - y' - matrixAction A z = 0 := by
    apply hB_inj
    simpa using hzero
  have hrel : x' - y' = matrixAction A z := by
    exact sub_eq_zero.mp hEq
  rw [hrel]

/-- The composition cokernel map onto the cokernel of `B` is induced by the
identity on the winding lattice. -/
noncomputable def matrixAction_cokernel_compProjection {n : ℕ}
    (A B : Fin n → Fin n → ℤ) :
    (Fin n → ℤ) ⧸ (matrixAction (matrixCompose A B)).range →+
      (Fin n → ℤ) ⧸ (matrixAction B).range := by
  let N : AddSubgroup (Fin n → ℤ) :=
    (matrixAction (matrixCompose A B)).range
  let M : AddSubgroup (Fin n → ℤ) := (matrixAction B).range
  have hNM : N ≤ AddSubgroup.comap (AddMonoidHom.id (Fin n → ℤ)) M := by
    intro z hz
    rw [AddSubgroup.mem_comap]
    rcases (AddMonoidHom.mem_range).mp hz with ⟨w, hw⟩
    rw [AddMonoidHom.mem_range]
    refine ⟨matrixAction A w, ?_⟩
    have hcomp : matrixAction (matrixCompose A B) w =
        matrixAction B (matrixAction A w) :=
      (matrixAction_comp A B w).symm
    simpa only [AddMonoidHom.id_apply] using hcomp.symm.trans hw
  exact QuotientAddGroup.map N M (AddMonoidHom.id (Fin n → ℤ)) hNM

/-- The projection from the cokernel of `B ∘ A` to the cokernel of `B` is
surjective. -/
theorem matrixAction_cokernel_compProjection_surjective {n : ℕ}
    (A B : Fin n → Fin n → ℤ) :
    Function.Surjective (matrixAction_cokernel_compProjection A B) := by
  let N : AddSubgroup (Fin n → ℤ) :=
    (matrixAction (matrixCompose A B)).range
  let M : AddSubgroup (Fin n → ℤ) := (matrixAction B).range
  have hNM : N ≤ AddSubgroup.comap (AddMonoidHom.id (Fin n → ℤ)) M := by
    intro z hz
    rw [AddSubgroup.mem_comap]
    rcases (AddMonoidHom.mem_range).mp hz with ⟨w, hw⟩
    rw [AddMonoidHom.mem_range]
    refine ⟨matrixAction A w, ?_⟩
    have hcomp : matrixAction (matrixCompose A B) w =
        matrixAction B (matrixAction A w) :=
      (matrixAction_comp A B w).symm
    simpa only [AddMonoidHom.id_apply] using hcomp.symm.trans hw
  intro y
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective M y
  refine ⟨(QuotientAddGroup.mk' N) v, ?_⟩
  change (QuotientAddGroup.map N M (AddMonoidHom.id (Fin n → ℤ)) hNM)
      ((QuotientAddGroup.mk' N) v) = (QuotientAddGroup.mk' M) v
  rw [QuotientAddGroup.map_mk' N M (AddMonoidHom.id (Fin n → ℤ)) hNM v]
  rfl

/-- The kernel of the projection onto the cokernel of `B` is exactly the
image of the composition map from the cokernel of `A`. -/
theorem matrixAction_cokernel_compProjection_ker_eq_range {n : ℕ}
    (A B : Fin n → Fin n → ℤ) :
    (matrixAction_cokernel_compProjection A B).ker =
      (matrixAction_cokernel_compMap A B).range := by
  let NA : AddSubgroup (Fin n → ℤ) := (matrixAction A).range
  let N : AddSubgroup (Fin n → ℤ) :=
    (matrixAction (matrixCompose A B)).range
  let M : AddSubgroup (Fin n → ℤ) := (matrixAction B).range
  have hNM : NA ≤ AddSubgroup.comap (matrixAction B) N := by
    intro z hz
    rw [AddSubgroup.mem_comap]
    rcases (AddMonoidHom.mem_range).mp hz with ⟨w, hw⟩
    rw [AddMonoidHom.mem_range]
    refine ⟨w, ?_⟩
    rw [← hw]
    exact congrArg (fun F : (Fin n → ℤ) →+ (Fin n → ℤ) => F w)
      (matrixAction_comp_hom A B)
  have hNP : N ≤ AddSubgroup.comap (AddMonoidHom.id (Fin n → ℤ)) M := by
    intro z hz
    rw [AddSubgroup.mem_comap]
    rcases (AddMonoidHom.mem_range).mp hz with ⟨w, hw⟩
    rw [AddMonoidHom.mem_range]
    refine ⟨matrixAction A w, ?_⟩
    have hcomp : matrixAction (matrixCompose A B) w =
        matrixAction B (matrixAction A w) :=
      (matrixAction_comp A B w).symm
    simpa only [AddMonoidHom.id_apply] using hcomp.symm.trans hw
  have hcomp :
      (matrixAction_cokernel_compProjection A B).comp
          (matrixAction_cokernel_compMap A B) = 0 := by
    apply AddMonoidHom.ext
    intro q
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective NA q
    change (QuotientAddGroup.map N M (AddMonoidHom.id (Fin n → ℤ)) hNP)
        ((QuotientAddGroup.map NA N (matrixAction B) hNM)
          ((QuotientAddGroup.mk' NA) z)) = 0
    rw [QuotientAddGroup.map_mk' NA N (matrixAction B) hNM z]
    change (QuotientAddGroup.map N M (AddMonoidHom.id (Fin n → ℤ)) hNP)
      ((QuotientAddGroup.mk' N) (matrixAction B z)) = 0
    rw [QuotientAddGroup.map_mk' N M (AddMonoidHom.id (Fin n → ℤ)) hNP]
    change (QuotientAddGroup.mk' M) (matrixAction B z) = 0
    change ((matrixAction B z : (Fin n → ℤ)) :
      (Fin n → ℤ) ⧸ M) = ((0 : (Fin n → ℤ)) : (Fin n → ℤ) ⧸ M)
    rw [QuotientAddGroup.eq_iff_sub_mem]
    simp only [sub_zero]
    exact (AddMonoidHom.mem_range).mpr ⟨z, rfl⟩
  ext q
  constructor
  · intro hq
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective N q
    change (QuotientAddGroup.map N M (AddMonoidHom.id (Fin n → ℤ)) hNP)
        ((QuotientAddGroup.mk' N) x) = 0 at hq
    rw [QuotientAddGroup.map_mk' N M (AddMonoidHom.id (Fin n → ℤ)) hNP] at hq
    change (x : (Fin n → ℤ) ⧸ M) = 0 at hq
    have hx : x ∈ M := by
      have := (QuotientAddGroup.eq_iff_sub_mem).mp hq
      simpa only [sub_zero] using this
    rcases (AddMonoidHom.mem_range).mp hx with ⟨z, hz⟩
    refine ⟨(QuotientAddGroup.mk' NA) z, ?_⟩
    change (QuotientAddGroup.map NA N (matrixAction B) hNM)
        ((QuotientAddGroup.mk' NA) z) = (QuotientAddGroup.mk' N) x
    rw [QuotientAddGroup.map_mk' NA N (matrixAction B) hNM z]
    exact congrArg (QuotientAddGroup.mk' N) hz
  · intro hq
    rcases hq with ⟨qA, rfl⟩
    change (matrixAction_cokernel_compProjection A B)
        ((matrixAction_cokernel_compMap A B) qA) = 0
    have hcomp_q := congrArg
      (fun F : ((Fin n → ℤ) ⧸ NA) →+ ((Fin n → ℤ) ⧸ M) => F qA) hcomp
    simpa only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply] using hcomp_q

/-- The lattice cokernels of a composable pair form a short exact sequence:
the composition embedding is injective when `det B ≠ 0`, its image is the
projection kernel, and the projection is surjective. -/
theorem matrixAction_cokernel_comp_shortExact_of_det_ne_zero
    {n : ℕ} (A B : Fin n → Fin n → ℤ) (hB : Matrix.det B ≠ 0) :
    Function.Injective (matrixAction_cokernel_compMap A B) ∧
      (matrixAction_cokernel_compProjection A B).ker =
        (matrixAction_cokernel_compMap A B).range ∧
      Function.Surjective (matrixAction_cokernel_compProjection A B) :=
  ⟨matrixAction_cokernel_compMap_injective_of_det_ne_zero A B hB,
    matrixAction_cokernel_compProjection_ker_eq_range A B,
    matrixAction_cokernel_compProjection_surjective A B⟩

/-- The first-isomorphism quotient of the composition cokernel sequence is
canonically the cokernel of `B`.  This packages the projection quotient as an
explicit additive equivalence, rather than only recording its kernel and
surjectivity separately. -/
noncomputable def matrixAction_cokernel_compProjection_quotientKerEquiv
    {n : ℕ} (A B : Fin n → Fin n → ℤ) :
    ((Fin n → ℤ) ⧸ (matrixAction (matrixCompose A B)).range) ⧸
        (matrixAction_cokernel_compProjection A B).ker ≃+
      (Fin n → ℤ) ⧸ (matrixAction B).range :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    (matrixAction_cokernel_compProjection A B)
    (matrixAction_cokernel_compProjection_surjective A B)

@[simp] theorem matrixAction_cokernel_compProjection_quotientKerEquiv_apply_mk
    {n : ℕ} (A B : Fin n → Fin n → ℤ)
    (q : (Fin n → ℤ) ⧸ (matrixAction (matrixCompose A B)).range) :
    matrixAction_cokernel_compProjection_quotientKerEquiv A B
        (QuotientAddGroup.mk'
          (matrixAction_cokernel_compProjection A B).ker q) =
      matrixAction_cokernel_compProjection A B q := by
  exact QuotientAddGroup.kerLift_mk
    (matrixAction_cokernel_compProjection A B) q

/-- A nonzero determinant makes the winding-lattice cokernel finite. -/
theorem matrixAction_cokernel_finite {n : ℕ}
    (A : Fin n → Fin n → ℤ) (hA : Matrix.det A ≠ 0) :
    Finite ((Fin n → ℤ) ⧸ ((matrixAction A).range.toIntSubmodule)) := by
  apply Nat.finite_of_card_ne_zero
  rw [matrixAction_cokernel_card_eq_natAbs_det A hA]
  exact Int.natAbs_ne_zero.mpr hA

/-- A non-singular winding action has a full-rank image submodule. -/
theorem matrixAction_cokernel_full_rank {n : ℕ}
    (A : Fin n → Fin n → ℤ) (hA : Matrix.det A ≠ 0) :
    Module.finrank ℤ ((matrixAction A).range.toIntSubmodule) =
      Module.finrank ℤ (Fin n → ℤ) := by
  exact (Submodule.finiteQuotient_iff _).mp
    (matrixAction_cokernel_finite A hA)

/-- For a rectangular matrix, finiteness of the lattice cokernel is exactly
the full-target-rank condition. -/
theorem matrixAction_cokernel_finite_iff_full_rank
    {n m : ℕ} (A : Fin m → Fin n → ℤ) :
    Finite ((Fin m → ℤ) ⧸ ((matrixAction A).range.toIntSubmodule)) ↔
      Module.finrank ℤ ((matrixAction A).range.toIntSubmodule) =
        Module.finrank ℤ (Fin m → ℤ) :=
  Submodule.finiteQuotient_iff _

/-- Smith normal form presents the cokernel of any rectangular matrix whose
image has full rank in the target lattice. -/
noncomputable def matrixAction_cokernel_smithEquivOfFullRank
    {n m : ℕ} (A : Fin m → Fin n → ℤ)
    (hA : Module.finrank ℤ ((matrixAction A).range.toIntSubmodule) =
      Module.finrank ℤ (Fin m → ℤ)) :
    ((Fin m → ℤ) ⧸ ((matrixAction A).range.toIntSubmodule)) ≃+
      (∀ i : Fin m, ZMod ((Submodule.smithNormalFormCoeffs
        (Pi.basisFun ℤ (Fin m)) hA i).natAbs)) :=
  Submodule.quotientEquivPiZMod (matrixAction A).range.toIntSubmodule
    (Pi.basisFun ℤ (Fin m)) hA

/-- Smith normal form exposes the winding-lattice cokernel as a product of
finite cyclic groups. -/
noncomputable def matrixAction_cokernel_smithEquivOfDetNeZero {n : ℕ}
    (A : Fin n → Fin n → ℤ) (hA : Matrix.det A ≠ 0) :
    ((Fin n → ℤ) ⧸ ((matrixAction A).range.toIntSubmodule)) ≃+
      (∀ i : Fin n, ZMod ((Submodule.smithNormalFormCoeffs
        (Pi.basisFun ℤ (Fin n)) (matrixAction_cokernel_full_rank A hA) i).natAbs)) :=
  Submodule.quotientEquivPiZMod (matrixAction A).range.toIntSubmodule
    (Pi.basisFun ℤ (Fin n)) (matrixAction_cokernel_full_rank A hA)

/-- Extend the diagonal data of a (possibly rank-deficient) Smith-normal-form
pair to every coordinate of the ambient lattice.  Coordinates outside the
embedded Smith basis receive coefficient zero; consequently their `ZMod 0`
factors record the free part of the cokernel. -/
noncomputable def smithNormalFormFactor
    {m r : ℕ} {N : Submodule ℤ (Fin m → ℤ)}
    (snf : Module.Basis.SmithNormalForm N (Fin m) r) (i : Fin m) : ℤ :=
  if h : i ∈ Set.range snf.f then snf.a (Classical.choose h) else 0

@[simp] theorem smithNormalFormFactor_apply
    {m r : ℕ} {N : Submodule ℤ (Fin m → ℤ)}
    (snf : Module.Basis.SmithNormalForm N (Fin m) r) (j : Fin r) :
    smithNormalFormFactor snf (snf.f j) = snf.a j := by
  classical
  simp only [smithNormalFormFactor, dif_pos (Set.mem_range_self j)]
  congr 1
  apply snf.f.injective
  exact Classical.choose_spec (Set.mem_range_self j)

@[simp] theorem smithNormalFormFactor_eq_zero_of_not_mem_range
    {m r : ℕ} {N : Submodule ℤ (Fin m → ℤ)}
    (snf : Module.Basis.SmithNormalForm N (Fin m) r)
    {i : Fin m} (hi : i ∉ Set.range snf.f) :
    smithNormalFormFactor snf i = 0 := by
  simp [smithNormalFormFactor, hi]

/-- In Smith coordinates, an arbitrary-rank submodule is the product of the
coordinate ideals generated by its diagonal coefficients (with zero ideals
on the complementary free coordinates). -/
theorem map_smithNormalForm_eq_pi
    {m r : ℕ} {N : Submodule ℤ (Fin m → ℤ)}
    (snf : Module.Basis.SmithNormalForm N (Fin m) r) :
    Submodule.map (snf.bM.equivFun : (Fin m → ℤ) →ₗ[ℤ] (Fin m → ℤ)) N =
      Submodule.pi Set.univ
        (fun i => Submodule.span ℤ
          ({smithNormalFormFactor snf i} : Set ℤ)) := by
  classical
  ext x
  simp only [Submodule.mem_map, Submodule.mem_pi, Set.mem_univ, forall_true_left]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := snf.bN.mem_submodule_iff.mp hy
    intro i
    simp only [Submodule.mem_span_singleton]
    by_cases hi : i ∈ Set.range snf.f
    · obtain ⟨j, rfl⟩ := hi
      let yN : N := ⟨c.sum fun i x => x • (snf.bN i : (Fin m → ℤ)), by
        exact hy⟩
      refine ⟨snf.bN.repr yN j, ?_⟩
      rw [smithNormalFormFactor_apply snf j]
      change snf.bN.repr yN j * snf.a j =
        snf.bM.repr (yN : (Fin m → ℤ)) (snf.f j)
      rw [snf.repr_apply_embedding_eq_repr_smul]
      simp [mul_comm]
    · refine ⟨0, ?_⟩
      simp only [smithNormalFormFactor, dif_neg hi, zero_smul]
      let yN : N := ⟨c.sum fun i x => x • (snf.bN i : (Fin m → ℤ)), hy⟩
      change (0 : ℤ) = snf.bM.repr (yN : (Fin m → ℤ)) i
      exact (snf.repr_eq_zero_of_notMem_range yN hi).symm
  · intro hx
    have hxc : ∀ j : Fin r, ∃ c : ℤ, c * snf.a j = x (snf.f j) := by
      intro j
      rcases (Submodule.mem_span_singleton.mp (hx (snf.f j))) with ⟨c, hc⟩
      exact ⟨c, by simpa [smul_eq_mul, smithNormalFormFactor_apply snf j] using hc⟩
    choose c hc using hxc
    let y : (Fin m → ℤ) :=
      ∑ j : Fin r, c j • (snf.bN j : (Fin m → ℤ))
    have hy : y ∈ N := by
      dsimp [y]
      apply Submodule.sum_mem N
      intro j hj
      exact N.smul_mem (c j) (snf.bN j).property
    refine ⟨y, hy, ?_⟩
    ext i
    by_cases hi : i ∈ Set.range snf.f
    · obtain ⟨j, rfl⟩ := hi
      let yN : N := ⟨y, hy⟩
      change snf.bM.repr (yN : (Fin m → ℤ)) (snf.f j) = x (snf.f j)
      rw [snf.repr_apply_embedding_eq_repr_smul]
      have hyrepr : snf.bN.repr yN j = c j := by
        have hy_eq : yN = ∑ x, c x • snf.bN x := by
          apply Subtype.ext
          simp [yN, y]
        rw [hy_eq, snf.bN.repr_sum_self]
      rw [map_smul]
      change snf.a j * snf.bN.repr yN j = x (snf.f j)
      rw [hyrepr]
      simpa [mul_comm] using hc j
    · change snf.bM.repr y i = x i
      have hyzero : snf.bM.repr y i = 0 :=
        snf.repr_eq_zero_of_notMem_range ⟨y, hy⟩ hi
      have hxzero : x i = 0 := by
        rcases Submodule.mem_span_singleton.mp (hx i) with ⟨c, hc⟩
        have hc' : c * smithNormalFormFactor snf i = x i := by
          simpa [smul_eq_mul] using hc
        simpa [smithNormalFormFactor, hi] using hc'.symm
      exact hyzero.trans hxzero.symm

/-- The quotient by an arbitrary-rank Smith-normal-form submodule is the
coordinatewise product of the corresponding cyclic quotients.  The zero
coefficients on complementary coordinates are retained as `ZMod 0`, so the
equivalence records the free summand as well as the torsion summands. -/
noncomputable def submoduleCokernelSmithEquiv
    {m r : ℕ} {N : Submodule ℤ (Fin m → ℤ)}
    (snf : Module.Basis.SmithNormalForm N (Fin m) r) :
    ((Fin m → ℤ) ⧸ N) ≃+ (∀ i : Fin m, ZMod (smithNormalFormFactor snf i).natAbs) := by
  let p : (Fin m) → Submodule ℤ ℤ :=
    fun i => Submodule.span ℤ ({smithNormalFormFactor snf i} : Set ℤ)
  have hmap :
      Submodule.map (snf.bM.equivFun : (Fin m → ℤ) →ₗ[ℤ] (Fin m → ℤ)) N =
        Submodule.pi Set.univ p := by
    exact map_smithNormalForm_eq_pi snf
  let qEquiv : ((Fin m → ℤ) ⧸ N) ≃ₗ[ℤ]
      ((Fin m → ℤ) ⧸ Submodule.pi Set.univ p) := by
    exact Submodule.Quotient.equiv N (Submodule.pi Set.univ p)
      snf.bM.equivFun hmap
  let piEquiv : ((Fin m → ℤ) ⧸ Submodule.pi Set.univ p) ≃ₗ[ℤ]
      (∀ i : Fin m, ℤ ⧸ p i) := Submodule.quotientPi p
  let zmodEquiv : (∀ i : Fin m, ℤ ⧸ p i) ≃+
      (∀ i : Fin m, ZMod (smithNormalFormFactor snf i).natAbs) :=
    AddEquiv.piCongrRight fun i => Int.quotientSpanEquivZMod (smithNormalFormFactor snf i)
  exact (qEquiv.toAddEquiv.trans piEquiv.toAddEquiv).trans zmodEquiv

@[simp] theorem submoduleCokernelSmithEquiv_apply_mk
    {m r : ℕ} {N : Submodule ℤ (Fin m → ℤ)}
    (snf : Module.Basis.SmithNormalForm N (Fin m) r)
    (x : Fin m → ℤ) :
    submoduleCokernelSmithEquiv snf (Submodule.Quotient.mk x) =
      fun i => Int.quotientSpanEquivZMod (smithNormalFormFactor snf i)
        (Submodule.Quotient.mk
          (p := Submodule.span ℤ ({smithNormalFormFactor snf i} : Set ℤ))
          ((snf.bM.equivFun : (Fin m → ℤ) →ₗ[ℤ] (Fin m → ℤ)) x i)) := by
  rfl

/-- Smith normal form decomposes an arbitrary-rank lattice cokernel into cyclic
`ZMod` factors.  A factor with modulus zero is the free `ZMod 0` coordinate,
so this single equivalence records both torsion and free cokernel parts. -/
noncomputable def matrixAction_cokernel_smithEquiv {n m : ℕ}
    (A : Fin m → Fin n → ℤ) :
    ((Fin m → ℤ) ⧸ ((matrixAction A).range.toIntSubmodule)) ≃+
      (∀ i : Fin m, ZMod (smithNormalFormFactor
        (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
          (matrixAction A).range.toIntSubmodule).2 i).natAbs) := by
  exact submoduleCokernelSmithEquiv
    (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
      (matrixAction A).range.toIntSubmodule).2

/-- A finite product of `ZMod` coordinates is finite exactly when every
modulus is nonzero.  This is the finiteness criterion that detects whether an
arbitrary-rank Smith decomposition has a free coordinate. -/
theorem finite_zmod_pi_iff {m : ℕ} (n : Fin m → ℕ) :
    Finite (∀ i, ZMod (n i)) ↔ ∀ i, n i ≠ 0 := by
  constructor
  · intro hp i
    have hi : Finite (ZMod (n i)) := by
      letI : Finite (∀ j, ZMod (n j)) := hp
      apply Finite.of_injective (fun z => Function.update (fun j => 0) i z)
      intro a b hab
      have h := congrFun hab i
      simpa using h
    cases hn : n i with
    | zero =>
        rw [hn] at hi
        exact False.elim (ZMod.infinite.not_finite hi)
    | succ k => exact Nat.succ_ne_zero k
  · intro h
    letI : ∀ i, Finite (ZMod (n i)) := fun i => by
      cases hn : n i with
      | zero => exact (h i hn).elim
      | succ k => infer_instance
    infer_instance

/-- The arbitrary-rank Smith presentation gives an exact finiteness test for
the lattice cokernel: it is finite precisely when no complementary `ZMod 0`
factor occurs. -/
theorem matrixAction_cokernel_finite_iff_smithNormalFormFactor_ne_zero
    {n m : ℕ} (A : Fin m → Fin n → ℤ) :
    Finite ((Fin m → ℤ) ⧸ ((matrixAction A).range.toIntSubmodule)) ↔
      ∀ i : Fin m, smithNormalFormFactor
        (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
          (matrixAction A).range.toIntSubmodule).2 i ≠ 0 := by
  refine (Equiv.finite_iff (matrixAction_cokernel_smithEquiv A).toEquiv).trans ?_
  simpa only [Int.natAbs_ne_zero] using
    (finite_zmod_pi_iff (fun i =>
      (smithNormalFormFactor
        (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
          (matrixAction A).range.toIntSubmodule).2 i).natAbs))

/-- Combining the finite-quotient theorem with the Smith presentation yields
a direct full-rank criterion in terms of the diagonal coefficients. -/
theorem matrixAction_cokernel_full_rank_iff_smithNormalFormFactor_ne_zero
    {n m : ℕ} (A : Fin m → Fin n → ℤ) :
    Module.finrank ℤ ((matrixAction A).range.toIntSubmodule) =
        Module.finrank ℤ (Fin m → ℤ) ↔
      ∀ i : Fin m, smithNormalFormFactor
        (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
          (matrixAction A).range.toIntSubmodule).2 i ≠ 0 := by
  exact (matrixAction_cokernel_finite_iff_full_rank A).symm.trans
    (matrixAction_cokernel_finite_iff_smithNormalFormFactor_ne_zero A)

/-- Under full target rank, the Smith factors give the exact cardinality of
the lattice cokernel as their product of moduli. -/
theorem matrixAction_cokernel_card_eq_smithNormalFormProduct
    {n m : ℕ} (A : Fin m → Fin n → ℤ)
    (hA : Module.finrank ℤ ((matrixAction A).range.toIntSubmodule) =
      Module.finrank ℤ (Fin m → ℤ)) :
    Nat.card ((Fin m → ℤ) ⧸ ((matrixAction A).range.toIntSubmodule)) =
      ∏ i : Fin m, (Submodule.smithNormalFormCoeffs
        (Pi.basisFun ℤ (Fin m)) hA i).natAbs := by
  rw [Nat.card_congr (matrixAction_cokernel_smithEquivOfFullRank A hA).toEquiv]
  simp [Nat.card_pi, Nat.card_zmod]

/-- In the square nonsingular case, the product of the Smith moduli is the
determinant index.  This is the arithmetic compatibility between the
invariant-factor and determinant cardinality certificates. -/
theorem matrixAction_smithNormalFormProduct_eq_natAbs_det {n : ℕ}
    (A : Fin n → Fin n → ℤ) (hA : Matrix.det A ≠ 0) :
    ∏ i : Fin n, (Submodule.smithNormalFormCoeffs
      (Pi.basisFun ℤ (Fin n)) (matrixAction_cokernel_full_rank A hA) i).natAbs =
      Int.natAbs (Matrix.det A) := by
  rw [← matrixAction_cokernel_card_eq_smithNormalFormProduct A
    (matrixAction_cokernel_full_rank A hA)]
  exact matrixAction_cokernel_card_eq_natAbs_det A hA

/-- The matrix action is continuous for the product topologies on the
integer lattices. -/
noncomputable def matrixActionContinuous {n m : ℕ}
    (A : Fin m → Fin n → ℤ) :
    (Fin n → ℤ) →ₜ+ (Fin m → ℤ) where
  toAddMonoidHom := matrixAction A
  continuous_toFun := by
    apply continuous_pi
    intro j
    exact continuous_finsetSum Finset.univ (fun i _ =>
      (continuous_const.mul (continuous_apply i)))

/-- Continuous matrix actions satisfy the same composition law. -/
theorem matrixActionContinuous_comp {n m k : ℕ}
    (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ) :
    matrixActionContinuous (matrixCompose A B) =
      (matrixActionContinuous B).comp (matrixActionContinuous A) := by
  ext z l
  change matrixAction (matrixCompose A B) z l =
    matrixAction B (matrixAction A z) l
  exact congrFun (matrixAction_comp A B z).symm l

/-- The continuous identity matrix action is the identity morphism. -/
theorem matrixActionContinuous_id (n : ℕ) :
    matrixActionContinuous (matrixIdentity n) =
      ContinuousAddMonoidHom.id (Fin n → ℤ) := by
  ext z i
  change matrixAction (matrixIdentity n) z i = z i
  exact congrFun (matrixAction_id n z) i

lemma matrixSum_zsmul {α G : Type*} [AddCommGroup G]
    (s : Finset α) (a : α → ℤ) (x : G) :
    (∑ i ∈ s, a i) • x = ∑ i ∈ s, a i • x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, add_zsmul, ih]

/-- Matrix maps compose contravariantly on finite tori. -/
lemma matrixMap_comp {n m k : ℕ}
    (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ) :
    (matrixMap B).comp (matrixMap A) = matrixMap (matrixCompose A B) := by
  ext x l
  change (∑ j : Fin m, B l j • (∑ i : Fin n, A j i • x i)) =
    ∑ i : Fin n, (∑ j : Fin m, B l j * A j i) • x i
  rw [show (∑ j : Fin m, B l j • (∑ i : Fin n, A j i • x i)) =
      ∑ j : Fin m, ∑ i : Fin n, B l j • (A j i • x i) by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.smul_sum]]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [matrixSum_zsmul]
  apply Finset.sum_congr rfl
  intro j _
  simp [mul_zsmul]

/-- The identity matrix map is the identity continuous map. -/
lemma matrixMap_id (n : ℕ) :
    matrixMap (matrixIdentity n) = ContinuousMap.id (Carrier n) := by
  ext x i
  change (∑ j : Fin n, (if i = j then 1 else 0) • x j) = x i
  simp

/-- Matrix maps preserve the canonical zero basepoint. -/
lemma matrixMap_base {n m : ℕ} (A : Fin m → Fin n → ℤ) :
    matrixMap A (base n) = base m := by
  funext j
  simp [matrixMap, base]

/-! The adjugate-based nonsingular inverse is named explicitly at the
function level so that square matrices can be passed through the same
row-by-column API as the rectangular maps above. -/

/-- The canonical nonsingular inverse of a square integer matrix. -/
noncomputable def matrixNonsingInv {n : ℕ} (A : Fin n → Fin n → ℤ) :
    Fin n → Fin n → ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := A
  let B : Matrix (Fin n) (Fin n) ℤ := M⁻¹
  B

/-- The inverse matrix followed by `A` is the identity in the
`matrixCompose` convention. -/
theorem matrixCompose_nonsingInv_mul_of_det_unit {n : ℕ}
    (A : Fin n → Fin n → ℤ) (hA : IsUnit (Matrix.det A)) :
    matrixCompose A (matrixNonsingInv A) = matrixIdentity n := by
  let M : Matrix (Fin n) (Fin n) ℤ := A
  let B : Matrix (Fin n) (Fin n) ℤ := M⁻¹
  have hM : IsUnit (Matrix.det M) := by simpa [M] using hA
  ext i j
  change (B * M) i j = (1 : Matrix (Fin n) (Fin n) ℤ) i j
  rw [show B = M⁻¹ by rfl, Matrix.nonsing_inv_mul M hM]

/-- `A` followed by its nonsingular inverse is the identity in the
`matrixCompose` convention. -/
theorem matrixCompose_mul_nonsingInv_of_det_unit {n : ℕ}
    (A : Fin n → Fin n → ℤ) (hA : IsUnit (Matrix.det A)) :
    matrixCompose (matrixNonsingInv A) A = matrixIdentity n := by
  let M : Matrix (Fin n) (Fin n) ℤ := A
  let B : Matrix (Fin n) (Fin n) ℤ := M⁻¹
  have hM : IsUnit (Matrix.det M) := by simpa [M] using hA
  ext i j
  change (M * B) i j = (1 : Matrix (Fin n) (Fin n) ℤ) i j
  rw [show B = M⁻¹ by rfl, Matrix.mul_nonsing_inv M hM]

/-! A matrix with an explicit two-sided integer inverse acts by equivalences at
every level of the construction.  Keeping the inverse equations as hypotheses
avoids importing determinant machinery and works uniformly for rectangular
types that happen to be isomorphic. -/

/-- An explicit two-sided matrix inverse yields an additive equivalence of
winding lattices. -/
noncomputable def matrixActionEquivOfInverse {n m : ℕ}
    (A : Fin m → Fin n → ℤ) (B : Fin n → Fin m → ℤ)
    (hAB : matrixCompose A B = matrixIdentity n)
    (hBA : matrixCompose B A = matrixIdentity m) :
    (Fin n → ℤ) ≃+ (Fin m → ℤ) where
  toFun := matrixAction A
  invFun := matrixAction B
  left_inv := by
    intro z
    have hcomp := congrArg (fun F : (Fin n → ℤ) →+ (Fin n → ℤ) => F z)
      (matrixAction_comp_hom A B)
    rw [hAB, matrixAction_id_hom] at hcomp
    exact hcomp.symm
  right_inv := by
    intro z
    have hcomp := congrArg (fun F : (Fin m → ℤ) →+ (Fin m → ℤ) => F z)
      (matrixAction_comp_hom B A)
    rw [hBA, matrixAction_id_hom] at hcomp
    exact hcomp.symm
  map_add' := (matrixAction A).map_add

/-- The inverse matrix action is continuous for the product topologies. -/
noncomputable def matrixActionContinuousEquivOfInverse {n m : ℕ}
    (A : Fin m → Fin n → ℤ) (B : Fin n → Fin m → ℤ)
    (hAB : matrixCompose A B = matrixIdentity n)
    (hBA : matrixCompose B A = matrixIdentity m) :
    (Fin n → ℤ) ≃ₜ+ (Fin m → ℤ) where
  toEquiv := matrixActionEquivOfInverse A B hAB hBA
  map_add' := (matrixAction A).map_add
  continuous_toFun := (matrixActionContinuous A).continuous_toFun
  continuous_invFun := (matrixActionContinuous B).continuous_toFun

/-- An explicit two-sided matrix inverse yields a homeomorphism of finite
tori. -/
noncomputable def matrixMapHomeomorphOfInverse {n m : ℕ}
    (A : Fin m → Fin n → ℤ) (B : Fin n → Fin m → ℤ)
    (hAB : matrixCompose A B = matrixIdentity n)
    (hBA : matrixCompose B A = matrixIdentity m) :
    Carrier n ≃ₜ Carrier m where
  toFun := matrixMap A
  invFun := matrixMap B
  left_inv := by
    intro x
    have hcomp := congrArg (fun F : C(Carrier n, Carrier n) => F x)
      (matrixMap_comp A B)
    rw [ContinuousMap.comp_apply, hAB, matrixMap_id] at hcomp
    exact hcomp
  right_inv := by
    intro x
    have hcomp := congrArg (fun F : C(Carrier m, Carrier m) => F x)
      (matrixMap_comp B A)
    rw [ContinuousMap.comp_apply, hBA, matrixMap_id] at hcomp
    exact hcomp
  continuous_toFun := (matrixMap A).continuous_toFun
  continuous_invFun := (matrixMap B).continuous_toFun

/-- A unimodular square matrix yields an additive equivalence of winding
lattices using its canonical nonsingular inverse. -/
noncomputable def matrixActionEquivOfDetUnit {n : ℕ}
    (A : Fin n → Fin n → ℤ) (hA : IsUnit (Matrix.det A)) :
    (Fin n → ℤ) ≃+ (Fin n → ℤ) :=
  matrixActionEquivOfInverse A (matrixNonsingInv A)
    (matrixCompose_nonsingInv_mul_of_det_unit A hA)
    (matrixCompose_mul_nonsingInv_of_det_unit A hA)

/-- The determinant-level lattice equivalence is continuous for the product
topologies on the discrete winding lattices. -/
noncomputable def matrixActionContinuousEquivOfDetUnit {n : ℕ}
    (A : Fin n → Fin n → ℤ) (hA : IsUnit (Matrix.det A)) :
    (Fin n → ℤ) ≃ₜ+ (Fin n → ℤ) :=
  matrixActionContinuousEquivOfInverse A (matrixNonsingInv A)
    (matrixCompose_nonsingInv_mul_of_det_unit A hA)
    (matrixCompose_mul_nonsingInv_of_det_unit A hA)

/-- A unimodular square matrix acts as a homeomorphism of the finite torus. -/
noncomputable def matrixMapHomeomorphOfDetUnit {n : ℕ}
    (A : Fin n → Fin n → ℤ) (hA : IsUnit (Matrix.det A)) :
    Carrier n ≃ₜ Carrier n :=
  matrixMapHomeomorphOfInverse A (matrixNonsingInv A)
    (matrixCompose_nonsingInv_mul_of_det_unit A hA)
    (matrixCompose_mul_nonsingInv_of_det_unit A hA)

/-- Basepoint transport is stable under changing the endpoint types by an
explicit equality.  The quotient cast on the loop class records the same
change of basepoint on the source side. -/
theorem basepointChangeContinuousMulEquiv_pathCast
    {X : Type*} [TopologicalSpace X]
    {x₀ x₁ x₀' x₁' : X}
    (p : _root_.Path x₀ x₁) (hx : x₀' = x₀) (hy : x₁' = x₁)
    (q : QuotientFundamentalGroup.LoopQuot X x₀') :
    QuotientFundamentalGroup.basepointChangeContinuousMulEquiv
        (p.cast hx hy) q =
      (QuotientFundamentalGroup.basepointChangeContinuousMulEquiv p
        (_root_.Path.Homotopic.Quotient.cast q hx.symm hx.symm)).cast hy hy := by
  cases hx
  cases hy
  rw [_root_.Path.cast_rfl_rfl]
  simp only [_root_.Path.Homotopic.Quotient.cast_rfl_rfl]

/-- Two successive endpoint casts cancel. -/
lemma quotientCast_roundtrip
    {X : Type*} [TopologicalSpace X]
    {x y : X} (h : x = y)
    (q : QuotientFundamentalGroup.LoopQuot X x) :
    (q.cast h.symm h.symm).cast h h = q := by
  cases h
  simp only [_root_.Path.Homotopic.Quotient.cast_rfl_rfl]

/-- Equality of continuous maps transports the induced quotient map across
the corresponding endpoint equality. -/
lemma quotientMap_cast_of_continuousMap_eq
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (hfg : f = g) (x : X)
    (q : QuotientFundamentalGroup.LoopQuot X x) :
    ((_root_.Path.Homotopic.Quotient.map q f).cast
      (congrArg (fun F : C(X, Y) => F x) hfg.symm)
      (congrArg (fun F : C(X, Y) => F x) hfg.symm)) =
      _root_.Path.Homotopic.Quotient.map q g := by
  cases hfg
  simp only [_root_.Path.Homotopic.Quotient.cast_rfl_rfl]

/-- An integer matrix induces a continuous multiplicative homomorphism on
the quotient fundamental groups at every chosen torus basepoint. -/
noncomputable def matrixMapQuotientContinuousMulHomAt {n m : ℕ}
    (A : Fin m → Fin n → ℤ) (x : Carrier n) :
    QuotientFundamentalGroup.LoopQuot (Carrier n) x →ₜ*
      QuotientFundamentalGroup.LoopQuot (Carrier m) (matrixMap A x) :=
  QuotientFundamentalGroup.inducedContinuousMonoidHom (matrixMap A) x

@[simp] theorem matrixMapQuotientContinuousMulHomAt_apply {n m : ℕ}
    (A : Fin m → Fin n → ℤ) (x : Carrier n)
    (q : QuotientFundamentalGroup.LoopQuot (Carrier n) x) :
    matrixMapQuotientContinuousMulHomAt A x q =
      _root_.Path.Homotopic.Quotient.map q (matrixMap A) :=
  rfl

/-- An explicit two-sided matrix inverse upgrades the arbitrary-basepoint
quotient homomorphism to a continuous multiplicative equivalence.  The inverse
uses the matrix inverse on loops and the endpoint cast supplied by the torus
homeomorphism. -/
noncomputable def matrixMapQuotientContinuousMulEquivAtOfInverse {n m : ℕ}
    (A : Fin m → Fin n → ℤ) (B : Fin n → Fin m → ℤ)
    (hAB : matrixCompose A B = matrixIdentity n)
    (hBA : matrixCompose B A = matrixIdentity m)
    (x : Carrier n) :
    QuotientFundamentalGroup.LoopQuot (Carrier n) x ≃ₜ*
      QuotientFundamentalGroup.LoopQuot (Carrier m) (matrixMap A x) :=
  QuotientFundamentalGroup.homeomorphInducedContinuousMulEquiv
    (matrixMapHomeomorphOfInverse A B hAB hBA) x

/-- A unimodular square matrix upgrades the quotient homomorphism at every
basepoint to a continuous multiplicative equivalence using its canonical
nonsingular inverse. -/
noncomputable def matrixMapQuotientContinuousMulEquivAtOfDetUnit {n : ℕ}
    (A : Fin n → Fin n → ℤ) (hA : IsUnit (Matrix.det A))
    (x : Carrier n) :
    QuotientFundamentalGroup.LoopQuot (Carrier n) x ≃ₜ*
      QuotientFundamentalGroup.LoopQuot (Carrier n) (matrixMap A x) :=
  matrixMapQuotientContinuousMulEquivAtOfInverse A (matrixNonsingInv A)
    (matrixCompose_nonsingInv_mul_of_det_unit A hA)
    (matrixCompose_mul_nonsingInv_of_det_unit A hA) x

@[simp] theorem matrixMapQuotientContinuousMulEquivAtOfInverse_apply
    {n m : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin n → Fin m → ℤ)
    (hAB : matrixCompose A B = matrixIdentity n)
    (hBA : matrixCompose B A = matrixIdentity m)
    (x : Carrier n)
    (q : QuotientFundamentalGroup.LoopQuot (Carrier n) x) :
    matrixMapQuotientContinuousMulEquivAtOfInverse A B hAB hBA x q =
      matrixMapQuotientContinuousMulHomAt A x q := by
  rfl

theorem matrixMapQuotientContinuousMulEquivAtOfInverse_injective
    {n m : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin n → Fin m → ℤ)
    (hAB : matrixCompose A B = matrixIdentity n)
    (hBA : matrixCompose B A = matrixIdentity m)
    (x : Carrier n) :
    Function.Injective (matrixMapQuotientContinuousMulHomAt A x) := by
  intro p q h
  exact (matrixMapQuotientContinuousMulEquivAtOfInverse A B hAB hBA x).injective h

theorem matrixMapQuotientContinuousMulEquivAtOfInverse_surjective
    {n m : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin n → Fin m → ℤ)
    (hAB : matrixCompose A B = matrixIdentity n)
    (hBA : matrixCompose B A = matrixIdentity m)
    (x : Carrier n) :
    Function.Surjective (matrixMapQuotientContinuousMulHomAt A x) := by
  intro q
  obtain ⟨p, hp⟩ :=
    (matrixMapQuotientContinuousMulEquivAtOfInverse A B hAB hBA x).surjective q
  exact ⟨p, hp⟩

@[simp] theorem matrixMapQuotientContinuousMulEquivAtOfDetUnit_apply
    {n : ℕ} (A : Fin n → Fin n → ℤ) (hA : IsUnit (Matrix.det A))
    (x : Carrier n)
    (q : QuotientFundamentalGroup.LoopQuot (Carrier n) x) :
    matrixMapQuotientContinuousMulEquivAtOfDetUnit A hA x q =
      matrixMapQuotientContinuousMulHomAt A x q := by
  change matrixMapQuotientContinuousMulEquivAtOfInverse A
      (matrixNonsingInv A)
      (matrixCompose_nonsingInv_mul_of_det_unit A hA)
      (matrixCompose_mul_nonsingInv_of_det_unit A hA) x q = _
  exact matrixMapQuotientContinuousMulEquivAtOfInverse_apply A
    (matrixNonsingInv A)
    (matrixCompose_nonsingInv_mul_of_det_unit A hA)
    (matrixCompose_mul_nonsingInv_of_det_unit A hA) x q

/-- The determinant-level arbitrary-basepoint equivalence is injective. -/
theorem matrixMapQuotientContinuousMulEquivAtOfDetUnit_injective
    {n : ℕ} (A : Fin n → Fin n → ℤ) (hA : IsUnit (Matrix.det A))
    (x : Carrier n) :
    Function.Injective (matrixMapQuotientContinuousMulHomAt A x) := by
  exact matrixMapQuotientContinuousMulEquivAtOfInverse_injective A
    (matrixNonsingInv A)
    (matrixCompose_nonsingInv_mul_of_det_unit A hA)
    (matrixCompose_mul_nonsingInv_of_det_unit A hA) x

/-- The determinant-level arbitrary-basepoint equivalence is surjective. -/
theorem matrixMapQuotientContinuousMulEquivAtOfDetUnit_surjective
    {n : ℕ} (A : Fin n → Fin n → ℤ) (hA : IsUnit (Matrix.det A))
    (x : Carrier n) :
    Function.Surjective (matrixMapQuotientContinuousMulHomAt A x) := by
  exact matrixMapQuotientContinuousMulEquivAtOfInverse_surjective A
    (matrixNonsingInv A)
    (matrixCompose_nonsingInv_mul_of_det_unit A hA)
    (matrixCompose_mul_nonsingInv_of_det_unit A hA) x

/-- Matrix maps commute with basepoint transport along every explicit path
from the canonical torus basepoint. -/
theorem matrixMapQuotientContinuousMulHomAt_basepointChange
    {n m : ℕ} (A : Fin m → Fin n → ℤ) (x : Carrier n)
    (p : _root_.Path (base n) x) (q : LoopQuot n) :
    matrixMapQuotientContinuousMulHomAt A x
        (QuotientFundamentalGroup.basepointChangeContinuousMulEquiv p q) =
      QuotientFundamentalGroup.basepointChangeContinuousMulEquiv
        (p.map (matrixMap A).continuous)
        (matrixMapQuotientContinuousMulHomAt A (base n) q) := by
  change _root_.Path.Homotopic.Quotient.map
      (QuotientFundamentalGroup.basepointChangeContinuousMulEquiv p q)
        (matrixMap A) =
    QuotientFundamentalGroup.basepointChangeContinuousMulEquiv
      (p.map (matrixMap A).continuous)
      (_root_.Path.Homotopic.Quotient.map q (matrixMap A))
  exact QuotientFundamentalGroup.basepointChange_quotientMap_naturality
    p (matrixMap A) q

/-- Arbitrary-basepoint matrix homomorphisms compose contravariantly, with
the endpoint equality induced by matrix-map composition made explicit. -/
theorem matrixMapQuotientContinuousMulHomAt_comp_cast_apply
    {n m k : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ)
    (x : Carrier n) (q : QuotientFundamentalGroup.LoopQuot (Carrier n) x) :
    (((matrixMapQuotientContinuousMulHomAt B (matrixMap A x)).comp
        (matrixMapQuotientContinuousMulHomAt A x)) q).cast
      (congrArg (fun F : C(Carrier n, Carrier k) => F x)
        (matrixMap_comp A B).symm)
      (congrArg (fun F : C(Carrier n, Carrier k) => F x)
        (matrixMap_comp A B).symm) =
      matrixMapQuotientContinuousMulHomAt (matrixCompose A B) x q := by
  dsimp
  rw [QuotientFundamentalGroup.quotientMap_comp]
  exact quotientMap_cast_of_continuousMap_eq (matrixMap_comp A B) x q

/-- The identity matrix induces the identity arbitrary-basepoint quotient
homomorphism, with the endpoint equality induced by `matrixMap_id` explicit. -/
theorem matrixMapQuotientContinuousMulHomAt_id_cast_apply
    (n : ℕ) (x : Carrier n)
    (q : QuotientFundamentalGroup.LoopQuot (Carrier n) x) :
    ((matrixMapQuotientContinuousMulHomAt (matrixIdentity n) x) q).cast
      (congrArg (fun F : C(Carrier n, Carrier n) => F x)
        (matrixMap_id n).symm)
      (congrArg (fun F : C(Carrier n, Carrier n) => F x)
        (matrixMap_id n).symm) = q := by
  dsimp
  have hcast := quotientMap_cast_of_continuousMap_eq (matrixMap_id n) x q
  have hid := QuotientFundamentalGroup.quotientMap_id x q
  exact hcast.trans hid

lemma zsmul_circleCover (a : ℤ) (r : ℝ) :
    a • circleCover r = circleCover (a • r) := by
  change a • (r : AddCircle (1 : ℝ)) = ((a • r : ℝ) : AddCircle (1 : ℝ))
  exact (AddCircle.coe_zsmul (p := (1 : ℝ))).symm

lemma sum_circleCover (s : Finset (Fin n)) (u : Fin n → ℝ) :
    (∑ i ∈ s, circleCover (u i)) = circleCover (∑ i ∈ s, u i) := by
  induction s using Finset.induction_on with
  | empty => simp [circleCover]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, ih]
      change ((u i : ℝ) : AddCircle (1 : ℝ)) +
        ((∑ i ∈ s, u i : ℝ) : AddCircle (1 : ℝ)) =
        ((∑ i ∈ insert i s, u i : ℝ) : AddCircle (1 : ℝ))
      rw [Finset.sum_insert hi, ← AddCircle.coe_add]

/-- Standard winding representatives are natural for arbitrary integer
matrix maps. -/
theorem matrixMap_standardLoop {n m : ℕ} (A : Fin m → Fin n → ℤ)
    (z : Fin n → ℤ) :
    ((standardLoop z).map (matrixMap A).continuous).cast
      (matrixMap_base A).symm (matrixMap_base A).symm =
      standardLoop (matrixAction A z) := by
  apply _root_.Path.ext
  funext t
  funext j
  change (∑ i : Fin n, A j i • circleCover (t * (z i : ℝ))) =
    circleCover (t * ∑ i : Fin n, A j i * z i)
  rw [show (∑ i : Fin n, A j i • circleCover (t * (z i : ℝ))) =
      ∑ i : Fin n, circleCover (A j i • (t * (z i : ℝ))) by
        apply Finset.sum_congr rfl
        intro i _
        exact zsmul_circleCover _ _]
  rw [sum_circleCover]
  congr 1
  simp only [Int.cast_sum, Int.cast_mul]
  rw [(Finset.mul_sum (Finset.univ : Finset (Fin n))
    (fun i => (A j i : ℝ) * (z i : ℝ)) (t : ℝ))]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The quotient map induced by an integer matrix, with its endpoint cast to
the canonical target basepoint made explicit. -/
noncomputable def matrixMapQuotientMap {n m : ℕ}
    (A : Fin m → Fin n → ℤ) : LoopQuot n → LoopQuot m :=
  fun q =>
    (_root_.Path.Homotopic.Quotient.map q (matrixMap A)).cast
      (matrixMap_base A).symm (matrixMap_base A).symm

/-- Matrix maps send explicit standard quotient representatives to explicit
standard representatives. -/
lemma matrixMapQuotientMap_decode {n m : ℕ}
    (A : Fin m → Fin n → ℤ) (z : Fin n → ℤ) :
    matrixMapQuotientMap A (decode z) =
      decode (matrixAction A z) := by
  change Quotient.mk'
      (((standardLoop z).map (matrixMap A).continuous).cast
        (matrixMap_base A).symm (matrixMap_base A).symm) =
    Quotient.mk' (standardLoop (matrixAction A z))
  rw [matrixMap_standardLoop]

/-- The quotient winding classifier intertwines an integer matrix map with
the corresponding lattice action. -/
theorem encode_matrixMapQuotientMap {n m : ℕ}
    (A : Fin m → Fin n → ℤ) (q : LoopQuot n) :
    encode (matrixMapQuotientMap A q) = matrixAction A (encode q) := by
  induction q using _root_.Path.Homotopic.Quotient.ind with
  | mk γ =>
    change encode (matrixMapQuotientMap A (Quotient.mk' γ)) =
      matrixAction A (encode (Quotient.mk' γ))
    rw [← decode_encode (Quotient.mk' γ)]
    rw [matrixMapQuotientMap_decode]
    simp only [encode_decode]

/-- The path-based winding classifier is natural for arbitrary integer
matrix maps, including the explicit endpoint cast from the mapped source
basepoint to the canonical target basepoint. -/
theorem loopQuotContinuousMulEquivIntVector_at_path_matrixMap
    {n m : ℕ} (A : Fin m → Fin n → ℤ) (x : Carrier n)
    (p : _root_.Path (base n) x)
    (q : QuotientFundamentalGroup.LoopQuot (Carrier n) x) :
    (loopQuotContinuousMulEquivIntVector_at_path m
      (matrixMap A x)
      ((p.map (matrixMap A).continuous).cast
        (matrixMap_base A).symm rfl))
        (matrixMapQuotientContinuousMulHomAt A x q) =
      Multiplicative.ofAdd
        (matrixAction A
          (Multiplicative.toAdd
            (loopQuotContinuousMulEquivIntVector_at_path n x p q))) := by
  let r : LoopQuot n :=
    (QuotientFundamentalGroup.basepointChangeContinuousMulEquiv p).symm q
  have hr :
      _root_.Path.Homotopic.Quotient.map q (matrixMap A) =
        QuotientFundamentalGroup.basepointChangeContinuousMulEquiv
          (p.map (matrixMap A).continuous)
          (_root_.Path.Homotopic.Quotient.map r (matrixMap A)) := by
    have hnat :=
      QuotientFundamentalGroup.basepointChange_quotientMap_naturality
        p (matrixMap A) r
    have hpr :
        QuotientFundamentalGroup.basepointChangeContinuousMulEquiv p
            ((QuotientFundamentalGroup.basepointChangeContinuousMulEquiv p).symm q) = q :=
      (QuotientFundamentalGroup.basepointChangeContinuousMulEquiv p).apply_symm_apply q
    rw [hpr] at hnat
    exact hnat
  have hcast :
      QuotientFundamentalGroup.basepointChangeContinuousMulEquiv
          ((p.map (matrixMap A).continuous).cast
            (matrixMap_base A).symm rfl)
          ((_root_.Path.Homotopic.Quotient.map r (matrixMap A)).cast
            (matrixMap_base A).symm (matrixMap_base A).symm) =
        QuotientFundamentalGroup.basepointChangeContinuousMulEquiv
          (p.map (matrixMap A).continuous)
          (_root_.Path.Homotopic.Quotient.map r (matrixMap A)) := by
    have htest := basepointChangeContinuousMulEquiv_pathCast
      (p.map (matrixMap A).continuous)
      (matrixMap_base A).symm rfl
      ((_root_.Path.Homotopic.Quotient.map r (matrixMap A)).cast
        (matrixMap_base A).symm (matrixMap_base A).symm)
    have hround := quotientCast_roundtrip
      (X := Carrier m) (matrixMap_base A)
      (_root_.Path.Homotopic.Quotient.map r (matrixMap A))
    rw [hround] at htest
    simpa only [_root_.Path.Homotopic.Quotient.cast_rfl_rfl] using htest
  rw [loopQuotContinuousMulEquivIntVector_at_path,
    matrixMapQuotientContinuousMulHomAt_apply]
  change
    (loopQuotContinuousMulEquivIntVector m)
      ((QuotientFundamentalGroup.basepointChangeContinuousMulEquiv
        ((p.map (matrixMap A).continuous).cast
          (matrixMap_base A).symm rfl)).symm
        (_root_.Path.Homotopic.Quotient.map q (matrixMap A))) =
      Multiplicative.ofAdd
        (matrixAction A
          (Multiplicative.toAdd
            (((QuotientFundamentalGroup.basepointChangeContinuousMulEquiv p).symm.trans
              (loopQuotContinuousMulEquivIntVector n)) q)))
  rw [hr]
  have hinv :
      (QuotientFundamentalGroup.basepointChangeContinuousMulEquiv
        ((p.map (matrixMap A).continuous).cast
          (matrixMap_base A).symm rfl)).symm
          (QuotientFundamentalGroup.basepointChangeContinuousMulEquiv
            (p.map (matrixMap A).continuous)
            (_root_.Path.Homotopic.Quotient.map r (matrixMap A))) =
        (_root_.Path.Homotopic.Quotient.map r (matrixMap A)).cast
          (matrixMap_base A).symm (matrixMap_base A).symm := by
    rw [← hcast]
    exact (QuotientFundamentalGroup.basepointChangeContinuousMulEquiv
      ((p.map (matrixMap A).continuous).cast
        (matrixMap_base A).symm rfl)).symm_apply_apply _
  rw [hinv]
  apply Multiplicative.ext
  change encode ((_root_.Path.Homotopic.Quotient.map r (matrixMap A)).cast
      (matrixMap_base A).symm (matrixMap_base A).symm) =
    matrixAction A (encode r)
  simpa [matrixMapQuotientMap] using
    (encode_matrixMapQuotientMap A r)

/-- The canonical arbitrary-basepoint winding classifier is natural for
integer matrix maps, by path-independence of the abelian target transport. -/
theorem loopQuotContinuousMulEquivIntVector_at_matrixMap
    {n m : ℕ} (A : Fin m → Fin n → ℤ) (x : Carrier n)
    (q : QuotientFundamentalGroup.LoopQuot (Carrier n) x) :
    (loopQuotContinuousMulEquivIntVector_at m
      (matrixMap A x))
        (matrixMapQuotientContinuousMulHomAt A x q) =
      Multiplicative.ofAdd
        (matrixAction A
          (Multiplicative.toAdd
            (loopQuotContinuousMulEquivIntVector_at n x q))) := by
  let p : _root_.Path (base n) x := PathConnectedSpace.somePath (base n) x
  let p' : _root_.Path (base m) (matrixMap A x) :=
    PathConnectedSpace.somePath (base m) (matrixMap A x)
  have h := loopQuotContinuousMulEquivIntVector_at_path_matrixMap
    A x p q
  have ht := loopQuotContinuousMulEquivIntVector_at_path_eq m
    (matrixMap A x)
    ((p.map (matrixMap A).continuous).cast (matrixMap_base A).symm rfl) p'
  have htq := congrArg
    (fun E => E (matrixMapQuotientContinuousMulHomAt A x q)) ht
  rw [htq] at h
  have hs := loopQuotContinuousMulEquivIntVector_at_path_eq n x p
    (PathConnectedSpace.somePath (base n) x)
  have hsq := congrArg (fun E => E q) hs
  rw [← hsq] at h
  simpa [p, p', loopQuotContinuousMulEquivIntVector_at_path,
    loopQuotContinuousMulEquivIntVector_at,
    QuotientFundamentalGroup.pathConnectedBasepointContinuousMulEquiv] using h

/-- At arbitrary basepoints, the image of the matrix-induced quotient
homomorphism is exactly the image of the corresponding lattice action. -/
theorem matrixMapQuotientContinuousMulHomAt_mem_range_iff
    {n m : ℕ} (A : Fin m → Fin n → ℤ) (x : Carrier n)
    (q : QuotientFundamentalGroup.LoopQuot (Carrier m) (matrixMap A x)) :
    q ∈ Set.range (matrixMapQuotientContinuousMulHomAt A x) ↔
      Multiplicative.toAdd
          ((loopQuotContinuousMulEquivIntVector_at m (matrixMap A x)) q) ∈
        Set.range (matrixAction A) := by
  let eₙ := loopQuotContinuousMulEquivIntVector_at n x
  let eₘ := loopQuotContinuousMulEquivIntVector_at m (matrixMap A x)
  constructor
  · rintro ⟨p, rfl⟩
    have hnat := loopQuotContinuousMulEquivIntVector_at_matrixMap A x p
    have hvec :
        Multiplicative.toAdd (eₘ
            (matrixMapQuotientContinuousMulHomAt A x p)) =
          matrixAction A (Multiplicative.toAdd (eₙ p)) := by
      rw [hnat]
      rfl
    rw [hvec]
    exact ⟨Multiplicative.toAdd (eₙ p), rfl⟩
  · rintro ⟨z, hz⟩
    refine ⟨eₙ.symm (Multiplicative.ofAdd z), ?_⟩
    apply eₘ.injective
    have hnat := loopQuotContinuousMulEquivIntVector_at_matrixMap A x
      (eₙ.symm (Multiplicative.ofAdd z))
    rw [hnat]
    apply Multiplicative.ext
    change matrixAction A
        (Multiplicative.toAdd (eₙ (eₙ.symm (Multiplicative.ofAdd z)))) =
      Multiplicative.toAdd (eₘ q)
    rw [eₙ.apply_symm_apply]
    exact hz

/-- At arbitrary basepoints, the kernel of the matrix-induced quotient
homomorphism is exactly the kernel of the integer matrix action. -/
theorem matrixMapQuotientContinuousMulHomAt_eq_one_iff
    {n m : ℕ} (A : Fin m → Fin n → ℤ) (x : Carrier n)
    (q : QuotientFundamentalGroup.LoopQuot (Carrier n) x) :
    matrixMapQuotientContinuousMulHomAt A x q = 1 ↔
      matrixAction A
          (Multiplicative.toAdd
            ((loopQuotContinuousMulEquivIntVector_at n x) q)) = 0 := by
  let eₙ := loopQuotContinuousMulEquivIntVector_at n x
  let eₘ := loopQuotContinuousMulEquivIntVector_at m (matrixMap A x)
  constructor
  · intro h
    have hq := congrArg (fun r => eₘ r)
      (show matrixMapQuotientContinuousMulHomAt A x q = 1 from h)
    have hnat := loopQuotContinuousMulEquivIntVector_at_matrixMap A x q
    rw [hnat] at hq
    have h_one : eₘ (1 : QuotientFundamentalGroup.LoopQuot
        (Carrier m) (matrixMap A x)) = 1 := eₘ.map_one
    rw [h_one] at hq
    apply Multiplicative.ofAdd.injective
    exact hq
  · intro h
    apply eₘ.injective
    have hnat := loopQuotContinuousMulEquivIntVector_at_matrixMap A x q
    rw [hnat]
    have h_one : eₘ (1 : QuotientFundamentalGroup.LoopQuot
        (Carrier m) (matrixMap A x)) = 1 := eₘ.map_one
    rw [h_one]
    apply Multiplicative.ext
    change matrixAction A (Multiplicative.toAdd (eₙ q)) = 0
    exact h

/-- Injectivity of the arbitrary-basepoint matrix quotient homomorphism is
exactly injectivity of the induced integer matrix action. -/
theorem matrixMapQuotientContinuousMulHomAt_injective_iff
    {n m : ℕ} (A : Fin m → Fin n → ℤ) (x : Carrier n) :
    Function.Injective (matrixMapQuotientContinuousMulHomAt A x) ↔
      Function.Injective (matrixAction A) := by
  let eₙ := loopQuotContinuousMulEquivIntVector_at n x
  let eₘ := loopQuotContinuousMulEquivIntVector_at m (matrixMap A x)
  constructor
  · intro hinj z w hzw
    let p := eₙ.symm (Multiplicative.ofAdd z)
    let q := eₙ.symm (Multiplicative.ofAdd w)
    have hmap :
        matrixMapQuotientContinuousMulHomAt A x p =
          matrixMapQuotientContinuousMulHomAt A x q := by
      apply eₘ.injective
      have hp := loopQuotContinuousMulEquivIntVector_at_matrixMap A x p
      have hq := loopQuotContinuousMulEquivIntVector_at_matrixMap A x q
      rw [hp, hq]
      apply Multiplicative.ext
      change matrixAction A (Multiplicative.toAdd (eₙ p)) =
        matrixAction A (Multiplicative.toAdd (eₙ q))
      simp [p, q, hzw]
    have hpq := hinj hmap
    have heq := congrArg (fun r => eₙ r) hpq
    have hvec := congrArg (fun r => Multiplicative.toAdd r) heq
    simpa [p, q] using hvec
  · intro hinj p q hmap
    apply eₙ.injective
    apply Multiplicative.ext
    apply hinj
    have hmap' := congrArg (fun r => eₘ r) hmap
    have hp := loopQuotContinuousMulEquivIntVector_at_matrixMap A x p
    have hq := loopQuotContinuousMulEquivIntVector_at_matrixMap A x q
    rw [hp, hq] at hmap'
    exact Multiplicative.ofAdd.injective hmap'

/-- Surjectivity of the arbitrary-basepoint matrix quotient homomorphism is
exactly surjectivity of the induced integer matrix action. -/
theorem matrixMapQuotientContinuousMulHomAt_surjective_iff
    {n m : ℕ} (A : Fin m → Fin n → ℤ) (x : Carrier n) :
    Function.Surjective (matrixMapQuotientContinuousMulHomAt A x) ↔
      Function.Surjective (matrixAction A) := by
  let eₙ := loopQuotContinuousMulEquivIntVector_at n x
  let eₘ := loopQuotContinuousMulEquivIntVector_at m (matrixMap A x)
  constructor
  · intro hsurj w
    obtain ⟨q, hq⟩ := hsurj (eₘ.symm (Multiplicative.ofAdd w))
    have hq' := congrArg (fun r => eₘ r) hq
    have hnat := loopQuotContinuousMulEquivIntVector_at_matrixMap A x q
    rw [hnat] at hq'
    rw [eₘ.apply_symm_apply] at hq'
    refine ⟨Multiplicative.toAdd (eₙ q), ?_⟩
    exact Multiplicative.ofAdd.injective hq'
  · intro hsurj q
    obtain ⟨z, hz⟩ := hsurj (Multiplicative.toAdd (eₘ q))
    refine ⟨eₙ.symm (Multiplicative.ofAdd z), ?_⟩
    apply eₘ.injective
    have hnat := loopQuotContinuousMulEquivIntVector_at_matrixMap A x
      (eₙ.symm (Multiplicative.ofAdd z))
    rw [hnat]
    apply Multiplicative.ext
    change matrixAction A
        (Multiplicative.toAdd (eₙ (eₙ.symm (Multiplicative.ofAdd z)))) =
      Multiplicative.toAdd (eₘ q)
    rw [eₙ.apply_symm_apply]
    exact hz

/-- At every basepoint, a square matrix induces an injective quotient
homomorphism exactly when its determinant is nonzero. -/
theorem matrixMapQuotientContinuousMulHomAt_injective_iff_det_ne_zero
    {n : ℕ} (A : Fin n → Fin n → ℤ) (x : Carrier n) :
    Function.Injective (matrixMapQuotientContinuousMulHomAt A x) ↔
      Matrix.det A ≠ 0 := by
  rw [matrixMapQuotientContinuousMulHomAt_injective_iff,
    matrixAction_injective_iff_det_ne_zero]

/-- At every basepoint, a square matrix induces a surjective quotient
homomorphism exactly when its determinant is a unit in `ℤ`. -/
theorem matrixMapQuotientContinuousMulHomAt_surjective_iff_isUnit_det
    {n : ℕ} (A : Fin n → Fin n → ℤ) (x : Carrier n) :
    Function.Surjective (matrixMapQuotientContinuousMulHomAt A x) ↔
      IsUnit (Matrix.det A) := by
  rw [matrixMapQuotientContinuousMulHomAt_surjective_iff,
    matrixAction_surjective_iff_isUnit_det]

/-- Matrix quotient maps compose contravariantly. -/
theorem matrixMapQuotientMap_comp {n m k : ℕ}
    (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ)
    (q : LoopQuot n) :
    matrixMapQuotientMap B (matrixMapQuotientMap A q) =
      matrixMapQuotientMap (matrixCompose A B) q := by
  apply (equivIntVector k).injective
  change encode (matrixMapQuotientMap B (matrixMapQuotientMap A q)) =
    encode (matrixMapQuotientMap (matrixCompose A B) q)
  rw [encode_matrixMapQuotientMap, encode_matrixMapQuotientMap,
    encode_matrixMapQuotientMap]
  exact matrixAction_comp A B (encode q)

/-- The identity matrix induces the identity quotient map. -/
theorem matrixMapQuotientMap_id {n : ℕ} (q : LoopQuot n) :
    matrixMapQuotientMap (matrixIdentity n) q = q := by
  apply (equivIntVector n).injective
  change encode (matrixMapQuotientMap (matrixIdentity n) q) = encode q
  rw [encode_matrixMapQuotientMap]
  exact matrixAction_id n (encode q)

/-- The image of a matrix quotient map is exactly the preimage of the lattice
image under the winding equivalence. -/
theorem matrixMapQuotientMap_mem_range_iff {n m : ℕ}
    (A : Fin m → Fin n → ℤ) (q : LoopQuot m) :
    q ∈ Set.range (matrixMapQuotientMap A) ↔
      encode q ∈ Set.range (matrixAction A) := by
  constructor
  · rintro ⟨p, rfl⟩
    rw [encode_matrixMapQuotientMap]
    exact ⟨encode p, rfl⟩
  · rintro ⟨z, hz⟩
    refine ⟨decode z, ?_⟩
    apply (equivIntVector m).injective
    change encode (matrixMapQuotientMap A (decode z)) = encode q
    rw [encode_matrixMapQuotientMap, encode_decode]
    exact hz

/-- The kernel of a matrix quotient map is the kernel of its winding-lattice
action. -/
theorem matrixMapQuotientMap_eq_zero_iff {n m : ℕ}
    (A : Fin m → Fin n → ℤ) (q : LoopQuot n) :
    matrixMapQuotientMap A q = (0 : LoopQuot m) ↔
      matrixAction A (encode q) = 0 := by
  constructor
  · intro h
    have h' := congrArg (fun r => encode r) h
    rw [encode_matrixMapQuotientMap] at h'
    have hm : encode (0 : LoopQuot m) = 0 :=
      (loopQuotAddEquivIntVector m).map_zero
    rw [hm] at h'
    exact h'
  · intro h
    apply (equivIntVector m).injective
    change encode (matrixMapQuotientMap A q) = encode (0 : LoopQuot m)
    rw [encode_matrixMapQuotientMap]
    have hm : encode (0 : LoopQuot m) = 0 :=
      (loopQuotAddEquivIntVector m).map_zero
    rw [hm]
    exact h

/-- Injectivity of a matrix quotient map is exactly injectivity of its integer
matrix action. -/
theorem matrixMapQuotientMap_injective_iff {n m : ℕ}
    (A : Fin m → Fin n → ℤ) :
    Function.Injective (matrixMapQuotientMap A) ↔
      Function.Injective (matrixAction A) := by
  constructor
  · intro hinj z w hzw
    let p : LoopQuot n := decode z
    let q : LoopQuot n := decode w
    have hmap : matrixMapQuotientMap A p = matrixMapQuotientMap A q := by
      apply (equivIntVector m).injective
      change encode (matrixMapQuotientMap A p) =
        encode (matrixMapQuotientMap A q)
      rw [encode_matrixMapQuotientMap, encode_matrixMapQuotientMap]
      simpa [p, q] using hzw
    have hpq := hinj hmap
    have hvec := congrArg (fun r => encode r) hpq
    simpa [p, q] using hvec
  · intro hinj p q hmap
    apply (equivIntVector n).injective
    change encode p = encode q
    apply hinj
    have hmap' := congrArg (fun r => encode r) hmap
    rw [encode_matrixMapQuotientMap, encode_matrixMapQuotientMap] at hmap'
    exact hmap'

/-- Surjectivity of a matrix quotient map is exactly surjectivity of its
integer matrix action. -/
theorem matrixMapQuotientMap_surjective_iff {n m : ℕ}
    (A : Fin m → Fin n → ℤ) :
    Function.Surjective (matrixMapQuotientMap A) ↔
      Function.Surjective (matrixAction A) := by
  constructor
  · intro hsurj w
    obtain ⟨q, hq⟩ := hsurj (decode w)
    have hq' := congrArg (fun r => encode r) hq
    rw [encode_matrixMapQuotientMap, encode_decode] at hq'
    exact ⟨encode q, hq'⟩
  · intro hsurj q
    obtain ⟨z, hz⟩ := hsurj (encode q)
    refine ⟨decode z, ?_⟩
    apply (equivIntVector m).injective
    change encode (matrixMapQuotientMap A (decode z)) = encode q
    rw [encode_matrixMapQuotientMap, encode_decode]
    exact hz

/-- For a square matrix, the canonical quotient action is injective exactly
when the matrix determinant is nonzero. -/
theorem matrixMapQuotientMap_injective_iff_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℤ) :
    Function.Injective (matrixMapQuotientMap A) ↔ Matrix.det A ≠ 0 := by
  rw [matrixMapQuotientMap_injective_iff,
    matrixAction_injective_iff_det_ne_zero]

/-- For a square matrix, the canonical quotient action is surjective exactly
when the determinant is a unit in `ℤ`. -/
theorem matrixMapQuotientMap_surjective_iff_isUnit_det {n : ℕ}
    (A : Fin n → Fin n → ℤ) :
    Function.Surjective (matrixMapQuotientMap A) ↔ IsUnit (Matrix.det A) := by
  rw [matrixMapQuotientMap_surjective_iff,
    matrixAction_surjective_iff_isUnit_det]

/-- Matrix quotient maps preserve the transported additive group law. -/
lemma matrixMapQuotientMap_map_zero {n m : ℕ}
    (A : Fin m → Fin n → ℤ) :
    matrixMapQuotientMap A (0 : LoopQuot n) = (0 : LoopQuot m) := by
  apply (equivIntVector m).injective
  change encode (matrixMapQuotientMap A (0 : LoopQuot n)) =
    encode (0 : LoopQuot m)
  rw [encode_matrixMapQuotientMap]
  have hn : encode (0 : LoopQuot n) = 0 :=
    (loopQuotAddEquivIntVector n).map_zero
  have hm : encode (0 : LoopQuot m) = 0 :=
    (loopQuotAddEquivIntVector m).map_zero
  rw [hn, hm]
  exact (matrixAction A).map_zero

lemma matrixMapQuotientMap_map_add {n m : ℕ}
    (A : Fin m → Fin n → ℤ) (x y : LoopQuot n) :
    matrixMapQuotientMap A (x + y) =
      matrixMapQuotientMap A x + matrixMapQuotientMap A y := by
  apply (equivIntVector m).injective
  change encode (matrixMapQuotientMap A (x + y)) =
    encode (matrixMapQuotientMap A x + matrixMapQuotientMap A y)
  rw [encode_matrixMapQuotientMap]
  have hxy : encode (x + y) = encode x + encode y :=
    (loopQuotAddEquivIntVector n).map_add x y
  have hmap :
      encode (matrixMapQuotientMap A x + matrixMapQuotientMap A y) =
        encode (matrixMapQuotientMap A x) +
          encode (matrixMapQuotientMap A y) :=
    (loopQuotAddEquivIntVector m).map_add _ _
  rw [hxy, hmap, encode_matrixMapQuotientMap,
    encode_matrixMapQuotientMap]
  exact (matrixAction A).map_add _ _

/-- The quotient action of an explicit two-sided matrix inverse is an
equivalence of based finite-torus loop classes. -/
noncomputable def matrixMapQuotientEquivOfInverse {n m : ℕ}
    (A : Fin m → Fin n → ℤ) (B : Fin n → Fin m → ℤ)
    (hAB : matrixCompose A B = matrixIdentity n)
    (hBA : matrixCompose B A = matrixIdentity m) :
    LoopQuot n ≃ LoopQuot m where
  toFun := matrixMapQuotientMap A
  invFun := matrixMapQuotientMap B
  left_inv := by
    intro q
    have hcomp := matrixMapQuotientMap_comp A B q
    rw [hAB, matrixMapQuotientMap_id] at hcomp
    exact hcomp
  right_inv := by
    intro q
    have hcomp := matrixMapQuotientMap_comp B A q
    rw [hBA, matrixMapQuotientMap_id] at hcomp
    exact hcomp

/-- The quotient equivalence from an explicit matrix inverse is a
homeomorphism for the discrete quotient topologies. -/
noncomputable def matrixMapQuotientHomeomorphOfInverse {n m : ℕ}
    (A : Fin m → Fin n → ℤ) (B : Fin n → Fin m → ℤ)
    (hAB : matrixCompose A B = matrixIdentity n)
    (hBA : matrixCompose B A = matrixIdentity m) :
    LoopQuot n ≃ₜ LoopQuot m where
  toEquiv := matrixMapQuotientEquivOfInverse A B hAB hBA
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- The inverse quotient action is a continuous additive equivalence for the
transported winding-group structures. -/
noncomputable def matrixMapQuotientContinuousAddEquivOfInverse {n m : ℕ}
    (A : Fin m → Fin n → ℤ) (B : Fin n → Fin m → ℤ)
    (hAB : matrixCompose A B = matrixIdentity n)
    (hBA : matrixCompose B A = matrixIdentity m) :
    LoopQuot n ≃ₜ+ LoopQuot m where
  toEquiv := matrixMapQuotientEquivOfInverse A B hAB hBA
  map_add' := matrixMapQuotientMap_map_add A
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- The canonical quotient equivalence induced by a unimodular square
matrix. -/
noncomputable def matrixMapQuotientEquivOfDetUnit {n : ℕ}
    (A : Fin n → Fin n → ℤ) (hA : IsUnit (Matrix.det A)) :
    LoopQuot n ≃ LoopQuot n :=
  matrixMapQuotientEquivOfInverse A (matrixNonsingInv A)
    (matrixCompose_nonsingInv_mul_of_det_unit A hA)
    (matrixCompose_mul_nonsingInv_of_det_unit A hA)

/-- A unimodular square matrix induces a homeomorphism of the discrete
finite-torus loop-class quotient. -/
noncomputable def matrixMapQuotientHomeomorphOfDetUnit {n : ℕ}
    (A : Fin n → Fin n → ℤ) (hA : IsUnit (Matrix.det A)) :
    LoopQuot n ≃ₜ LoopQuot n :=
  matrixMapQuotientHomeomorphOfInverse A (matrixNonsingInv A)
    (matrixCompose_nonsingInv_mul_of_det_unit A hA)
    (matrixCompose_mul_nonsingInv_of_det_unit A hA)

/-- The unimodular quotient action is a continuous additive equivalence for
the transported winding-group structure. -/
noncomputable def matrixMapQuotientContinuousAddEquivOfDetUnit {n : ℕ}
    (A : Fin n → Fin n → ℤ) (hA : IsUnit (Matrix.det A)) :
    LoopQuot n ≃ₜ+ LoopQuot n :=
  matrixMapQuotientContinuousAddEquivOfInverse A (matrixNonsingInv A)
    (matrixCompose_nonsingInv_mul_of_det_unit A hA)
    (matrixCompose_mul_nonsingInv_of_det_unit A hA)

noncomputable def matrixMapQuotientAddHom {n m : ℕ}
    (A : Fin m → Fin n → ℤ) : LoopQuot n →+ LoopQuot m where
  toFun := matrixMapQuotientMap A
  map_zero' := matrixMapQuotientMap_map_zero A
  map_add' := matrixMapQuotientMap_map_add A

@[simp] theorem matrixMapQuotientAddHom_apply {n m : ℕ}
    (A : Fin m → Fin n → ℤ) (q : LoopQuot n) :
    matrixMapQuotientAddHom A q = matrixMapQuotientMap A q :=
  rfl

/-- The rectangular finite-torus quotient maps inherit the additive cokernel
sequence for arbitrary composable dimensions.  Injectivity of the second
quotient action is the exact hypothesis needed for the first map. -/
theorem matrixMapQuotientAddHom_rectangular_cokernel_shortExact_of_injective
    {n m k : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ)
    (hB : Function.Injective (matrixMapQuotientAddHom B)) :
    ∃ f : LoopQuot m ⧸ (matrixMapQuotientAddHom A).range →+
          LoopQuot k ⧸
            ((matrixMapQuotientAddHom B).comp
              (matrixMapQuotientAddHom A)).range,
    ∃ g : LoopQuot k ⧸
          ((matrixMapQuotientAddHom B).comp
            (matrixMapQuotientAddHom A)).range →+
          LoopQuot k ⧸ (matrixMapQuotientAddHom B).range,
    ∃ e : ((LoopQuot k ⧸
          ((matrixMapQuotientAddHom B).comp
            (matrixMapQuotientAddHom A)).range) ⧸ g.ker) ≃+
          LoopQuot k ⧸ (matrixMapQuotientAddHom B).range,
      Function.Injective f ∧ g.ker = f.range ∧ Function.Surjective g := by
  refine ⟨addCokernelCompMap (matrixMapQuotientAddHom A)
      (matrixMapQuotientAddHom B),
    addCokernelCompProjection (matrixMapQuotientAddHom A)
      (matrixMapQuotientAddHom B),
    addCokernelCompProjection_quotientKerEquiv
      (matrixMapQuotientAddHom A) (matrixMapQuotientAddHom B), ?_⟩
  exact addCokernelComp_shortExact_of_injective
    (matrixMapQuotientAddHom A) (matrixMapQuotientAddHom B) hB

/-- Injectivity of the rectangular winding action is transported directly to
the corresponding finite-torus quotient cokernel sequence. -/
theorem matrixMapQuotientAddHom_rectangular_cokernel_shortExact_of_matrixAction_injective
    {n m k : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ)
    (hB : Function.Injective (matrixAction B)) :
    ∃ f : LoopQuot m ⧸ (matrixMapQuotientAddHom A).range →+
          LoopQuot k ⧸
            ((matrixMapQuotientAddHom B).comp
              (matrixMapQuotientAddHom A)).range,
    ∃ g : LoopQuot k ⧸
          ((matrixMapQuotientAddHom B).comp
            (matrixMapQuotientAddHom A)).range →+
          LoopQuot k ⧸ (matrixMapQuotientAddHom B).range,
    ∃ e : ((LoopQuot k ⧸
          ((matrixMapQuotientAddHom B).comp
            (matrixMapQuotientAddHom A)).range) ⧸ g.ker) ≃+
          LoopQuot k ⧸ (matrixMapQuotientAddHom B).range,
      Function.Injective f ∧ g.ker = f.range ∧ Function.Surjective g := by
  apply matrixMapQuotientAddHom_rectangular_cokernel_shortExact_of_injective
    A B
  change Function.Injective (matrixMapQuotientMap B)
  exact (matrixMapQuotientMap_injective_iff B).mpr hB

/-- The rectangular topological cokernel embedding has the same exact
preimage-of-image injectivity criterion. -/
theorem matrixMapQuotientAddHom_rectangular_cokernel_compMap_injective_iff
    {n m k : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ) :
    Function.Injective
        (addCokernelCompMap (matrixMapQuotientAddHom A)
          (matrixMapQuotientAddHom B)) ↔
      AddSubgroup.comap (matrixMapQuotientAddHom B)
          ((matrixMapQuotientAddHom B).comp
            (matrixMapQuotientAddHom A)).range =
        (matrixMapQuotientAddHom A).range := by
  exact addCokernelCompMap_injective_iff
    (matrixMapQuotientAddHom A) (matrixMapQuotientAddHom B)

/-- The winding equivalence identifies the image of every integer-matrix
quotient map with the corresponding lattice image, as additive subgroups.
Unlike the determinant-index corollary below, this transport does not require
the matrix to be square or nonsingular. -/
theorem matrixMapQuotientAddHom_range_map {n m : ℕ}
    (A : Fin m → Fin n → ℤ) :
    (matrixMapQuotientAddHom A).range.map
        (loopQuotAddEquivIntVector m : LoopQuot m →+ (Fin m → ℤ)) =
      (matrixAction A).range := by
  ext z
  constructor
  · intro hz
    rw [AddSubgroup.mem_map] at hz
    rcases hz with ⟨p, hp, hpeq⟩
    rcases hp with ⟨q, hq⟩
    refine ⟨loopQuotAddEquivIntVector n q, ?_⟩
    rw [← hpeq, ← hq]
    change matrixAction A (loopQuotAddEquivIntVector n q) =
      loopQuotAddEquivIntVector m (matrixMapQuotientAddHom A q)
    rw [matrixMapQuotientAddHom_apply]
    exact (encode_matrixMapQuotientMap A q).symm
  · intro hz
    rcases hz with ⟨v, rfl⟩
    refine ⟨matrixMapQuotientAddHom A
        ((loopQuotAddEquivIntVector n).symm v),
      ⟨(loopQuotAddEquivIntVector n).symm v, rfl⟩, ?_⟩
    have hnat := encode_matrixMapQuotientMap A
      ((loopQuotAddEquivIntVector n).symm v)
    have hev : loopQuotAddEquivIntVector n
        ((loopQuotAddEquivIntVector n).symm v) = v :=
      (loopQuotAddEquivIntVector n).apply_symm_apply v
    calc
      loopQuotAddEquivIntVector m
          (matrixMapQuotientAddHom A
            ((loopQuotAddEquivIntVector n).symm v)) =
          matrixAction A
            (loopQuotAddEquivIntVector n
              ((loopQuotAddEquivIntVector n).symm v)) := by
        change encode (matrixMapQuotientMap A
            ((loopQuotAddEquivIntVector n).symm v)) =
          matrixAction A (encode
            ((loopQuotAddEquivIntVector n).symm v))
        exact hnat
      _ = matrixAction A v := by rw [hev]

/-! The subgroup-level range calculation lifts to a quotient equivalence for
every rectangular matrix.  This is the structural winding transport used by
the square Smith-normal-form corollaries below, but it does not require a
determinant or a dimension equality. -/

/-- The winding equivalence transports the finite-torus cokernel of every
rectangular matrix to the corresponding integer-lattice cokernel. -/
noncomputable def matrixMapQuotientAddHom_cokernel_windingEquiv
    {n m : ℕ} (A : Fin m → Fin n → ℤ) :
    (LoopQuot m ⧸ (matrixMapQuotientAddHom A).range) ≃+
      ((Fin m → ℤ) ⧸ (matrixAction A).range) := by
  exact QuotientAddGroup.congr
    (matrixMapQuotientAddHom A).range (matrixAction A).range
    (loopQuotAddEquivIntVector m)
    (matrixMapQuotientAddHom_range_map A)

@[simp] theorem matrixMapQuotientAddHom_cokernel_windingEquiv_apply_mk
    {n m : ℕ} (A : Fin m → Fin n → ℤ) (q : LoopQuot m) :
    matrixMapQuotientAddHom_cokernel_windingEquiv A
        (QuotientAddGroup.mk'
          (matrixMapQuotientAddHom A).range q) =
      QuotientAddGroup.mk' (matrixAction A).range
        (loopQuotAddEquivIntVector m q) := by
  rfl

/-- The rectangular finite-torus and lattice cokernels have the same
cardinality, including the infinite case. -/
theorem matrixMapQuotientAddHom_cokernel_card_eq_matrixAction_cokernel
    {n m : ℕ} (A : Fin m → Fin n → ℤ) :
    Nat.card (LoopQuot m ⧸ (matrixMapQuotientAddHom A).range) =
      Nat.card ((Fin m → ℤ) ⧸ (matrixAction A).range) := by
  exact Nat.card_congr
    (matrixMapQuotientAddHom_cokernel_windingEquiv A).toEquiv

/-- Finiteness of a rectangular finite-torus cokernel is equivalent to
finiteness of its lattice cokernel. -/
theorem matrixMapQuotientAddHom_cokernel_finite_iff_matrixAction_cokernel
    {n m : ℕ} (A : Fin m → Fin n → ℤ) :
    Finite (LoopQuot m ⧸ (matrixMapQuotientAddHom A).range) ↔
      Finite ((Fin m → ℤ) ⧸ (matrixAction A).range) := by
  exact Equiv.finite_iff
    (matrixMapQuotientAddHom_cokernel_windingEquiv A).toEquiv

/-- The image of a square matrix on quotient loop classes has the same finite
index as its winding-lattice image. -/
theorem matrixMapQuotientAddHom_range_index_eq_natAbs_det {n : ℕ}
    (A : Fin n → Fin n → ℤ) (hA : Matrix.det A ≠ 0) :
    (matrixMapQuotientAddHom A).range.index = Int.natAbs (Matrix.det A) := by
  let e := loopQuotAddEquivIntVector n
  have hmap :
      (matrixMapQuotientAddHom A).range.map (e : LoopQuot n →+ (Fin n → ℤ)) =
        (matrixAction A).range := by
    exact matrixMapQuotientAddHom_range_map A
  have hi := AddSubgroup.index_map_equiv
      (matrixMapQuotientAddHom A).range e
  rw [hmap] at hi
  rw [← hi]
  rw [AddSubgroup.index_eq_card]
  let N : Submodule ℤ (Fin n → ℤ) := AddSubgroup.toIntSubmodule (matrixAction A).range
  let eQ : ((Fin n → ℤ) ⧸ (matrixAction A).range) ≃
      ((Fin n → ℤ) ⧸ N) :=
    Quotient.congr (Equiv.refl _) (by
      intro x y
      simp only [Equiv.refl_apply, QuotientAddGroup.leftRel_apply,
        Submodule.quotientRel_def]
      change -x + y ∈ (matrixAction A).range ↔ x - y ∈ (matrixAction A).range
      constructor
      · rintro ⟨z, hz⟩
        refine ⟨-z, ?_⟩
        rw [(matrixAction A).map_neg]
        simpa [sub_eq_add_neg, add_comm] using congrArg Neg.neg hz
      · rintro ⟨z, hz⟩
        refine ⟨-z, ?_⟩
        rw [(matrixAction A).map_neg]
        simpa [sub_eq_add_neg, add_comm] using congrArg Neg.neg hz)
  rw [Nat.card_congr eQ]
  simpa [N] using (matrixAction_cokernel_card_eq_natAbs_det A hA)

/-- The quotient of the finite-torus loop group by a non-singular matrix image
has cardinality `natAbs (det A)`. -/
theorem matrixMapQuotientAddHom_cokernel_card_eq_natAbs_det {n : ℕ}
    (A : Fin n → Fin n → ℤ) (hA : Matrix.det A ≠ 0) :
    Nat.card (LoopQuot n ⧸ (matrixMapQuotientAddHom A).range) =
      Int.natAbs (Matrix.det A) := by
  calc
    Nat.card (LoopQuot n ⧸ (matrixMapQuotientAddHom A).range) =
        (matrixMapQuotientAddHom A).range.index :=
      (AddSubgroup.index_eq_card _).symm
    _ = Int.natAbs (Matrix.det A) :=
      matrixMapQuotientAddHom_range_index_eq_natAbs_det A hA

/-- The topological quotient obstruction has the same multiplicative index
law under composition of non-singular square matrix maps. -/
theorem matrixMapQuotientAddHom_cokernel_card_comp {n : ℕ}
    (A B : Fin n → Fin n → ℤ)
    (hA : Matrix.det A ≠ 0) (hB : Matrix.det B ≠ 0) :
    Nat.card (LoopQuot n ⧸
        (matrixMapQuotientAddHom (matrixCompose A B)).range) =
      Int.natAbs (Matrix.det A) * Int.natAbs (Matrix.det B) := by
  rw [matrixMapQuotientAddHom_cokernel_card_eq_natAbs_det (matrixCompose A B)]
  · rw [matrixCompose_det, Int.natAbs_mul]
    exact Nat.mul_comm _ _
  · rw [matrixCompose_det]
    exact mul_ne_zero hB hA

/-- Composition induces the canonical additive map from the topological
quotient cokernel of `A` into that of `B ∘ A`. -/
noncomputable def matrixMapQuotientAddHom_cokernel_compMap {n : ℕ}
    (A B : Fin n → Fin n → ℤ) :
    LoopQuot n ⧸ (matrixMapQuotientAddHom A).range →+
      LoopQuot n ⧸ (matrixMapQuotientAddHom (matrixCompose A B)).range := by
  let N : AddSubgroup (LoopQuot n) := (matrixMapQuotientAddHom A).range
  let M : AddSubgroup (LoopQuot n) :=
    (matrixMapQuotientAddHom (matrixCompose A B)).range
  have hNM : N ≤ AddSubgroup.comap (matrixMapQuotientAddHom B) M := by
    intro q hq
    rw [AddSubgroup.mem_comap]
    rcases (AddMonoidHom.mem_range).mp hq with ⟨w, hw⟩
    rw [AddMonoidHom.mem_range]
    refine ⟨w, ?_⟩
    rw [← hw]
    have hcomp : matrixMapQuotientAddHom (matrixCompose A B) w =
        matrixMapQuotientAddHom B (matrixMapQuotientAddHom A w) := by
      change matrixMapQuotientMap (matrixCompose A B) w =
        matrixMapQuotientMap B (matrixMapQuotientMap A w)
      exact (matrixMapQuotientMap_comp A B w).symm
    exact hcomp
  exact QuotientAddGroup.map N M (matrixMapQuotientAddHom B) hNM

/-- If `B` has nonzero determinant, the topological quotient cokernel map
induced by composition is injective. -/
theorem matrixMapQuotientAddHom_cokernel_compMap_injective_of_det_ne_zero
    {n : ℕ} (A B : Fin n → Fin n → ℤ) (hB : Matrix.det B ≠ 0) :
    Function.Injective (matrixMapQuotientAddHom_cokernel_compMap A B) := by
  let N : AddSubgroup (LoopQuot n) := (matrixMapQuotientAddHom A).range
  let M : AddSubgroup (LoopQuot n) :=
    (matrixMapQuotientAddHom (matrixCompose A B)).range
  have hNM : N ≤ AddSubgroup.comap (matrixMapQuotientAddHom B) M := by
    intro q hq
    rw [AddSubgroup.mem_comap]
    rcases (AddMonoidHom.mem_range).mp hq with ⟨w, hw⟩
    rw [AddMonoidHom.mem_range]
    refine ⟨w, ?_⟩
    rw [← hw]
    have hcomp : matrixMapQuotientAddHom (matrixCompose A B) w =
        matrixMapQuotientAddHom B (matrixMapQuotientAddHom A w) := by
      change matrixMapQuotientMap (matrixCompose A B) w =
        matrixMapQuotientMap B (matrixMapQuotientMap A w)
      exact (matrixMapQuotientMap_comp A B w).symm
    exact hcomp
  intro x y hxy
  obtain ⟨x', rfl⟩ := QuotientAddGroup.mk'_surjective N x
  obtain ⟨y', rfl⟩ := QuotientAddGroup.mk'_surjective N y
  change (QuotientAddGroup.map N M (matrixMapQuotientAddHom B) hNM)
      ((QuotientAddGroup.mk' N) x') =
    (QuotientAddGroup.map N M (matrixMapQuotientAddHom B) hNM)
      ((QuotientAddGroup.mk' N) y') at hxy
  rw [QuotientAddGroup.map_mk' N M (matrixMapQuotientAddHom B) hNM x',
    QuotientAddGroup.map_mk' N M (matrixMapQuotientAddHom B) hNM y'] at hxy
  change (x' : LoopQuot n ⧸ N) = (y' : LoopQuot n ⧸ N)
  rw [QuotientAddGroup.eq_iff_sub_mem] at hxy ⊢
  rcases hxy with ⟨z, hz⟩
  rw [AddMonoidHom.mem_range]
  refine ⟨z, ?_⟩
  have hB_inj : Function.Injective (matrixMapQuotientAddHom B) :=
    (matrixMapQuotientMap_injective_iff_det_ne_zero B).mpr hB
  have hzero : matrixMapQuotientAddHom B
      (x' - y' - matrixMapQuotientAddHom A z) = 0 := by
    rw [map_sub, map_sub]
    have hcomp : matrixMapQuotientAddHom (matrixCompose A B) z =
        matrixMapQuotientAddHom B (matrixMapQuotientAddHom A z) :=
      by
        change matrixMapQuotientMap (matrixCompose A B) z =
          matrixMapQuotientMap B (matrixMapQuotientMap A z)
        exact (matrixMapQuotientMap_comp A B z).symm
    rw [← hcomp, hz]
    simp
  have hEq : x' - y' - matrixMapQuotientAddHom A z = 0 := by
    apply hB_inj
    simpa only [map_zero] using hzero
  have hrel : x' - y' = matrixMapQuotientAddHom A z := by
    exact sub_eq_zero.mp hEq
  rw [hrel]

/-- The composition cokernel map onto the cokernel of `B` is induced by the
identity on the topological loop-class quotient. -/
noncomputable def matrixMapQuotientAddHom_cokernel_compProjection {n : ℕ}
    (A B : Fin n → Fin n → ℤ) :
    LoopQuot n ⧸
        (matrixMapQuotientAddHom (matrixCompose A B)).range →+
      LoopQuot n ⧸ (matrixMapQuotientAddHom B).range := by
  let N : AddSubgroup (LoopQuot n) :=
    (matrixMapQuotientAddHom (matrixCompose A B)).range
  let M : AddSubgroup (LoopQuot n) := (matrixMapQuotientAddHom B).range
  have hNM : N ≤ AddSubgroup.comap (AddMonoidHom.id (LoopQuot n)) M := by
    intro q hq
    rw [AddSubgroup.mem_comap]
    rcases (AddMonoidHom.mem_range).mp hq with ⟨w, hw⟩
    rw [AddMonoidHom.mem_range]
    refine ⟨matrixMapQuotientAddHom A w, ?_⟩
    have hcomp : matrixMapQuotientAddHom (matrixCompose A B) w =
        matrixMapQuotientAddHom B (matrixMapQuotientAddHom A w) := by
      change matrixMapQuotientMap (matrixCompose A B) w =
        matrixMapQuotientMap B (matrixMapQuotientMap A w)
      exact (matrixMapQuotientMap_comp A B w).symm
    simpa only [AddMonoidHom.id_apply] using hcomp.symm.trans hw
  exact QuotientAddGroup.map N M (AddMonoidHom.id (LoopQuot n)) hNM

/-- The projection from the topological cokernel of `B ∘ A` to the cokernel
of `B` is surjective. -/
theorem matrixMapQuotientAddHom_cokernel_compProjection_surjective
    {n : ℕ} (A B : Fin n → Fin n → ℤ) :
    Function.Surjective
      (matrixMapQuotientAddHom_cokernel_compProjection A B) := by
  let N : AddSubgroup (LoopQuot n) :=
    (matrixMapQuotientAddHom (matrixCompose A B)).range
  let M : AddSubgroup (LoopQuot n) := (matrixMapQuotientAddHom B).range
  have hNM : N ≤ AddSubgroup.comap (AddMonoidHom.id (LoopQuot n)) M := by
    intro q hq
    rw [AddSubgroup.mem_comap]
    rcases (AddMonoidHom.mem_range).mp hq with ⟨w, hw⟩
    rw [AddMonoidHom.mem_range]
    refine ⟨matrixMapQuotientAddHom A w, ?_⟩
    have hcomp : matrixMapQuotientAddHom (matrixCompose A B) w =
        matrixMapQuotientAddHom B (matrixMapQuotientAddHom A w) := by
      change matrixMapQuotientMap (matrixCompose A B) w =
        matrixMapQuotientMap B (matrixMapQuotientMap A w)
      exact (matrixMapQuotientMap_comp A B w).symm
    simpa only [AddMonoidHom.id_apply] using hcomp.symm.trans hw
  intro y
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective M y
  refine ⟨(QuotientAddGroup.mk' N) v, ?_⟩
  change (QuotientAddGroup.map N M (AddMonoidHom.id (LoopQuot n)) hNM)
      ((QuotientAddGroup.mk' N) v) = (QuotientAddGroup.mk' M) v
  rw [QuotientAddGroup.map_mk' N M (AddMonoidHom.id (LoopQuot n)) hNM v]
  rfl

/-- The kernel of the topological projection onto the cokernel of `B` is
exactly the image of the composition map from the cokernel of `A`. -/
theorem matrixMapQuotientAddHom_cokernel_compProjection_ker_eq_range
    {n : ℕ} (A B : Fin n → Fin n → ℤ) :
    (matrixMapQuotientAddHom_cokernel_compProjection A B).ker =
      (matrixMapQuotientAddHom_cokernel_compMap A B).range := by
  let NA : AddSubgroup (LoopQuot n) := (matrixMapQuotientAddHom A).range
  let N : AddSubgroup (LoopQuot n) :=
    (matrixMapQuotientAddHom (matrixCompose A B)).range
  let M : AddSubgroup (LoopQuot n) := (matrixMapQuotientAddHom B).range
  have hNM : NA ≤ AddSubgroup.comap (matrixMapQuotientAddHom B) N := by
    intro q hq
    rw [AddSubgroup.mem_comap]
    rcases (AddMonoidHom.mem_range).mp hq with ⟨w, hw⟩
    rw [AddMonoidHom.mem_range]
    refine ⟨w, ?_⟩
    rw [← hw]
    have hcomp : matrixMapQuotientAddHom (matrixCompose A B) w =
        matrixMapQuotientAddHom B (matrixMapQuotientAddHom A w) := by
      change matrixMapQuotientMap (matrixCompose A B) w =
        matrixMapQuotientMap B (matrixMapQuotientMap A w)
      exact (matrixMapQuotientMap_comp A B w).symm
    exact hcomp
  have hNP : N ≤ AddSubgroup.comap (AddMonoidHom.id (LoopQuot n)) M := by
    intro q hq
    rw [AddSubgroup.mem_comap]
    rcases (AddMonoidHom.mem_range).mp hq with ⟨w, hw⟩
    rw [AddMonoidHom.mem_range]
    refine ⟨matrixMapQuotientAddHom A w, ?_⟩
    have hcomp : matrixMapQuotientAddHom (matrixCompose A B) w =
        matrixMapQuotientAddHom B (matrixMapQuotientAddHom A w) := by
      change matrixMapQuotientMap (matrixCompose A B) w =
        matrixMapQuotientMap B (matrixMapQuotientMap A w)
      exact (matrixMapQuotientMap_comp A B w).symm
    simpa only [AddMonoidHom.id_apply] using hcomp.symm.trans hw
  have hcomp :
      (matrixMapQuotientAddHom_cokernel_compProjection A B).comp
          (matrixMapQuotientAddHom_cokernel_compMap A B) = 0 := by
    apply AddMonoidHom.ext
    intro q
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective NA q
    change (QuotientAddGroup.map N M (AddMonoidHom.id (LoopQuot n)) hNP)
        ((QuotientAddGroup.map NA N (matrixMapQuotientAddHom B) hNM)
          ((QuotientAddGroup.mk' NA) z)) = 0
    rw [QuotientAddGroup.map_mk' NA N (matrixMapQuotientAddHom B) hNM z]
    change (QuotientAddGroup.map N M (AddMonoidHom.id (LoopQuot n)) hNP)
      ((QuotientAddGroup.mk' N) (matrixMapQuotientAddHom B z)) = 0
    rw [QuotientAddGroup.map_mk' N M (AddMonoidHom.id (LoopQuot n)) hNP]
    change (QuotientAddGroup.mk' M) (matrixMapQuotientAddHom B z) = 0
    change ((matrixMapQuotientAddHom B z : LoopQuot n) :
      LoopQuot n ⧸ M) = ((0 : LoopQuot n) : LoopQuot n ⧸ M)
    rw [QuotientAddGroup.eq_iff_sub_mem]
    simp only [sub_zero]
    exact (AddMonoidHom.mem_range).mpr ⟨z, rfl⟩
  ext q
  constructor
  · intro hq
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective N q
    change (QuotientAddGroup.map N M (AddMonoidHom.id (LoopQuot n)) hNP)
        ((QuotientAddGroup.mk' N) x) = 0 at hq
    rw [QuotientAddGroup.map_mk' N M (AddMonoidHom.id (LoopQuot n)) hNP] at hq
    change (x : LoopQuot n ⧸ M) = 0 at hq
    have hx : x ∈ M := by
      have := (QuotientAddGroup.eq_iff_sub_mem).mp hq
      simpa only [sub_zero] using this
    rcases (AddMonoidHom.mem_range).mp hx with ⟨z, hz⟩
    refine ⟨(QuotientAddGroup.mk' NA) z, ?_⟩
    change (QuotientAddGroup.map NA N (matrixMapQuotientAddHom B) hNM)
        ((QuotientAddGroup.mk' NA) z) = (QuotientAddGroup.mk' N) x
    rw [QuotientAddGroup.map_mk' NA N (matrixMapQuotientAddHom B) hNM z]
    exact congrArg (QuotientAddGroup.mk' N) hz
  · intro hq
    rcases hq with ⟨qA, rfl⟩
    change (matrixMapQuotientAddHom_cokernel_compProjection A B)
        ((matrixMapQuotientAddHom_cokernel_compMap A B) qA) = 0
    have hcomp_q := congrArg
      (fun F : (LoopQuot n ⧸ NA) →+ (LoopQuot n ⧸ M) => F qA) hcomp
    simpa only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply] using hcomp_q

/-- The topological cokernels of a composable pair form a short exact
sequence: the composition embedding is injective when `det B ≠ 0`, its image
is the projection kernel, and the projection is surjective. -/
theorem matrixMapQuotientAddHom_cokernel_comp_shortExact_of_det_ne_zero
    {n : ℕ} (A B : Fin n → Fin n → ℤ) (hB : Matrix.det B ≠ 0) :
    Function.Injective (matrixMapQuotientAddHom_cokernel_compMap A B) ∧
      (matrixMapQuotientAddHom_cokernel_compProjection A B).ker =
        (matrixMapQuotientAddHom_cokernel_compMap A B).range ∧
      Function.Surjective
        (matrixMapQuotientAddHom_cokernel_compProjection A B) :=
  ⟨matrixMapQuotientAddHom_cokernel_compMap_injective_of_det_ne_zero A B hB,
    matrixMapQuotientAddHom_cokernel_compProjection_ker_eq_range A B,
    matrixMapQuotientAddHom_cokernel_compProjection_surjective A B⟩

/-- The first-isomorphism quotient of the topological composition cokernel
sequence is canonically the topological quotient cokernel of `B`. -/
noncomputable def matrixMapQuotientAddHom_cokernel_compProjection_quotientKerEquiv
    {n : ℕ} (A B : Fin n → Fin n → ℤ) :
    (LoopQuot n ⧸
        (matrixMapQuotientAddHom (matrixCompose A B)).range) ⧸
        (matrixMapQuotientAddHom_cokernel_compProjection A B).ker ≃+
      LoopQuot n ⧸ (matrixMapQuotientAddHom B).range :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    (matrixMapQuotientAddHom_cokernel_compProjection A B)
    (matrixMapQuotientAddHom_cokernel_compProjection_surjective A B)

@[simp] theorem matrixMapQuotientAddHom_cokernel_compProjection_quotientKerEquiv_apply_mk
    {n : ℕ} (A B : Fin n → Fin n → ℤ)
    (q : LoopQuot n ⧸
        (matrixMapQuotientAddHom (matrixCompose A B)).range) :
    matrixMapQuotientAddHom_cokernel_compProjection_quotientKerEquiv A B
        (QuotientAddGroup.mk'
          (matrixMapQuotientAddHom_cokernel_compProjection A B).ker q) =
      matrixMapQuotientAddHom_cokernel_compProjection A B q := by
  exact QuotientAddGroup.kerLift_mk
    (matrixMapQuotientAddHom_cokernel_compProjection A B) q

/-- The canonical topological quotient cokernel is an abelian group with the
same Smith-normal-form decomposition as the winding-lattice cokernel. -/
noncomputable def matrixMapQuotientAddHom_cokernel_smithAddEquivOfDetNeZero
    {n : ℕ} (A : Fin n → Fin n → ℤ) (hA : Matrix.det A ≠ 0) :
    (LoopQuot n ⧸ (matrixMapQuotientAddHom A).range) ≃+
      (∀ i : Fin n, ZMod ((Submodule.smithNormalFormCoeffs
        (Pi.basisFun ℤ (Fin n)) (matrixAction_cokernel_full_rank A hA) i).natAbs)) := by
  let H := (matrixMapQuotientAddHom A).range
  have hmap :
      H.map (loopQuotAddEquivIntVector n : LoopQuot n →+ (Fin n → ℤ)) =
        (matrixAction A).range :=
    matrixMapQuotientAddHom_range_map A
  let qAddEquiv :
      (LoopQuot n ⧸ H) ≃+
        ((Fin n → ℤ) ⧸ (matrixAction A).range) := by
    exact QuotientAddGroup.congr H (matrixAction A).range
      (loopQuotAddEquivIntVector n) hmap
  exact qAddEquiv.trans (matrixAction_cokernel_smithEquivOfDetNeZero A hA)

/-- The rectangular finite-torus cokernel inherits the Smith-normal-form
product whenever the matrix image has full target rank. -/
noncomputable def matrixMapQuotientAddHom_cokernel_smithAddEquivOfFullRank
    {n m : ℕ} (A : Fin m → Fin n → ℤ)
    (hA : Module.finrank ℤ ((matrixAction A).range.toIntSubmodule) =
      Module.finrank ℤ (Fin m → ℤ)) :
    (LoopQuot m ⧸ (matrixMapQuotientAddHom A).range) ≃+
      (∀ i : Fin m, ZMod ((Submodule.smithNormalFormCoeffs
        (Pi.basisFun ℤ (Fin m)) hA i).natAbs)) := by
  let H := (matrixMapQuotientAddHom A).range
  have hmap :
      H.map (loopQuotAddEquivIntVector m : LoopQuot m →+ (Fin m → ℤ)) =
        (matrixAction A).range :=
    matrixMapQuotientAddHom_range_map A
  let qAddEquiv :
      (LoopQuot m ⧸ H) ≃+
        ((Fin m → ℤ) ⧸ (matrixAction A).range) := by
    exact QuotientAddGroup.congr H (matrixAction A).range
      (loopQuotAddEquivIntVector m) hmap
  exact qAddEquiv.trans (matrixAction_cokernel_smithEquivOfFullRank A hA)

/-- The rectangular finite-torus cokernel has the same arbitrary-rank Smith
normal form as the winding-lattice cokernel.  Zero factors retain the free
part, while nonzero factors describe the finite torsion obstruction. -/
noncomputable def matrixMapQuotientAddHom_cokernel_smithAddEquiv
    {n m : ℕ} (A : Fin m → Fin n → ℤ) :
    (LoopQuot m ⧸ (matrixMapQuotientAddHom A).range) ≃+
      (∀ i : Fin m, ZMod (smithNormalFormFactor
        (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
          (matrixAction A).range.toIntSubmodule).2 i).natAbs) := by
  let H := (matrixMapQuotientAddHom A).range
  have hmap :
      H.map (loopQuotAddEquivIntVector m : LoopQuot m →+ (Fin m → ℤ)) =
        (matrixAction A).range :=
    matrixMapQuotientAddHom_range_map A
  let qAddEquiv :
      (LoopQuot m ⧸ H) ≃+
        ((Fin m → ℤ) ⧸ (matrixAction A).range) := by
    exact QuotientAddGroup.congr H (matrixAction A).range
      (loopQuotAddEquivIntVector m) hmap
  exact qAddEquiv.trans (matrixAction_cokernel_smithEquiv A)

/-- The finite-torus cokernel is finite exactly when the corresponding lattice
cokernel has full target rank. -/
theorem matrixMapQuotientAddHom_cokernel_finite_iff_full_rank
    {n m : ℕ} (A : Fin m → Fin n → ℤ) :
    Finite (LoopQuot m ⧸ (matrixMapQuotientAddHom A).range) ↔
      Module.finrank ℤ ((matrixAction A).range.toIntSubmodule) =
        Module.finrank ℤ (Fin m → ℤ) :=
  (matrixMapQuotientAddHom_cokernel_finite_iff_matrixAction_cokernel A).trans
    (matrixAction_cokernel_finite_iff_full_rank A)

/-- The arbitrary-rank topological Smith presentation detects finiteness
exactly: there is no finite quotient precisely when a complementary `ZMod 0`
factor remains. -/
theorem matrixMapQuotientAddHom_cokernel_finite_iff_smithNormalFormFactor_ne_zero
    {n m : ℕ} (A : Fin m → Fin n → ℤ) :
    Finite (LoopQuot m ⧸ (matrixMapQuotientAddHom A).range) ↔
      ∀ i : Fin m, smithNormalFormFactor
        (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
          (matrixAction A).range.toIntSubmodule).2 i ≠ 0 := by
  refine (Equiv.finite_iff
      (matrixMapQuotientAddHom_cokernel_smithAddEquiv A).toEquiv).trans ?_
  simpa only [Int.natAbs_ne_zero] using
    (finite_zmod_pi_iff (fun i =>
      (smithNormalFormFactor
        (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
          (matrixAction A).range.toIntSubmodule).2 i).natAbs))

/-- The canonical finite-torus cokernel is full-rank exactly when all of its
Smith coordinates are torsion coordinates (nonzero moduli). -/
theorem matrixMapQuotientAddHom_cokernel_full_rank_iff_smithNormalFormFactor_ne_zero
    {n m : ℕ} (A : Fin m → Fin n → ℤ) :
    Module.finrank ℤ ((matrixAction A).range.toIntSubmodule) =
        Module.finrank ℤ (Fin m → ℤ) ↔
      ∀ i : Fin m, smithNormalFormFactor
        (Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m))
          (matrixAction A).range.toIntSubmodule).2 i ≠ 0 := by
  exact (matrixMapQuotientAddHom_cokernel_finite_iff_full_rank A).symm.trans
    (matrixMapQuotientAddHom_cokernel_finite_iff_smithNormalFormFactor_ne_zero A)

/-- The finite-torus cokernel has the same exact Smith-factor cardinality as
the lattice cokernel whenever the matrix has full target rank. -/
theorem matrixMapQuotientAddHom_cokernel_card_eq_smithNormalFormProduct
    {n m : ℕ} (A : Fin m → Fin n → ℤ)
    (hA : Module.finrank ℤ ((matrixAction A).range.toIntSubmodule) =
      Module.finrank ℤ (Fin m → ℤ)) :
    Nat.card (LoopQuot m ⧸ (matrixMapQuotientAddHom A).range) =
      ∏ i : Fin m, (Submodule.smithNormalFormCoeffs
        (Pi.basisFun ℤ (Fin m)) hA i).natAbs := by
  rw [Nat.card_congr
    (matrixMapQuotientAddHom_cokernel_smithAddEquivOfFullRank A hA).toEquiv]
  simp [Nat.card_pi, Nat.card_zmod]

/-- The topological square cokernel carries the same determinant-index
identity: its Smith-modulus product is exactly `Int.natAbs (Matrix.det A)`. -/
theorem matrixMapQuotientAddHom_smithNormalFormProduct_eq_natAbs_det {n : ℕ}
    (A : Fin n → Fin n → ℤ) (hA : Matrix.det A ≠ 0) :
    ∏ i : Fin n, (Submodule.smithNormalFormCoeffs
      (Pi.basisFun ℤ (Fin n)) (matrixAction_cokernel_full_rank A hA) i).natAbs =
      Int.natAbs (Matrix.det A) := by
  calc
    _ = Nat.card (LoopQuot n ⧸ (matrixMapQuotientAddHom A).range) :=
      (matrixMapQuotientAddHom_cokernel_card_eq_smithNormalFormProduct A
        (matrixAction_cokernel_full_rank A hA)).symm
    _ = _ := matrixMapQuotientAddHom_cokernel_card_eq_natAbs_det A hA

/-- The finite-torus quotient cokernel is finite whenever the matrix
determinant is nonzero. -/
theorem matrixMapQuotientAddHom_cokernel_finite {n : ℕ}
    (A : Fin n → Fin n → ℤ) (hA : Matrix.det A ≠ 0) :
    Finite (LoopQuot n ⧸ (matrixMapQuotientAddHom A).range) := by
  apply Nat.finite_of_card_ne_zero
  rw [matrixMapQuotientAddHom_cokernel_card_eq_natAbs_det A hA]
  exact Int.natAbs_ne_zero.mpr hA

/-! The determinant count has a structural refinement: the topological
quotient obstruction itself, not only its cardinality, inherits the Smith
normal-form cyclic factors of the winding lattice. -/

/-- The canonical finite-torus quotient cokernel is explicitly equivalent to
the product of cyclic `ZMod` factors supplied by Smith normal form. -/
noncomputable def matrixMapQuotientAddHom_cokernel_smithEquivOfDetNeZero
    {n : ℕ} (A : Fin n → Fin n → ℤ) (hA : Matrix.det A ≠ 0) :
    (LoopQuot n ⧸ (matrixMapQuotientAddHom A).range) ≃
      (∀ i : Fin n, ZMod ((Submodule.smithNormalFormCoeffs
        (Pi.basisFun ℤ (Fin n)) (matrixAction_cokernel_full_rank A hA) i).natAbs)) := by
  let e := loopQuotAddEquivIntVector n
  let H := (matrixMapQuotientAddHom A).range
  let N : Submodule ℤ (Fin n → ℤ) :=
    (H.map (e : LoopQuot n →+ (Fin n → ℤ))).toIntSubmodule
  have hadd_comm : ∀ x y : LoopQuot n, x + y = y + x := by
    intro x y
    rw [← quotientTrans_eq_add, ← quotientTrans_eq_add]
    exact quotientTrans_comm x y
  have hmap :
      H.map (e : LoopQuot n →+ (Fin n → ℤ)) = (matrixAction A).range := by
    exact matrixMapQuotientAddHom_range_map A
  let qEquiv :
      Quotient (QuotientAddGroup.leftRel H) ≃
        Quotient (Submodule.quotientRel N) :=
    Quotient.congr e.toEquiv (by
      intro x y
      simp only [QuotientAddGroup.leftRel_apply, Submodule.quotientRel_def]
      change -x + y ∈ H ↔ e x - e y ∈ N
      constructor
      · intro hxy
        change e x - e y ∈ H.map (e : LoopQuot n →+ (Fin n → ℤ))
        have hsub : x - y ∈ H := by
          have hEq : x - y = -(-x + y) := by
            simpa [sub_eq_add_neg, neg_add, neg_neg] using hadd_comm x (-y)
          rw [hEq]
          exact H.neg_mem hxy
        have hmem : e (x - y) ∈
            H.map (e : LoopQuot n →+ (Fin n → ℤ)) :=
          ⟨x - y, hsub, rfl⟩
        simpa [map_sub] using hmem
      · intro hxy
        change e x - e y ∈ H.map (e : LoopQuot n →+ (Fin n → ℤ)) at hxy
        rcases (AddSubgroup.mem_map).mp hxy with ⟨q, hq, hEq⟩
        have hsub : x - y = q := by
          apply e.injective
          simpa [map_sub] using hEq.symm
        have hsub' : x - y ∈ H := hsub ▸ hq
        have hEq : -x + y = -(x - y) := by
          simpa [sub_eq_add_neg, neg_add, neg_neg] using (hadd_comm (-x) y)
        rw [hEq]
        exact H.neg_mem hsub')
  exact qEquiv.trans (by
    have hN : N = (matrixAction A).range.toIntSubmodule := by
      dsimp [N]
      rw [hmap]
    rw [hN]
    exact (matrixAction_cokernel_smithEquivOfDetNeZero A hA).toEquiv)

/-- Membership in the matrix quotient homomorphism's kernel is exactly the
kernel condition for its winding-lattice action. -/
theorem matrixMapQuotientAddHom_mem_ker_iff {n m : ℕ}
    (A : Fin m → Fin n → ℤ) (q : LoopQuot n) :
    q ∈ (matrixMapQuotientAddHom A).ker ↔
      matrixAction A (encode q) = 0 := by
  change matrixMapQuotientMap A q = (0 : LoopQuot m) ↔ _
  exact matrixMapQuotientMap_eq_zero_iff A q

theorem matrixMapQuotientAddHom_comp {n m k : ℕ}
    (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ) :
    matrixMapQuotientAddHom (matrixCompose A B) =
      (matrixMapQuotientAddHom B).comp (matrixMapQuotientAddHom A) := by
  ext q
  exact (matrixMapQuotientMap_comp A B q).symm

/-! The quotient winding equivalence has a composition-compatible form whose
target is written using the explicit homomorphism composite.  This makes the
naturality statement below independent of proof-irrelevant subgroup casts. -/

/-- The winding equivalence for a rectangular composite written as an
explicit additive-homomorphism composition. -/
noncomputable def matrixMapQuotientAddHom_cokernel_windingEquiv_comp
    {n m k : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ) :
    (LoopQuot k ⧸
        ((matrixMapQuotientAddHom B).comp
          (matrixMapQuotientAddHom A)).range) ≃+
      ((Fin k → ℤ) ⧸
        ((matrixAction B).comp (matrixAction A)).range) := by
  have hmap :
      ((matrixMapQuotientAddHom B).comp
          (matrixMapQuotientAddHom A)).range.map
          (loopQuotAddEquivIntVector k : LoopQuot k →+ (Fin k → ℤ)) =
        ((matrixAction B).comp (matrixAction A)).range := by
    rw [← matrixMapQuotientAddHom_comp A B,
      ← matrixAction_comp_hom A B]
    exact matrixMapQuotientAddHom_range_map (matrixCompose A B)
  exact QuotientAddGroup.congr _ _ (loopQuotAddEquivIntVector k) hmap

@[simp] theorem matrixMapQuotientAddHom_cokernel_windingEquiv_comp_apply_mk
    {n m k : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ)
    (q : LoopQuot k) :
    matrixMapQuotientAddHom_cokernel_windingEquiv_comp A B
        (QuotientAddGroup.mk'
          ((matrixMapQuotientAddHom B).comp
            (matrixMapQuotientAddHom A)).range q) =
      QuotientAddGroup.mk'
        ((matrixAction B).comp (matrixAction A)).range
        (loopQuotAddEquivIntVector k q) := by
  rfl

/-- The explicit composite finite-torus and lattice cokernels have the same
cardinality in all composable dimensions. -/
theorem matrixMapQuotientAddHom_cokernel_comp_card_eq_matrixAction_cokernel_comp
    {n m k : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ) :
    Nat.card (LoopQuot k ⧸
        ((matrixMapQuotientAddHom B).comp
          (matrixMapQuotientAddHom A)).range) =
      Nat.card ((Fin k → ℤ) ⧸
        ((matrixAction B).comp (matrixAction A)).range) := by
  exact Nat.card_congr
    (matrixMapQuotientAddHom_cokernel_windingEquiv_comp A B).toEquiv

/-- Finiteness of the explicit composite finite-torus cokernel is equivalent
to finiteness of its lattice counterpart. -/
theorem matrixMapQuotientAddHom_cokernel_comp_finite_iff_matrixAction_cokernel_comp
    {n m k : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ) :
    Finite (LoopQuot k ⧸
        ((matrixMapQuotientAddHom B).comp
          (matrixMapQuotientAddHom A)).range) ↔
      Finite ((Fin k → ℤ) ⧸
        ((matrixAction B).comp (matrixAction A)).range) := by
  exact Equiv.finite_iff
    (matrixMapQuotientAddHom_cokernel_windingEquiv_comp A B).toEquiv

/-! The quotient-level matrix map is natural with respect to the winding
equivalences: applying the topological cokernel embedding and then decoding
windings agrees with first decoding and applying the lattice embedding. -/

/-- Naturality of the rectangular cokernel embedding under the winding
equivalence. -/
theorem matrixMapQuotientAddHom_cokernel_windingEquiv_compMap_naturality
    {n m k : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ) :
    (matrixMapQuotientAddHom_cokernel_windingEquiv_comp A B).toAddMonoidHom.comp
        (addCokernelCompMap (matrixMapQuotientAddHom A)
          (matrixMapQuotientAddHom B)) =
      (addCokernelCompMap (matrixAction A) (matrixAction B)).comp
        (matrixMapQuotientAddHom_cokernel_windingEquiv A).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro q
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective
    (matrixMapQuotientAddHom A).range q
  simp only [AddMonoidHom.comp_apply]
  change
    matrixMapQuotientAddHom_cokernel_windingEquiv_comp A B
        (addCokernelCompMap (matrixMapQuotientAddHom A)
          (matrixMapQuotientAddHom B)
          (QuotientAddGroup.mk' (matrixMapQuotientAddHom A).range x)) =
      addCokernelCompMap (matrixAction A) (matrixAction B)
        (matrixMapQuotientAddHom_cokernel_windingEquiv A
          (QuotientAddGroup.mk' (matrixMapQuotientAddHom A).range x))
  rw [show addCokernelCompMap (matrixMapQuotientAddHom A)
          (matrixMapQuotientAddHom B)
          (QuotientAddGroup.mk' (matrixMapQuotientAddHom A).range x) =
        QuotientAddGroup.mk'
          ((matrixMapQuotientAddHom B).comp
            (matrixMapQuotientAddHom A)).range
          (matrixMapQuotientAddHom B x) by
    rfl]
  rw [show matrixMapQuotientAddHom_cokernel_windingEquiv A
          (QuotientAddGroup.mk' (matrixMapQuotientAddHom A).range x) =
        QuotientAddGroup.mk' (matrixAction A).range
          (loopQuotAddEquivIntVector m x) by rfl]
  rw [show matrixMapQuotientAddHom_cokernel_windingEquiv_comp A B
        (QuotientAddGroup.mk'
          ((matrixMapQuotientAddHom B).comp
            (matrixMapQuotientAddHom A)).range
          (matrixMapQuotientAddHom B x)) =
      QuotientAddGroup.mk'
        ((matrixAction B).comp (matrixAction A)).range
        (loopQuotAddEquivIntVector k
          (matrixMapQuotientAddHom B x)) by rfl]
  simp only [addCokernelCompMap, QuotientAddGroup.map_mk']
  apply congrArg
    (QuotientAddGroup.mk' ((matrixAction B).comp (matrixAction A)).range)
  change encode (matrixMapQuotientMap B x) =
    matrixAction B (encode x)
  exact encode_matrixMapQuotientMap B x

/-- Naturality of the rectangular cokernel projection under the winding
equivalence. -/
theorem matrixMapQuotientAddHom_cokernel_windingEquiv_compProjection_naturality
    {n m k : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ) :
    (matrixMapQuotientAddHom_cokernel_windingEquiv B).toAddMonoidHom.comp
        (addCokernelCompProjection (matrixMapQuotientAddHom A)
          (matrixMapQuotientAddHom B)) =
      (addCokernelCompProjection (matrixAction A) (matrixAction B)).comp
        (matrixMapQuotientAddHom_cokernel_windingEquiv_comp A B).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro q
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective
    ((matrixMapQuotientAddHom B).comp
      (matrixMapQuotientAddHom A)).range q
  simp only [AddMonoidHom.comp_apply]
  change
    matrixMapQuotientAddHom_cokernel_windingEquiv B
        (addCokernelCompProjection (matrixMapQuotientAddHom A)
          (matrixMapQuotientAddHom B)
          (QuotientAddGroup.mk'
            ((matrixMapQuotientAddHom B).comp
              (matrixMapQuotientAddHom A)).range x)) =
      addCokernelCompProjection (matrixAction A) (matrixAction B)
        (matrixMapQuotientAddHom_cokernel_windingEquiv_comp A B
          (QuotientAddGroup.mk'
            ((matrixMapQuotientAddHom B).comp
              (matrixMapQuotientAddHom A)).range x))
  rw [show addCokernelCompProjection (matrixMapQuotientAddHom A)
          (matrixMapQuotientAddHom B)
          (QuotientAddGroup.mk'
            ((matrixMapQuotientAddHom B).comp
              (matrixMapQuotientAddHom A)).range x) =
        QuotientAddGroup.mk' (matrixMapQuotientAddHom B).range x by
    rfl]
  rw [show matrixMapQuotientAddHom_cokernel_windingEquiv B
          (QuotientAddGroup.mk' (matrixMapQuotientAddHom B).range x) =
        QuotientAddGroup.mk' (matrixAction B).range
          (loopQuotAddEquivIntVector k x) by rfl]
  rw [show matrixMapQuotientAddHom_cokernel_windingEquiv_comp A B
          (QuotientAddGroup.mk'
            ((matrixMapQuotientAddHom B).comp
              (matrixMapQuotientAddHom A)).range x) =
        QuotientAddGroup.mk'
          ((matrixAction B).comp (matrixAction A)).range
          (loopQuotAddEquivIntVector k x) by rfl]
  simp only [addCokernelCompProjection, QuotientAddGroup.map_mk']
  rfl

/-! The two naturality laws and the two exactness packages can be consumed as
one diagram-level certificate.  This avoids making downstream users recover
the common maps from the existential rectangular statements separately. -/

/-- The rectangular topological and lattice cokernel sequences are short exact
and form a commuting winding diagram whenever the second lattice action is
injective. -/
theorem matrixMapQuotientAddHom_rectangular_cokernel_winding_shortExact
    {n m k : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ)
    (hB : Function.Injective (matrixAction B)) :
    Function.Injective
          (addCokernelCompMap (matrixMapQuotientAddHom A)
            (matrixMapQuotientAddHom B)) ∧
      (addCokernelCompProjection (matrixMapQuotientAddHom A)
          (matrixMapQuotientAddHom B)).ker =
        (addCokernelCompMap (matrixMapQuotientAddHom A)
          (matrixMapQuotientAddHom B)).range ∧
      Function.Surjective
        (addCokernelCompProjection (matrixMapQuotientAddHom A)
          (matrixMapQuotientAddHom B)) ∧
      Function.Injective
          (addCokernelCompMap (matrixAction A) (matrixAction B)) ∧
      (addCokernelCompProjection (matrixAction A) (matrixAction B)).ker =
        (addCokernelCompMap (matrixAction A) (matrixAction B)).range ∧
      Function.Surjective
        (addCokernelCompProjection (matrixAction A) (matrixAction B)) ∧
      (matrixMapQuotientAddHom_cokernel_windingEquiv_comp A B).toAddMonoidHom.comp
          (addCokernelCompMap (matrixMapQuotientAddHom A)
            (matrixMapQuotientAddHom B)) =
        (addCokernelCompMap (matrixAction A) (matrixAction B)).comp
          (matrixMapQuotientAddHom_cokernel_windingEquiv A).toAddMonoidHom ∧
      (matrixMapQuotientAddHom_cokernel_windingEquiv B).toAddMonoidHom.comp
          (addCokernelCompProjection (matrixMapQuotientAddHom A)
            (matrixMapQuotientAddHom B)) =
        (addCokernelCompProjection (matrixAction A) (matrixAction B)).comp
          (matrixMapQuotientAddHom_cokernel_windingEquiv_comp A B).toAddMonoidHom := by
  have hB' : Function.Injective (matrixMapQuotientAddHom B) := by
    change Function.Injective (matrixMapQuotientMap B)
    exact (matrixMapQuotientMap_injective_iff B).mpr hB
  have hTop := addCokernelComp_shortExact_of_injective
    (matrixMapQuotientAddHom A) (matrixMapQuotientAddHom B) hB'
  have hLat := addCokernelComp_shortExact_of_injective
    (matrixAction A) (matrixAction B) hB
  exact ⟨hTop.1, hTop.2.1, hTop.2.2,
    hLat.1, hLat.2.1, hLat.2.2,
    matrixMapQuotientAddHom_cokernel_windingEquiv_compMap_naturality A B,
    matrixMapQuotientAddHom_cokernel_windingEquiv_compProjection_naturality A B⟩

/-! The square-matrix cokernel maps exposed earlier use the canonical
`matrixCompose` target ranges.  The same two naturality laws are recorded
directly for those named maps, so users can invoke the checked diagram without
first rewriting to explicit homomorphism compositions. -/

/-- Naturality of the canonical square cokernel embedding under winding. -/
theorem matrixMapQuotientAddHom_cokernel_windingEquiv_compMap_matrixCompose_naturality
    {n : ℕ} (A B : Fin n → Fin n → ℤ) :
    (matrixMapQuotientAddHom_cokernel_windingEquiv (matrixCompose A B)).toAddMonoidHom.comp
        (matrixMapQuotientAddHom_cokernel_compMap A B) =
      (matrixAction_cokernel_compMap A B).comp
        (matrixMapQuotientAddHom_cokernel_windingEquiv A).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro q
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective
    (matrixMapQuotientAddHom A).range q
  simp only [AddMonoidHom.comp_apply]
  change
    matrixMapQuotientAddHom_cokernel_windingEquiv (matrixCompose A B)
        (matrixMapQuotientAddHom_cokernel_compMap A B
          (QuotientAddGroup.mk' (matrixMapQuotientAddHom A).range x)) =
      matrixAction_cokernel_compMap A B
        (matrixMapQuotientAddHom_cokernel_windingEquiv A
          (QuotientAddGroup.mk' (matrixMapQuotientAddHom A).range x))
  rw [show matrixMapQuotientAddHom_cokernel_compMap A B
          (QuotientAddGroup.mk' (matrixMapQuotientAddHom A).range x) =
        QuotientAddGroup.mk'
          (matrixMapQuotientAddHom (matrixCompose A B)).range
          (matrixMapQuotientAddHom B x) by
    rfl]
  rw [show matrixMapQuotientAddHom_cokernel_windingEquiv A
          (QuotientAddGroup.mk' (matrixMapQuotientAddHom A).range x) =
        QuotientAddGroup.mk' (matrixAction A).range
          (loopQuotAddEquivIntVector n x) by rfl]
  rw [show matrixMapQuotientAddHom_cokernel_windingEquiv (matrixCompose A B)
          (QuotientAddGroup.mk'
            (matrixMapQuotientAddHom (matrixCompose A B)).range
            (matrixMapQuotientAddHom B x)) =
        QuotientAddGroup.mk' (matrixAction (matrixCompose A B)).range
          (loopQuotAddEquivIntVector n (matrixMapQuotientAddHom B x)) by
    rfl]
  simp only [matrixAction_cokernel_compMap, QuotientAddGroup.map_mk']
  apply congrArg
    (QuotientAddGroup.mk' (matrixAction (matrixCompose A B)).range)
  change encode (matrixMapQuotientMap B x) =
    matrixAction B (encode x)
  exact encode_matrixMapQuotientMap B x

/-- Naturality of the canonical square cokernel projection under winding. -/
theorem matrixMapQuotientAddHom_cokernel_windingEquiv_compProjection_matrixCompose_naturality
    {n : ℕ} (A B : Fin n → Fin n → ℤ) :
    (matrixMapQuotientAddHom_cokernel_windingEquiv B).toAddMonoidHom.comp
        (matrixMapQuotientAddHom_cokernel_compProjection A B) =
      (matrixAction_cokernel_compProjection A B).comp
        (matrixMapQuotientAddHom_cokernel_windingEquiv (matrixCompose A B)).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro q
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective
    (matrixMapQuotientAddHom (matrixCompose A B)).range q
  simp only [AddMonoidHom.comp_apply]
  change
    matrixMapQuotientAddHom_cokernel_windingEquiv B
        (matrixMapQuotientAddHom_cokernel_compProjection A B
          (QuotientAddGroup.mk'
            (matrixMapQuotientAddHom (matrixCompose A B)).range x)) =
      matrixAction_cokernel_compProjection A B
        (matrixMapQuotientAddHom_cokernel_windingEquiv (matrixCompose A B)
          (QuotientAddGroup.mk'
            (matrixMapQuotientAddHom (matrixCompose A B)).range x))
  rw [show matrixMapQuotientAddHom_cokernel_compProjection A B
          (QuotientAddGroup.mk'
            (matrixMapQuotientAddHom (matrixCompose A B)).range x) =
        QuotientAddGroup.mk' (matrixMapQuotientAddHom B).range x by
    rfl]
  rw [show matrixMapQuotientAddHom_cokernel_windingEquiv B
          (QuotientAddGroup.mk' (matrixMapQuotientAddHom B).range x) =
        QuotientAddGroup.mk' (matrixAction B).range
          (loopQuotAddEquivIntVector n x) by rfl]
  rw [show matrixMapQuotientAddHom_cokernel_windingEquiv (matrixCompose A B)
          (QuotientAddGroup.mk'
            (matrixMapQuotientAddHom (matrixCompose A B)).range x) =
        QuotientAddGroup.mk' (matrixAction (matrixCompose A B)).range
          (loopQuotAddEquivIntVector n x) by rfl]
  simp only [matrixAction_cokernel_compProjection, QuotientAddGroup.map_mk']
  rfl

/-- The image of a rectangular finite-torus composite is independent of
whether it is written as an explicit homomorphism composition or through the
row-by-column `matrixCompose` operation. -/
theorem matrixMapQuotientAddHom_comp_range_eq_matrixCompose_range
    {n m k : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ) :
    ((matrixMapQuotientAddHom B).comp
      (matrixMapQuotientAddHom A)).range =
      (matrixMapQuotientAddHom (matrixCompose A B)).range := by
  rw [← matrixMapQuotientAddHom_comp A B]

/-- The rectangular finite-torus exact sequence can be consumed directly
through the canonical matrix-composition notation. -/
theorem matrixMapQuotientAddHom_rectangular_cokernel_shortExact_of_matrixCompose_injective
    {n m k : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ)
    (hB : Function.Injective (matrixMapQuotientAddHom B)) :
    ∃ f : LoopQuot m ⧸ (matrixMapQuotientAddHom A).range →+
          LoopQuot k ⧸
            (matrixMapQuotientAddHom (matrixCompose A B)).range,
    ∃ g : LoopQuot k ⧸
          (matrixMapQuotientAddHom (matrixCompose A B)).range →+
          LoopQuot k ⧸ (matrixMapQuotientAddHom B).range,
    ∃ e : ((LoopQuot k ⧸
          (matrixMapQuotientAddHom (matrixCompose A B)).range) ⧸
        g.ker) ≃+
          LoopQuot k ⧸ (matrixMapQuotientAddHom B).range,
      Function.Injective f ∧ g.ker = f.range ∧ Function.Surjective g := by
  rw [← matrixMapQuotientAddHom_comp_range_eq_matrixCompose_range A B]
  exact matrixMapQuotientAddHom_rectangular_cokernel_shortExact_of_injective
    A B hB

/-- The exact preimage-of-image criterion for the rectangular finite-torus
cokernel map also has a canonical matrix-compose presentation. -/
theorem matrixMapQuotientAddHom_rectangular_cokernel_compMap_injective_iff_matrixCompose
    {n m k : ℕ} (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ) :
    Function.Injective
        (addCokernelCompMap (matrixMapQuotientAddHom A)
          (matrixMapQuotientAddHom B)) ↔
      AddSubgroup.comap (matrixMapQuotientAddHom B)
          (matrixMapQuotientAddHom (matrixCompose A B)).range =
        (matrixMapQuotientAddHom A).range := by
  rw [← matrixMapQuotientAddHom_comp_range_eq_matrixCompose_range A B]
  exact matrixMapQuotientAddHom_rectangular_cokernel_compMap_injective_iff
    A B

theorem matrixMapQuotientAddHom_id (n : ℕ) :
    matrixMapQuotientAddHom (matrixIdentity n) =
      AddMonoidHom.id (LoopQuot n) := by
  ext q
  exact matrixMapQuotientMap_id q

/-- The matrix quotient homomorphism is continuous for the discrete quotient
topologies. -/
noncomputable def matrixMapQuotientContinuousAddHom {n m : ℕ}
    (A : Fin m → Fin n → ℤ) : LoopQuot n →ₜ+ LoopQuot m where
  toAddMonoidHom := matrixMapQuotientAddHom A
  continuous_toFun := continuous_of_discreteTopology

@[simp] theorem matrixMapQuotientContinuousAddHom_apply {n m : ℕ}
    (A : Fin m → Fin n → ℤ) (q : LoopQuot n) :
    matrixMapQuotientContinuousAddHom A q = matrixMapQuotientMap A q :=
  rfl

theorem matrixMapQuotientContinuousAddHom_comp {n m k : ℕ}
    (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ) :
    matrixMapQuotientContinuousAddHom (matrixCompose A B) =
      (matrixMapQuotientContinuousAddHom B).comp
        (matrixMapQuotientContinuousAddHom A) := by
  ext q
  exact (matrixMapQuotientMap_comp A B q).symm

theorem matrixMapQuotientContinuousAddHom_id (n : ℕ) :
    matrixMapQuotientContinuousAddHom (matrixIdentity n) =
      ContinuousAddMonoidHom.id (LoopQuot n) := by
  ext q
  exact matrixMapQuotientMap_id q

/-- Every finite-torus loop homotopy class is open in the compact-open loop
space. -/
theorem isOpen_homotopyClass {n : ℕ} (γ : Loop n) :
    IsOpen {δ : Loop n | γ.Homotopic δ} := by
  exact
    QuotientFundamentalGroup.isOpen_homotopyClass_of_isOpen_nullHomotopyClass
      (Carrier n) (base n) (isOpen_nullHomotopyClass n) γ

/-- Finite-torus loop homotopy as a Mathlib discrete quotient relation. -/
noncomputable def loopHomotopyDiscreteQuotient (n : ℕ) :
    DiscreteQuotient (Loop n) where
  toSetoid := _root_.Path.Homotopic.setoid (base n) (base n)
  isOpen_setOf_rel := isOpen_homotopyClass

/-- The square of the finite-torus loop quotient map is a quotient map. -/
theorem loopQuotientProd_isQuotientMap (n : ℕ) :
    IsQuotientMap
      (fun p : Loop n × Loop n =>
        ((Quotient.mk' p.1 : LoopQuot n), (Quotient.mk' p.2 : LoopQuot n))) := by
  exact QuotientFundamentalGroup.loopQuotientProd_isQuotientMap
    (Carrier n) (base n) (isOpen_nullHomotopyClass n)

/-- Loop-class composition is continuous for the ordinary product topology. -/
theorem continuous_quotientTrans (n : ℕ) :
    Continuous
      (fun p : LoopQuot n × LoopQuot n =>
        _root_.Path.Homotopic.Quotient.trans p.1 p.2) :=
  QuotientFundamentalGroup.continuous_quotientTrans
    (Carrier n) (base n) (isOpen_nullHomotopyClass n)

/-- Loop-class reversal is continuous. -/
theorem continuous_quotientSymm (n : ℕ) :
    Continuous
      (_root_.Path.Homotopic.Quotient.symm : LoopQuot n → LoopQuot n) :=
  QuotientFundamentalGroup.continuous_quotientSymm (Carrier n) (base n)

end FiniteTorusWinding

end
end GeometricTopology
end Path
end ComputationalPaths
