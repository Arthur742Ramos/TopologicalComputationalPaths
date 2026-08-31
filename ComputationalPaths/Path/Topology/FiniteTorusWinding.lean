import ComputationalPaths.Path.Topology.TopologicalWindingHomeomorph
import ComputationalPaths.Path.Topology.QuotientFundamentalGroup
import ComputationalPaths.Path.Topology.SemilocallySimplyConnected
import Mathlib.Topology.Homotopy.Product
import Mathlib.Topology.Algebra.ContinuousMonoidHom

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
groups.
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

noncomputable def matrixMapQuotientAddHom {n m : ℕ}
    (A : Fin m → Fin n → ℤ) : LoopQuot n →+ LoopQuot m where
  toFun := matrixMapQuotientMap A
  map_zero' := matrixMapQuotientMap_map_zero A
  map_add' := matrixMapQuotientMap_map_add A

@[simp] theorem matrixMapQuotientAddHom_apply {n m : ℕ}
    (A : Fin m → Fin n → ℤ) (q : LoopQuot n) :
    matrixMapQuotientAddHom A q = matrixMapQuotientMap A q :=
  rfl

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
