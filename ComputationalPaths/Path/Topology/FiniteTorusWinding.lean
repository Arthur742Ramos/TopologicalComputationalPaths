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
quotient map.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open Set Topology
open scoped ContinuousMap Topology

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
