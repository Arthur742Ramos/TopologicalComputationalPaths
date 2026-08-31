import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Homotopy.Product
import Mathlib.Topology.Homotopy.HSpaces
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Maps.OpenQuotient
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Follow-up challenge: quotient-topological fundamental groups

First prove that the compact-open based-loop quotient is functorial under
continuous maps, invariant under homeomorphism and change of basepoint along
a path, and preserves binary products whenever the product of the two loop
projections is a quotient map.  For every pointed space, prove that it is a
quasitopological group: reversal and both one-variable translations are
continuous.  Prove the exact criterion that this quotient is discrete if and
only if the null-homotopy class is open.  Derive open quotient projection,
the quotient-square property, and joint continuity of multiplication in the
positive case.

Then instantiate the criterion for every finite product of additive circles,
including an explicit winding classification by the integer lattice.
In locally path-connected spaces, also prove the converse finite-ladder
criterion: semilocal simple connectivity is equivalent to discreteness of
every based quotient fundamental group, and every based-loop homotopy class is
open.  The finite-torus certificate additionally exposes the all-basepoint
semilocal consequence and the all-basepoint integer-lattice classifier from
the basepoint-transport theorem.  It strengthens this family with a
continuous multiplicative equivalence to `Multiplicative (Fin n → ℤ)` and
explicit commutativity of quotient multiplication at every basepoint.  The
finite-torus winding vector is natural under coordinate-selection maps (the
certificate records the fixed-dimensional reindexing instance), and the
standard representatives and quotient classifier satisfy the matching
reindexing equations.  The multiplicative lattice classifier satisfies the
same reindexing law, including selections between different finite dimensions.
The path-based classifier also satisfies the corresponding naturality square
at arbitrary torus basepoints after mapping the chosen transport path.
By abelian-target path independence, the canonical classifier satisfies the
same square without exposing a path choice.
The lattice reindexings are continuous additive morphisms with their own
identity and composition coherence.
For finite index equivalences, the coordinate map is a torus homeomorphism
and the lattice reindexing is a continuous additive equivalence with matching
coherence.
The arbitrary-basepoint classifier naturality squares are also stated through
the continuous additive reindexing morphism.
Surjective and injective index maps additionally yield the matching
injectivity and surjectivity results for torus maps, lattice reindexing, and
typed quotient maps.
For an arbitrary index map, the image is characterized exactly by winding
vectors constant on its fibers, at both the lattice and typed quotient levels.
The converses are included as exact iff criteria at the raw torus, lattice,
and typed quotient levels.  Typed quotient coordinate maps also compose
contravariantly and preserve the transported additive structure continuously
for the discrete quotient topologies, with their kernels characterized by
vanishing on the index-map image.  At arbitrary torus basepoints, coordinate
selection is also exposed as a continuous multiplicative homomorphism between
the corresponding quotient fundamental groups, with explicit
identity/composition coherence and a direct classifier-naturality statement.
The canonical classifiers also transport the exact fiber-constant image,
injectivity/surjectivity converse, and kernel descriptions to every torus
basepoint.  The induced homomorphism also commutes with explicit basepoint
transport, giving a naturality square before any classifier is chosen.
The supporting finite-torus module additionally extends these coordinate
selection results to arbitrary integer matrices: matrix maps act continuously
on the torus and on its integer lattice, compose with the usual row-by-column
law, and transfer exact image, kernel, injectivity, and surjectivity statements
through winding.  It also exposes the induced continuous multiplicative
homomorphisms at arbitrary basepoints, proves their compatibility with
basepoint transport, and states the path-based classifier square with the
endpoint cast made explicit.  Abelian-target path independence then gives
the same matrix naturality square for the canonical classifier without a
path parameter.  The canonical classifier also transfers the exact matrix
image and kernel descriptions, and the injectivity/surjectivity iff criteria,
to every chosen basepoint, each as an explicit iff theorem.
The arbitrary-basepoint homomorphisms additionally satisfy typed
contravariant composition and identity laws with explicit endpoint casts.
An explicit two-sided integer-matrix inverse further yields a continuous
additive lattice equivalence, a torus homeomorphism, and quotient
homeomorphism and continuous additive equivalence for the transported
loop-class groups.  At every arbitrary torus basepoint, it also yields a
continuous multiplicative quotient equivalence with explicit injectivity and
surjectivity consequences.
For square matrices, injectivity of the lattice and canonical quotient action
is equivalent to a nonzero determinant, while surjectivity is equivalent to a
unit determinant.  The canonical nonsingular inverse of a unimodular matrix
therefore supplies all of the preceding equivalence layers without an extra
inverse witness, including at arbitrary basepoints.
    For every nonzero determinant, the winding-lattice cokernel is finite with
    cardinality exactly `Int.natAbs (Matrix.det A)`, and finiteness is exposed
    explicitly as a quantitative index certificate.
    At the canonical finite-torus basepoint, the induced quotient image has the
    same exact index and cokernel cardinality, with an explicit finiteness
    theorem identifying the topological quotient obstruction with the
    determinant index.
    For composable non-singular square matrices, the determinant index is
    multiplicative under matrix composition on both the lattice and canonical
    quotient cokernel.
    Composition by a non-singular matrix `B` also induces a canonical additive
    map from the cokernel of `A` into that of `B ∘ A`, proved injective on both
    the winding lattice and the topological quotient.
    The projection from the cokernel of `B ∘ A` onto the cokernel of `B` is
    surjective with exactly that image as its kernel, giving a short exact
    sequence on both sides.
    The quotient of the composition cokernel by the projection kernel is also
    equipped with an explicit first-isomorphism additive equivalence to the
    cokernel of `B`, including its action on quotient representatives.
    The underlying first-isomorphism argument is packaged for arbitrary
    composable additive homomorphisms, so rectangular integer matrices in any
    composable dimensions inherit the same short-exact sequence under
    injectivity of the second action; the finite-torus quotient maps satisfy
    the corresponding transported theorem.  The composite ranges are also
    identified with the canonical row-by-column `matrixCompose` ranges, and
    the exact-sequence and converse-criterion interfaces are exposed in that
    notation.  The substantive finite-torus module additionally lifts the
    winding equivalence to rectangular cokernels and verifies naturality for
    both maps in the exact diagram, including direct naturality theorems for
    the named square-matrix `matrixCompose` maps.  The substantive module also
    packages both exact sequences and both commuting squares in one
    rectangular diagram certificate.  The abstract map and projection also
    have explicit quotient-representative formulas.  The substantive module
    transports cardinality and finiteness across the rectangular winding
    equivalence for individual matrices and explicit composites.
    It also generalizes the Smith-normal-form product to arbitrary-rank
    rectangular maps: complementary coordinates contribute explicit `ZMod 0`
    free factors and embedded Smith coordinates contribute cyclic torsion
    factors.  Under full target rank, the exact product of Smith moduli is
    transported to the torus cokernel as well, and the lattice finite-cokernel
    condition is characterized exactly by full target rank.  The arbitrary-rank
    factorization also gives a direct finiteness test on both sides: every
    Smith modulus is nonzero exactly when the corresponding cokernel is finite.
    In the square nonsingular specialization, the product of Smith moduli is
    also identified with the determinant index `Int.natAbs (Matrix.det A)` on
    both the lattice and finite-torus sides.
    The arbitrary-rank presentation additionally proves the exact `Nat.card`
    product formula without a finiteness assumption, including infinite cases
    through the `ZMod 0` factors.
    The same arbitrary-rank presentation identifies the additive exponent with
    the lcm of the Smith-factor moduli, so a zero factor forces exponent zero
    and records the free summand both elementwise and globally.
    Equivalently, exponent zero is characterized by a zero Smith factor; for
    rectangular lattice and finite-torus cokernels this is exactly failure of
    full target rank.
    More generally, a proposed global annihilator `k` is divisible by the
    Smith exponent exactly when every Smith-factor modulus divides `k`, with a
    zero factor forcing `k = 0`.
    The sharp trivial-cokernel boundary is the exponent-one case: the
    exponent is one exactly when every Smith factor has unit absolute value.
    Consequently, a rectangular lattice or finite-torus matrix action is
    surjective exactly when all of its Smith factors have unit absolute value.
    For square matrices, the adjugate annihilator also gives the global bound
    `AddMonoid.exponent (cokernel) ∣ Int.natAbs (Matrix.det A)`, including the
    singular case.
    The finite/infinite dichotomy is equivalently global: each Smith cokernel
    is finite exactly when its exponent is nonzero, so the zero-exponent
    criterion is also a complete finiteness test.
    It also supplies exact Smith-coordinate divisibility tests for lattice and
    finite-torus matrix-image membership, including the zero-factor equations.
    The topological Smith equivalence has an explicit quotient-representative
    formula, making the decoder directly usable on loop classes.
    For every square matrix, the adjugate gives an explicit preimage of each
    determinant multiple, and the determinant annihilates both the lattice and
    finite-torus cokernel classes without a nonzero-determinant hypothesis.
    Whenever all Smith moduli are nonzero, the cyclic factors are further
    decomposed by the Chinese remainder theorem into explicit prime-power
    cyclic factors on both lattice and finite-torus cokernels, with a
    representative formula for the refined decoder.
    The refined product has an exact cardinality certificate: its prime-power
    orders multiply back to each Smith modulus, identifying both cokernel
    cardinalities with the resulting full double product.
    Its additive exponent is also identified exactly with the least common
    multiple of the Smith moduli, exposing the precise finite-cokernel
    annihilator.
    The same Smith coordinates give an elementwise annihilation criterion:
    a multiple of a lattice or finite-torus cokernel class vanishes exactly
    when each transformed coordinate is divisible by the corresponding
    multiple of its Smith factor, including the zero-factor equations.
    The additive order of each class is the lcm of the additive orders of its
    decoded Smith coordinates; a nonzero free `ZMod 0` coordinate records
    infinite class order.
    When all factors are nonzero, each coordinate order is computed explicitly
    as its Smith modulus divided by the gcd with the transformed integer
    coordinate.
    For arbitrary rank, infinite order is characterized elementwise: it occurs
    exactly when a zero Smith factor carries a nonzero transformed coordinate,
    and the same free-coordinate criterion is exposed on lattice and
    finite-torus matrix representatives.
    Equivalently, a natural number is a multiple of a class's additive order
    exactly when it satisfies the corresponding coordinatewise Smith
    divisibility equations, including the free-coordinate vanishing
    constraints.
    Conversely, a class has finite additive order exactly when every zero
    Smith factor carries a zero transformed coordinate; this torsion test is
    exposed on the lattice and finite-torus matrix representatives as well.
    The non-singular lattice cokernel is additionally presented by an explicit
    Smith-normal-form product of finite cyclic `ZMod` factors, and the same
    cyclic-factor presentation is transported to the canonical quotient
    cokernel of the induced torus homomorphism as an explicit additive
    equivalence of finite abelian groups.
The general certificate also records that basepoint transport is independent
of the chosen path representative up to
endpoint-fixed homotopy, is the identity on constant paths, and composes along
concatenated paths; reversing a path supplies the inverse transport.  It also
records preservation of path-class concatenation
under continuous maps and naturality of basepoint transport, together with
the conjugacy law for homotopic maps.  It also records basepoint invariance
of the joint-continuity boundary, and the pointed specialization that a
basepoint-fixing homotopy induces equal based homomorphisms.
On path-connected spaces it also records that joint continuity at one
basepoint is equivalent to joint continuity at every basepoint, discreteness
at one basepoint is equivalent to discreteness at every basepoint, and the
genuine topological-group boundary has the same one-point criterion.  The
global joint-continuity property is invariant under homotopy equivalence of
path-connected spaces, and locally path-connected path-connected spaces admit
a one-basepoint semilocal criterion.
It also records homotopy and path invariance of the T1 separation boundary,
its all-basepoint reduction on path-connected spaces, and homotopy invariance
of that global T1 property.  Finally, it records the exact central-relative
criterion for equality of two transports, and its abelian-target
corollary: in an abelian target quotient, transport is independent of the
chosen path even without an endpoint-fixed homotopy between the paths.
-/

/-! Statement-facing copies of the small project aliases used below.  The
challenge is compiled by Palomar in a scratch environment without the
project's generated `.olean` files, so these declarations intentionally use
only the Mathlib path quotient and keep the publication statement standalone.
The substantive definitions with the same names are imported by the solution
from the checked project modules; Comparator checks that the resulting
statement constants agree. -/
namespace ComputationalPaths
namespace Path
namespace GeometricTopology
namespace QuotientFundamentalGroup

universe u

abbrev Loop (X : Type u) [TopologicalSpace X] (x : X) : Type u :=
  _root_.Path x x

abbrev LoopQuot (X : Type u) [TopologicalSpace X] (x : X) : Type u :=
  _root_.Path.Homotopic.Quotient x x

def SemilocallySimplyConnectedAt
    (X : Type u) [TopologicalSpace X] (x : X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∀ γ : Loop X x, Set.range γ ⊆ U →
      γ.Homotopic (_root_.Path.refl x)

def SemilocallySimplyConnected
    (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ x : X, SemilocallySimplyConnectedAt X x

end QuotientFundamentalGroup
end GeometricTopology
end Path
end ComputationalPaths

namespace TopologicalComputationalPathsFollowup

open Set Topology
open scoped ContinuousMap Topology

attribute [local instance] _root_.Path.Homotopic.setoid

universe u

abbrev GenericLoop (X : Type u) [TopologicalSpace X] (x : X) : Type u :=
  _root_.Path x x

abbrev GenericLoopQuot (X : Type u) [TopologicalSpace X] (x : X) : Type u :=
  _root_.Path.Homotopic.Quotient x x

noncomputable local instance genericLoopQuotTopologicalSpace
    (X : Type u) [TopologicalSpace X] (x : X) :
    TopologicalSpace (GenericLoopQuot X x) :=
  TopologicalSpace.coinduced
    (Quotient.mk' : GenericLoop X x → GenericLoopQuot X x) inferInstance

noncomputable local instance genericLoopQuotGroup
    (X : Type u) [TopologicalSpace X] (x : X) :
    Group (GenericLoopQuot X x) :=
  inferInstanceAs (Group (FundamentalGroup X x))

def nullHomotopyClass
    (X : Type u) [TopologicalSpace X] (x : X) : Set (GenericLoop X x) :=
  {γ | γ.Homotopic (_root_.Path.refl x)}

/-- Functorial, basepoint-invariant, product-compatible theory of the
quotient-topological fundamental group. -/
structure QuotientTopologicalFundamentalGroupTheory where
  quotient_map_continuous :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      (f : C(X, Y)) (x : X),
      Continuous
        (fun q : GenericLoopQuot X x =>
          _root_.Path.Homotopic.Quotient.map q f)
  quotient_map_id :
    ∀ (X : Type u) [TopologicalSpace X] (x : X)
      (q : GenericLoopQuot X x),
      _root_.Path.Homotopic.Quotient.map q (.id X) = q
  quotient_map_comp :
    ∀ (X Y Z : Type u)
      [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
      (f : C(X, Y)) (g : C(Y, Z)) (x : X)
      (q : GenericLoopQuot X x),
      _root_.Path.Homotopic.Quotient.map
          (_root_.Path.Homotopic.Quotient.map q f) g =
        _root_.Path.Homotopic.Quotient.map q (g.comp f)
  quotient_map_trans :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      (f : C(X, Y)) {x₀ x₁ x₂ : X}
      (P : _root_.Path.Homotopic.Quotient x₀ x₁)
      (Q : _root_.Path.Homotopic.Quotient x₁ x₂),
      _root_.Path.Homotopic.Quotient.map
          (_root_.Path.Homotopic.Quotient.trans P Q) f =
        _root_.Path.Homotopic.Quotient.trans
          (_root_.Path.Homotopic.Quotient.map P f)
          (_root_.Path.Homotopic.Quotient.map Q f)
  quotient_homeomorph_invariant :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      (e : X ≃ₜ Y) (x : X),
      ∃ E : GenericLoopQuot X x ≃ₜ GenericLoopQuot Y (e x),
        ∀ q : GenericLoopQuot X x,
          E q = _root_.Path.Homotopic.Quotient.map q ⟨e, e.continuous⟩
  quotient_homotopy_equiv_invariant :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      (e : ContinuousMap.HomotopyEquiv X Y) (x : X),
      ∃ E : GenericLoopQuot X x ≃ₜ GenericLoopQuot Y (e x),
        ∀ q : GenericLoopQuot X x,
          E q = _root_.Path.Homotopic.Quotient.map q e.toFun
  quotient_discrete_homotopy_invariant :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      (e : ContinuousMap.HomotopyEquiv X Y) (x : X),
      DiscreteTopology (GenericLoopQuot X x) ↔
        DiscreteTopology (GenericLoopQuot Y (e x))
  quotient_discrete_basepoint_invariant :
    ∀ (X : Type u) [TopologicalSpace X]
      {x₀ x₁ : X} (p : _root_.Path x₀ x₁),
      DiscreteTopology (GenericLoopQuot X x₀) ↔
        DiscreteTopology (GenericLoopQuot X x₁)
  quotient_trans_continuity_homotopy_invariant :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      (e : ContinuousMap.HomotopyEquiv X Y) (x : X),
      Continuous
          (fun p : GenericLoopQuot X x × GenericLoopQuot X x =>
            _root_.Path.Homotopic.Quotient.trans p.1 p.2) ↔
        Continuous
          (fun p : GenericLoopQuot Y (e x) × GenericLoopQuot Y (e x) =>
            _root_.Path.Homotopic.Quotient.trans p.1 p.2)
  quotient_trans_continuity_basepoint_invariant :
    ∀ (X : Type u) [TopologicalSpace X] {x₀ x₁ : X}
      (p : _root_.Path x₀ x₁),
      Continuous
          (fun q : GenericLoopQuot X x₀ × GenericLoopQuot X x₀ =>
            _root_.Path.Homotopic.Quotient.trans q.1 q.2) ↔
        Continuous
          (fun q : GenericLoopQuot X x₁ × GenericLoopQuot X x₁ =>
            _root_.Path.Homotopic.Quotient.trans q.1 q.2)
  quotient_trans_continuity_all_basepoints :
    ∀ (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] (x₀ : X),
      Continuous
          (fun q : GenericLoopQuot X x₀ × GenericLoopQuot X x₀ =>
            _root_.Path.Homotopic.Quotient.trans q.1 q.2) ↔
        ∀ x : X, Continuous
          (fun q : GenericLoopQuot X x × GenericLoopQuot X x =>
            _root_.Path.Homotopic.Quotient.trans q.1 q.2)
  quotient_discrete_all_basepoints :
    ∀ (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] (x₀ : X),
      DiscreteTopology (GenericLoopQuot X x₀) ↔
        ∀ x : X, DiscreteTopology (GenericLoopQuot X x)
  quotient_t1_homotopy_invariant :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      (e : ContinuousMap.HomotopyEquiv X Y) (x : X),
      T1Space (GenericLoopQuot X x) ↔
        T1Space (GenericLoopQuot Y (e x))
  quotient_t1_basepoint_invariant :
    ∀ (X : Type u) [TopologicalSpace X] {x₀ x₁ : X}
      (p : _root_.Path x₀ x₁),
      T1Space (GenericLoopQuot X x₀) ↔
        T1Space (GenericLoopQuot X x₁)
  quotient_t1_all_basepoints :
    ∀ (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] (x₀ : X),
      T1Space (GenericLoopQuot X x₀) ↔
        ∀ x : X, T1Space (GenericLoopQuot X x)
  quotient_t1_all_basepoints_homotopy_invariant :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      [PathConnectedSpace X] [PathConnectedSpace Y]
      (e : ContinuousMap.HomotopyEquiv X Y) (x₀ : X),
      (∀ x : X, T1Space (GenericLoopQuot X x)) ↔
        ∀ y : Y, T1Space (GenericLoopQuot Y y)
  quotient_trans_continuity_all_basepoints_homotopy_invariant :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      [PathConnectedSpace X] [PathConnectedSpace Y]
      (e : ContinuousMap.HomotopyEquiv X Y) (x₀ : X),
      (∀ x : X, Continuous
        (fun q : GenericLoopQuot X x × GenericLoopQuot X x =>
          _root_.Path.Homotopic.Quotient.trans q.1 q.2)) ↔
        ∀ y : Y, Continuous
          (fun q : GenericLoopQuot Y y × GenericLoopQuot Y y =>
            _root_.Path.Homotopic.Quotient.trans q.1 q.2)
  quotient_topological_group_all_basepoints :
    ∀ (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] (x₀ : X),
      Nonempty (ContinuousMul (GenericLoopQuot X x₀)) ↔
        ∀ x : X, Nonempty (ContinuousMul (GenericLoopQuot X x))
  quotient_basepoint_change :
    ∀ (X : Type u) [TopologicalSpace X] {x₀ x₁ : X}
      (p : _root_.Path x₀ x₁),
      ∃ E : GenericLoopQuot X x₀ ≃ₜ GenericLoopQuot X x₁,
        ∀ q : GenericLoopQuot X x₀,
          E q =
            _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (Quotient.mk' p.symm) q)
              (Quotient.mk' p)
  quotient_basepoint_change_homotopy_invariant :
    ∀ (X : Type u) [TopologicalSpace X] {x₀ x₁ : X}
      (p q : _root_.Path x₀ x₁),
      p.Homotopic q →
        ∀ z : GenericLoopQuot X x₀,
          _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (Quotient.mk' p.symm) z)
              (Quotient.mk' p) =
            _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (Quotient.mk' q.symm) z)
              (Quotient.mk' q)
  quotient_basepoint_change_relative_comm :
    ∀ (X : Type u) [TopologicalSpace X] {x₀ x₁ : X}
      (p q : _root_.Path x₀ x₁),
      (∀ b : GenericLoopQuot X x₁,
        _root_.Path.Homotopic.Quotient.trans
            (_root_.Path.Homotopic.Quotient.trans
              (Quotient.mk' p.symm) (Quotient.mk' q)) b =
          _root_.Path.Homotopic.Quotient.trans b
            (_root_.Path.Homotopic.Quotient.trans
              (Quotient.mk' p.symm) (Quotient.mk' q))) →
        ∀ z : GenericLoopQuot X x₀,
          _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (Quotient.mk' p.symm) z)
              (Quotient.mk' p) =
            _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (Quotient.mk' q.symm) z)
              (Quotient.mk' q)
  quotient_basepoint_change_relative_comm_iff :
    ∀ (X : Type u) [TopologicalSpace X] {x₀ x₁ : X}
      (p q : _root_.Path x₀ x₁),
      (∀ z : GenericLoopQuot X x₀,
        _root_.Path.Homotopic.Quotient.trans
            (_root_.Path.Homotopic.Quotient.trans
              (Quotient.mk' p.symm) z)
              (Quotient.mk' p) =
          _root_.Path.Homotopic.Quotient.trans
            (_root_.Path.Homotopic.Quotient.trans
              (Quotient.mk' q.symm) z)
            (Quotient.mk' q)) ↔
      (∀ b : GenericLoopQuot X x₁,
        _root_.Path.Homotopic.Quotient.trans
            (_root_.Path.Homotopic.Quotient.trans
              (Quotient.mk' p.symm) (Quotient.mk' q)) b =
          _root_.Path.Homotopic.Quotient.trans b
            (_root_.Path.Homotopic.Quotient.trans
              (Quotient.mk' p.symm) (Quotient.mk' q)))
  quotient_basepoint_change_target_comm :
    ∀ (X : Type u) [TopologicalSpace X] {x₀ x₁ : X}
      (p q : _root_.Path x₀ x₁),
      (∀ a b : GenericLoopQuot X x₁, a * b = b * a) →
        ∀ z : GenericLoopQuot X x₀,
          _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (Quotient.mk' p.symm) z)
              (Quotient.mk' p) =
            _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (Quotient.mk' q.symm) z)
              (Quotient.mk' q)
  quotient_basepoint_change_composition :
    ∀ (X : Type u) [TopologicalSpace X]
      {x₀ x₁ x₂ : X} (p : _root_.Path x₀ x₁) (q : _root_.Path x₁ x₂),
      ∀ z : GenericLoopQuot X x₀,
        _root_.Path.Homotopic.Quotient.trans
            (_root_.Path.Homotopic.Quotient.trans
              (Quotient.mk' q.symm)
              (_root_.Path.Homotopic.Quotient.trans
                (_root_.Path.Homotopic.Quotient.trans
                  (Quotient.mk' p.symm) z)
                (Quotient.mk' p)))
            (Quotient.mk' q) =
            _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (Quotient.mk' (p.trans q).symm) z)
              (Quotient.mk' (p.trans q))
  quotient_basepoint_change_identity :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      ∀ z : GenericLoopQuot X x,
        _root_.Path.Homotopic.Quotient.trans
            (_root_.Path.Homotopic.Quotient.trans
              (Quotient.mk' (_root_.Path.refl x)) z)
            (Quotient.mk' (_root_.Path.refl x)) = z
  quotient_basepoint_change_reverse :
    ∀ (X : Type u) [TopologicalSpace X]
      {x₀ x₁ : X} (p : _root_.Path x₀ x₁),
      ∀ z : GenericLoopQuot X x₁,
        _root_.Path.Homotopic.Quotient.trans
            (_root_.Path.Homotopic.Quotient.trans
              (Quotient.mk' p.symm)
              (_root_.Path.Homotopic.Quotient.trans
                (_root_.Path.Homotopic.Quotient.trans
                  (Quotient.mk' p) z)
                (Quotient.mk' p.symm)))
            (Quotient.mk' p) = z
  quotient_basepoint_change_naturality :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      (f : C(X, Y)) {x₀ x₁ : X} (p : _root_.Path x₀ x₁)
      (q : GenericLoopQuot X x₀),
      _root_.Path.Homotopic.Quotient.map
          (_root_.Path.Homotopic.Quotient.trans
            (_root_.Path.Homotopic.Quotient.trans
              (Quotient.mk' p.symm) q)
            (Quotient.mk' p)) f =
        _root_.Path.Homotopic.Quotient.trans
          (_root_.Path.Homotopic.Quotient.trans
            (Quotient.mk' (p.map f.continuous).symm)
            (_root_.Path.Homotopic.Quotient.map q f))
          (Quotient.mk' (p.map f.continuous))
  quotient_map_homotopy_naturality :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      {f g : C(X, Y)} (H : f.Homotopy g) (x : X)
      (q : GenericLoopQuot X x),
      _root_.Path.Homotopic.Quotient.trans
          (_root_.Path.Homotopic.Quotient.trans
            (Quotient.mk' (H.evalAt x).symm)
            (_root_.Path.Homotopic.Quotient.map q f))
            (Quotient.mk' (H.evalAt x)) =
        _root_.Path.Homotopic.Quotient.map q g
  quotient_map_eq_of_pointed_homotopy :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      {f g : C(X, Y)} (H : f.Homotopy g) (x : X)
      (hfix : ∀ t : unitInterval, H (t, x) = f x),
      FundamentalGroup.mapOfEq f
          (show f x = g x by
            exact (hfix 1).symm.trans (H.apply_one x)) =
        FundamentalGroup.map g x
  quotient_path_connected_basepoint_independent :
    ∀ (X : Type u) [TopologicalSpace X] [PathConnectedSpace X]
      (x₀ x₁ : X),
      Nonempty (GenericLoopQuot X x₀ ≃ₜ* GenericLoopQuot X x₁)
  quotient_product_preserved :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      (x : X) (y : Y),
      IsQuotientMap
          (fun p : GenericLoop X x × GenericLoop Y y =>
            ((Quotient.mk' p.1 : GenericLoopQuot X x),
              (Quotient.mk' p.2 : GenericLoopQuot Y y))) →
        ∃ E : (GenericLoopQuot X x × GenericLoopQuot Y y) ≃ₜ
            GenericLoopQuot (X × Y) (x, y),
          ∀ q : GenericLoopQuot X x × GenericLoopQuot Y y,
            E q = _root_.Path.Homotopic.prod q.1 q.2
  quotient_product_hypothesis_sharp :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      (¬ Continuous
        (fun p : GenericLoopQuot X x × GenericLoopQuot X x =>
          _root_.Path.Homotopic.Quotient.trans p.1 p.2)) →
      ¬ IsQuotientMap
        (fun p : GenericLoop X x × GenericLoop X x =>
          ((Quotient.mk' p.1 : GenericLoopQuot X x),
            (Quotient.mk' p.2 : GenericLoopQuot X x)))
  quotient_symm_continuous :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      Continuous
        (_root_.Path.Homotopic.Quotient.symm :
          GenericLoopQuot X x → GenericLoopQuot X x)
  quotient_trans_left_continuous :
    ∀ (X : Type u) [TopologicalSpace X] (x : X)
      (a : GenericLoopQuot X x),
      Continuous
        (fun b : GenericLoopQuot X x =>
          _root_.Path.Homotopic.Quotient.trans a b)
  quotient_trans_right_continuous :
    ∀ (X : Type u) [TopologicalSpace X] (x : X)
      (b : GenericLoopQuot X x),
      Continuous
        (fun a : GenericLoopQuot X x =>
          _root_.Path.Homotopic.Quotient.trans a b)
  quotient_homogeneous :
    ∀ (X : Type u) [TopologicalSpace X] (x : X)
      (a b : GenericLoopQuot X x),
      ∃ e : GenericLoopQuot X x ≃ₜ GenericLoopQuot X x, e a = b
  quotient_discrete_iff_null_class_open :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      DiscreteTopology (GenericLoopQuot X x) ↔
        IsOpen (nullHomotopyClass X x)
  quotient_t1_iff_null_class_closed :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      T1Space (GenericLoopQuot X x) ↔
        IsClosed (nullHomotopyClass X x)
  quotient_t1_iff_all_classes_closed :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      T1Space (GenericLoopQuot X x) ↔
        ∀ γ : GenericLoop X x,
          IsClosed {δ : GenericLoop X x | γ.Homotopic δ}
  quotient_discrete_implies_semilocally_simply_connected :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      DiscreteTopology (GenericLoopQuot X x) →
        ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.SemilocallySimplyConnectedAt
          X x
  quotient_discrete_iff_semilocally_simply_connected_in_locally_path_connected_spaces :
    ∀ (X : Type u) [TopologicalSpace X]
      [LocallyPathConnectedSpace X],
      ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.SemilocallySimplyConnected X ↔
        ∀ x : X, DiscreteTopology (GenericLoopQuot X x)
  homotopy_classes_open_of_semilocally_simply_connected :
    ∀ (X : Type u) [TopologicalSpace X]
      [LocallyPathConnectedSpace X],
      ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.SemilocallySimplyConnected X →
        ∀ x : X, ∀ γ : GenericLoop X x,
          IsOpen {δ : GenericLoop X x | γ.Homotopic δ}
  semilocally_simply_connected_homotopy_invariant :
    ∀ (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
      [LocallyPathConnectedSpace X] [LocallyPathConnectedSpace Y]
      (e : ContinuousMap.HomotopyEquiv X Y),
      ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.SemilocallySimplyConnected X ↔
        ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.SemilocallySimplyConnected Y
  semilocally_simply_connected_iff_quotient_discrete_at_of_path_connected :
    ∀ (X : Type u) [TopologicalSpace X]
      [LocallyPathConnectedSpace X] [PathConnectedSpace X] (x₀ : X),
      ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.SemilocallySimplyConnected X ↔
        DiscreteTopology (GenericLoopQuot X x₀)
  covering_map_induces_injection :
    ∀ (E B : Type u) [TopologicalSpace E] [TopologicalSpace B]
      (p : E → B) (hp : IsCoveringMap p) (e : E),
      Function.Injective
        (fun q : GenericLoopQuot E e =>
          _root_.Path.Homotopic.Quotient.map q ⟨p, hp.continuous⟩)
  covering_map_image_is_monodromy_stabilizer :
    ∀ (E B : Type u) [TopologicalSpace E] [TopologicalSpace B]
      (p : E → B) (hp : IsCoveringMap p) (e : E)
      (q : GenericLoopQuot B (p e)),
      q ∈ Set.range (fun r : GenericLoopQuot E e =>
          _root_.Path.Homotopic.Quotient.map r ⟨p, hp.continuous⟩) ↔
        hp.monodromy q ⟨e, rfl⟩ = ⟨e, rfl⟩
  quotient_topological_group_agreement :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      Continuous
          (fun p : GenericLoopQuot X x × GenericLoopQuot X x =>
            _root_.Path.Homotopic.Quotient.trans p.1 p.2) ↔
        Nonempty (ContinuousMul (GenericLoopQuot X x))
  homotopy_classes_open_of_null_class_open :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      IsOpen (nullHomotopyClass X x) →
      ∀ γ : GenericLoop X x,
        IsOpen {δ : GenericLoop X x | γ.Homotopic δ}
  quotient_open_of_null_class_open :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      IsOpen (nullHomotopyClass X x) →
      IsOpenQuotientMap
        (Quotient.mk' : GenericLoop X x → GenericLoopQuot X x)
  quotient_square_of_null_class_open :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      IsOpen (nullHomotopyClass X x) →
      IsQuotientMap
        (fun p : GenericLoop X x × GenericLoop X x =>
          ((Quotient.mk' p.1 : GenericLoopQuot X x),
            (Quotient.mk' p.2 : GenericLoopQuot X x)))
  quotient_trans_continuous_of_null_class_open :
    ∀ (X : Type u) [TopologicalSpace X] (x : X),
      IsOpen (nullHomotopyClass X x) →
      Continuous
        (fun p : GenericLoopQuot X x × GenericLoopQuot X x =>
          _root_.Path.Homotopic.Quotient.trans p.1 p.2)

abbrev Circle : Type := AddCircle (1 : ℝ)
abbrev FiniteTorus (n : ℕ) : Type := Fin n → Circle
noncomputable abbrev base (n : ℕ) : FiniteTorus n := fun _ => 0
abbrev Loop (n : ℕ) : Type := _root_.Path (base n) (base n)
abbrev LoopQuot (n : ℕ) : Type :=
  _root_.Path.Homotopic.Quotient (base n) (base n)
abbrev WindingVector (n : ℕ) : Type := Fin n → ℤ

/-! Statement-facing matrix actions used to expose the cokernel composition
certificate without importing the substantive finite-torus module. -/
noncomputable def matrixAction {n m : ℕ} (A : Fin m → Fin n → ℤ) :
    (Fin n → ℤ) →+ (Fin m → ℤ) where
  toFun z j := ∑ i : Fin n, A j i * z i
  map_zero' := by
    ext j
    simp
  map_add' z w := by
    ext j
    simp [mul_add, Finset.sum_add_distrib]

def matrixCompose {n m k : ℕ}
    (A : Fin m → Fin n → ℤ) (B : Fin k → Fin m → ℤ) :
    Fin k → Fin n → ℤ :=
  fun l i => ∑ j : Fin m, B l j * A j i

/-- Coordinate-selection maps between finite tori, used to state winding
naturality without importing the substantive implementation. -/
noncomputable def coordinateProjection {n m : ℕ} (f : Fin m → Fin n) :
    C(FiniteTorus n, FiniteTorus m) :=
  ⟨fun x j => x (f j), continuous_pi (fun j => continuous_apply (f j))⟩

noncomputable def coordinateReindex {n m : ℕ} (f : Fin m → Fin n) :
    WindingVector n → WindingVector m :=
  fun z j => z (f j)

noncomputable instance loopQuotTopology (n : ℕ) :
    TopologicalSpace (LoopQuot n) :=
  TopologicalSpace.coinduced
    (Quotient.mk' : Loop n → LoopQuot n) inferInstance

/-- Full publication-facing certificate for the finite-torus theorem. -/
structure FiniteTorusTopologicalClassification (n : ℕ) where
  winding : Loop n → WindingVector n
  winding_coordinate_projection :
    ∀ (f : Fin n → Fin n) (γ : Loop n),
      winding (γ.map (coordinateProjection f).continuous) =
        fun j => winding γ (f j)
  standardLoop : WindingVector n → Loop n
  standard_loop_coordinate_projection :
    ∀ (f : Fin n → Fin n) (z : WindingVector n),
      (standardLoop z).map (coordinateProjection f).continuous =
        standardLoop (fun j => z (f j))
  classifier : LoopQuot n ≃ₜ WindingVector n
  classifier_coordinate_projection :
    ∀ (f : Fin n → Fin n) (q : LoopQuot n),
      classifier (_root_.Path.Homotopic.Quotient.map q (coordinateProjection f)) =
        fun j => classifier q (f j)
  classifier_continuous_mul_equiv :
    LoopQuot n ≃ₜ* Multiplicative (WindingVector n)
  classifier_multiplicative_coordinate_projection :
    ∀ (f : Fin n → Fin n) (q : LoopQuot n),
      Multiplicative.ofAdd (coordinateReindex f (classifier q)) =
        classifier_continuous_mul_equiv
          (_root_.Path.Homotopic.Quotient.map q (coordinateProjection f))
  classifier_continuous_mul_equiv_at :
    ∀ x : FiniteTorus n,
      ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.LoopQuot
          (FiniteTorus n) x ≃ₜ* Multiplicative (WindingVector n)
  classifier_continuous_mul_equiv_at_path :
    ∀ (x : FiniteTorus n) (p : _root_.Path (base n) x),
      ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.LoopQuot
          (FiniteTorus n) x ≃ₜ* Multiplicative (WindingVector n)
  classifier_at_path_coordinate_projection :
    ∀ (f : Fin n → Fin n) (x : FiniteTorus n)
      (p : _root_.Path (base n) x)
      (q : ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.LoopQuot
        (FiniteTorus n) x),
      classifier_continuous_mul_equiv_at_path
          (coordinateProjection f x)
          (p.map (coordinateProjection f).continuous)
          (_root_.Path.Homotopic.Quotient.map q (coordinateProjection f)) =
        Multiplicative.ofAdd
          (coordinateReindex f
            (Multiplicative.toAdd
              (classifier_continuous_mul_equiv_at_path x p q)))
  classifier_at_coordinate_projection :
    ∀ (f : Fin n → Fin n) (x : FiniteTorus n)
      (q : ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.LoopQuot
        (FiniteTorus n) x),
      classifier_continuous_mul_equiv_at
          (coordinateProjection f x)
          (_root_.Path.Homotopic.Quotient.map q (coordinateProjection f)) =
        Multiplicative.ofAdd
          (coordinateReindex f
            (Multiplicative.toAdd
              (classifier_continuous_mul_equiv_at x q)))
  classifier_continuous_mul_equiv_at_path_independent :
    ∀ (x : FiniteTorus n) (p q : _root_.Path (base n) x),
      classifier_continuous_mul_equiv_at_path x p =
        classifier_continuous_mul_equiv_at_path x q
  quotient_mul_commutative :
    ∀ x y : LoopQuot n, x * y = y * x
  quotient_mul_commutative_at :
    ∀ (x : FiniteTorus n)
      (p q : ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.LoopQuot
        (FiniteTorus n) x),
      p * q = q * p
  classifier_at :
    ∀ x : FiniteTorus n,
      ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.LoopQuot
          (FiniteTorus n) x ≃ₜ WindingVector n
  classifier_mk :
    ∀ γ : Loop n, classifier (Quotient.mk' γ) = winding γ
  winding_standard :
    ∀ z : WindingVector n, winding (standardLoop z) = z
  standard_complete :
    ∀ γ : Loop n, (standardLoop (winding γ)).Homotopic γ
  winding_identity :
    winding (_root_.Path.refl (base n)) = 0
  winding_trans :
    ∀ γ δ : Loop n, winding (γ.trans δ) = winding γ + winding δ
  classifier_trans :
    ∀ x y : LoopQuot n,
      classifier (_root_.Path.Homotopic.Quotient.trans x y) =
        classifier x + classifier y
  quotient_discrete : DiscreteTopology (LoopQuot n)
  quotient_discrete_at :
    ∀ x : FiniteTorus n,
      DiscreteTopology
        (ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.LoopQuot
          (FiniteTorus n) x)
  semilocally_simply_connected :
    ComputationalPaths.Path.GeometricTopology.QuotientFundamentalGroup.SemilocallySimplyConnected
      (FiniteTorus n)
  null_class_open :
    IsOpen (nullHomotopyClass (FiniteTorus n) (base n))
  homotopy_classes_open :
    ∀ γ : Loop n, IsOpen {δ : Loop n | _root_.Path.Homotopic γ δ}
  quotient_square :
    IsQuotientMap
      (fun p : Loop n × Loop n =>
        ((Quotient.mk' p.1 : LoopQuot n),
          (Quotient.mk' p.2 : LoopQuot n)))
  quotient_trans_continuous :
    Continuous
      (fun p : LoopQuot n × LoopQuot n =>
        _root_.Path.Homotopic.Quotient.trans p.1 p.2)
  quotient_symm_continuous :
    Continuous
      (_root_.Path.Homotopic.Quotient.symm :
        LoopQuot n → LoopQuot n)
  matrix_cokernel_short_exact :
    ∀ (A B : Fin n → Fin n → ℤ) (hB : Matrix.det B ≠ 0),
      ∃ f : (Fin n → ℤ) ⧸ (matrixAction A).range →+
          (Fin n → ℤ) ⧸ (matrixAction (matrixCompose A B)).range,
      ∃ g : (Fin n → ℤ) ⧸ (matrixAction (matrixCompose A B)).range →+
          (Fin n → ℤ) ⧸ (matrixAction B).range,
      ∃ e : (((Fin n → ℤ) ⧸ (matrixAction (matrixCompose A B)).range) ⧸ g.ker) ≃+
          (Fin n → ℤ) ⧸ (matrixAction B).range,
        Function.Injective f ∧ g.ker = f.range ∧ Function.Surjective g
  matrix_cokernel_rectangular_short_exact :
    ∀ {n m k : ℕ} (A : Fin m → Fin n → ℤ)
      (B : Fin k → Fin m → ℤ)
      (hB : Function.Injective (matrixAction B)),
      ∃ f : (Fin m → ℤ) ⧸ (matrixAction A).range →+
          (Fin k → ℤ) ⧸
            (matrixAction (matrixCompose A B)).range,
      ∃ g : (Fin k → ℤ) ⧸
          (matrixAction (matrixCompose A B)).range →+
          (Fin k → ℤ) ⧸ (matrixAction B).range,
      ∃ e : (((Fin k → ℤ) ⧸
          (matrixAction (matrixCompose A B)).range) ⧸ g.ker) ≃+
          (Fin k → ℤ) ⧸ (matrixAction B).range,
        Function.Injective f ∧ g.ker = f.range ∧ Function.Surjective g

/-- The general criterion and its winding-classified finite-torus family. -/
theorem main_result :
    Nonempty QuotientTopologicalFundamentalGroupTheory ∧
      ∀ n : ℕ, Nonempty (FiniteTorusTopologicalClassification n) := by
  sorry

end TopologicalComputationalPathsFollowup
