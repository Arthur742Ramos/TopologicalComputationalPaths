# Follow-up: quotient-topological fundamental groups

## Selected result

The follow-up is centered on a theorem for every pointed topological space,
not on a new computation of the fundamental group of a torus.

For the endpoint-fixed homotopy quotient of the compact-open based loop space,
the formalization proves:

1. every continuous map induces a continuous homomorphism, with formal
   identity and composition laws;
2. homotopy equivalences induce continuous multiplicative equivalences
   (strictly strengthening homeomorphism invariance);
3. every path between basepoints induces a continuous multiplicative
   equivalence between the corresponding quotient fundamental groups;
4. arbitrary indexed products are preserved by a continuous multiplicative
   equivalence whenever the indexed product of the loop projections is a
   quotient map (with the binary theorem as a concrete specialization);
5. reversal is continuous;
6. concatenation is continuous in each variable separately;
7. right translations are homeomorphisms, so the quotient is homogeneous;
8. the quotient is T1 if and only if the null-homotopy class is closed,
   equivalently if every based-loop homotopy class is closed;
9. the quotient is discrete if and only if the null-homotopy class is open in
   the based loop space; and
10. discreteness implies semilocal simple connectivity at the basepoint;
11. in locally path-connected spaces, semilocal simple connectivity implies
    openness of every based-loop homotopy class and discreteness of every
    based quotient fundamental group; and
12. quotient discreteness is invariant under homotopy equivalence and under
    basepoint change along a path; and
13. among locally path-connected spaces, semilocal simple connectivity is a
   homotopy invariant; and
14. joint continuity of quotient concatenation (equivalently, the genuine
    topological-group structure) is invariant under homotopy equivalence; and
15. under the exact open-null-class criterion, every homotopy class is open, the quotient map
   is open, its square is a quotient map, and concatenation is jointly
   continuous for the ordinary product topology.
16. the basepoint-change equivalence depends only on the endpoint-fixed
    homotopy class of the chosen path.
17. basepoint transport composes along concatenated paths, giving a coherent
   transport system on the fundamental-groupoid basepoints.
18. transport along a constant path is the identity equivalence, completing
    the identity/composition coherence laws for basepoint transport.
19. continuous maps preserve concatenation of endpoint-fixed path classes;
    and
20. basepoint transport is natural for continuous maps, so induced quotient
    maps commute with transport along mapped paths.
21. a homotopy between continuous maps induces the corresponding conjugacy
    relation on quotient maps, with the homotopy's basepoint path as witness.
22. the joint-continuity/topological-group boundary is also invariant under
    basepoint change along a path.
23. a homotopy that fixes the chosen basepoint throughout induces equal based
    homomorphisms, with the endpoint equality handled by `mapOfEq`.
24. on a path-connected space, joint continuity at one basepoint is equivalent
    to joint continuity at every basepoint.
25. on a path-connected space, discreteness at one basepoint is equivalent to
    discreteness at every basepoint.
26. between path-connected spaces, the global joint-continuity property is
    invariant under homotopy equivalence.
27. on a path-connected space, the genuine topological-group boundary can be
    checked at one basepoint or at every basepoint.
28. in locally path-connected, path-connected spaces, semilocal simple
    connectivity is equivalent to discreteness at one chosen basepoint.
29. T1 separation of the quotient is invariant under homotopy equivalence and
    path-based basepoint transport.
30. on a path-connected space, T1 separation at one basepoint is equivalent
    to T1 separation at every basepoint, and this global property is homotopy
    invariant between path-connected spaces.
31. if the target quotient group is abelian, basepoint transport is independent
    of the chosen path even without an endpoint-fixed homotopy between paths.
32. more generally, two transports agree if and only if their relative loop is
    central in the target quotient group.
33. finite-torus winding is natural under every coordinate-selection map; the
    induced quotient classifier reindexes the integer lattice vector.
34. the coordinate-selection maps satisfy identity and composition coherence,
    giving the reindexing construction an explicit contravariant functorial
    interface.
35. reversing a basepoint path gives the inverse continuous multiplicative
    transport, completing the groupoid-action coherence.

The distinction between separate and joint continuity is essential.  The
formalization now proves that discontinuous quotient multiplication forces
the product of loop quotient maps not to be a quotient map, and instantiates
this theorem with the accepted package's Fabel-style Hawaiian-earring facts.
Thus the product hypothesis is formally sharp at the existing negative
example.  It also proves that the quotient topology itself is a genuine
topological-group topology exactly when multiplication is jointly continuous.

Covering maps additionally induce injective continuous homomorphisms on these
quotient fundamental groups, by unique path lifting.

## Finite-torus application

For every `n`, coordinate winding classifies genuine compact-open loops in
the finite torus `(Fin n → AddCircle 1)` modulo endpoint-fixed homotopy:

```text
Path.Homotopic.Quotient (0 : (Fin n → AddCircle 1)) 0 ≃ₜ (Fin n → ℤ).
```

The formalization constructs coordinatewise standard loops, proves winding
completeness and additivity, proves the null class open, and applies the
general criterion.  It obtains a discrete quotient, an open quotient map, a
quotient square, and continuous concatenation and reversal.  Internally,
winding is also packaged as a continuous additive equivalence, and the
transported addition is proved equal to path-class concatenation.  The same
classifier is exposed as a continuous multiplicative equivalence to
`Multiplicative (Fin n → ℤ)`, so the actual quotient multiplication is
identified with lattice addition and is commutative.  Dimensions `0` and `1`
are included uniformly.  The new basepoint-transport theorem
upgrades the discrete quotient statement from the zero basepoint to every
point of the torus; the resulting theorem packages semilocal simple
connectivity at all points for every finite torus.  The same transport gives a
continuous multiplicative equivalence (and hence commutativity) from every
based quotient to the same integer lattice, so the classification is
independent of the chosen basepoint as a topological and algebraic statement,
not only as a discreteness statement.  More strongly, the classifier may be
defined along any explicit path from the canonical basepoint, and all such
path-based classifiers are equal by the abelian-target transport theorem.
The core classifier is also natural for every coordinate-selection map
`Fin m → Fin n`: the induced loop and quotient maps simply reindex the
integer winding vector (with the fixed-dimensional instance exposed in the
publication certificate).
The explicit standard-loop representatives and quotient decoder obey the same
reindexing equation.
The coordinate-selection maps themselves satisfy identity and composition
coherence, so this is an explicit contravariant functorial interface.

## Literature and novelty boundary

The mathematical facts that the quotient fundamental group is a
quasitopological group, is homogeneous, and is discrete for familiar
semilocally simply connected spaces are established in the literature.  The
circle and finite-torus fundamental-group calculations are classical.  This
package makes no novelty claim for those paper theorems.

The new follow-up proof closes the locally path-connected converse explicitly
at the compact-open level: a finite path subdivision, path-connected vertex
refinement, and finite homotopy ladder produce an open class around each loop.
It then transports quotient discreteness across the continuous quotient
equivalences induced by homotopy equivalences and basepoint paths, giving
homotopy invariance of semilocal simple connectivity in the stated locally
path-connected category.  The same multiplicative homeomorphisms transport
the boundary between separate and joint continuity, so the topological-group
failure is itself a homotopy-invariant quotient-topology phenomenon.  The
basepoint-change maps are also proved independent of the chosen path
representative whenever two paths are endpoint-fixed homotopic.
They satisfy the corresponding composition law for concatenated paths, so
the transport is coherent as well as homotopy-invariant.  Transport along a
constant path is separately identified with the identity equivalence, so the
coherence package has both its unit and composition laws explicitly.  Reversing
a path is also proved to give the inverse continuous multiplicative transport,
so these laws assemble into a genuine groupoid action.  Finally,
when the target quotient is abelian, the path-independence statement no longer
requires a homotopy between the paths; this is the mechanism that makes the
finite-torus lattice classifier canonical at each basepoint.
The formal proof actually characterizes equality by relative centrality, so
the abelian result is a corollary rather than the limit of the transport
argument.
Quotient functoriality is recorded at the path-composition level, and the
basepoint-change equivalences satisfy the resulting naturality square for
every continuous map.
The pointed homotopy-naturality law is also exposed: a homotopy between maps
relates their induced quotient maps by conjugation along the path traced at the
basepoint.
The same continuous multiplicative transport preserves the joint-continuity
boundary at any two basepoints connected by a path.
As a pointed specialization, when the homotopy is constant at the chosen
basepoint, the two induced based homomorphisms are equal after the canonical
endpoint cast.
For path-connected spaces, the basepoint result upgrades this to a global
criterion: the topological-group boundary may be checked at any one chosen
basepoint or simultaneously at all basepoints.
The same path-connected upgrade holds for discreteness, and the global
joint-continuity property is invariant under homotopy equivalences between
path-connected spaces.  In the locally path-connected setting, the
semilocal/discrete equivalence therefore reduces to a single chosen
basepoint.  The basepoint equivalence exposed by the certificate is
continuous and multiplicative, so these are algebraic-topological statements,
not only bare homeomorphism assertions.
The T1/closed-class boundary is transported by the same homotopy and path
equivalences.  Consequently, on path-connected spaces a single based quotient
detects the T1 status of every based quotient, and homotopy-equivalent
path-connected spaces have the same global T1 status.

The contribution is a focused, kernel-checked Lean realization that connects
the general quotient-topological mechanism to explicit compact-open winding
classifiers and to the final-versus-ordinary product distinction of the
accepted computational-path package.  Exact source relationships are recorded
in `formalization-followup.yaml`.

## Verification surface

- `FollowupChallenge.lean` and `FollowupSolution.lean`;
- `ComputationalPaths/Path/Topology/QuotientFundamentalGroupFunctorial.lean`;
- `TopologicalComputationalPathsFollowup.main_result`;
- `comparator-followup.json`;
- `formalization-followup.yaml`;
- `scripts/check-followup.sh`; and
- `scripts/verify-comparator.sh comparator-followup.json`.

The challenge contains one deliberate statement-side `sorry`.  The solution
and substantive modules contain none.
