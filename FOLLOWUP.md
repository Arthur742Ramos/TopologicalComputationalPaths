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
transported addition is proved equal to path-class concatenation.  Dimensions
`0` and `1` are included uniformly.  The new basepoint-transport theorem
upgrades the discrete quotient statement from the zero basepoint to every
point of the torus; the resulting theorem packages semilocal simple
connectivity at all points for every finite torus.  The same transport gives a
homeomorphism from every based quotient to the same integer lattice, so the
classification is independent of the chosen basepoint as a topological
statement, not only as a discreteness statement.

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
failure is itself a homotopy-invariant quotient-topology phenomenon.

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
