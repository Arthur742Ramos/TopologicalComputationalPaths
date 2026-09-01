# First-presentation audit for the selected follow-up

Audit date: 2026-09-01

This note documents the provenance boundary for the exact declaration selected
by `comparator-followup.json`:

```text
TopologicalComputationalPathsFollowup.topological_smith_exactness
```

The `original-proof` source label is deliberately limited to the exact
six-field synthesis stated by `TopologicalSmithExactnessCertificate`.  It does
not claim first discovery of winding numbers, fundamental groups, Smith normal
form, determinant indices, or the ordinary algebraic topology used as
ingredients.

The comparison was made on 2026-09-01 against the pinned source records in
`formalization.yaml`, the parent manuscript snapshot, and the repository's
selected declaration.  The question was whether one source states the whole
six-field conjunction below—not whether a source contains one of its standard
ingredients.  The negative result is recorded conservatively: it supports the
bounded first-presentation description of this exact synthesis, but does not
make a priority claim about any ingredient or about the independent concrete
path APIs in the repository.

## Comparison record

| Source | What it supplies | What is absent from the selected bundle |
| --- | --- | --- |
| Hatcher, *Algebraic Topology*, Chapter 1 | Circle winding, products, and the classical computation of torus fundamental groups | The quotient-topological homeomorphism, the all-rectangular matrix action, the Smith-coordinate image test, and the combined Lean certificate |
| Norman, *Finitely Generated Abelian Groups and Similarity of Matrices over a Field* | Smith/invariant-factor decompositions and finite/free abelian-group calculations | The finite-torus quotient, winding classifier, topological matrix naturality, and path-presentation fields |
| Brazas--Fabel, *On Fundamental Groups with the Quotient Topology* | Quotient-topological and quasitopological fundamental-group context | The finite-torus winding/Smith comparison and its rectangular cokernel package |
| Calcut--McCarthy, *Discreteness and Homogeneity of the Topological Fundamental Group* | Discreteness and homogeneity context for quotient fundamental groups | The selected winding-lattice matrix certificate and its Smith image obstruction |
| Ramos--de Queiroz--Grisi de Oliveira--de Veras, *Topological Semantics for Scoped Computational Paths* | The parent computational-path setting and its topological semantics | The finite-torus Smith synthesis selected here; the selected bridge is intentionally only an abstract traced presentation |
| Mathlib (pinned revision in `formalization.yaml`) | Kernel-checked APIs used to implement the definitions and proofs | No prior statement of this exact six-field theorem group |

The audit checked each source for all six top-level fields of the selected
structure, rather than treating a list of ingredients as the result:

1. `winding_matrix_compatibility`, including the quotient winding classifier,
   rectangular matrix naturality, and the Smith image criterion (with its
   nested abstract traced-presentation bridge);
2. `matrix_composition`;
3. `rectangular_composition_profile`, including its finite-cokernel gates;
4. `smith_cokernel_profile`, including explicit free `ZMod 0` factors;
5. `determinant_index`; and
6. `prime_power_torsion_profile`.

The nested abstract-trace normal-form and matrix-realizability fields are
therefore part of item 1's stated structure, not an unrecorded seventh result.

No source in the comparison record presents that conjunction as one theorem or
formal certificate.  We therefore record this submission as the first
presentation of this exact bundled theorem group, while explicitly treating
the ingredients above as prior classical mathematics or contextual
formalization.  This is a bounded first-presentation claim based on the audit,
not a priority claim for any ingredient theorem and not a claim that the
repository's local implementation is an external source.

The concrete endpoint-varying `ComputationalPaths.Path` developments in this
repository are supporting material.  The selected declaration's traced field
is honestly described as an abstract interface with arbitrary raw types and
based-loop realizations; no first-presentation claim is made for those
supporting APIs.
