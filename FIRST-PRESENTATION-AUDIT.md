# Provenance audit for the selected follow-up

Audit date: 2026-09-01

This note documents the provenance boundary for the exact declaration selected
by `comparator-followup.json`:

```text
TopologicalComputationalPathsFollowup.topological_smith_exactness
```

The `original-proof` source label is deliberately limited to the exact
three-layer synthesis selected by the declaration: the covering-map
monodromy-stabilizer criterion, the sharp product-quotient obstruction, and the
nine-field `TopologicalSmithExactnessCertificate`.  It does not claim first
discovery of winding numbers, fundamental groups, Smith normal form, determinant
indices, or the ordinary algebraic topology used as ingredients.
It records that this repository supplies the checked proof of the exact bundle;
priority and novelty of the underlying mathematics are left unknown unless a
separate source comparison establishes them.

The comparison was made on 2026-09-01 against the pinned source records in
`formalization.yaml`, the parent manuscript snapshot, and the repository's
selected declaration.  The question was whether one source states the whole
three-layer certificate below—not whether a source contains one of its standard
ingredients.  The negative result is recorded conservatively: it supports the
bounded provenance description of this exact synthesis, but does not make a
priority claim about the bundle, any ingredient, or the independent concrete
path APIs in the repository.

## Comparison record

| Source | What it supplies | What is absent from the selected bundle |
| --- | --- | --- |
| Hatcher, *Algebraic Topology*, Chapter 1 | Circle winding, products, and the classical computation of torus fundamental groups | The quotient-topological homeomorphism, the all-rectangular matrix action, the cokernel exactness/first-isomorphism package, the Smith-coordinate image test, and the combined Lean certificate |
| Norman, *Finitely Generated Abelian Groups and Similarity of Matrices over a Field* | Smith/invariant-factor decompositions and finite/free abelian-group calculations | The finite-torus quotient, winding classifier, rectangular exact-sequence packaging, topological matrix naturality, and path-presentation fields |
| Brazas--Fabel, *On Fundamental Groups with the Quotient Topology* | Quotient-topological and quasitopological fundamental-group context | The finite-torus winding/Smith comparison and its rectangular cokernel package |
| Calcut--McCarthy, *Discreteness and Homogeneity of the Topological Fundamental Group* | Discreteness and homogeneity context for quotient fundamental groups | The selected winding-lattice matrix certificate and its Smith image obstruction |
| Ramos--de Queiroz--Grisi de Oliveira--de Veras, *Topological Semantics for Scoped Computational Paths* | The parent computational-path setting and its topological semantics | The finite-torus Smith synthesis selected here; the selected bridge is intentionally only an abstract traced presentation |
| Mathlib (pinned revision in `formalization.yaml`) | Kernel-checked APIs used to implement the definitions and proofs | No prior statement of this exact three-layer theorem group |

The audit checked each source for both general topological fields and all
nine top-level fields of the selected certificate, rather than treating a list
of ingredients as the result:

1. the covering-map image-equals-monodromy-stabilizer criterion;
2. the sharp product-quotient obstruction under failure of joint continuity;
3. `rectangular_cokernel_short_exact`, including the exact sequence and
   first-isomorphism quotient;
4. `winding_matrix_compatibility`, including the quotient winding classifier,
   rectangular matrix naturality, and the Smith image criterion (with its
   nested abstract traced-presentation bridge);

5. `matrix_composition`;
6. `rectangular_composition_profile`, including its finite-cokernel gates;
7. `smith_cokernel_profile`, including explicit free `ZMod 0` factors;
8. `determinant_index`; and
9. `prime_power_torsion_profile`.

The nested abstract-trace normal-form and matrix-realizability fields are
therefore part of item 4's stated structure, not an unrecorded tenth result.

No source in the comparison record presents that certificate as one theorem or
formal certificate.  We therefore record the local development as an
`original-proof` source for this exact bundled statement, while leaving
mathematical novelty and priority unknown.  This is a bounded provenance record
based on the audit, not a priority claim for any ingredient theorem and not a
claim that the repository's local implementation is an external source.

The concrete endpoint-varying `ComputationalPaths.Path` developments in this
repository are supporting material.  The selected declaration's traced field
is honestly described as an abstract interface with arbitrary raw types and
based-loop realizations; no first-presentation claim is made for those
supporting APIs.
