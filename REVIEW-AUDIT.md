# Follow-up reassessment — 2026-09-06

The artifact is not yet demonstrated to meet the research-interest objection.
Passing Lean, Comparator and NanoDa establishes mechanical properties, not
novelty or research significance. This revision repairs a selected-statement
weakening and removes unsupported promotional claims; it is not a new submission.

Implementation follow-through: a separate `comparator-preimage.json` artifact
now implements the certificate-driven solver proposed below, including
certificate existence for all rectangular matrices, witnesses, row obstructions,
and the complete affine kernel family in fixed torus semantics. See
PREIMAGE-RESEARCH-NOTE.md. This addresses the missing executable interface but
does not itself settle the research-interest objection or constitute submission.

| Issue | Finding and disposition |
| --- | --- |
| Topological classifier | The previous selected field was only an equivalence. Added continuity of the classifier and its inverse, using the explicit coinduced topology on the actual loop quotient. |
| Concrete trace semantics | The list syntax and recursive loop realization are genuine, but letters range over all integer vectors. The zero/one minimum is elementary for this alphabet. It is not geometric length, coordinate-generator length, rewrite complexity or bit complexity. |
| Winding identification | The solution instantiates concrete winding and standard loops. The selected proposition existentially quantifies these witnesses and constrains them by laws; it does not pin a unique oriented winding definition. |
| Exactness scope | The selected rectangular short exact sequence and Smith profiles are lattice statements. Image, injectivity, surjectivity and Smith image criteria are connected to actual quotient matrix maps. The stronger repository quotient-level exact-sequence wrappers are not selected. |
| Finite/free boundary | Finite cardinality and prime-support conclusions retain finite-cokernel hypotheses. Zero Smith factors retain free ZMod 0 directions. No new finite formula is claimed for those directions. |
| Provenance | Classical sources remain ingredient sources. Not finding this exact bundle does not imply that its mathematical content is new. The earlier bounded inventory is not an exhaustive priority audit. |
| Research interest | Unresolved. Renaming the bundle a methods contribution or adding a trivial normal form does not address this objection. |
| Mechanical delivery | Revised Lean build, Comparator statement comparison, NanoDa and Lean kernel replay, both metadata validations, and the follow-up quality gate all passed on 2026-09-06. Challenge: 1,000 lines, 51,972 bytes. Existing linter warnings remain. |

## What would substantively strengthen the research case

A focused contribution needs an independently assessable benefit: for example,
a certified executable integer-matrix procedure with a proved end-to-end
connection to the topological question and informative benchmarks, or a
nonroutine topological application of the interface. These are proposals, not
implemented results or guarantees of acceptance. Merely replacing the alphabet
with signed coordinate generators and proving the classical l1 minimum would
improve cost semantics but would not by itself establish research novelty.

The existing broad supporting inventory should not be offered as if it were
part of the selected theorem. A future submission should identify the exact new
result, compare its closest prior work, and explain its research benefit before
another external intake.

## Sources checked for this reassessment

- [Hatcher's Algebraic Topology](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf):
  the fundamental group of the finite torus is a classical computation.
- [Palomar overview](https://palomar-registry.org/about):
  mechanical verification and the minimum research-interest review are distinct;
  registration is not publication.

This is a focused reassessment, not a comprehensive new literature survey.
