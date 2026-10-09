# Optional formalization extensions

Source assessment: 8 October 2026, integrated proof source
`1922376592442324448b474de068db6a09af18f8`, Lean 4.32.0 and Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`. These are proposed additional
results, not claims made by the present paper or blockers for its editorial
revision. No implementation or new example family was started.

## Ordinary quotient-topological fundamental group of the rose

The desired result is a homeomorphism from the compact-open based-loop
homotopy quotient of the actual rose to discrete F2, compatible with the
existing realization comparison. It would connect the nonabelian example
more directly to the paper's topological semantics. Its geometric and
algebraic foundations are already checked, so this is the more useful next
mathematical milestone.

A route through the covering avoids a new development of local rose charts:

1. Use Mathlib's `ContinuousEval (Path x y) I X` to make the universal family
   of based rose loops jointly continuous. `IsCoveringMap.liftHomotopy`
   lifts this family continuously to the actual Cayley realization, with
   constant initial vertex. Endpoint evaluation gives a continuous map into
   the fiber over the rose basepoint.
2. The covering fiber is discrete by `discreteTopology_fiber`. Prove that the
   inverse image of its initial vertex is precisely the null-homotopy class,
   using the checked monodromy equivalence and the simple-connectivity
   instance supplied by `CayleyContraction.simplyConnected`. That makes the
   null class open; apply `QuotientFundamentalGroup.quotientDiscreteTopology`.
3. Upgrade the existing algebraic `RoseFundamentalGroup` equivalences to
   explicit homeomorphisms and prove realization compatibility. The
   computational fixed-endpoint quotients are already discrete. Preserve
   `traceQuotientEquiv_mul` and Mathlib's multiplication reversal; use the
   existing opposite-group/inversion convention where appropriate.

Expected cost is one focused topology module, continuity/subtype and
null-class-identification lemmas, wrapper homeomorphisms, and replay-manifest
coverage. Proof risk is low to moderate: continuous family lifting exists in
the pinned Mathlib, but endpoint subtype continuity and the exact null-class
set equality still need checked proofs. The winding pair only abelianizes F2
and cannot replace the monodromy classifier. Completion means exact-toolchain
kernel and independent replay acceptance of ordinary-quotient discreteness,
explicit homeomorphisms and realization formulas, without adding discreteness
as an assumption.

## Flat operations and final-domain groupoid interface

This would give the equal-slot model the same reusable operation interface
as the earlier binary package. It improves formal coverage and audit clarity,
with smaller mathematical payoff than the ordinary rose comparison.

The ingredients already include equal-slot reversal/weighted composition,
`weightedConcatenationInvariant`,
`FlatWordContinuity.weightedConcatenation_continuous_family`, word
concatenation/reversal continuity, and the actual representative/final-pair
domains in `LiteralWordPairs`.

1. Define explicit flat coherent units, reversal and length-weighted
   composition. Derive endpoint-nullness of zero-length chosen paths from
   coherence before omitting them in weighted concatenation.
2. Prove raw continuity on each fixed-length pair stratum and assemble it
   across the clopen length strata. The observable proof must use its own
   length/path coordinates; the full-word proof also uses continuous word
   concatenation and reversal.
3. Descend operations through scoped rewriting, prove structural laws and
   package continuity on the final composable-pair quotient. Ordinary-domain
   continuity still requires the existing compatibility hypothesis.

Expected cost is medium: an operations layer and a quotient/interface layer,
with zero-length boundary cases, continuity assembly and instance management.
Existing binary continuity instances cannot establish flat continuity. A
coherent-elimination transport may simplify operations on classes, but a
claim about raw weighted operations must verify their actual formulas.
Completion means a checked flat interface, separate observable/full-word
continuity certificates and final-pair multiplication, with the ordinary
compatibility boundary intact.

Recommended order: publish the completed editorial cleanup, then pursue the
ordinary rose topology bridge as its own reviewed milestone. Package flat
operations afterward if reusable flat semantics is the next development goal.
The present paper accurately records both extensions as further work.
