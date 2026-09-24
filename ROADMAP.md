# Roadmap: strengthening the topological semantics paper

This file lists results that would make *Topological Semantics for Scoped
Computational Paths* (arXiv:2608.04228) a substantially stronger paper, and
the Lean work each one needs. The revised manuscript source from
`ComputationalPathsLean` commit `b6f47117` is mirrored at
[`paper/topological/main.tex`](paper/topological/main.tex). The parent
repository remains the source for its broader Lean artifact.

## Progress in this working tree

| Goal | Current state |
| --- | --- |
| 1. Based fibers | The paper proves the positive subspace-fiber result using a published open-quotient theorem. Lean identifies the universal fixed-endpoint quotient with the ordinary based-loop quotient and proves its discreteness, pair-quotient property, and ordinary multiplication continuity. It identifies based paths with the compact-open based-path subspace and, assuming an open global quotient, proves a homeomorphism from the ordinary loop quotient to the global based-arrow subspace and its discreteness under the semilocal hypothesis. A Lean proof of the global open-map theorem remains. |
| 2. Open quotient | The paper and Lean prove the general open-arrow criterion. Lean identifies `TotalComposable` with the raw endpoint pullback, proves that the universal path-class projection is quotient, and proves that its openness implies product-quotient compatibility and continuous ordinary multiplication. |
| 3. Global theorem | The paper applies Holkar, Hossain, and Kulkarni, Corollary 3.7 and Theorem 3.9. The general open-map theorem is not yet proved in Lean. Lean proves the endpoint-varying local ladder, a positive-tail compact-open reparametrization, and an unconditional global special case: for a totally disconnected space, the universal path-class projection is a homeomorphism and ordinary composition is continuous. |
| 4. Products | The paper and Lean now define a sound product presentation with lifted factor rules and both primitive and whole-trace interchange. Lean proves sorting and based trace completeness from completeness of the factors. Deriving whole-trace interchange from primitive squares alone remains open. |
| 5. Trace sensitivity | The paper proves the continuous-section criterion, based circle/torus corollaries, and a nonconstant circle example where the quotient topologies differ. Lean proves the general criterion and universal collapse. It checks signed-count invariance for the duplicate-circle presentation and proves that the trace-to-observable scoped quotient comparison is continuous but its inverse is not. The exact finite-generator circle and torus presentations are now based-complete in Lean, so their continuous trace choices give unconditional based quotient comparisons. |
| 6. Paper and Lean | Projection continuity, the observable Hawaiian based-fiber topology, and the weaker discrete field are proved in this working tree. Lean builds the realized fundamental-groupoid comparison, an integer-indexed circle certificate, and the exact finite circle/torus based winding homeomorphisms, including their global subspace fibers. The internal roadmap bundle now has 18 fields and includes the totally disconnected universal case. A separate Mathlib-only selection states the open-arrow pair quotient, composition transfer, and ordinary circle/torus loop-quotient homeomorphisms for possible Palomar review. Its full mechanical preflight, external review, and registration remain. |

The registered Palomar version 1 is an immutable earlier snapshot. Current
working-tree improvements must not be attributed to that registration.

## Where the paper stands

The paper separates two problems cleanly:
geometric completeness (which arrows are equal) and product-quotient
compatibility (which topology composition needs). Its weaknesses are these:

- Most theorems are standard quotient-topology facts written in the language
  of scoped presentations. The normal-form completeness criterion is close to
  a tautology once it is set up.
- The earlier manuscript offered compact-Hausdorff and discrete sufficient
  conditions, which rarely apply to geometric path spaces. The revision adds
  an open-quotient criterion and a positive universal example.
- The earlier manuscript showed completeness only for the circle and torus.
  The revision adds a product closure theorem and finite-torus corollaries.
- The revised paper now separates the two topologies using distinct labels
  for the same nonconstant circle loop. Lean checks the actual scoped quotient
  separation, including continuity of the forward comparison and failure of
  continuity of its inverse.

The goals below address these weaknesses in order of payoff per unit of effort.

## Goal 1: positive theorem on based fibers

**Statement.** Let $X$ be locally path-connected and semilocally simply
connected. In every based fiber of the universal presentation
$\mathcal U_X$, the final and ordinary composable-pair topologies agree,
and ordinary multiplication is continuous.

**Proof.** The fiberwise lemma identifies $G_{\mathcal U_X}(x,x)$ with
$\pi_1^q(X,x)$. Under the hypotheses that group is discrete. The paper's
discrete corollary then applies.

**Why it matters.** Together with the Hawaiian earring, which is locally
path-connected but not semilocally simply connected, this gives the paper a
positive case to set against its negative one.

**Lean work: small.** It is mostly glue between existing results:
- `QuotientFundamentalGroup.quotientDiscreteTopology_of_semilocallySimplyConnected`
  and `semilocallySimplyConnected_iff_quotientDiscreteTopology` in
  `SemilocallySimplyConnected.lean`
- the one-letter section in `UniversalCompPathHomotopyEquivalence.lean`
- `discrete_recovers_ordinary` in the registered certificate

The based fiber must carry the subspace topology from the observable carrier.
`UniversalGlobalBasedFiber.lean` now proves this comparison under the open-map
hypothesis. The global open-map theorem still needs a Lean proof. The Hawaiian
module's full observable based topology is handled separately (see Goal 6b).

**Check before citing.** The converse appears to fail, because the harmonic
archipelago has an indiscrete $\pi_1^q$, which is still a topological group.
Confirm against the literature before stating it.

## Goal 2: open-quotient criterion

**Statement.** If the homotopy quotient
$q_I : X^I \to \Pi_1^q(X)$ is an open map, then the universal presentation
has product-quotient compatibility. In that case $G_{\mathcal U_X}\cong\Pi_1^q(X)$
is a topological groupoid in the standard sense, with continuous
multiplication on the ordinary pullback.

**Proof sketch.** The ordinary pair map factors as
$T^{(2)} \to X^I\times_X X^I \to \Pi^{(2)}$.
- The first map has the continuous section $\sigma\times\sigma$, so it is a
  quotient map.
- $q_I\times q_I$ is open. $X^I\times_X X^I$ is the full preimage of the
  composable pairs, because composability depends only on endpoints and
  $q_I$ preserves them. So the second map is an open surjection, hence a
  quotient map.
- A composite of quotient maps is a quotient map. Transport along
  $G_{\mathcal U_X}\cong\Pi_1^q(X)$ and apply the ordinary/final comparison
  theorem.

A general version also holds for any presentation: if $q:T\to G_{\mathcal P}$
is open, then $q_{\mathrm{ord}}^{(2)}$ is an open surjection and
compatibility holds.

**Lean work.** The general open-arrow theorem is
`scopedProductCompatibility_of_open_arrow` in
`ScopedGeometricRewriteGroupoid.lean`. `UniversalQuotientTransfer.lean`
now proves the universal path projection quotient and derives ordinary
product compatibility from its openness. The open-map theorem itself is
Goal 3.

## Goal 3: the global theorem for semilocally simply connected spaces

**Statement.** If $X$ is locally path-connected and semilocally simply
connected, then $q_I : X^I\to\Pi_1^q(X)$ is open. With Goal 2, the whole
quotient-topologized fundamental groupoid is then a topological groupoid,
not just its based fibers.

**Proof sketch for a future Lean formalization.** The cited literature proves
the theorem; the following geometric argument indicates the local lemmas a
direct formal proof would need.
Let $W$ be open and let $\delta$ be homotopic to some $\gamma\in W$. We need a
neighbourhood of $\delta$ inside the saturation of $W$.

1. **Absorption (needs no semilocal hypothesis).** Shrink $W$ to a
   subdivision-type basic set $\bigcap_j\langle I_j,O_j\rangle$ around
   $\gamma$. There are neighbourhoods $U$ of $\gamma(0)$ and $V$ of
   $\gamma(1)$ with the following property. For all paths $\alpha$ in $U$
   and $\beta$ in $V$, a reparametrization of $\alpha^{-1}\gamma\beta$ lies
   in $W$. The reparametrization spends a small time $\varepsilon$ on each
   end, and a Lebesgue-number argument controls the shift of $\gamma$ on the
   middle part.
2. **Ladder (needs local path-connectedness and the semilocal hypothesis).**
   Every path $\delta'$ close enough to $\delta$ is homotopic to
   $\alpha^{-1}\delta\beta$ for short paths $\alpha$ and $\beta$ in chosen
   neighbourhoods of the endpoints. The proof subdivides and fills the
   squares of the ladder with null-homotopic loops.

Then $\delta'\simeq\alpha^{-1}\delta\beta\simeq\alpha^{-1}\gamma\beta$, which
is homotopic to a path in $W$.

**Prior art.** Holkar, Hossain, and Kulkarni prove openness of the compact-open
path-class quotient under these hypotheses in Corollary 3.7, and the
topological-groupoid conclusion in Theorem 3.9 of
[their 2024 paper](https://www.uni-muenster.de/FB10/mjm/vol_17/mjm_vol_17_06.pdf).
The manuscript credits this theorem and uses it to explain where the
Hawaiian-earring obstruction disappears. The global statement is not a new
result of this project.

**Lean work: substantial.** `EndpointVaryingLadder.lean` now proves an
endpoint-varying local ladder from the finite null-homotopy subdivision in
`SemilocallySimplyConnected.lean`. For any open neighborhoods of a path's
endpoints, it produces a compact-open neighborhood of that path and shows
that every nearby path differs by endpoint connectors confined to those
neighborhoods. `EndpointAbsorption.lean` also proves that every compact-open
neighborhood contains a positive-tail reparametrization of its center path.
Still missing:
- the rest of absorption: insert small endpoint connectors into that
  reparametrization within the given open set and prove the resulting path
  retains the required endpoint-fixed homotopy class;
- the final saturation and quotient-map argument applying both lemmas.

`UniversalTotallyDisconnected.lean` settles a different global case without
these lemmas. Every interval path into a totally disconnected space is
constant; the universal path-class projection is quotient and injective,
hence a homeomorphism. The module also checks ordinary pair compatibility,
ordinary multiplication continuity, and the global based-fiber comparison.
This does not prove the locally path-connected semilocal theorem above.

## Goal 4: products preserve completeness

**Statement.** Let $\mathcal P$ be a presentation on $X$ that is complete on
the based fiber at $x$, and $\mathcal Q$ one on $Y$ that is complete at $y$.
Define the product presentation $\mathcal P\boxtimes\mathcal Q$ on $X\times Y$:
- its steps are $E\times Y\sqcup X\times F$, where $(e,y')$ realizes
  $t\mapsto(\rho(e)(t),y')$;
- its named rules are the lifted rules of $\mathcal P$ and $\mathcal Q$,
  the commuting squares $(e,s f);(t e,f)\simeq(s e,f);(e,t f)$, and the
  corresponding interchange for arbitrary factor traces.

Then $\mathcal P\boxtimes\mathcal Q$ is complete on the based fiber at
$(x,y)$.

**Proof sketch.**
1. Induct on product traces, using whole-trace interchange to sort every
   loop into a lifted $\mathcal P$-loop at $x$ followed by a lifted
   $\mathcal Q$-loop at $y$.
2. Project to $X$ and $Y$. The $\mathcal Q$-letters project to constant
   paths, so homotopic loops have homotopic $\mathcal P$-parts and homotopic
   $\mathcal Q$-parts.
3. Completeness of each factor gives derivations, and these lift along the
   inclusion presentation maps $x'\mapsto(x',y)$ and $y'\mapsto(x,y')$.

**Why it matters.** It replaces the ad hoc torus proof with a general
theorem. The torus and the $n$-torus become corollaries of the circle.

**Lean work.** `ProductGeometricStepSystem.lean`,
`ProductScopedPresentation.lean`, and `ProductScopedSorting.lean` now check
the continuous step system, soundness, lifted derivations, sorting, and
based trace completeness. A smaller presentation with only primitive
interchange would require deriving the whole-trace rule.

Existing assets: the sorting argument in `ConcreteTorusWinding.lean`,
functoriality in `ContinuousGeometricStepSystemMap.lean`, and the
geometric $n$-torus classification with homeomorphism in
`FiniteTorusWinding.lean`.

## Goal 5: make the trace-sensitive topology earn its place

**Statement.** Suppose $\mathcal P$ is geometrically complete and the
projection from $T_{\mathrm{tr}}$ to represented paths has a continuous
section. Then the comparison $J : G^{\mathrm{tr}}_{\mathcal P}\to G^{\mathrm{obs}}_{\mathcal P}$
is a homeomorphism.

**Proof.** With section $s$, the map $\theta = s\circ\pi : T_{\mathrm{obs}}\to T_{\mathrm{tr}}$
is continuous. Completeness gives $q_{\mathrm{tr}}\circ\theta = q_{\mathrm{obs}}$,
so $J^{-1}\circ q_{\mathrm{obs}}$ is continuous.

**Corollaries.**
- The universal presentation, which the paper already treats.
- The circle and torus based fibers. There the section is
  $\gamma\mapsto(c_{w(\gamma)},\gamma)$, which is continuous because winding
  is locally constant.

So the two topologies can differ only where completeness or the section
fails. Example 2.5 is incomplete.

**Open questions.** Does completeness alone force $J$ to be a homeomorphism?
The revised paper answers the geometric separation question: two distinct
labels for the same nonconstant circle loop yield a non-homeomorphic quotient
comparison. Whether completeness alone forces $J$ to be a homeomorphism
remains open.

**Lean work.** `TraceSensitiveTopologicalCompPath.lean` supplies the two
representative topologies, `TraceSensitiveUniversalCollapse.lean` now states
`traceSensitiveHomeomorph_of_complete_section`, and
`TraceSensitiveSeparation.lean` checks the finite separation model.
`ScopedCircleTraceCollapse.lean` checks the fixed-endpoint integer-indexed
circle section. `TraceSensitiveSeparation.lean` proves that two labels for
the same nonconstant circle loop give distinct scoped classes while their
observable codes coincide, and that the two quotient topologies differ.
`FiniteCircleTorusTraceSection.lean` checks continuous choices
of signed finite-generator words for the circle and torus.
`FiniteCircleScopedCompleteness.lean` and `FiniteTorusScopedCompleteness.lean`
prove based completeness for the exact finite rule sets, instantiate those
topology comparisons, and identify their based scoped quotients with
$\mathbb Z$ and $\mathbb Z^2$ and directly with the ordinary geometric loop
quotients.

## Goal 6: close the gaps between paper and Lean

a. **Projections.** The working source now includes continuity of both
   projections from the final domain in
   `ScopedFinalTopologicalGroupoidCertificate`.

b. **Hawaiian topology.** The working source now induces
   `hawaiianObservableOpenFiberTopology` from the full observable carrier
   and proves the one-letter section continuous. Section 10 of the paper
   retains the caveat for the immutable registered version 1.

c. **Scoped-side homeomorphisms.** The finite circle and torus presentations
   now have checked homeomorphisms from the actual based subspaces of their
   global scoped arrow quotients to $\mathbb Z$ and $\mathbb Z^2$, and hence to
   the corresponding ordinary geometric loop quotients. The proof extends
   winding continuously over all global scoped arrows by translating each
   variable-basepoint loop to the identity. It then uses finite based
   completeness to show that winding is injective on the based subspace.
   These results are in `FiniteCircleGlobalBasedFiber.lean` and
   `FiniteTorusGlobalBasedFiber.lean`.

d. **Discrete field.** The working source now assumes discreteness of
   $G_{\mathcal P}$ alone in `discrete_recovers_ordinary` and proves the
   supporting compatibility theorem.

e. **New selection.** `comparator-roadmap.json` selects an 18-field
   `RoadmapCertificate` covering the checked conditional universal results,
   open-arrow and projection results, product closure, finite based
   completeness and global subspace homeomorphisms, trace-section criterion,
   and quotient-topology separation. `formalization-roadmap.yaml` records the
   exact boundary. The challenge imports the substantive Lean development,
   and the solution assembles its declarations. CI has replayed this bundle
   with Comparator, NanoDa, and Lean's kernel. Palomar's current Challenge
   provenance rule does not permit that local import, so the bundle is an
   internal check rather than a registration candidate.
   `comparator-registry-roadmap.json` separately selects four standalone
   Mathlib-only statements: the open-arrow ordinary-pair quotient, the
   continuity transfer for multiplication, and the ordinary circle and torus
   loop-quotient homeomorphisms. Its preflight, external review,
   registration as a new Palomar record, and the corresponding Section 10
   manuscript update remain. Palomar requires a later version to retain the
   earlier Comparator path, so this separate configuration cannot become
   version 2 of the existing ID. The direct Lean proof of Goal 3 is absent.

## Longer-term goals (not planned yet)

These would each be a major project, mostly because Mathlib lacks the
classical inputs.

- **Fabel's theorem in Lean.** This would make the Hawaiian-earring transfer
  unconditional. It needs at least the fundamental groups of finite wedges
  of circles (free groups) and the retractions of the earring onto them.
  None of this is in Mathlib.
- **Edge-path completeness.** Show that for a graph (edges as steps, no rules)
  or a 2-complex (2-cell boundaries as rules), the combinatorial presentation
  is geometrically complete. This needs geometric realization, and for
  2-complexes cellular or simplicial approximation.
- **A Seifert–van Kampen theorem for scoped presentations.** Show that gluing
  complete presentations along a suitable cover gives a complete
  presentation. This connects to the existing SVK preprint and would tie the
  paper series together.

## Remaining order

1. Formalize the universal path-class open map under local path-connectedness
   and semilocal simple connectivity. The conditional transfer and the
   global subspace based-fiber comparison are already checked (Goals 1--3).
2. Derive whole-trace interchange from primitive squares if a presentation
   with only primitive interchange is needed (Goal 4).
3. Run Palomar's full mechanical preflight on a final commit and the
   Mathlib-only Comparator selection. Seek review and register a new record
   only after the required maintainer authorization and registration decision
   (Goal 6e). Treat the longer-term goals as separate projects.
