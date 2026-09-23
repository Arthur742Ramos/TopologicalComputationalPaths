# Roadmap: strengthening the topological semantics paper

This file lists results that would make *Topological Semantics for Scoped
Computational Paths* (arXiv:2608.04228) a substantially stronger paper, and
the Lean work each one needs. The revised manuscript source lives in
[ComputationalPathsLean](https://github.com/Arthur742Ramos/ComputationalPathsLean)
under `paper/topological/`.

## Where the paper stands

The mathematics is correct, and the paper separates two problems cleanly:
geometric completeness (which arrows are equal) and product-quotient
compatibility (which topology composition needs). Its weaknesses are these:

- Most theorems are standard quotient-topology facts written in the language
  of scoped presentations. The normal-form completeness criterion is close to
  a tautology once it is set up.
- The only sufficient conditions for compatibility are compact-Hausdorff and
  discrete. The carrier contains path spaces, so these almost never apply to
  geometric examples. The paper has one negative example (the Hawaiian earring)
  and no positive geometric one.
- Completeness is shown only for the circle and torus, by ad hoc arguments.
- The trace-sensitive topology is only shown to differ from the observable
  one on a one-point space with two constant steps.

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
The Hawaiian module currently uses a coarser topology (see Goal 6b).

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

**Lean work: small to moderate.** It is general topology plus the existing
universal section.

## Goal 3: the global theorem for semilocally simply connected spaces

**Statement.** If $X$ is locally path-connected and semilocally simply
connected, then $q_I : X^I\to\Pi_1^q(X)$ is open. With Goal 2, the whole
quotient-topologized fundamental groupoid is then a topological groupoid,
not just its based fibers.

**Proof sketch.** This has been checked on paper, not yet written carefully.
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

**Novelty check.** Compare with Brown and Danesh-Naruie's lifted topology
and with Brazas's work on quotient-topologized fundamental groups. The
identification of the quotient and lifted topologies in this setting may be
known. Its value here is in pinning down exactly where the Hawaiian
obstruction disappears.

**Lean work: substantial.** Useful assets in
`SemilocallySimplyConnected.lean`: `exists_finite_null_subdivision`,
`homotopic_concat_of_homotopic_ladder`, `isOpen_loops_mapsTo`, and
`isOpen_homotopyClass_of_semilocallySimplyConnected`. The last one covers
fixed endpoints only. Still missing:
- an endpoint-varying ladder
- a subdivision basis for the compact-open topology on `C(I, X)`; check
  Mathlib first
- the reparametrization estimate

## Goal 4: products preserve completeness

**Statement.** Let $\mathcal P$ be a presentation on $X$ that is complete on
the based fiber at $x$, and $\mathcal Q$ one on $Y$ that is complete at $y$.
Define the product presentation $\mathcal P\boxtimes\mathcal Q$ on $X\times Y$:
- its steps are $E\times Y\sqcup X\times F$, where $(e,y')$ realizes
  $t\mapsto(\rho(e)(t),y')$;
- its named rules are the lifted rules of $\mathcal P$ and $\mathcal Q$,
  plus the commuting squares $(e,s f);(t e,f)\simeq(s e,f);(e,t f)$.

Then $\mathcal P\boxtimes\mathcal Q$ is complete on the based fiber at
$(x,y)$.

**Proof sketch.**
1. Use the commuting squares to sort every loop word into a lifted
   $\mathcal P$-loop at $x$ followed by a lifted $\mathcal Q$-loop at $y$. An
   inversion count decreases at each step.
2. Project to $X$ and $Y$. The $\mathcal Q$-letters project to constant
   paths, so homotopic loops have homotopic $\mathcal P$-parts and homotopic
   $\mathcal Q$-parts.
3. Completeness of each factor gives derivations, and these lift along the
   inclusion presentation maps $x'\mapsto(x',y)$ and $y'\mapsto(x,y')$.

**Why it matters.** It replaces the ad hoc torus proof with a general
theorem. The torus and the $n$-torus become corollaries of the circle.

**Lean work: substantial but well-scoped.** It needs:
- a product step system, with a sum of step types
- the commuting-square rules and their soundness
- the sorting normalization
- lifting of derivations along presentation maps

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
Is there a geometric, non-degenerate presentation where $J$ fails to be one?
If neither pans out, shrink the trace-sensitive material to a remark.

**Lean work: small for the criterion, moderate for the corollaries.**

## Goal 6: close the gaps between paper and Lean

a. **Projections.** Add continuity of the two projections from the final
   domain to `ScopedFinalTopologicalGroupoidCertificate`. The paper's
   definition now requires it. It follows from
   `pr_i ∘ q_fin = q ∘ pr_i`. Effort: easy.

b. **Hawaiian topology.** `hawaiianObservableOpenFiberTopology` is induced by
   the geometric projection alone. Restate the based-fiber certificate with
   the subspace topology from the observable carrier, which
   `TotalOpenGeometricCompPath.instTopologicalSpace` already induces from
   `observation`. That removes the caveat in Section 10.2 of the paper.
   Effort: modest.

c. **Scoped-side homeomorphisms.** Connect the scoped based fiber
   $G_{\mathcal P}(0,0)$ of the finite circle and torus presentations to the
   geometric homeomorphisms that already exist. Those are
   `topologicalLoopQuotHomeomorphInt` in `TopologicalWindingHomeomorph.lean`
   and the $n$-torus version in `FiniteTorusWinding.lean`. Effort: moderate.

d. **Discrete field.** Weaken the hypotheses of `discrete_recovers_ordinary`
   to discreteness of $G_{\mathcal P}$ alone. The final domain is then
   discrete automatically. Effort: easy.

e. **New selection.** Bundle Goals 1, 2, 5 and 6a to 6d, plus 3 and 4 if finished,
   into a new comparator selection, following the pattern of
   `comparator-followup.json`. Register it as a new Palomar version, and
   update Section 10 and Table 2 of the paper to match.

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

## Suggested order

1. Goals 1, 2, 5 and 6a/6d. They are cheap, and they change the paper's
   story from "an obstruction exists" to "here is exactly where it goes
   away".
2. Goal 3 or Goal 4 as the headline theorem of the next version.
3. Goal 6b/6c, then the new registration in 6e.
4. The longer-term goals, as separate projects.
