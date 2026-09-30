# Fixed-measure profiles and the transfer quantifiers: adversarial audit

Date: 2026-09-30.

Scope: a fresh reading of `output/pdf/packing-unforced-finite-profile.tex`, `output/pdf/packing-unforced-hard-dimension.tex`, and the transfer and selected-cap embedding they import. This note also independently checks the new construction in `research/2026-09-30-profile-realizability.md`. No published manuscript or Lean source was changed.

## Findings

I found no new counterexample or missing hypothesis in the finite-regularization, component-recombination, or Borel-reduction steps examined here. This is an internal mathematical audit, not a formal certificate and not a claim that all analytic inputs have been independently reproved.

The new substantive conclusion is that the realization construction survives the precise fixed-measure setup of the transfer: one can select **two fixed separated compact supports**, retain the extremal profiles on **the actual annular block grid**, and force **every sufficiently large regular component** to remain close to those profiles. Thus these three possible sources of additional restrictions do not eliminate the matching profiles. This is still only a statement about branching profiles; it is not a construction of null pinned distance sets.

## 1. Independent checks of the realization argument

Write

$$
d=1+a,\qquad D=1+b,\qquad h(x)=x+g(x).
$$

The proposed continuous branching function on a block is

$$
F(t)=\max\{dt,N_jh(t/N_j)-(D-d)N_{j-1}\}.
$$

Both entries are nondecreasing and 2-Lipschitz. Taking their maximum preserves both properties. The initial linear part of the template makes the values agree with the preceding block at the left endpoint; the endpoint condition on the template makes the value at the right endpoint exactly the prescribed lower line. The resulting bounds

$$
dt\le F(t)\le Dt,
\qquad
0\le N_jh(t/N_j)-F(t)\le(D-d)N_{j-1}
\quad(0\le t\le N_j)
$$

are therefore valid globally, including before the current block.

The digit count

$$
F_{\rm dyad}(n)=2\left\lfloor F(n)/2\right\rfloor
$$

has increments zero or two and differs from the continuous count by less than two at integer depths. Its product construction gives exact equal masses to all occupied squares, and the ball estimate is

$$
\mu(B(z,2^{-n}))\le C2^{-F_{\rm dyad}(n)}
\le 4C2^{-dn}.
$$

This is an actual uniform Frostman bound, not merely a lower local-dimension assertion. The upper Hausdorff bound follows from the covers at the endpoint scales. The claimed lower packing bound is also correct: in any countable cover of the support, at least one covering set has positive outer measure for this probability. Covering that set by radius-scale balls and using the first inequality above forces its upper box dimension to be at least the upper limiting branching exponent. No strong separation assumption or measurability of individual covering sets is needed for this argument.

The regular-component sandwich in the realization note has the correct signs. If an original occupied depth-scale cube has mass exactly the reciprocal of the branching count and a restriction of mass at least the prescribed small power is regular, its normalized cube masses give

$$
F_{\rm dyad}(n)+\log_2 w-eN\le f(n)\le F_{\rm dyad}(n).
$$

The lower bound uses domination by the original probability divided by the restriction mass. The upper bound uses the number of available occupied cubes and the fact that the restricted probability has mass one. Neither bound requires the restriction to retain all descendants of any intermediate cube.

## 2. Two fixed separated cylinders retain the same profiles

Here is a precise addition to the realization argument.

Let an occupied depth-scale square have depth equal to a fixed integer $$k$$. Restrict the homogeneous probability to that square and normalize it; call the result $$\nu$$. Its support can be taken to be the corresponding compact digit cylinder. For every integer depth at least $$k$$, every occupied descendant square has mass

$$
2^{-\{F_{\rm dyad}(n)-F_{\rm dyad}(k)\}}.
$$

At a smaller depth there is just one occupied ancestor. Thus the cumulative branching function for this restriction is

$$
A_k(n)=
\begin{cases}
0,&0\le n\le k,\\
F_{\rm dyad}(n)-F_{\rm dyad}(k),&n\ge k.
\end{cases}
$$

In particular,

$$
\sup_{0\le n\le N}|A_k(n)-F_{\rm dyad}(n)|\le 2k.
$$

The same bound holds after linear interpolation. Hence the normalized profiles of the fixed restriction converge along the realization scales to the same template:

$$
\sup_{x\in[0,1]}
\left|\frac{A_k(N_jx)}{N_j}-x-g(x)\right|\longrightarrow0.
$$

The original measure is nonatomic and its support is not a point. Choose two distinct support points, disjoint neighborhoods about them with positive distance between their closures, and sufficiently deep occupied digit cylinders contained in those neighborhoods. The corresponding compact cylinder supports are separated and have positive original mass. Their normalized restrictions are fixed probabilities and retain the uniform Frostman exponent. The calculation above applies to both of them, regardless of whether their chosen depths agree.

Each restriction also has exact Hausdorff dimension equal to the lower limiting branching exponent and exact packing dimension equal to the upper one: subtracting a fixed branching count does not change either limit, and the same covering and outer-mass arguments apply. Consequently the source-pin separation demanded by the analytic transfer does not prevent the matching profiles from recurring in a single fixed pair of admissible measures.

## 3. The exceptional scales can lie on every eventual fixed block grid

The realization theorem permits the endpoint scales to grow arbitrarily rapidly. They may therefore be chosen additionally so that

$$
4j!\mid N_j.
$$

For example, after choosing the preceding scale, take a sufficiently large multiple of the displayed integer to meet the required ratio bound. For every fixed positive block size $$T$$, all sufficiently large indices then satisfy

$$
N_j\in4T\mathbb N.
$$

These are exactly the depth indices used by the annular decomposition in the finite-profile proof. Thus choosing the regularization block size after constructing the measure does not, by itself, avoid the realization scales. The same single measure works for every fixed eventual block grid.

This conclusion is about infinitely many scales, not every scale. The separate sparsity statement in the realization note remains compatible with it.

## 4. Large regular components of the separated restrictions

Apply finite regularization to the fixed cylinder restriction above at a realization depth. Let a regular component have restriction mass $$w\ge2^{-\gamma N_j}$$ and regularity error $$eN_j$$. The same counting argument, now using its exact original exponent $$A_k$$, gives at every block depth

$$
A_k(n)- (\gamma+e)N_j\le f(n)\le A_k(n).
$$

After interpolation, the additional error is at most a fixed multiple of the block size. Therefore

$$
\sup_{x\in[0,1]}
\left|\frac{f(N_jx)}{N_j}-x-g(x)\right|
\le\gamma+e+o_j(1)+O(T/N_j).
$$

This holds for **every** regular component meeting the mass threshold, not only for one favorable component or for a particular implementation of the regularization. In the transfer, the small losses can be made as small as desired by choosing the block size and regularization parameters. In that small-loss limit all such components remain near the same template. Continuity of the bounded-chain limiting cost, proved in the realization note by bounded-length compression, then preserves its limiting matching cost.

At a fixed nonzero regularization error this gives closeness by that error, not exact equality of costs. In particular it must not be used to claim an endpoint obstruction with no error allowance. It rules out discarding the matching template by a purely large-component selection argument.

## 5. Targeted transfer checks and their limits

I separately checked the following interfaces against the actual manuscript, rather than inferring their validity from profile sharpness.

- The regularization is applied to terminal-cube mass data and then transferred back to original restrictions. Every conditional energy estimate only uses the preserved coarser masses and the original parent as a lower bound for its enlarged mass. No infinite regular component or boundary-sliver lower bound is assumed.
- The radial projection theorem is applied before regularization, to fixed separated probabilities with Frostman exponents above one. Its averaged bound on a component is multiplied by the reciprocal component mass, as recorded in the proof. The primary formulation is [Keleti--Shmerkin, Proposition 3.11](https://arxiv.org/html/1801.08745), rather than a result requiring the component itself to have uniform infinite-scale constants.
- Each shell has an exact good-plus-bad density decomposition. The source probability remains fixed; only its smooth shell functions and the pin restrictions vary. The weighted component sums avoid a factor counting components. Strict decay of the good **squared** norms still gives summable good norms over the geometric shells.
- The selected-cap reconstruction first sums whole smooth standard packets, and only afterwards refines their circular spectral measures. The primary remote-packet statement in [Liu, Lemma 4.2](https://arxiv.org/html/2603.15328v3) concerns whole standard packets. The manuscript uses it in that order; it does not assume localization of individually hard-truncated fine packets. The fine angular labels instead enter the separately proved selected-cap embedding.
- The hard-dimension proof uses an open numerical region. Its two profile costs agree at their joining boundary, and the low-branch guard is strict throughout the dimension region where it is invoked. Lowering the source exponent and increasing the upper-cover exponent can therefore be done before selecting the fixed measures. Strict packing cutoffs avoid the unsupported equality case at ambient dimension two.
- The Borel reduction can first take a positive-mass member of the packing cover and then a compact positive-mass restriction. A further pair of separated compact restrictions preserves the Frostman estimate and the pin covering bound. The resulting pins belong to the original Borel set.

No new analytic defect emerged from these checks. The remaining uncertainty is substantive but limited: this audit does not independently reproduce all standard packet integration-by-parts estimates to arbitrary order, and it is not kernel-checked formalization of the assembled argument. Its new obstruction is only to eliminating the sharp profiles using fixedness of the measures, separation, the annular block grid, or large-component regularization. Geometric or Fourier information beyond the branching counts remains available in principle.
