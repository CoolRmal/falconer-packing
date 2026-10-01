# Sharp profile bounds and an improved pinned-distance criterion

30 September 2026.

The [proof manuscript](packing-unforced-proof.pdf) proves the following sufficient
condition for a Borel planar set. Write

$$
d=\dim_H E,\qquad D=\dim_P E,\qquad
\Delta_y(E)=\{|x-y|:x\in E\}.
$$

$$
B_{\mathrm H}(d)=
\begin{cases}
2d-1,&1<d\le d_\alpha,\\[6pt]
1+r_2(d-1),&d_\alpha<d\le d_c,\\[6pt]
\dfrac1{3-2d},&d_c<d\le\dfrac54,
\end{cases}
$$

$$
d_\alpha=\frac{7-\sqrt7}{4}\approx1.088562172,
\qquad d_c=\frac{2+\sqrt6}{4}\approx1.112372436.
$$

The radical in the middle branch is

$$
r_2(a)=\frac{2-a+8a^2-\sqrt{4-28a-63a^2+32a^3+64a^4}}
{4(1+4a-2a^2)}.
$$

Then

$$
1<d\le\frac54,\qquad D<B_{\mathrm H}(d)
\quad\Longrightarrow\quad
\exists y\in E:\ |\Delta_y(E)|>0.
$$

The radical is real throughout the stated middle branch, and both joins are
continuous. Every packing inequality is strict. At Hausdorff dimension five
quarters this covers packing dimension strictly below two. Above five quarters,
GIOW already gives the conclusion without a packing restriction.

![The current cutoff and earlier bounds, with the improvement shaded.](../figures/packing-unforced.svg)

## Exact examples

The new result covers

$$
d=\frac{109}{100}=1.09,\qquad D=\frac{1181}{1000}=1.181.
$$

Its exact profile cost and margin are

$$
C_2\left(\frac9{100},\frac{181}{1000}\right)=\frac{4619}{51529},
\qquad \frac9{100}-\frac{4619}{51529}=\frac{1861}{5152900}>0.
$$

It also covers

$$
d=\frac{23}{20}=1.15,\qquad D=\frac75=1.40,
$$

with cost 5/36 and positive margin 1/90. Exact cutoff values include

$$
B_{\mathrm H}(11/10)=\frac{28}{23},\qquad
B_{\mathrm H}(23/20)=\frac{10}{7},\qquad
B_{\mathrm H}(31/25)=\frac{25}{13}.
$$

## The sharp profile estimates

The proof studies 1-Lipschitz functions with two linear barriers and chains whose
edges have the following admissibility condition and cost:

$$
ax\le g(x)\le bx,\qquad
2n-m\le1,\qquad
c_g(m,n)=g(m)-\min_{[m,n]}g.
$$

Define

$$
b_c(a)=\frac{1+2a}{4+2a},\qquad
R(a,b)=4(1+a)b^2-4(a+2)b+1+3a.
$$

The new estimates are

$$
\begin{aligned}
C_1(a,b)&=\frac{b-a}{1+2b},\\[5pt]
C_2(a,b)&=\frac{(b-a)(2+a-2b-4ab)}{(1-a)(1+2b)^2}.
\end{aligned}
$$

For upper slopes at most one half, the limiting universal optimal chain cost is
exactly the second expression below the transition when the guard holds, and
exactly the first above it:

$$
\mathcal M(a,b)=
\begin{cases}
C_2(a,b),&0<a<b\le b_c(a),\quad b\le1/2,\quad R(a,b)\le0,\\[5pt]
C_1(a,b),&0<a<b\le1/2,\quad b\ge b_c(a).
\end{cases}
$$

The earlier high-slope estimate gives the first expression above one half as
well. All upper estimates produce bounded finite chains, with the grid and barrier
errors required by the analytic transfer.

Endpoint clipping reduces the problem to profiles ending on the lower barrier.
Keleti–Shmerkin's hard-component identity then represents the optimal cost as a
sum of drops across complementary gaps. Keeping two positive gaps and bounding
the remaining tail gives two finite inequalities with explicit nonnegative
weights. Matching one- and two-collapse profiles prove sharpness. The proof uses
exact identities; numerical linear programming was only a discovery aid.

## What is optimal, and what remains open

The explicit dimension curve is the exact threshold for the following specified
combination of sufficient tests:

$$
b<2a\quad\text{or}\quad\mathcal M(a,b)<a,
\qquad a=d-1,\quad b=D-1.
$$

This is a sharp statement about the profile model and that criterion. It does not
give a planar set whose pinned distances have zero length. Stronger analytic
information or a different argument could improve the actual distance theorem.
The weakest possible Hausdorff–packing condition therefore remains unproved.

The manuscript contains the complete analytic transfer with cited established
inputs, the earlier sufficient curves, and a plan for Lean formalization. The new
gap proof, exact algebra, and assembled mathematical statement have independent
internal audits. A fresh analytic audit also checks the pinned identity, packet
marking, and joint limit. These internal audits are not external refereeing.

The [Lean algebra module](../../FalconerPacking/HardGapAlgebra.lean) proves both
weighted certificates, the difference of the two costs, their strict-threshold
equivalences, and the exact example margins. All seven theorem axiom reports are
`[propext, Classical.choice, Quot.sound]`, with no holes. The geometric reduction
and analytic transfer are not certified by these algebraic theorems. The
unconditional Lean proof remains unfinished.

The new limitations section proves that matching profiles recur along infinitely
many scales of a single compact set with exact Hausdorff and packing dimensions,
carrying a Frostman probability of the exact lower exponent. Large regular
components and two fixed separated restrictions retain the profiles. A separate
finite-start identity shows that the precise initial-localization cost cannot
improve the limiting profile test. The same fixed separated measures can also
have nearly saturated source Fourier energy at the frequencies where the pin
profile is near-extremal. These results do not prove necessity for positive
pinned distance length.

## Stronger integrability under the same curve

The selected compact source and pin probabilities can be chosen so that the
actual joint distance law has a density in some strong space with exponent
greater than one. In particular the individual pinned densities have that
integrability for almost every selected pin. The finite-profile proof varies
the good/bad thresholds, treats the discarded pin remainder separately, and sums
the full annular densities. The coherent proof interpolates summable first-norm
differences with polynomial higher-norm bounds for the positive approximations.

For the coherent measure assumptions, write

$$
\delta=2s-1-u>0,\qquad \eta=\frac{q-1}{2q-1},
$$

where the source has Frostman exponent $$s$$ and covering exponent $$u$$, and
$$q>1$$ is its chosen centers' averaged angular exponent. The proved range is

$$
1<p<\left(1-\eta\frac\delta s\right)^{-1}.
$$

Both improvements require their existing strict dimension margin. They do not
prove a weaker dimension condition or a new endpoint. The natural-language proof
is the current focus; no additional Lean certification is claimed for these
arguments.

## A quantitative endpoint extension

The [critical covering theorem](packing-unforced-critical-covering.tex) now
reaches the boundary of the coherent condition when the source has an
additional covering margin. For a compact source carrying an s-Frostman
probability, the following bound on its occupied-square count at dyadic
depth n is sufficient:

$$
N_n\le C\,2^{n(2s-1)}e^{-c\sqrt n},\qquad 1<s<2.
$$

Then the raw joint distance law is absolutely continuous for every compact pin
Frostman probability of exponent greater than one, including the source
probability itself. The exact summability test for separated supports is

$$
\sum_n\left(2^{-n(2s-1)}N_{n+1}\right)^{\eta_q}<\infty,
\qquad \eta_q=\frac{q-1}{2q-1}>0.
$$

The [direct frequency-band proof](packing-unforced-band-comparison.tex)
removes the factor n from the earlier variable-exponent estimate. It sums the
actual translation and angular increments before approaching critical source
regularity. In particular a covering margin of the form

$$
N_n\le C2^{n(2s-1)}n^{-b}
$$

now suffices when

$$
b>\frac1{\eta_q},
$$

instead of the earlier sufficient requirement of one plus this reciprocal.
The proof also retains the source-cell masses, giving the stronger criterion

$$
\sum_n\left[
2^{-n(2s-1)}
\left(\sum_{Q\text{ at depth }n+1}\sqrt{\mu(Q)}\right)^2
\right]^{\eta_q}<\infty.
$$

The original subpower margin still works for every positive angular exponent.
No logarithmic improvement of the source Frostman bound is assumed.

Before inserting the Frostman estimate, the same argument gives a stronger
positive energy test using the curvature scale:

$$
J_\delta(\lambda)=\iint
\min\{|x-x'|^{-1},\delta^2|x-x'|^{-3}\}\,d\lambda(x)d\lambda(x').
$$

This keeps the actual close-pair geometry. Summability of the corresponding
mass-weighted quantities along selected depths suffices for raw absolute
continuity; no finite energy at the critical Frostman exponent is assumed.

The [common angular-tail refinement](packing-unforced-angular-tails.tex)
improves this summation step. For either the covering or curvature-energy
coefficients along a selected sequence, write their decreasing rearrangement
as follows. With the same fixed radial exponent, it suffices that

$$
V_k^*\text{ is the decreasing rearrangement of }V_j,\qquad
\sum_{k\ge1} k^{1/[2(q-1)]}\sqrt{V_k^*}<\infty.
$$

This is strictly weaker as a numerical condition than summability of the
eta-th powers. The proof uses the full angular tail and chooses the centers
once for the whole sequence. In particular, for separated source and pin
measures with the stated radial exponent, the critical covering estimate

$$
N_n\le C2^{n(2s-1)}n^{-1/\eta_q}(\log n)^{-\beta},
\qquad \beta>2,
$$

implies raw pinned absolute continuity for almost every pin. The preceding
power-sum test required the larger logarithmic exponent

$$
\beta>1/\eta_q>2.
$$

The [detailed tail argument](2026-09-30-common-radial-tail-summability.md)
also gives the exact criterion using the actual tail, and explains why the
logarithmic endpoint two cannot be obtained uniformly from arbitrary finite
angular moments using that numerical bound alone. Its scalar obstruction is
not asserted realizable by a planar source and pin pair.

The [curvature-energy obstruction](packing-unforced-curvature-obstruction.tex)
is a different, geometric construction. For every

$$
1<d<\frac32,\qquad 2d-1\le D<2,
$$

there is a compact set with finite positive critical Hausdorff and packing
measures such that the curvature coefficients fail to tend to zero for every
source probability on the set and every sequence of selected global depths.
The lower bound also allows arbitrary partitions into pieces of uniformly
bounded diameter at those scales. This rules out deriving the sufficient
series merely by replacing the source, choosing other global scales, or
using a translated grid. It does not prove failure of actual affine-law
convergence or positive-length distances; partitions using a different
depth for each piece would require a separate analysis.

The [explicit compact construction](packing-unforced-critical-moran.tex) gives,
for every dimension in the indicated range,

$$
1<d\le\frac32,\qquad D=2d-1,\qquad
0<\mathcal H^d(K)<\infty,\qquad
\dim_H K=d,\quad\dim_P K=D.
$$

It satisfies the required covering margin and the hereditary inequality

$$
\dim_H S\le\frac dD\dim_P S\qquad(S\subset K).
$$

Consequently it contains no positive-dimensional subset with equal Hausdorff
and packing dimensions. When d is at most the first branch transition, no
subset with Hausdorff dimension greater than one satisfies the previous
strict packing criterion either. Nevertheless its natural source probability
has positive-length distance sets for almost every pin under that same
probability. One exact example is

$$
d=\frac{21}{20},\qquad D=\frac{11}{10}.
$$

This is a proved endpoint class with extra quantitative covering information.
It does not replace the strict dimension inequality by a non-strict inequality
for arbitrary sets. The two-dimension curve and the unresolved global
optimality claim are unchanged.

## Favorable scales beyond the dimension-only curve

The [selected-scale construction](packing-unforced-sparse-moran.tex) brings an
additional family from the earlier research notes into the complete manuscript.
For every pair in the range

$$
1<d<D\le\frac{4d}{d+2}<2,
$$

it constructs a compact set and a natural source probability satisfying

$$
0<\mathcal H^d(K)<\infty,\qquad
\dim_H K=d,\qquad\dim_P K=D,\qquad
\dim_H S\le\frac dD\dim_P S\quad(S\subset K).
$$

The raw pinned distance law is absolutely continuous for almost every pin
under any compact pin Frostman probability of exponent greater than one.
This includes the source probability itself.

The proof uses low covering counts at selected depths only. Its ordinary
Frostman bound is complemented by

$$
N_{n_j}\le C2^{dn_j},\qquad
\sum_j2^{-2\gamma\eta_q(2n_j-n_{j+1})}<\infty,
\qquad 0<\gamma<\frac{d-1}{2}.
$$

In the interior the next depth is at most a fixed multiple less than two of
the preceding depth. At the boundary a logarithmic adjustment to the branching
construction supplies a positive logarithmic gap below twice that depth,
which is enough because the selected depths grow geometrically.

One concrete example has

$$
d=\frac{21}{20},\qquad D=\frac65>\frac{11}{10}=B_{\mathrm H}(d).
$$

The same Hausdorff dimension permits packing dimension as large as 84/61
in this constructed family. No subset of Hausdorff dimension greater than
one meets the earlier strict dimension criterion, and no subset has positive
equal Hausdorff and packing dimensions. Thus regular-subset selection does not
reduce these examples to the preceding dimension-only result.

The [critical-measure obstruction](2026-09-30-critical-measure-gauge-extraction-obstruction.md)
also shows why finite positive critical Hausdorff and packing measures alone
do not supply the new all-scale criterion. In its zero-gauge examples, every
source of Frostman exponent greater than one fails that weighted covering
criterion. The examples within the first branch of the dimension curve
nevertheless have raw absolute continuity by the sparse argument. Failure of the numerical all-scale test therefore does not show
failure of the actual distance conclusion.

This is a theorem about an explicitly constructed class and its favorable
scales. The inequality on its two dimensions is not asserted sufficient for
arbitrary sets. The family and the square-root version of its boundary
mechanism were already present in earlier research notes; the present account
supplies the full integrated proof and the logarithmic boundary construction.

## What a refined positive decomposition must prove

The manuscript proves a sharper quadratic selection estimate for a finite
train-track model, including all retained cross-track interactions. Deleting
only the pin's own track works exactly when the model's covering exponent is at
least four thirds. Below that, averaging over the actual deterministic pin slats
now gives an optimal deletion order for the averaged squared norm. With the
model parameters, the new order is

$$
\delta^{2\alpha\beta/(1-\alpha)},\qquad
\alpha=u-1<\frac13,\qquad \beta=\frac{s-1}{2}.
$$

The proof retains the equal-radius resonances and counts all other vertical
slat shifts. A matching lower bound applies to arbitrary positive selections.
This improves the former sufficient order
$$\delta^{\alpha\beta/(1-2\alpha)}$$ for the averaged norm. The earlier
bound remains uniform at every pin; the new estimate is averaged over pins.
Neither finite-model estimate is a new dimension-only theorem.

For fixed source and pin measures, vanishing total deletion and uniformly bounded
full quadratic norms would force the original joint law into the quadratic
space. The fixed-measure example rules out that overly strong target. Retaining
a fixed positive mass with a controlled norm is sufficient for a nonzero
absolutely continuous component. Persistent deletion is one implementation,
but proving its geometric estimates from dimensions alone remains open here.

For fixed measures, the new angular truncation retains positive mass once for
all resolutions and bounds its near-source collisions by

$$
C A\left(\varepsilon^{-1}r^{s+1}+r^{s-1}\right).
$$

At a source cutoff $$r=\varepsilon^\alpha$$ with
$$1/(s+1)<\alpha<1$$, this has a summable positive power of the resolution.
Uniform control of the remaining far-source collisions is still a hypothesis.
The separate bisector criterion uses a mixed norm of reflection
autocorrelations of an actual source measure. Both criteria preserve geometry
discarded by the scalar profile, but neither missing geometric bound is deduced
here from dimensions beyond the existing curve.

The [new crowding reduction](packing-unforced-crowding.tex) needs less than a
bounded whole far-collision integral. At arbitrarily fine scales, it is enough
that a fixed positive mass of retained source–pin pairs has bounded far-annulus
crowding. Restricting to those pairs gives a uniformly bounded quadratic
mollified law; the already proved near-collision error tends to zero. Weak
compactness yields an actual positive absolutely continuous component, without
assuming nested selections.

The supremum over finite crowding thresholds of the limiting good-pair mass
equals exactly the absolutely continuous mass of the chosen joint law. This is
a measure-theoretic characterization, not a necessary condition for positive
length of its support and not a weakest dimension inequality. A logarithmic
crowding moment gives full absolute continuity with finite entropy. The
[fractional criterion](packing-unforced-fractional-crowding.tex) also gives
power integrability from a rich near-bisector tail satisfying

$$
\varkappa<\beta(s-1).
$$

Here the incidence normalization and tail exponents are defined in the proof;
no inequality relating them to the two set dimensions is assumed or proved.
The existing angular and Frostman strip estimates retain a resolution loss
and do not establish the new tail hypothesis. These results weaken the analytic
estimate sought, while leaving the proved dimension curve unchanged.

The manuscript also checks the natural scale correspondence for a hybrid
argument: affine source depth is half the corresponding Fourier depth. Matching
profiles can obstruct both the existing coherent summability test and the
strict chain-cost test at these scales, including a nondecaying endpoint
example. This limits a direct combination of those criteria; it does not rule
out a new estimate connecting them.

## Local decoupling and the profile optimum

The new local packet estimate preserves a single source function throughout each
frequency annulus and leaves the local energy needed for the remaining chain.
It also permits the weighted refined-decoupling estimate at exponents between
two and six. The resulting profile optimization has the exact value

$$
\inf_{\substack{0\le m<1\\2\le p\le6}}
\bigl(\Phi_g(m)+T_p(g,m)\bigr)=\Phi_g(1).
$$

Here the chain cost and terminal expression are defined explicitly in the
manuscript. This identity holds for every 1-Lipschitz profile, without dimension
barriers or an endpoint normalization. Its proof uses the hard-component
potential, bounded finite chains, and uniform approximation. It shows that this
specific decoupling construction cannot improve the existing curve. It makes no
claim about all uses of decoupling or the optimal distance-set threshold.

## What the geometric tests establish

The fixed recursive source construction has

$$
\dim_H K=\frac{11}{10},\qquad
\dim_P K=\overline{\dim}_{\mathrm B}K=\frac{13}{11}.
$$

It carries a probability that is Frostman at every exponent below 11/10.
Use this same probability as the fixed pin probability on K. For **every** nonzero
finite positive source measure supported on K, the raw joint pinned distance
law, even restricted to the radial interval from 1/64 to 1/16, has no weak-Lq
density for q greater than 9/8. In particular no such source
with finite first energy can satisfy the proposed bisector mixed norm. The
construction also handles matching positive source and pin restrictions.
It does not rule out independent pin restrictions or pin-dependent positive
pair selections. The dimensions satisfy the earlier coherent sufficient
condition, so this is not a distance-set counterexample.

Two further checks identify the missing geometric information. Bounded angular
densities at both members of a source pair need not improve the Frostman strip
power; source-pair averaging remains essential. Uniform arithmetic slat counts
from the finite example cannot be reused at infinitely many scales for one
fixed measure, even after retaining a fixed positive mass. The inherited
occupied length forces a growing counting constant.

For comparison, a fully proved parameter-averaged estimate gives raw pinned
quadratic densities after almost every arbitrarily small elliptic deformation
of a source with finite first energy. This is consistent with the established
random-metric results of [Hofmann and Iosevich](https://arxiv.org/abs/math/0305132).
Its bound deteriorates as the deformation neighborhood shrinks, so it does
not prove the conclusion for the original Euclidean metric. These tests do
not enlarge the dimension-only sufficient region.

## Proof and audit files

- [Complete manuscript](packing-unforced-proof.pdf)
- [Main LaTeX source](packing-unforced-proof.tex)
- [Sharp hard-gap estimates and matching profiles](packing-unforced-hard-gaps.tex)
- [Explicit dimension curve and precise model optimality](packing-unforced-hard-dimension.tex)
- [Finite-start identity and endpoint limitation](packing-unforced-finite-start.tex)
- [Local refined-decoupling estimate and source reconstruction](packing-unforced-local-decoupling.tex)
- [Exact profile comparison for the weighted decoupling family](packing-unforced-decoupling-profile.tex)
- [Detailed local decoupling transfer](2026-09-30-local-giow-terminal-transfer.md)
- [Independent packet and source-selector audit](2026-09-30-local-terminal-selector-audit.md)
- [Detailed universal profile comparison](2026-09-30-local-giow-profile-redundancy.md)
- [Weighted refined-decoupling exponent calculation](2026-09-30-weighted-decoupling-profile-comparison.md)
- [Independent hard-component and approximation audit](2026-09-30-local-decoupling-redundancy-independent-audit.md)
- [Independent weighted-exponent and profile audit](2026-09-30-terminal-redundancy-independent-audit.md)
- [Realization by a single Frostman measure](packing-unforced-realizability.tex)
- [Simultaneous obstruction at curvature-matched scales](packing-unforced-hybrid-obstruction.tex)
- [Independent curvature-scale audit and its exact scope](2026-09-30-curvature-matched-hybrid-audit.md)
- [Detailed endpoint investigation](2026-09-30-critical-profile-endpoint.md)
- [Detailed realization construction](2026-09-30-profile-realizability.md)
- [Synchronized profile and Fourier-energy saturation](2026-09-30-profile-fourier-saturation.md)
- [Independent energy-saturation audit](2026-09-30-profile-energy-independent-audit.md)
- [Lean build and axiom verification](2026-09-30-hard-gap-lean-verification.md)
- [Independent realization audit](2026-09-30-profile-realizability-independent-audit.md)
- [Lean statement-fidelity audit](2026-09-30-hard-gap-lean-fidelity-audit.md)
- [Fixed-measure and transfer quantifier audit](2026-09-30-fixed-measure-transfer-adversarial-audit.md)
- [Finite regularization, deletion, and summation](packing-unforced-finite-profile.tex)
- [Subquadratic profile transfer and its precise exponent range](packing-unforced-subquadratic.tex)
- [Coherent strong integrability and the combined conclusion](packing-unforced-coherent-lp.tex)
- [Direct frequency-band comparison and weighted selected-scale criterion](packing-unforced-band-comparison.tex)
- [Common angular tails and the weaker rearranged summability test](packing-unforced-angular-tails.tex)
- [Full tail optimization and exact scalar endpoint obstructions](2026-09-30-common-radial-tail-summability.md)
- [Curvature-energy barriers for all sources and selected global depths](packing-unforced-curvature-obstruction.tex)
- [Detailed profile formula and selected-scale obstruction](2026-09-30-curvature-profile-selected-scale-obstruction.md)
- [All-source obstruction with finite critical measures and arbitrary common-scale partitions](2026-09-30-all-source-curvature-certificate-obstruction.md)
- [Critical covering summability and the subpower endpoint theorem](packing-unforced-critical-covering.tex)
- [Sparse covering scales and the complete irregular family](packing-unforced-sparse-moran.tex)
- [Full comparison and exact curvature-kernel derivation](2026-09-30-no-log-positive-band-comparison.md)
- [Independent audit of the comparison without logarithmic loss](2026-09-30-band-comparison-independent-audit.md)
- [Independent analytic and sparse-construction audit](2026-09-30-frequency-band-and-sparse-moran-independent-audit.md)
- [Sparse-family derivation and provenance](2026-09-30-sparse-coherent-covering.md)
- [Why critical measure finiteness cannot supply the all-scale criterion](2026-09-30-critical-measure-gauge-extraction-obstruction.md)
- [Explicit endpoint examples and their hereditary dimension inequality](packing-unforced-critical-moran.tex)
- [Full compact construction and its exact dimensions](2026-09-30-critical-covering-moran-examples.md)
- [Earlier variable-exponent and compact-construction audit](2026-09-30-variable-exponent-coherent-endpoint-audit.md)
- [Fresh adversarial audit of the core Fourier transfer](2026-09-30-core-fourier-transfer-adversarial-audit.md)
- [Limits of optimizing coherent estimates using cell masses alone](2026-09-30-coherent-mass-only-obstruction.md)
- [Circular-incidence estimates tested against the far-crowding criterion](2026-09-30-circular-incidence-crowding-test.md)
- [Detailed subquadratic derivation and raw weak-norm obstructions](2026-09-30-subquadratic-profile-transfer.md)
- [Independent subquadratic-transfer audit](2026-09-30-subquadratic-transfer-independent-audit.md)
- [Detailed coherent integrability proof](2026-09-30-coherent-subquadratic-regularity.md)
- [Independent coherent integrability audit](2026-09-30-coherent-lp-independent-audit.md)
- [Positive selection for the finite train-track family](2026-09-30-positive-train-track-selection.md)
- [Independent positive-selection audit](2026-09-30-positive-selection-independent-audit.md)
- [Weighted selected-cap estimate and soft selection](2026-09-30-selected-cap-superposition-audit.md)
- [Positive selection criteria and the sharper finite-model estimate](packing-unforced-positive-selection.tex)
- [Persistent selection and the half-order transverse potential](2026-09-30-persistent-selection-and-half-potential.md)
- [Independent persistent-selection audit](2026-09-30-persistent-selection-independent-audit.md)
- [Sharp averaged deletion theorem and full arithmetic proof](packing-unforced-sharp-selection.tex)
- [Detailed sharp finite-model derivation](2026-09-30-sharp-finite-train-track-deletion.md)
- [Independent cross-track resonance and optimality audit](2026-09-30-train-track-cross-resonance-audit.md)
- [Second independent finite-deletion audit](2026-09-30-sharp-finite-deletion-independent-audit.md)
- [Fixed positive angular selection and its near-source gain](packing-unforced-angular-selection.tex)
- [Detailed angular-selection proof and bisector audit](2026-09-30-fixed-angular-selection-collisions.md)
- [Positive far-crowding selection, exact mass identity, and entropy proof](packing-unforced-crowding.tex)
- [Detailed low-crowding and logarithmic criterion](2026-09-30-low-far-crowding-and-entropy.md)
- [Independent endpoint and entropy audit](2026-09-30-crowding-endpoint-independent-audit.md)
- [Fractional moments and rich near-bisector incidences](packing-unforced-fractional-crowding.tex)
- [Detailed fractional moment and incidence-tail proof](2026-09-30-fractional-far-bisector-crowding.md)
- [Independent fractional-moment audit](2026-09-30-fractional-crowding-independent-audit.md)
- [Positive pair selection on the fixed recursive example](2026-09-30-positive-selection-on-recursive-tracks.md)
- [Primary-source audit of possible dimensional improvements](2026-09-30-primary-pinned-literature-audit.md)
- [Conditional mixed-norm bisector criterion](packing-unforced-bisector.tex)
- [Reflection geometry, exact exponents, and primary-source review](2026-09-30-bisector-mixed-norm-route.md)
- [Fixed obstruction for every source measure on one support](packing-unforced-source-restriction-obstruction.tex)
- [Complete recursive construction and weak-norm proof](2026-09-30-nonremovable-bisector-source-obstruction.md)
- [Audit of all scales, dimensions, and the stronger source quantifier](2026-09-30-source-obstruction-root-audit.md)
- [Independent recursive-construction audit](2026-09-30-source-restriction-independent-audit.md)
- [The exact limitation of two bounded angular marginals](packing-unforced-angular-obstruction.tex)
- [Detailed angular-marginal obstruction](2026-09-30-two-angular-marginals-far-collision-obstruction.md)
- [Inherited-slat and generic-metric proofs](packing-unforced-geometric-transfer-limits.tex)
- [Why uniform finite slat averaging does not persist](2026-09-30-inherited-slat-obstruction.md)
- [Quantitative generic-metric bound and profile preservation](2026-09-30-generic-metric-pinned-energy.md)
- [Modified Fourier transfer](packing-unforced-transfer.tex)
- [Detailed selected-cap weighted embedding](packing-unforced-embedding.tex)
- [Coherent analytic branch](packing-bound-original-branch.tex)
- [Independent hard-gap proof audit](2026-09-30-sharp-gap-independent-audit.md)
- [Independent high-branch and cutoff algebra audit](2026-09-30-two-gap-high-branch-algebra-audit.md)
- [Fresh joint-limit and packet audit](2026-09-30-joint-limit-packet-audit.md)
- [Research derivation of the sharp certificates](2026-09-30-sharp-two-gap-bound.md)
- [Independent free-frontier argument](2026-09-30-actual-free-frontier.md)
- [Earlier adaptive profile refinement](packing-unforced-adaptive.tex)
- [Earlier minimum refinement](packing-unforced-minimum.tex)
- [Multiple-collapse profile obstructions](2026-09-30-unforced-multiple-collapse.md)
- [Raw off-cluster collision obstruction](2026-09-30-off-cluster-collision-obstruction.md)

Compile the main LaTeX file in this directory; its figure is in the adjacent
`figures` directory. Earlier manuscripts and the original Lean target are retained.
