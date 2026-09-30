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

![The new explicit curve and the preceding adaptive bound, with an enlarged comparison.](../figures/packing-unforced.svg)

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

## What a refined positive decomposition must prove

The manuscript proves a sharper quadratic selection estimate for a finite
train-track model, including all retained cross-track interactions. Deleting
only the pin's own track works exactly when the model's covering exponent is at
least four thirds; below that, a larger transverse deletion gives a controlled
norm. These model estimates do not give a new dimension-only theorem.

For fixed source and pin measures, vanishing total deletion and uniformly bounded
full quadratic norms would force the original joint law into the quadratic
space. The fixed-measure example rules out that overly strong target. Retaining
a fixed positive mass with a controlled norm is sufficient for a nonzero
absolutely continuous component. Persistent deletion is one implementation,
but proving its geometric estimates from dimensions alone remains open here.

The manuscript also checks the natural scale correspondence for a hybrid
argument: affine source depth is half the corresponding Fourier depth. Matching
profiles can obstruct both the existing coherent summability test and the
strict chain-cost test at these scales, including a nondecaying endpoint
example. This limits a direct combination of those criteria; it does not rule
out a new estimate connecting them.

## Proof and audit files

- [Complete manuscript](packing-unforced-proof.pdf)
- [Main LaTeX source](packing-unforced-proof.tex)
- [Sharp hard-gap estimates and matching profiles](packing-unforced-hard-gaps.tex)
- [Explicit dimension curve and precise model optimality](packing-unforced-hard-dimension.tex)
- [Finite-start identity and endpoint limitation](packing-unforced-finite-start.tex)
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
