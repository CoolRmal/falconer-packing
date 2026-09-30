# Adaptive scale selection for self-pinned distances

30 September 2026.

The [proof manuscript](packing-unforced-proof.pdf) proves a sufficient
condition for a Borel planar set. Write

$$
d=\dim_H E,\qquad D=\dim_P E,\qquad
\Delta_y(E)=\{|x-y|:x\in E\}.
$$

$$
B_{\mathrm A}(d)=
\begin{cases}
2d-1,&1<d\le\dfrac{11}{10},\\[7pt]
1+\beta(d-1),&\dfrac{11}{10}<d<\dfrac76,\\[7pt]
\dfrac1{3-2d},&\dfrac76\le d\le\dfrac54.
\end{cases}
$$

Then

$$
1<d\le\frac54,\qquad D<B_{\mathrm A}(d)
\quad\Longrightarrow\quad
\exists y\in E:\ |\Delta_y(E)|>0.
$$

Every packing inequality is strict. At Hausdorff dimension five quarters this
covers packing dimension strictly below two. Above five quarters, GIOW already
gives the conclusion without a packing restriction.

## Exact definition of the middle branch

The parameters range over

$$
\frac1{10}\le a\le\frac16,\qquad 2a\le b\le\frac12,
\qquad 0\le\theta\le1.
$$

Define

$$
\begin{aligned}
k&=2b-a,&q&=\frac b{k},\\
h_\theta&=\frac{1+q}{2}-\frac{\theta a}{4k},&
r_\theta&=\frac\theta{4b},\\
L_0&=\frac{1-2a}{4},&\lambda&=\frac{1-2b}{4b},\\
A_0&=\frac{1-a-3b}{3},&\gamma&=\frac{6b-1-2a}{3a}.
\end{aligned}
$$

The early and zero-terminal bounds are

$$
\begin{aligned}
m_\theta&=\frac{a h_\theta}{1-a r_\theta},\\
E_\theta&=A_0+\gamma m_\theta,\\
J_E&=\frac{\gamma L_0+\lambda A_0}{\gamma+\lambda},\\
Z&=\min\left\{\frac{1-q}{3},\frac{(1-a)(b-a)}{4(2b-a)(1-b)}\right\}.
\end{aligned}
$$

The two late routes give

$$
\begin{aligned}
A_v&=\frac{1-a}{3}-\frac{(1-b)h_\theta}{2},&
\sigma_v&=\frac{1-a}{6a}-\frac{(1-b)r_\theta}{2},\\
A_\ell&=\frac{1-a}{3}-h_\theta,&
\sigma_\ell&=\frac{a+2}{3a}-r_\theta.
\end{aligned}
$$

$$
P_i=A_i+a\sigma_i,\qquad
J_i=\frac{\sigma_i L_0+\lambda A_i}{\sigma_i+\lambda}
\quad(i=v,\ell).
$$

Finally set

$$
\begin{aligned}
C_\theta(a,b)&=\max\{Z,\min(E_\theta,J_E),
                         \min(P_v,J_v,P_\ell,J_\ell)\},\\[4pt]
C_{\mathrm A}(a,b)&=\min_{0\le\theta\le1}C_\theta(a,b).
\end{aligned}
$$

All denominators are positive. Compactness gives the last minimum. The proof
establishes continuity and strict increase in the upper slope, so the number in
the middle branch is uniquely defined by

$$
\beta(a)\in[2a,1/2],\qquad C_{\mathrm A}(a,\beta(a))=a.
$$

Its endpoint values are

$$
\beta(1/10)=1/5,\qquad \beta(1/6)=1/2.
$$

The curve includes the previous actual-minimum bound. The parameter zero retains
its chain constructions, while endpoint normalization adds stronger restrictions.
The parameter one uses the fully adaptive head interval; intermediate values can
improve both endpoint choices.

![Adaptive and preceding sufficient cutoffs, with a close view of the latest improvement.](../figures/packing-unforced.svg)

## Exact new examples

The choice

$$
d=\frac{111}{100}=1.11,\qquad D=\frac{49}{40}=1.225,
\qquad\theta=1
$$

has the exact cost and margin

$$
C_1\left(\frac{11}{100},\frac9{40}\right)=\frac{644}{5925},
\qquad \frac{11}{100}-\frac{644}{5925}=\frac{31}{23700}>0.
$$

The earlier cutoff there was 1.22. An interpolated choice also covers

$$
d=\frac{57}{50}=1.14,\qquad D=\frac{46}{35},\qquad\theta=\frac13,
$$

with cost 452437/3234750 and positive margin 214/1617375. These rational
inequalities establish the examples without relying on the plotted optimization.
The cutoff at Hausdorff dimension 1.24 remains 25/13, approximately 1.923077.

## What the proof adds

The Fourier argument separates standard source wave packets from finer spectral
caps and removes the prescribed midpoint from scale selection. The latest step
clips the endpoint to the lower barrier without decreasing any edge cost. It then
uses the actual tail minimum to enlarge the region of free continuation and to
choose the preceding interval. A supporting line handles the early free-terminal
case, while reflection and two variation bounds handle the remaining cases.

The PDF contains all three sufficient curves, both analytic branches, finite
regularization and deletion, the shell limit and Borel reduction, the weighted
embedding proof, and a detailed plan for Lean formalization.

## Scope and verification

The weakest condition for actual planar distance sets is not established.
The [multiple-collapse profiles](2026-09-30-unforced-multiple-collapse.md) give
obstructions to the scale-chain model. The
[off-cluster construction](2026-09-30-off-cluster-collision-obstruction.md) rules
out unrestricted raw collision control even after removing microscopic self-pairs.
Neither is a counterexample to pinned distance positivity.

The argument uses explicitly cited established theorems and internal independent
audits. It has not been externally refereed or fully verified in Lean. No Lean
statement, comparator target, or axiom requirement was changed. The unconditional
formalization remains unfinished; the plan requires only standard Lean axioms.

## Proof files

- [Complete manuscript](packing-unforced-proof.pdf)
- [Main LaTeX source](packing-unforced-proof.tex)
- [Finite regularization, deletion, and summation](packing-unforced-finite-profile.tex)
- [Previous unforced profile bound](packing-unforced-profile.tex)
- [Previous minimum refinement](packing-unforced-minimum.tex)
- [New endpoint normalization and adaptive family](packing-unforced-adaptive.tex)
- [Modified Fourier transfer](packing-unforced-transfer.tex)
- [Detailed selected-cap weighted embedding](packing-unforced-embedding.tex)
- [Sharp upper-slope profile](packing-unforced-obstruction.tex)
- [Coherent analytic branch](packing-bound-original-branch.tex)
- [Independent geometry and root audit](2026-09-30-normalized-supporting-line-independent-audit.md)
- [Assembled-source audit](2026-09-30-normalized-adaptive-head-audit.md)
- [Exact optimized-root derivation](2026-09-30-normalized-family-root.md)
- [Simpler closed-form subfamily and algebra](2026-09-30-normalized-bound-algebra.md)
- [Previous assembled-proof audit](2026-09-30-unforced-complete-audit.md)

Compile the main LaTeX file in this directory; its figure is in the adjacent
`figures` directory. Earlier manuscripts and the original Lean target are retained.
