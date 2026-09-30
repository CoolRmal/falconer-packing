# Refined scale selection for self-pinned distances

30 September 2026.

The [proof manuscript](packing-unforced-proof.pdf) gives the following sufficient
condition for a Borel planar set. Put

$$
d=\dim_H E,\qquad D=\dim_P E,\qquad
\Delta_y(E)=\{|x-y|:x\in E\}.
$$

$$
B_{\mathrm M}(d)=
\begin{cases}
2d-1,&1<d\le\dfrac98,\\[7pt]
1+b_*(d-1),&\dfrac98<d<\dfrac76,\\[7pt]
\dfrac1{3-2d},&\dfrac76\le d\le\dfrac54.
\end{cases}
$$

Then

$$
1<d\le\frac54,\qquad D<B_{\mathrm M}(d)
\quad\Longrightarrow\quad
\exists y\in E:\ |\Delta_y(E)|>0.
$$

## Exact definition of the middle branch

For the following parameter range, define four rational functions:

$$
\frac18\le a\le\frac16,\qquad 2a\le b\le\frac12,
$$

$$
\begin{aligned}
E(a,b)&=\frac{(b-a)(1+6b-4a)}{6(2b-a)},\\[6pt]
J_E(a,b)&=\frac{(1-a)(b-a)(6b-1)}{24b^2-14ab+3a-4b},\\[6pt]
J_F(a,b)&=\frac{(b-a)(8b-a-2a^2-2ab)}{2(2b-a)(8b+3a-2ab)},\\[6pt]
J_V(a,b)&=\frac{(b-a)(12a^2b-4a^2-18ab^2-ab+a+4b)}
{4(2b-a)(3a+2b-8ab)}.
\end{aligned}
$$

$$
V(a,b)=\max\{\min(E(a,b),J_E(a,b)),\ \min(J_F(a,b),J_V(a,b))\}.
$$

All denominators are positive. For each fixed lower slope, this function is
continuous and strictly increasing in the upper slope. The number used in the
middle branch is defined exactly by

$$
b_*(a)\in[2a,1/2],\qquad V(a,b_*(a))=a.
$$

The proof establishes existence, uniqueness, continuity, and endpoint values

$$
b_*(1/8)=1/4,\qquad b_*(1/6)=1/2.
$$

Thus the theorem uses an exact root, not a numerical assumption. Every packing
inequality is strict. At Hausdorff dimension five quarters, the theorem covers
packing dimension strictly below two. Above five quarters, the GIOW theorem
already gives the conclusion without a packing restriction.

![Refined and earlier sufficient cutoffs, with a close view of the latest improvement.](../figures/packing-unforced.svg)

An exact new example is

$$
d=\frac{23}{20}=1.15,\qquad D=\frac{27}{20}=1.35.
$$

For these slopes the profile cost and margin are

$$
V\left(\frac3{20},\frac7{20}\right)=\frac{187}{1255},
\qquad \frac3{20}-\frac{187}{1255}=\frac1{1004}>0.
$$

The exact cutoff there is

$$
B_{\mathrm M}(23/20)=\frac{37+\sqrt{13}}{30}\approx1.353518376,
$$

compared with 1.33 in the preceding unforced proof and 1.30 in the originally quoted
theorem. The cutoff at Hausdorff
dimension 1.24 remains 25/13, approximately 1.923077.

## What the proof adds

The Fourier argument separates standard source wave packets from finer spectral
caps and removes the prescribed midpoint from scale selection. The latest profile
estimate retains the height and location of a tail minimum, as well as a preceding
minimum. Enlarging the region of free continuation and comparing several chains
produces the four rational bounds above. One chain uses negative variation in
place of interval length. Their exact comparisons give the unique-root cutoff.

The PDF contains the previous simpler curve, both analytic branches, finite
regularization and deletion, the shell limit and Borel reduction, and a detailed
weighted embedding proof for the Fourier inflation step.

## Scope and verification

The weakest condition for actual planar distance sets is not established.
Sharpness of the upper-slope profile estimate is a statement about the specified
scale-chain model, not a planar set with null distance sets. A separate
[fixed-measure construction](2026-09-30-synchronized-profile-energy-obstruction.md)
also rules out a power saving in global source energy from synchronized profiles
alone; it does not rule out stronger estimates of source–pin interactions.

The mathematical argument uses explicitly cited established theorems and has
internal audits. It has not been externally refereed or fully verified in Lean.
No Lean statement, comparator target, or axiom requirement was changed. The PDF
includes a formalization plan, but the unconditional Lean proof remains unfinished.

## Proof files

- [Complete manuscript](packing-unforced-proof.pdf)
- [Main LaTeX source](packing-unforced-proof.tex)
- [Finite regularization, deletion, and summation](packing-unforced-finite-profile.tex)
- [Previous unforced profile bound](packing-unforced-profile.tex)
- [Refined minimum argument and root characterization](packing-unforced-minimum.tex)
- [Modified Fourier transfer](packing-unforced-transfer.tex)
- [Detailed selected-cap weighted embedding](packing-unforced-embedding.tex)
- [Sharp upper-slope profile](packing-unforced-obstruction.tex)
- [Coherent analytic branch](packing-bound-original-branch.tex)
- [Previous assembled-proof audit](2026-09-30-unforced-complete-audit.md)
- [Independent audit of the refined profile proof](2026-09-30-actual-minimum-audit.md)
- [Independent algebra and exact cutoff audit](2026-09-30-minimum-algebra-audit.md)
- [Focused one-step stress test and proof](2026-09-30-one-step-inflation-stress.md)
- [Exact reduction to an affine-barrier total-drop problem](2026-09-30-ks-affine-barrier-reduction.md)

Compile the main LaTeX file in this directory; its figure is in the adjacent
`figures` directory. [Earlier forced-midpoint manuscripts](../packing-refinement/README.md)
are retained separately.
