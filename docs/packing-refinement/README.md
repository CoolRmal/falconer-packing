# A sharper sufficient condition

30 September 2026.

The [complete proof manuscript](packing-refinement-proof.pdf) improves the quoted
packing bound. It includes both analytic branches, the running-minimum reflection
lemma, the Borel-set reduction, and an explicit obstruction for the profile method.

For a Borel planar set, write

$$
d=\dim_H E,\qquad D=\dim_P E,
\qquad \Delta_y(E)=\{|x-y|:x\in E\}.
$$

Set

$$
d_L=1+a_L\approx1.188783591,\qquad d_J=1+a_J\approx1.195322471,
$$

where the respective roots are specified by

$$
16a_L^3+6a_L^2-7a_L+1=0,\qquad 3/16<a_L<19/100,
$$

$$
32a_J^4-28a_J^3-75a_J^2-5a_J+4=0,\qquad 19/100<a_J<1/5.
$$

For the middle branch define

$$
A(a)=3+13a+12a^2,\qquad J(a)=1-13a-12a^2,
$$

$$
b_F(a)=\frac{A(a)-\sqrt{A(a)^2+8(1+a)J(a)}}{4(1+a)}.
$$

The refined sufficient condition is

$$
1<d\le\frac54,\qquad D<B_{\mathrm{new}}(d)
\quad\Longrightarrow\quad
\exists y\in E:\ |\Delta_y(E)|>0,
$$

where

$$
B_{\mathrm{new}}(d)=
\begin{cases}
2d-1,
  &1<d\le d_L,\\[5pt]
1+b_F(d-1),
  &d_L<d\le d_J,\\[6pt]
\dfrac{d(8d-7)}{d+1},
  &d_J<d\le\dfrac54.
\end{cases}
$$

![Comparison of the refined and previous sufficient packing cutoffs.](../figures/packing-refinement.svg)

For example, the condition covers

$$
d=\frac{31}{25}=1.24,\qquad D=\frac85=1.60.
$$

The quoted previous cutoff at this Hausdorff dimension was approximately 1.506696.
The new cutoff and the strict exponent margin for this pair are

$$
B_{\mathrm{new}}(1.24)=\frac{2263}{1400}\approx1.616428571,
\qquad (d-1)-C(d,D)=\frac{23}{4650}>0.
$$

At Hausdorff dimension five quarters the new sufficient packing cutoff is five thirds.

## Why the bound improves

Normalize a finite profile to a 1-Lipschitz function between two linear barriers.
An early tail minimum allows a cone estimate and a zero-cost landing. For a late
minimum, reflect the profile upward by its running deficit, producing an early
minimum. A telescoping bound controls the effect of this reflection on every
chain. Compare that chain with a route through the original late minimum and
then through three quarters. Their weighted comparison gives the second cost below.

The reflection argument bounds the cost per unit terminal depth by the maximum of

$$
\mathcal E(a,b)=\frac{1-2a-2a^2+(2+a)b}{6(1+a)},
\qquad
\mathcal M(a,b)=\frac{3b}{8}+\frac3{16}-\frac{3a}{4},
$$

up to controlled grid errors. Every constructed chain has bounded length,
satisfies the curvature constraint, and visits the mandatory midpoint.
For the relevant range, the early-cost inequality already implies the late one:

$$
0<a\le\frac14,\qquad
\mathcal E(a,b)<a
\quad\Longrightarrow\quad
\mathcal M(a,b)<a.
$$

Substituting the Frostman and covering exponents gives

$$
a=s-1,\qquad b=u-1,
\qquad
\mathcal E(a,b)<a
\quad\Longleftrightarrow\quad
u<\frac{s(8s-7)}{s+1}.
$$

For small upper barrier slopes, a supporting affine line improves the early
cost further. Its explicit bound is

$$
\mathcal F(a,b)=\frac{b-a}{2(1+a)}+\frac{1-2a}{4}
-\frac{(1-2b)(1-a)(1+b)}{8(1-b)(1+a)},\qquad b\le\frac12.
$$

Using the minimum of the early costs gives the middle branch in the full curve.
Its onset and both joins follow from exact polynomial identities.

The Fourier transfer pays the resulting profile cost in the frequency exponent. The
coherent branch supplies the other part of the displayed dimension cutoff.

## What is established and what remains open

The manuscript supplies a mathematical proof using explicitly cited established
analytic results. Separate internal checks covered the reflection, both chain
constructions, Fourier transfer, angular estimate, algebra, and exact example.
These checks are not external refereeing or Lean kernel verification.

The weakest possible condition remains unproved. The manuscript proves an exact
limiting forced-chain cost for an explicit family of profiles, including the
boundary pairs at Hausdorff dimensions 1.24 and 1.25. This is an obstruction to
improving the present method from its stated profile hypotheses alone. No
counterexample establishes necessity of the cutoff for actual distance sets.
For Hausdorff dimension greater than five quarters, GIOW already gives a pin
with positive-length distances without a packing restriction.

No Lean target or comparator definition was changed for this research update.
The new profile lemmas and unconditional analytic branches still need complete
Lean proofs using only standard axioms. A proof of an algebraic combination under
analytic hypotheses does not prove the unconditional theorem.

The manuscript also proves an improved coherent conditional-energy summability
criterion, with logarithmic endpoint consequences. This does not by itself
improve a condition involving only the two dimensions.

## Files

- [Proof PDF](packing-refinement-proof.pdf)
- [Main LaTeX source](packing-refinement-proof.tex)
- [Reflection and competing-chain lemma](packing-refinement-reflection-lemma.tex)
- [Supporting affine-line improvement](packing-refinement-small-slope.tex)
- [Exact profile obstruction](packing-refinement-profile-obstruction.tex)
- [Full finite-profile analytic branch](packing-refinement-finite-profile.tex)
- [Original coherent analytic branch](packing-bound-original-branch.tex)
- [Earlier affine-envelope lemma](packing-refinement-profile-lemma.tex)
- [Earlier minimum-split lemma](packing-refinement-minimum-lemma.tex)
- [Independent reflection audit](2026-09-30-reflected-minimum-audit.md)
- [Independent supporting-line audit](2026-09-30-low-slope-envelope-audit.md)
- [Fresh Fourier stress audit](2026-09-30-fourier-stress-audit.md)
- [Coherent argument audit](2026-09-30-coherent-audit.md)
- [Analytic transfer audit](2026-09-30-inflation-audit.md)

Compile the main LaTeX source from this directory; its figure is in the adjacent
`figures` directory.

The principal literature inputs are [Orponen](https://arxiv.org/abs/1710.11053),
[Keleti–Shmerkin](https://arxiv.org/abs/1801.08745),
[Guth–Iosevich–Ou–Wang](https://arxiv.org/abs/1808.09346),
[Liu's pinned identity](https://arxiv.org/abs/1802.00350), and
[Liu's 2026 regular-pin theorem](https://arxiv.org/abs/2603.15328).
