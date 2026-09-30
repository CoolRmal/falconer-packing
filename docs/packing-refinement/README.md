# A sharper sufficient condition

30 September 2026.

The [complete proof manuscript](packing-refinement-proof.pdf) improves the quoted
packing bound. It includes both analytic branches, the new scale-selection lemma,
the reduction to Borel sets, and a stronger conditional-energy convergence theorem.

For a Borel planar set, write

$$
d=\dim_H E,\qquad D=\dim_P E,
\qquad \Delta_y(E)=\{|x-y|:x\in E\}.
$$

Set

$$
d_A = \frac{4+\sqrt{10}}6\approx1.193712943,
\qquad
d_B = \frac{47+\sqrt{649}}{60}\approx1.207924640.
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
  &1<d\le d_A,\\[4pt]
\dfrac{d(8d-7)}{d+1},
  &d_A<d\le d_B,\\[8pt]
3d-\dfrac{13}{6},
  &d_B<d\le\dfrac{11}{9},\\[8pt]
\dfrac{7d-6+\sqrt{49d^2-96d+56}}4,
  &\dfrac{11}{9}<d\le\dfrac54.
\end{cases}
$$

![Comparison of the refined and previous sufficient packing cutoffs.](../figures/packing-refinement.svg)

For example, the new condition covers

$$
d=\frac{31}{25}=1.24,\qquad D=\frac{77}{50}=1.54.
$$

The quoted previous cutoff at this Hausdorff dimension was approximately 1.506696.
The new cutoff and the
strict analytic exponent margin are

$$
B_{\mathrm{new}}(1.24)\approx1.546869432,
\qquad (d-1)-C(d,D)=\frac{3}{520}>0.
$$

## Why the bound improves

The finite profile has lower slope constraint a and upper slope constraint b.
Choose a minimum above the mandatory midpoint. An early minimum allows a
Lipschitz-cone estimate and a zero-cost landing at the minimum. A late minimum
improves the cost of the final jump. The resulting cost per unit terminal depth
is at most the maximum of

$$
\mathcal E(a,b)=\frac{1-2a-2a^2+(2+a)b}{6(1+a)},
$$

and

$$
\mathcal L(a,b)=
\begin{cases}
\dfrac{1+6b-10a}{8},&b\le\dfrac12,\\[6pt]
\dfrac{b-a}{1+2b}+\dfrac b2-\dfrac{3a}{4},&b\ge\dfrac12.
\end{cases}
$$

up to controlled grid errors. The chain has a bounded number of edges, satisfies
the curvature constraint, and visits the midpoint. The Fourier argument pays
this cost in the exponent. The four-branch cutoff follows by setting

$$
a=s-1,\qquad b=u-1,
\qquad
\max\{\mathcal E(a,b),\mathcal L(a,b)\}<s-1.
$$

The manuscript also improves the sufficient coherent energy summability condition to

$$
\sum_n Z_n^{(q-1)/q}<\infty,\qquad 1<q\le2,
$$

from the previous exponent

$$
\frac{q-1}{2q-1}.
$$

That improvement gives additional logarithmic endpoint criteria, but does not by
itself improve a condition involving only the two dimensions.

## What is established and what remains open

The manuscript supplies a mathematical proof using the explicitly cited established
analytic results. Separate internal checks covered the scale-selection lemma,
the Fourier transfer, the angular estimate, the algebra, and the exact example.
These checks are not external refereeing or Lean kernel verification.

The weakest possible condition remains unproved. No counterexample establishes
necessity of the new cutoff, and even the scale-selection upper bound has not been
proved optimal. For Hausdorff dimension greater than five quarters, GIOW already
gives a pin with positive-length distances without a packing restriction.

No Lean target or comparator definition was changed for this research update.
The new profile lemma and the unconditional analytic branches still need complete
Lean proofs using only standard axioms. A proof of an algebraic combination under
analytic hypotheses does not prove the unconditional theorem.

## Files

- [Proof PDF](packing-refinement-proof.pdf)
- [Main LaTeX source](packing-refinement-proof.tex)
- [New midpoint lemma](packing-refinement-profile-lemma.tex)
- [Universal minimum-split lemma](packing-refinement-minimum-lemma.tex)
- [Full finite-profile analytic branch](packing-refinement-finite-profile.tex)
- [Original coherent analytic branch](packing-bound-original-branch.tex)
- [Coherent argument and independent midpoint audit](2026-09-30-coherent-audit.md)
- [Analytic transfer audit](2026-09-30-inflation-audit.md)
- [Profile optimization and its remaining limitations](2026-09-30-profile-optimization.md)
- [Minimum-location split and cutoff algebra](2026-09-30-tail-minimum-split.md)

Compile the main LaTeX source from this directory; its figure is in the adjacent
`figures` directory.

The principal literature inputs are [Orponen](https://arxiv.org/abs/1710.11053),
[Keleti–Shmerkin](https://arxiv.org/abs/1801.08745),
[Guth–Iosevich–Ou–Wang](https://arxiv.org/abs/1808.09346),
[Liu's pinned identity](https://arxiv.org/abs/1802.00350), and
[Liu's 2026 regular-pin theorem](https://arxiv.org/abs/2603.15328).
