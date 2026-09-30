# Unforced scale selection for self-pinned distances

30 September 2026.

The [complete proof manuscript](packing-unforced-proof.pdf) gives a weaker
sufficient condition than the earlier forced-midpoint refinement. For a Borel
planar set, put

$$
d=\dim_H E,\qquad D=\dim_P E,\qquad
\Delta_y(E)=\{|x-y|:x\in E\}.
$$

Define

$$
B_{\mathrm U}(d)=
\begin{cases}
2d-1,&1<d\le\dfrac87,\\[7pt]
\dfrac{2+2d-3d^2}{6-5d},&\dfrac87<d\le\dfrac76,\\[9pt]
\dfrac1{3-2d},&\dfrac76<d\le\dfrac54.
\end{cases}
$$

The sufficient condition is

$$
1<d\le\frac54,\qquad D<B_{\mathrm U}(d)
\quad\Longrightarrow\quad
\exists y\in E:\ |\Delta_y(E)|>0.
$$

Every join is continuous, and every packing inequality is strict. At Hausdorff
dimension five quarters, the theorem covers packing dimension strictly less than
two. It does not include equality at that endpoint. Above five quarters, GIOW
already supplies the conclusion without a packing restriction.

![The latest sufficient curve compared with the originally quoted one.](../figures/packing-unforced.svg)

For example,

$$
d=1.24\quad\Longrightarrow\quad D<\frac{25}{13}\approx1.923077
$$

is sufficient. The smaller-dimensional example

$$
d=1.15,\qquad D=1.32
$$

has exact profile margin one over 392; its cutoff is 1.33.

## What changes in the analytic argument

The spatial source packets keep the standard angular width. Finer caps partition
only the spectral functions used in quadratic inflation. Their marks remain
constant on the same standard-cap ancestor. Consequently initial packet
reconstruction still sums whole standard caps, while later Fourier estimates
may use finer labels without a new packet-multiplicity loss.

Both required angular inequalities follow from admissibility of an edge. There
is no longer a prescribed midpoint in the scale chain. The corresponding
bounded-length unforced profile estimate is

$$
U(a,b)=
\begin{cases}
\dfrac{(b-a)(1-a)}{2(2b-a)},&a\le b\le\dfrac12,\\[8pt]
\dfrac{b-a}{1+2b},&\dfrac12\le b\le1.
\end{cases}
$$

Setting the lower and upper profile slopes to the dimension exponents minus one,
and requiring this cost to be strictly below the source exponent minus one,
gives the last two branches. The earlier coherent argument gives the first.

## Scope and verification

The manuscript includes both analytic branches, the elementary profile proofs,
the complete modified Fourier argument, the shell limit, and the compact/Borel
reduction. It uses explicitly cited established theorems. The proof underwent
separate internal audits; this is not external refereeing or Lean verification.

An explicit single-peak profile proves that the upper-slope unforced estimate
is sharp under its stated profile hypotheses. These profiles are not planar
sets with null distance sets. The weakest sufficient condition for actual sets
remains unknown, and no unrestricted improvement below the five-quarters
threshold is asserted.

No Lean statement or comparator setting was changed. A formalization plan is
included in the PDF, but the unconditional theorem still needs a Lean proof
with only the standard axioms. A conditional algebraic combination would not
meet that requirement.

## Proof and audit files

- [Complete proof PDF](packing-unforced-proof.pdf)
- [Main LaTeX source](packing-unforced-proof.tex)
- [Finite regularization, deletion, and summation](packing-unforced-finite-profile.tex)
- [Unforced profile estimate](packing-unforced-profile.tex)
- [Full modified Fourier transfer](packing-unforced-transfer.tex)
- [Exact profile obstruction](packing-unforced-obstruction.tex)
- [Coherent analytic branch](packing-bound-original-branch.tex)
- [Complete assembled-proof audit](2026-09-30-unforced-complete-audit.md)
- [Independent packet-refinement audit](2026-09-30-unforced-standard-packet-audit.md)
- [Profile derivation and obstruction](2026-09-30-unforced-small-slope.md)

Compile the main LaTeX file in this directory; the figure is in the adjacent
`figures` directory. Earlier forced-midpoint manuscripts remain in
[the preceding research folder](../packing-refinement/README.md).
