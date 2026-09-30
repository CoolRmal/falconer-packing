# Audit of the unforced profile bound retaining actual minima

30 September 2026. This is an independent mathematical audit of `output/pdf/packing-unforced-minimum.tex`, including the corrected derivative formula and exact cutoff at $a=3/20$. I also checked its exponent selection and starting-scale interface in `packing-unforced-proof.tex` and `packing-unforced-transfer.tex`.

**Verdict:** I found no remaining mathematical defect in this profile refinement or its stated interface with the previously audited transfer argument. This is a written-proof audit, not a Lean verification or an external peer review. It establishes a sufficient bound; it does not establish the optimal profile minimax or the weakest possible distance-set condition.

## Geometric constructions

The parameter domain $1/8\le a\le1/6$, $2a\le b\le1/2$ implies $q=b/(2b-a)\le2/3$ and $h=(1+q)/2\le5/6$. Consequently every early minimum and every reflected head minimum is strictly below the permitted starting scale $n_0\ge7/8$.

The slope-$c$ potential is nondecreasing when $c\ge1/2$, since its derivative is $2c-g'\ge0$. On its positive region, negative variation is bounded by the potential drop divided by $2c+1$. Shortening the last edge to the boundary keeps the variation integral inside that region. On the nonpositive region, a leftmost interval minimum gives a free, strictly decreasing admissible edge. The cone construction only uses the Lipschitz property and a minimum on the relevant tail; it does not require a linear upper barrier.

For the actual minimum $m$ on $[q,1]$, the relations $aq\le m\le bq$ imply

$$
q\le Q_m=\frac{1+m/b}{2}\le h.
$$

The expanded free interval is valid even if a selected minimum crosses below $q$: the original free continuation then applies. The affine floor majorizes $bz$ for $z\ge m/b$. All left endpoints used before reaching $Q_m$ lie in that domain. Its potential is nonpositive at $Q_m$, and its value at $1$ is nonnegative because it majorizes $g(1)$. Thus the displayed floor cost is a genuine nonnegative upper bound.

In the early case, the interval $[2t-1,q]$ is nonempty. Choosing its minimum gives the exact terminal cost $(g(v)-m)_+$, because the remaining segment $[q,t]$ is bounded below by $m$. The two ensuing scalar bounds and their intersection with the floor cost are valid.

For reflection, the running-minimum correction is nondecreasing, and the direct two-point proof that $f=g+r$ is 1-Lipschitz is sound. It is unchanged to the left of $u$, is bounded below by $w$ on $[q,1]$, and has endpoint $e+w-m$. The edgewise estimate

$$
c_g(v,n)\le c_f(v,n)+r(n)-r(v)
$$

telescopes with total penalty at most $w-m$, including when the global minimum lies above $n_0$. The reflected function's lack of the original upper barrier to the right of $u$ is irrelevant to its cone construction.

In the case $w\ge b(2u-1)$, both terminal edges are free. The middle path can be bounded separately by its length and by negative variation. If $t>n_0$, restricting that path to $[h,n_0]$ decreases both bounds; adding the omitted, nonnegative cone allowance therefore preserves both stated estimates. This verifies the $J_F$ and $J_V$ routes in the potentially delicate late-start case.

## Length and stability

For piecewise affine profiles, a leftmost minimum is a breakpoint or the left endpoint, so the finite construction terminates. Consecutive free edges merge without changing their zero cost whenever their union is admissible. After all adjacent merges, each pair of retained free edges more than doubles the complementary depth. The other portions use maximal edges apart from a bounded number of terminal adjustments. This gives the asserted logarithmic edge count independently of the number of breakpoints.

Linear interpolation preserves both barriers and the Lipschitz constant. The uniform edge bound permits passage to a finite limiting chain; interval minima are continuous under uniform convergence of profiles and convergence of endpoints. Rounding endpoints down preserves admissibility and changes each edge cost by at most twice the mesh. Clamping an approximate profile between the two linear barriers preserves the Lipschitz constant and has the claimed uniform perturbation cost.

## Scalar algebra and the unique root

Exact symbolic calculation agrees with the closed formula for $J_E$, its derivative, all four level polynomials, the four rational values at $(a,b)=(3/20,7/20)$, and the claimed margin $1/1004$. The polynomial proving that $E_1$ is redundant expands exactly as stated after $b=2a+x$.

For $J_F$ and $J_V$, the corrected differentiation formula is

$$
J'=\frac{\sigma\lambda'(S-L_0)+\lambda(\sigma+\lambda)S'}{(\sigma+\lambda)^2}>0.
$$

All its signs hold throughout the closed parameter domain, including $b=1/2$. Together with strict monotonicity of $E_2,J_E$ and the endpoint evaluations, this proves the unique-root characterization and continuity of $b_*$. The comparison $V<U$ for $b<1/2$ follows from the two intersections to the right of $m=aq$.

I verified independently that

$$
b_*(3/20)=\frac{7+\sqrt{13}}{30},
\qquad
J_F(3/20,9/25)-3/20=-\frac{136}{51015}.
$$

Direct numerical bisection also reproduces every displayed sample value of $b_*$; these computations serve only as checks and are not used as proof.

## Interface with the distance criterion

In the new branch $9/8<d<7/6$, the separate treatment of $D<2d-1$ leaves $2(d-1)\le D-1<1/2$. Strictness of $V(d-1,D-1)<d-1$ and continuity allow the required exponents $s<d$, $u>D$ while preserving the profile domain, including the boundary case $D=2d-1$. The transfer section chooses a fixed $\zeta<1/8$; its grid error is bounded independently of $N$, so its starting scale is at least $7N/8$ for all sufficiently large shells. The finitely many remaining shells do not affect summability. No additional midpoint constraint is introduced by this refinement.
