# Endpoint-normalized adaptive-head estimates

30 September 2026. This records an independent audit of the stronger late estimates proposed by the root agent, and supplies the missing early zero-terminal estimate. These are mathematical bounds, not a claim of global optimality.

## Endpoint normalization

For $ax\le g(x)\le bx$ and $g$ 1-Lipschitz, replacing $g$ by

$$
\widetilde g(x)=\min\{g(x),1+a-x\}
$$

preserves the barriers and Lipschitz constant, sets $\widetilde g(1)=a$, and increases every edge cost. The edgewise proof is in `research/2026-09-30-ks-affine-barrier-reduction.md`. Therefore a uniform upper bound proved for endpoint-normalized profiles is valid for all profiles, with exactly the same chain endpoints, edge count, and admissibility.

For the normalized profile, use

$$
q=\frac b{2b-a},\quad m=\min_{[q,1]}g,\quad e=g(1)=a,
\quad Q_m=\frac{1+m/b}{2},\quad H_m=\frac{3+m/b}{4}.
$$

The extra relation is $m\le a$.

## Audit of the normalized late estimate

In the late free-terminal case, the variation construction from the adaptive-head note gives

$$
S(m)=\frac{-1-8a+9b}{24}
+\frac{4b-3a-ab}{24ab}m.
$$

The floor construction gives

$$
L(m)=\frac{1-2a}{4}-\frac{1-2b}{4b}m.
$$

The slope of $S$ is positive for $2a\le b$, $a\le1/6$. Direct calculation yields

$$
S(a)=\frac{(1+3b)(b-a)}{8b},
\qquad
S(a)-L(a)=\frac{(b-a)(3b-1)}{8b}.
$$

Thus for $b\le1/3$, the relation $m\le a$ directly gives

$$
\min\{L(m),S(m)\}\le S(m)\le\frac{(1+3b)(b-a)}{8b}.
$$

For $b\ge1/3$, intersecting the decreasing and increasing lines gives the universal bound

$$
\min\{L(m),S(m)\}
\le\frac{(b-a)(2+a-9ab)}{2(4b+3a-13ab)}.
$$

Both formulas agree at $b=1/3$. The denominators are positive on the proposed domain $1/10\le a\le1/6$, $2a\le b\le1/2$. The full formulas and their transition follow by exact algebra; no numerical optimization is required. The geometric chain and the case $t>n_0$ are unchanged from the independently checked adaptive-head proof.

## The early zero-terminal branch

Suppose the cone construction reaches a tail minimum $t$, of value $m$, after which the continuation is free. This includes $t\le Q_m$ and the zero-positive-part subcase of $Q_m<t\le H_m$.

Besides the slope-one cone, use the two upper bounds

$$
g(z)\le bz,\qquad g(z)\le m+z-t\quad(z\ge t).
$$

They intersect at $z_*=(t-m)/(1-b)$. The affine function

$$
H(z)=\frac z2+\left(b-\frac12\right)z_*
$$

majorizes their minimum, since its slope lies between $b$ and $1$. The slope-$1/2$ potential construction down to $(1+t)/2$, followed by a free jump to $t$, gives a prefix cost at most

$$
\frac{H(1)-a}{2}
=\frac{1/2-a-\kappa(t-m)}2,
\qquad \kappa=\frac{1/2-b}{1-b}\ge0.
\tag{1}
$$

For completeness, $H(t)$ need not equal $m$. If the potential remains positive at $(1+t)/2$, stop there and discard its nonnegative remaining value before the free jump. If it reaches zero earlier, use free minimum steps until the threshold. The positive-potential estimate therefore remains valid in both cases. Its initial value is nonnegative because $H(1)\ge g(1)=a$.

Since $t\ge q$ and $m\le a$, we have $t-m\ge q-a$. Equation (1) is consequently bounded by

$$
F(a,b)=\frac{1/2-a-\kappa(q-a)}2
=\frac{(1-a)(b-a)}{4(2b-a)(1-b)}.
\tag{2}
$$

One can take the cheaper of (2) and the former zero-terminal bound $(1-q)/3$.

## Removal of the former onset obstruction

At $b=2a$, the three elementary normalized bounds are

$$
F(a,2a)=\frac{1-a}{12(1-2a)},\qquad
E(a,2a)=\frac{1+11a}{21},\qquad
S(a)=\frac{1+6a}{16}.
$$

The last two equal $a$ at $a=1/10$ and are strictly less than $a$ for $a>1/10$. The first is already strictly less than $a$ throughout $[1/10,1/6]$: the equivalent quadratic is

$$
24a^2-13a+1<0.
$$

In particular $F(1/10,1/5)=3/32<1/10$. Together with the positive-terminal and reflected cases already proved in the adaptive-head note, this removes the former $a=1/9$ obstruction and gives strict improvements beyond $b=2a$ for every $a>1/10$ sufficiently close to that line. The positive-terminal slope used there is nonnegative when $a\ge1/10$, since $6b-1-2a\ge10a-1\ge0$; equality at the endpoint causes no problem for the maximizing argument.

The supporting-line construction adds only one bounded number of chain portions. The same logarithmic edge-count, continuous-profile limiting, and grid-error arguments apply.

## Audit of the assembled TeX source

I subsequently reviewed `output/pdf/packing-unforced-adaptive.tex` line by line, including its full normalized interpolated family and root theorem. No mathematical defect was found in the reviewed version.

The review checked endpoint clipping edge by edge; the enlarged free interval and all interpolated endpoints; supporting-line stopping with positive remaining potential; both early subcases; reflection and its telescoping penalty; both late routes, including minima above the starting scale; finite-chain compression and continuous-profile limits; every denominator and slope sign; strict monotonicity in the upper barrier; compact minimization; root existence, uniqueness, continuity and endpoint values; and the comparison with the earlier cost $V$.

The derivative transcription is now correct:

$$
60b^2-12b+1-4a
=240a^2-28a+1+(240a-12)x+60x^2,
\qquad b=2a+x.
$$

The constant term is $3/5$ at $a=1/10$. The upper-endpoint identity is also correct: at $b=1/2$, $E_0=4L_0/3$. The stated lower bound for $\sigma_v$ is valid; direct minimization over the allowed $b,\theta$ even gives the stronger bound $(5-2a)/(48a)$.

Exact symbolic recomputation agrees with the displayed factorization of $E_\theta$, the derivative of $J_E$, both floor-minus-route differences at $m=aq$, the baseline values at $b=2a,\theta=1$, and all claimed rational examples. In particular the assembled examples have exactly the costs and margins

$$
\frac{644}{5925},\quad\frac{31}{23700},
\qquad
\frac{452437}{3234750},\quad\frac{214}{1617375}.
$$

The root's shorter lower-endpoint argument is sufficient: at $(a,b)=(1/10,1/5)$, $\gamma=0$ makes both early bounds equal to $a$ for every $\theta$, while $\theta=1$ supplies an upper bound $a$. At the upper endpoint all intersection values equal $L_0$, the endpoint late bounds are no smaller, and the zero-terminal bound is no larger. Thus the assembled proof indeed obtains the claimed unique continuous cutoff.

This is an audit of the written mathematics and algebraic transcription. It does not constitute Lean certification, prove global optimality, or independently replace the separate audit of the analytic transfer theorem.
