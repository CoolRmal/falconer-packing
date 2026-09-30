# Independent audit of the far-crowding criterion

Date: 2026-09-30.

Audited source: output/pdf/packing-unforced-crowding.tex, together with the near-source estimate in output/pdf/packing-unforced-angular-selection.tex.

Verdict: the complete argument is valid under its printed standing hypotheses. I found no mathematical correction needed. This audit checks the proofs, not merely their statements. In particular, the quantitative pin conclusion, the exact absolutely continuous mass formula, and the entropy constant all pass.

## 1. Compatibility with the near-source input

The source and pin probabilities have compact, positively separated supports. The fixed angular selection satisfies 0≤a_A≤1 and retains mass m_A>0. Consequently the selected pinned measure σ_y has mass at most one for every pin outside an irrelevant null set, and Π_A and Λ_A have the same total mass m_A≤1.

For ε∈(0,1) and 1/(s+1)<α<1, one has ε<ε^α, so the near-source proposition applies at r=ε^α. Its two powers are exactly

$$
\epsilon^{-1}(\epsilon^\alpha)^{s+1}
=\epsilon^{\alpha(s+1)-1},
\qquad
(\epsilon^\alpha)^{s-1}
=\epsilon^{\alpha(s-1)}.
$$

Both exponents are positive. Moreover ∫N_ε dΠ_A is precisely the near-source collision integral with both selection factors present. No pair-dependent angular selection or extra unproved estimate has been inserted.

The functions H_ε,N_ε,F_ε are nonnegative and jointly measurable: parameterized integrals of the Borel kernels give measurability, and N_ε counts a subset of the points counted by H_ε.

## 2. Positive bounded crowding gives an actual dominated L² component

The box mollifier has mass one and its autocorrelation is exactly

$$
(b_\epsilon*\widetilde b_\epsilon)(u)
=\frac{(\epsilon-|u|)_+}{\epsilon^2}.
$$

There is no missing factor of two. Expanding the squared norm of the selected positive law, and dropping only the second good-set indicator, gives

$$
\|f_j\|_2^2
\le\int_{G_j}H_{\epsilon_j}\,d\Pi_A
\le T\Pi_A(G_j)+\int N_{\epsilon_j}\,d\Pi_A.
$$

This uses the full near estimate, so no pointwise bound for N_ε on G_j is required. Passing to a subsequence whose selected masses converge to the stated limsup m gives uniform L² boundedness.

All radial supports belong to a common finite interval. Since ν is a probability, its indicator is a valid L² test function. Therefore weak L² convergence preserves the exact mass m, rather than merely a lower or upper bound. The nonnegative cone is weakly closed, and norm lower semicontinuity yields

$$
g\ge0,\qquad \int g=m,\qquad \|g\|_2^2\le Tm.
$$

The selected mollified densities are pointwise bounded by the mollifications of the fixed full selected law Λ_A. On nonnegative continuous tests, the latter converge to Λ_A by uniform continuity in the radial variable on the common compact region. Thus g(ν×dt)≤Λ_A as measures. No convergence, nesting, or stabilization of the individual pair selectors is assumed.

The reference to the positive compactness principle is legitimate, but the argument printed in this fragment already gives the necessary details.

## 3. Disintegration and the numerical pin constants

Measure domination gives, for ν-almost every y,

$$
g(y,t)\,dt\le\sigma_y(dt).
$$

This follows by testing on a countable generating collection of radial Borel sets and then extending to all Borel sets; all spaces are standard Borel. Hence

$$
h(y)=\int g(y,t)\,dt\le\sigma_y(\mathbb R)\le1,
\qquad \int h\,d\nu=m.
$$

Let a=ν{h≥m/2}. The stronger elementary estimate is

$$
m\le a+(1-a)m/2
\quad\Longrightarrow\quad
a\ge\frac{m}{2-m}\ge\frac m2.
$$

Markov's inequality gives

$$
\nu\left\{y:\int g(y,t)^2dt>4T\right\}
\le\frac{Tm}{4T}=\frac m4.
$$

The intersection used in the source therefore has measure at least m/4. For those pins, h≥m/2 and the squared norm is at most 4T, so

$$
|\Delta_y(\operatorname{supp}\mu)|
\ge\frac{h(y)^2}{\int g(y,t)^2dt}
\ge\frac{m^2}{16T}.
$$

Both printed constants are correct. The distance support is legitimate because σ_y is supported on the compact image Δ_y(supp μ), and the dominated component g is therefore supported there almost everywhere.

## 4. Exact absolutely continuous mass

For every finite threshold T, the first proposition gives an absolutely continuous dominated component of mass equal to the corresponding limsup good mass. It follows that

$$
\limsup_j\Pi_A\{F_{\epsilon_j}\le T\}\le m_{\rm ac}.
$$

For the reverse inequality, the joint Lebesgue decomposition does disintegrate as claimed. Indeed the absolutely continuous part f(ν×dt) is dominated by Λ_A, its conditional law is f(y,t)dt, and a joint reference-null carrier of the singular remainder has Lebesgue-null fibers for almost every y. Thus f(y,·) is exactly the density of the absolutely continuous part of σ_y for ν-almost every y.

The line differentiation theorem therefore gives

$$
\epsilon^{-1}\sigma_y([t-\epsilon,t+\epsilon])
\longrightarrow2f(y,t)
$$

at Lebesgue-almost every t for almost every y. The factor two is necessary and is correctly retained in the threshold comparison.

Since F_ε≤H_ε, pushforward first gives

$$
\Pi_A\{F_\epsilon\le T\}
\ge\int f(y,t)\,
1_{\{\epsilon^{-1}\sigma_y([t-\epsilon,t+\epsilon])\le T\}}
\,d\nu(y)dt.
$$

Using the strict set {2f<T} handles equality at the threshold. Fatou then gives the printed lower bound. Letting T increase to infinity recovers all m_ac. Together with the upper bound, this proves both exact equalities involving liminf and limsup along every sequence tending to zero.

Taking complements in the fixed finite measure Π_A proves the full-absolute-continuity consequence. In fact the same identity shows that this tail tightness condition is also necessary for full absolute continuity, although the manuscript only needs sufficiency.

As a separate check, on the singular part of each σ_y its symmetric Lebesgue density diverges to infinity almost everywhere, whereas N_ε→0 in Π_A-probability by the near estimate. On the absolutely continuous part, H_ε→2f and the same near term tends to zero in probability. This provides an independent interpretation of the formula: finite thresholds capture exactly the absolutely continuous mass as the threshold is increased.

## 5. The logarithmic estimate and its exact constant

The logarithmic moment assumption gives the tail bound

$$
\Pi_A\{F_{\epsilon_j}>T\}
\le C_0/\log(1+T),
$$

so the preceding mass formula yields full absolute continuity first. There is no circular use of a preexisting density in this step.

For the full selected mollification f_j=b_{ε_j}*σ_y, whenever the outer mollifier pairs t with a source radius r satisfying |t−r|≤ε_j/2, the defining interval for f_j is contained in [r−ε_j,r+ε_j]. Both normalizations are ε_j^{-1}; hence f_j(y,t)≤H_{ε_j}(x,y) exactly, with no additional constant.

Expanding the outer f_j integral against σ_y and using Tonelli therefore yields

$$
\int f_j\log(1+f_j)\,d\nu\,dt
\le\int\log(1+H_{\epsilon_j})\,d\Pi_A.
$$

The elementary inequality

$$
\log(1+F+N)\le\log(1+F)+N
$$

then gives an upper bound C_0+O(ε_j^κ). Fiberwise differentiation of the now absolutely continuous law, followed by Fubini and Fatou, proves

$$
\int f\log(1+f)\,d\nu\,dt\le C_0.
$$

The stated entropy constant is thus correct. No fixed power larger than one is needed.

## 6. The scalar example and its crowding moments

For

$$
f(t)=\frac{2\,1_{(0,e^{-1})}(t)}
 {t(\log(1/t))^3},
$$

the substitution v=log(1/t) gives

$$
\int f(t)\,dt=\int_1^\infty\frac2{v^3}\,dv=1.
$$

Also

$$
\log f=\log2+v-3\log v,\qquad
\int f\log f=\log2+\frac12<\infty.
$$

Here f≥2e³/27>1 on its support, so f log(1+f) differs from f log f by an integrable bounded multiple of f. On the other hand, for every β>0,

$$
\int f^{1+\beta}
=2^{1+\beta}\int_1^\infty
 e^{\beta v}v^{-3(1+\beta)}\,dv=\infty.
$$

The logarithmic crowding claim also holds. The Jensen step can be written explicitly as

$$
\begin{aligned}
\int f\log(1+H_\epsilon)
&=\int f\log f
 +\int f\log\frac{1+H_\epsilon}{f}\\
&\le\int f\log f
 +\log\int_{\{f>0\}}(1+H_\epsilon)\,dt\\
&\le\int f\log f+\log(|I|+2),
\end{aligned}
$$

since f(t)dt is a probability and ∫H_ε=2. All terms are well-defined here. Conversely, differentiation and Fatou imply that no uniform positive fractional crowding moment can hold for this example:

$$
\liminf_{\epsilon\to0}\int f H_\epsilon^\beta
\ge2^\beta\int f^{1+\beta}=\infty.
$$

Thus the example genuinely distinguishes the logarithmic criterion from every positive fractional moment, while making no claim about a planar Frostman realization.

## 7. Scope

The fragment correctly identifies its conclusions as measure-theoretic reductions. It does not establish a new dimension estimate, and its exact characterization is a statement about the absolutely continuous mass of the selected measure. It is not asserted as a necessary condition for positive Lebesgue measure of the distance support.

No changes to the audited TeX were made.
