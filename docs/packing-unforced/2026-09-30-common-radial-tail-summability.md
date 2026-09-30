# Common radial tails improve positive comparison summability

Date: 2026-09-30.

This note refines the summation step of the no-log positive affine comparison. A single family of centers can use the actual common angular-density tail, instead of applying the same power-law Markov estimate separately at every scale. This yields a strictly weaker numerical summability criterion. Explicit scalar density examples show that two natural boundary improvements cannot follow from the numerical Lq input alone. These examples concern the upper-bound certificate; they are not constructions of planar source and pin measures or counterexamples to a distance conclusion.

## 1. Fixed geometric setup

Let mu and nu be separated, compactly supported probabilities as in the positive affine comparison. Assume the source has finite first energy. Assume that its radial pin laws have jointly measurable densities

$$
(\Theta_x)_*\nu=\rho_x\sigma
\quad\text{for mu-almost every }x,
\qquad
\Theta_x(y)=\frac{x-y}{|x-y|},
\tag{1}
$$

where sigma is normalized arclength. Define their actual tails and their common average by

$$
T_x(A)=\int\rho_x(\theta)
                 1_{\{\rho_x(\theta)>A\}}\,d\sigma(\theta),
\qquad
T(A)=\int T_x(A)\,d\mu(x).
\tag{2}
$$

The density in (1) may be chosen jointly measurably by applying the Radon–Nikodym theorem to the joint source–angle law. Every T_x lies between zero and one. Let n_j be a fixed strictly increasing sequence of sufficiently large dyadic depths. For the comparison between n_j and n_{j+1}, let V_j be any valid center-independent geometric coefficient from the band comparison. In particular one can take the exact energy coefficient

$$
V_j=W_{n_j,n_{j+1}}
=2^{-n_{j+1}}
\left[\sum_{Q\text{ at level }n_{j+1}}
p_Q J_{2^{-2n_j}}(\mu_Q)^{1/2}\right]^2,
\tag{3}
$$

where

$$
J_\delta(\lambda)=\iint
\min\{|x-x'|^{-1},\delta^2|x-x'|^{-3}\}
\,d\lambda(x)d\lambda(x').
$$

For an s-Frostman source, with 1<s<2, the larger coefficient

$$
V_j=Z_{n_j,n_{j+1}}
=2^{-n_{j+1}-2n_j(s-1)}
\left(\sum_{Q\text{ at level }n_{j+1}}\sqrt{p_Q}\right)^2
\tag{4}
$$

also works, with the fixed Frostman constant absorbed into the comparison constant. These coefficients do not depend on the chosen source centers.

## 2. Simultaneous deterministic choice of centers

**Proposition.** For any prescribed thresholds A_j at least one, if

$$
\sum_j\left[(A_jV_j)^{1/2}+T(A_j)\right]<\infty,
\tag{5}
$$

then the raw pinned distance law is absolutely continuous for nu-almost every pin.

**Proof.** Each center at the selected level n_j occurs in at most two comparisons. For j at least one, put

$$
H_j(x)=T_x(A_{j-1})+T_x(A_j),
\qquad H_0(x)=T_x(A_0).
\tag{6}
$$

For every positive-mass level-n_j cell Q choose one center x_Q in Q, inside the common full-mu-measure set where (1) and finite projected energies hold, such that

$$
H_j(x_Q)\le\frac2{p_Q}\int_Q H_j(x)\,d\mu(x).
\tag{7}
$$

If the average is zero, almost every point in Q has H_j zero; otherwise the elementary averaging argument gives a positive-mass set of admissible choices. There are only countably many cells. Make these choices once for the entire prescribed schedule, and choose any admissible centers at unused levels. The resulting positive affine laws f_n are fixed across all comparisons.

For the comparison from n_j to n_{j+1}, delete pins at which either of the two selected angular densities exceeds A_j. For a descendant Q with ancestor P, the deleted pin mass is at most

$$
T_{x_P}(A_j)+T_{x_Q}(A_j).
\tag{8}
$$

This follows exactly from the pushforward identity (1), not from a Markov estimate. On retained pins both angular marginals are bounded by A_j sigma, so the same frequency-band proof gives the good contribution bounded by C times the square root of A_j V_j. The conditional density difference on deleted pins has L1 norm at most two.

Let

$$
S_j(A)=\sum_{Q\text{ at level }n_j}p_Q T_{x_Q}(A).
$$

Summing descendant masses over their ancestors gives

$$
\|f_{n_{j+1}}-f_{n_j}\|_1
\le C(A_jV_j)^{1/2}
  +2S_j(A_j)+2S_{j+1}(A_j).
\tag{9}
$$

The individual S_j terms need not each be bounded by a fixed multiple of T at the particular threshold. The simultaneous choice only needs their total:

$$
\begin{aligned}
\sum_{j\ge0}[S_j(A_j)+S_{j+1}(A_j)]
&=\sum_{j\ge0}\sum_{Q\text{ at level }n_j}p_QH_j(x_Q)\\
&\le2\sum_{j\ge0}\int H_j\,d\mu
=4\sum_{j\ge0}T(A_j).
\end{aligned}
\tag{10}
$$

All terms are nonnegative, so the rearrangement and limiting sums use Tonelli. Equations (5), (9), and (10) show that the selected positive affine densities are Cauchy in L1. Their limit remains nonnegative with mass one. Uniform approximation of the affine maps to distance identifies the limit with the raw joint distance law; disintegration proves the claim.

If one also wishes to retain the earlier center condition

$$
\|\rho_{x_Q}\|_q^q\le\frac2{p_Q}
                           \int_Q\|\rho_x\|_q^q\,d\mu(x),
$$

one may replace the constant two in (7) by four. Markov bounds the two excluded proportions by one-half and one-quarter, respectively, leaving a positive-mass intersection. This changes only an absolute constant in (10).

One exact scalar formulation of (5) is useful. Define

$$
\Phi(v)=\inf_{A\ge1}\{\sqrt{Av}+T(A)\}.
\tag{11}
$$

The condition that the sum of Phi(V_j) be finite is equivalent to existence of thresholds satisfying (5): select a threshold within an added error of 2 to power minus j from each infimum. Thus the complete common tail can be used without replacing it by a power-law envelope. No claim is made that (11) is a necessary condition for actual distance absolute continuity.

## 3. A weaker criterion using only the numerical Lq moment

Assume in addition that

$$
B=\int\!\int\rho_x(\theta)^q\,d\sigma(\theta)d\mu(x)<\infty,
\qquad q>1,
\qquad r=q-1,
\qquad \eta=\frac r{2r+1}.
\tag{12}
$$

Write V_k star for the nonincreasing rearrangement of the positive coefficients V_j. Zero coefficients can be treated separately by thresholds making their tails summable; in the nonzero probability setting (3) the coefficients are positive. The following sufficient condition is strictly weaker than summability of V_j to power eta:

$$
\sum_{k\ge1}k^{1/(2r)}\sqrt{V_k^*}<\infty.
\tag{13}
$$

Indeed, assign to the index of decreasing rank k the threshold

$$
A_j=k^{1/r}.
\tag{14}
$$

The sum of the good contributions is exactly (13). For the bad terms, Tonelli gives

$$
\begin{aligned}
\sum_{k\ge1}T(k^{1/r})
&=\int\!\int\rho_x(\theta)
       \#\{k\ge1:k^{1/r}<\rho_x(\theta)\}
                      \,d\sigma(\theta)d\mu(x)\\
&\le\int\!\int\rho_x(\theta)^{1+r}
                      \,d\sigma(\theta)d\mu(x)=B.
\end{aligned}
\tag{15}
$$

Thus (5) applies with one deterministic family of centers. A decreasing rearrangement exists whenever (13) is finite, since the coefficients then tend to zero with only finitely many exceeding any fixed positive level. Ties may be broken by their original indices.

To compare with the older condition, let

$$
a_k=(V_k^*)^\eta,
\qquad t=\frac1{2\eta}=1+\frac1{2r}>1.
$$

The sequence a_k decreases. If its sum is S finite, then k a_k is at most S and

$$
\sum_k k^{1/(2r)}\sqrt{V_k^*}
=\sum_k k^{t-1}a_k^t
\le S^{t-1}\sum_k a_k=S^t.
\tag{16}
$$

The implication is strict. For

$$
V_k^*=k^{-1/\eta}(\log k)^{-\beta},
\qquad k\ge3,
\tag{17}
$$

criterion (13) holds exactly when beta is greater than two. The old sum of V to power eta requires beta greater than 1/eta, which is strictly larger than two. Any beta strictly between two and 1/eta therefore witnesses a strict improvement.

For example, a consecutive critical count estimate of the form

$$
\mathcal N_{n+1}\le C\,2^{n(2s-1)}
n^{-1/\eta}(\log n)^{-\beta},\qquad \beta>2,
\tag{18}
$$

is enough. For an arbitrary sequence dominated by this decreasing model, its decreasing rearrangement is dominated by a constant multiple of the same model, so the condition applies even if the actual coefficients fluctuate.

## 4. Why the pure power boundary cannot be settled from numerical Lq alone

We now give scalar probability densities for which the exact common-tail test (5) fails at the pure power boundary, regardless of the threshold schedule. They do not assert anything about realizability as all radial laws of a planar source and pin pair.

Fix a number epsilon with

$$
0<\epsilon\le2r.
$$

There is a probability density rho on the normalized circle, with finite Lq norm, whose distribution tail under arclength satisfies

$$
\sigma\{\rho>A\}\asymp
\frac{A^{-q}}{(\log A)^{1+\epsilon}}
\quad\text{for sufficiently large }A.
\tag{19}
$$

For completeness, prescribe this decreasing survival function above a large fixed A_0 on a probability interval, complete it to a probability distribution on nonnegative values, and realize it by the inverse distribution function. Its first moment is finite and positive. Dividing the resulting function by that mean makes it a probability density; the asymptotic formula is unchanged up to constants. The q moment is finite because its tail integral is bounded by a constant times

$$
\int_{A_0}^\infty\frac{dA}{A(\log A)^{1+\epsilon}}<\infty.
$$

If S(A) denotes the survival probability in (19), the density-weighted tail is

$$
T(A)=A S(A)+\int_A^\infty S(t)\,dt
\asymp\frac{A^{-r}}{(\log A)^{1+\epsilon}}.
\tag{20}
$$

The lower bound is its first term. For the upper bound use the monotonic logarithmic factor and integrate t to power minus q, which is integrable at infinity.

Let every abstract source center have this same density, and take

$$
V_n=n^{-1/\eta}=n^{-(2r+1)/r}.
$$

For large n define the benchmark threshold

$$
A_n^*=n^{1/r}(\log n)^{-2(1+\epsilon)/(2r+1)}.
\tag{21}
$$

Its logarithm is comparable to log n. Direct substitution gives

$$
\sqrt{A_n^*V_n}\asymp T(A_n^*)
\asymp\frac1{n(\log n)^{(1+\epsilon)/(2r+1)}}.
\tag{22}
$$

For every possible threshold A, either A is at least A_n star, in which case the good term is at least the bound in (22), or A is at most A_n star, in which case monotonicity makes its tail term at least that bound. Therefore

$$
\inf_{A\ge1}\{\sqrt{AV_n}+T(A)\}
\ge\frac c{n(\log n)^{(1+\epsilon)/(2r+1)}}.
\tag{23}
$$

The sum diverges because epsilon is at most 2r. This rules out a universal pure-power boundary theorem derived solely by choosing thresholds in the existing good-term bound and using arbitrary finite-Lq common tails. Randomizing the thresholds cannot avoid this pointwise infimum lower bound.

## 5. The logarithmic boundary beta equal to two

The gain in (17) has its own sharp universal boundary within this numerical test. Choose a scalar probability density with

$$
S(A)=\sigma\{\rho>A\}\asymp
\frac{A^{-q}}{\log A\,(\log\log A)^{1+\epsilon}},
\qquad 0<\epsilon\le2r.
\tag{24}
$$

The same inverse-distribution construction and normalization apply. Its q moment is finite, since

$$
\int_{A_0}^\infty
\frac{dA}{A\log A\,(\log\log A)^{1+\epsilon}}<\infty.
$$

Its density-weighted tail satisfies

$$
T(A)\asymp
\frac{A^{-r}}{\log A\,(\log\log A)^{1+\epsilon}}.
\tag{25}
$$

Now take the boundary coefficients

$$
V_n=n^{-1/\eta}(\log n)^{-2}.
$$

The benchmark is

$$
A_n^*=n^{1/r}(\log\log n)^{-2(1+\epsilon)/(2r+1)}.
\tag{26}
$$

Both relevant terms are comparable to

$$
\frac1{n\log n\,(\log\log n)^{(1+\epsilon)/(2r+1)}}.
\tag{27}
$$

The same two-case argument gives this as a lower bound for every threshold choice. Its sum diverges when epsilon is at most 2r, including equality. Thus beta greater than two cannot be replaced by beta equal to two uniformly over all Lq angular densities using this exact numerical threshold certificate.

This obstruction is deliberately narrow. It neither shows failure of actual affine-law convergence nor exhibits a planar source and pin configuration with the prescribed identical angular densities. A geometric relation among radial laws, a sharper good-term estimate, or a different positive decomposition could yield additional gains. The positive result established here is the strictly weaker criterion (13), with a simultaneous fixed choice of centers and convergence of the actual positive distance law.

## 6. An additional logarithmic moment repairs the numerical boundary

The exact common-tail criterion also records precisely useful extra angular information. Suppose, for some kappa>0,

$$
\int\!\int\rho_x^q\bigl[\log(e+\rho_x)\bigr]^\kappa
\,d\sigma\,d\mu<\infty.
\tag{28}
$$

Choose a positive number a with ar less than kappa. For all sufficiently large decreasing ranks k, assign

$$
A_k=k^{1/r}(\log k)^{-a},
\tag{29}
$$

and make the finitely many initial thresholds at least one. These thresholds are eventually increasing. For a real z at least one, the number of ranks with A_k<z is bounded by

$$
C\bigl[1+z^r(\log(e+z))^{ar}\bigr].
\tag{30}
$$

Indeed, for large k the logarithm of A_k is at least log k divided by 2r. Thus A_k<z first implies log k at most 2r log z. Substitution back into k less than z to power r times (log k) to power ar gives (30). Tonelli now bounds the sum of the true tails at these thresholds by a constant times one plus the moment in (28).

For the boundary coefficients from Section 5, the good contribution becomes

$$
\sqrt{A_kV_k^*}
=\frac1{k(\log k)^{1+a/2}},
\tag{31}
$$

which is summable for every a>0. Hence any positive logarithmic improvement of the angular Lq moment suffices at that logarithmic boundary. At the pure-power boundary from Section 4, the same construction gives good terms equal to one divided by k times (log k) to power a/2. These are summable if a>2, which can be arranged under (28) when kappa>2r. These conclusions use explicitly stronger radial information and do not contradict the finite-Lq-only obstructions.
