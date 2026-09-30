# An all-source obstruction to the selected-scale curvature certificate

Date: 2026-09-30. This note concerns the sufficient coefficient in `output/pdf/packing-unforced-band-comparison.tex`. It constructs sets with finite positive critical Hausdorff and packing measures for which every selected-scale series of those coefficients diverges, for every replacement source probability. The statement also allows uniformly sized measurable partitions in place of the original dyadic cells. It is an obstruction to this numerical sufficient criterion, not to pinned absolute continuity or positive distance length.

## 1. The coefficient and a universal homogeneous lower bound

For a positive finite measure, use the positive kernel and energy

$$
k_\delta(z)=\min\{|z|^{-1},\delta^2|z|^{-3}\},
\qquad
J_\delta(\lambda)=\iint k_\delta(x-x')\,d\lambda(x)d\lambda(x'),
$$

with the value infinity on the diagonal. Let K be a homogeneous planar dyadic construction: at depth n retain all four children or only the lower-left child, using the same rule in every occupied square. Write the count of occupied depth-n cylinders as

$$
2^{F(n)},\qquad F(0)=0,\qquad F(n+1)-F(n)\in\{0,2\}.
$$

Assume infinitely many forced-zero levels, so that the compact symbolic cylinders have unambiguous half-open dyadic addresses. Define

$$
G(n)=F(n)-n,\qquad H(t)=\sum_{\ell\ge t}2^{-G(\ell)}.
\tag{1}
$$

The series may initially be interpreted in the extended nonnegative reals. In the examples below it is finite at every depth.

Fix a positive diameter constant. For each depth m, allow any countable Borel partition of K whose pieces satisfy

$$
\operatorname{diam}P\le C_0 2^{-m},\qquad C_0>0.
$$

The partition may depend on m and on the source probability. Given a probability eta on K, let its mass and normalized restriction on a positive-mass piece P be the following:

$$
p_P=\eta(P),\qquad \eta_P=p_P^{-1}\eta|_P.
$$

For integers n smaller than m, define the coefficient for this partition by

$$
W^{\eta,\mathcal P_m}_{n,m}
=2^{-m}
\left[\sum_{P\in\mathcal P_m}p_P
J_{2^{-2n}}(\eta_P)^{1/2}\right]^2.
\tag{2}
$$

**Universal lower bound.** There is a positive constant depending only on the diameter constant such that, for every probability eta, every permitted partition, and every pair of depths,

$$
W^{\eta,\mathcal P_m}_{n,m}
\ge c_{C_0}\,2^{G(m)}H(\max\{m,2n\}).
\tag{3}
$$

No Frostman condition or absolute continuity of eta with respect to the natural probability is required. The inequality holds in the extended sense if an energy is infinite.

To prove it, put L equal to the maximum of m and twice n, and delta equal to two to the power minus twice n. For distinct points define the same-cylinder kernel

$$
S_L(x,x')=
\sum_{\ell\ge L}2^\ell
\mathbf1_{\{x,x'\text{ lie in the same depth-}\ell\text{ cylinder}\}}.
$$

Its nonzero terms are an initial interval of depths, because the cylinders are nested. If the last such depth is k, the geometric sum is at most twice two to the power k, and membership in one depth-k square implies that this is at most a fixed constant divided by the distance between the two points. Moreover a nonzero term implies the distance is at most the square root of two times delta. In that range the positive kernel is at least half the reciprocal distance. Thus

$$
k_\delta(x-x')\ge c S_L(x,x').
\tag{4}
$$

The diagonal causes no issue: first use finite partial sums in (4) and then monotone convergence. For a partition piece P, its diameter bound implies that it meets at most a fixed number, depending only on the diameter constant, of the original depth-m dyadic squares. Each occupied depth-m cylinder has exactly the following number of occupied depth-ell descendants:

$$
2^{F(\ell)-F(m)}.
$$

Hence the part of K in P meets at most a constant times this many depth-ell cylinders. Cauchy–Schwarz gives

$$
\sum_{Q\text{ at depth }\ell}\eta(P\cap Q)^2
\ge c_{C_0}\,p_P^2\,2^{F(m)-F(\ell)}.
$$

Integrating (4) and summing the nonnegative terms proves

$$
J_\delta(\eta|_P)
\ge c_{C_0}\,p_P^2\,2^{F(m)}H(L).
$$

Take square roots, sum over P, and use that the masses add to one. Since the square root of the unnormalized energy is the mass times the square root of its conditional energy, multiplying the square of that sum by the prefactor in (2) proves (3).

For the original dyadic partition, the natural equal-weight measure has a matching upper bound, as proved independently in `research/2026-09-30-curvature-profile-selected-scale-obstruction.md`. Thus the natural measure minimizes these coefficients up to fixed constants among all source probabilities and all partitions of bounded diameter at that scale. The lower bound alone is sufficient below.

## 2. A crossing barrier for every selected sequence

Suppose there are increasing integers tending to infinity and a fixed constant such that

$$
a_j\longrightarrow\infty,\qquad
G(m)\ge G(a_j)-C_1
\quad\left(\frac{a_j}{2}<m\le a_j\right).
\tag{5}
$$

Then no strictly increasing selected sequence of integer depths tending to infinity can make the coefficients in (2) tend to zero, for any source probability or permitted partitions.

Indeed, for each sufficiently large barrier choose the selected edge crossing half its depth. Its consecutive selected endpoints satisfy

$$
n\le\frac{a_j}{2}<m.
$$

If m is at least twice n, the first term of the tail in (3) gives a fixed positive lower bound, because the tail begins at m. Otherwise twice n is at most the barrier depth, m lies in the interval in (5), and the tail contains its term at that barrier depth. Consequently

$$
W^{\eta,\mathcal P_m}_{n,m}
\ge c_{C_0}2^{G(m)-G(a_j)}
\ge c_{C_0}2^{-C_1}.
\tag{6}
$$

The edge indices obtained in this way tend to infinity along a subsequence: any one finite edge can cross only finitely many of the increasing barrier depths. Therefore infinitely many coefficients have the same positive lower bound. For every positive exponent,

$$
\sum_i
\left(W^{\eta,\mathcal P_{n_{i+1}}}_{n_i,n_{i+1}}\right)^\zeta
=\infty,\qquad \zeta>0.
\tag{7}
$$

The same construction obstructs all sources and sequences simultaneously; the barrier depths do not depend on either choice.

## 3. Explicit barriers with finite positive critical measures

Fix dimension parameters in the range

$$
1<d<\frac32,\qquad 2d-1\le D<2.
\tag{8}
$$

In particular D is strictly greater than d. We construct the branching count between the lower line and an even approximation to the upper line. Put

$$
V(n)=2\left\lfloor\frac{Dn}{2}\right\rfloor.
$$

Its increments are zero or two. Choose a sufficiently large initial lower stopping depth, and start with an even count within two of d times that depth. A finite initial path with increments zero or two realizes this value.

From each lower stop, increase the count by two at every step until first meeting V. This catch-up time is finite because the growing slope is two and D is smaller than two. The count meets V exactly: their even difference is initially negative and its increments during catch-up are zero or two. After meeting V at a depth c, follow V until an arbitrarily large integer b. Then freeze the count until the next lower stopping depth

$$
a=\left\lceil\frac{V(b)}d\right\rceil.
$$

Choose b large enough that the whole interval from half of a to b lies after c and has positive length. This is possible since the ratio of a to b tends to D divided by d, which is strictly between one and two. Repeat indefinitely.

The count satisfies, apart from a finite initial range absorbed in constants,

$$
dn-2\le F(n)\le Dn,
\qquad
F(b)=V(b)=Db+O(1),
\qquad
da-d<F(a)=F(b)\le da.
\tag{9}
$$

There are infinitely many growing and flat phases, so the lower stops tend to infinity and forced-zero levels occur infinitely often. Apply the homogeneous four-child or one-child rule to this count. Let K be the resulting compact set and mu its natural equal-weight probability.

On the part of the half-depth interval before the peak, the count agrees with V. Therefore

$$
G(m)\ge(D-1)m-2
\ge\frac{D-1}{2}a-2
\ge(d-1)a-2
\ge G(a)-2
\qquad\left(\frac a2<m\le b\right).
$$

The third inequality is exactly the dimension inequality in (8). On the remaining interval the count is constant, so

$$
G(m)=F(a)-m\ge F(a)-a=G(a)
\qquad(b\le m\le a).
$$

Thus (5) holds with the fixed constant two, including at the equality case in (8). Sections 1–2 prove failure of every selected-scale series for every replacement source and every permitted sequence of partitions.

For completeness, the critical measures have the following precise properties:

$$
0<\mathcal H^d(K)<\infty,
\qquad
0<\mathcal P^D(K)<\infty,
\qquad
\dim_HK=d,\quad\dim_PK=D,
\tag{10}
$$

and their normalized restrictions both equal the natural probability. Here are the measure arguments, which are the same peak-and-trough estimates as in the earlier gauge-extraction note.

The lower bound on F gives the d-Frostman upper ball bound by bounded overlap of comparable dyadic squares. This proves positive critical Hausdorff measure. At every lower stop, the full cylinder cover has critical Hausdorff cost bounded by a fixed constant, proving finiteness. The upper bound on F gives a lower ball mass bound of order radius to the power D: the containing cylinder at a sufficiently fine comparable scale is entirely inside the ball. Disjoint ball packings centered on K then have uniformly bounded D-dimensional packing sums, giving finite packing premeasure and measure.

At the peaks the uniform cylinder mass gives an upper ball mass bound of order two to the power minus D times the peak depth. A maximal family of separated peak-scale points in any subset of K gives a disjoint packing whose D-dimensional cost is at least a fixed constant times that subset's mu outer measure. Letting the peak depth tend to infinity proves this lower bound for the packing premeasure of every subset. Applying it to every countable cover of K proves positive packing measure. These arguments establish (10).

At a fixed depth all cylinders are translations of a common scaled tail set. They are disjoint compact Borel subsets of K, and both critical measures are finite and positive. Translation invariance therefore gives equal critical measure to every cylinder at that depth. Its normalized mass must be the reciprocal of the cylinder count, exactly the natural probability mass. The cylinder sets generate the Borel sigma algebra, so

$$
\frac{\mathcal H^d|_K}{\mathcal H^d(K)}
=\mu
=\frac{\mathcal P^D|_K}{\mathcal P^D(K)}.
\tag{11}
$$

The count lower bound also implies finite first energy of mu, so the obstruction is not caused by failure of that prerequisite. In fact the full-tail expression in (1) is finite because its exponent grows at least linearly with positive slope d minus one.

## 4. Consequence and precise limitation

For every parameter pair in (8), finite positive critical Hausdorff and packing measures do not force the selected-scale curvature certificate after source restriction, source replacement, or repartitioning into pieces of uniformly bounded diameter at each selected global scale. Failure holds for all such choices, even though a nonzero d-Frostman source and the requisite finite first energy are present.

This does not prove failure of raw pinned absolute continuity. The coefficient is an upper-bound device for comparing positive affine laws, and a lower bound for that coefficient is not a lower bound for the actual difference of those laws. Centers inherited through a flat chain can make the actual error vanish there. More refined comparisons that use this cancellation remain possible.

The partition statement keeps the prefactor at the selected global scale. It does not address a different analytic theorem with genuinely heterogeneous piece diameters and individual first-norm prefactors, nor a selection depending jointly on source and pin. Those would require a new comparison argument. No claim of a distance-set counterexample or optimal dimension threshold is made.

Independent review: the critical-endpoint agent checked the complete proof, including the pointwise kernel comparison at the geometric boundary, all-source quantifiers, arbitrary diameter-bounded partitions, every-sequence crossing argument, exact even upper track, and the critical-measure identities, without finding an error. The profile-minimax agent independently checked the same lower bound and construction before converting them into the manuscript's curvature-obstruction section.
