# Fractional far-bisector crowding for a fixed positive angular selection

30 September 2026. This note proves a subquadratic sufficient criterion for the actual positive selected distance law. It permits divergence of the ordinary collision integral. The proposed rich-incidence estimate is a geometric hypothesis; it is not deduced from Hausdorff and packing dimensions. No improved dimensional threshold is claimed.

## 1. The fixed measure and the fractional collision quantity

Use the standing hypotheses and notation of `2026-09-30-fixed-angular-selection-collisions.md`: source and pin probabilities have compact separated supports, the source is s-Frostman with s>1, and

$$
0<a_0\le |x-y|\le b_0.
$$

Fix one angular threshold A with retained mass

$$
M:=\Pi_A(\mathbb R^2\times\mathbb R^2)
\ge m_0:=1-BA^{1-q}>0,
\qquad
\Pi_A(dx,dy)=a_A(x,y)\,d\mu(x)d\nu(y).
$$

The positive kernel a_A is fixed at every subsequent resolution. Let

$$
\lambda_y=(d_y)_*(a_A(\cdot,y)\mu),\qquad
\Lambda_A(dy,dt)=d\nu(y)\lambda_y(dt).
$$

Choose a source cutoff exponent with

$$
\frac1{s+1}<\alpha<1,
\qquad
\kappa_0=\min\{\alpha(s+1)-1,\alpha(s-1)\}>0.
$$

At each sufficiently small resolution epsilon set r_epsilon=epsilon^alpha. For a retained pair (x,y), define

$$
\begin{aligned}
H_\varepsilon(x,y)
&=\varepsilon^{-1}\int
 a_A(x',y)\,
 \mathbf 1_{\{||x-y|-|x'-y||\le\varepsilon\}}\,d\mu(x'),\\
N_\varepsilon(x,y)
&=\varepsilon^{-1}\int_{|x-x'|\le r_\varepsilon}
 a_A(x',y)\,
 \mathbf 1_{\{||x-y|-|x'-y||\le\varepsilon\}}\,d\mu(x'),\\
F_\varepsilon(x,y)&=H_\varepsilon(x,y)-N_\varepsilon(x,y).
\end{aligned}
$$

Thus the two positive angular factors appear through integration of these quantities against Pi_A. The proved near-source estimate is exactly

$$
\int N_\varepsilon\,d\Pi_A\le C A\varepsilon^{\kappa_0}.
\tag{1}
$$

**Proposition 1.** Fix 0<gamma<1. If some sequence epsilon_j tending to zero obeys

$$
\sup_j\int F_{\varepsilon_j}^{\gamma}\,d\Pi_A\le L<\infty,
\tag{2}
$$

then Lambda_A has an actual density in L^{1+gamma}(nu times Lebesgue measure), with

$$
\left\|\frac{d\Lambda_A}{d\nu\,dt}\right\|_{1+\gamma}^{1+\gamma}
\le L.
\tag{3}
$$

In particular a positive-nu set of pins has positive-length distance sets. The same original selected law is used in (2) and (3); no scale-dependent or arbitrary source-pair mask is substituted.

**Proof.** Let phi_epsilon=epsilon^{-1}1_{[-epsilon/2,epsilon/2]}, and set f_epsilon(y,t)=phi_epsilon*lambda_y(t). Tonelli gives

$$
\int f_\varepsilon^{1+\gamma}\,d\nu\,dt
=\int d\nu(y)\int d\lambda_y(r)\,
 \varepsilon^{-1}\int_{|t-r|\le\varepsilon/2}
 f_\varepsilon(y,t)^\gamma\,dt.
$$

For every t in this inner interval,

$$
f_\varepsilon(y,t)
\le\varepsilon^{-1}\lambda_y([r-\varepsilon,r+\varepsilon]).
$$

Pulling r back to |x-y| therefore yields the exact bound

$$
\int f_\varepsilon^{1+\gamma}\,d\nu\,dt
\le\int H_\varepsilon^\gamma\,d\Pi_A.
\tag{4}
$$

Subadditivity of the gamma power and Holder on the fixed finite measure Pi_A imply

$$
\begin{aligned}
\int H_\varepsilon^\gamma\,d\Pi_A
&\le\int F_\varepsilon^\gamma\,d\Pi_A
   +\int N_\varepsilon^\gamma\,d\Pi_A\\
&\le\int F_\varepsilon^\gamma\,d\Pi_A
   +M^{1-\gamma}(CA\varepsilon^{\kappa_0})^\gamma.
\end{aligned}
\tag{5}
$$

All radial supports lie in one compact interval. Weak compactness in L^{1+gamma}(nu times Lebesgue measure) gives a weakly convergent subsequence of the smoothings. Testing against continuous compactly supported functions identifies its limit with the fixed law Lambda_A. Lower semicontinuity and (5) give (3). Its positive mass M gives the pinned positive-length conclusion by disintegration and Holder. This proof shows exactly why the available near-source first moment also controls every fractional moment: concavity is applied under the original fixed selected pair measure, whose total mass is at most one.

## 2. A tail criterion and a geometric rich-bisector formulation

A first useful consequence is the following. If, uniformly along a sequence of resolutions,

$$
\Pi_A\{F_\varepsilon>t\}\le C_*t^{-\beta}
\quad(t\ge1)
\tag{6}
$$

for some beta>0, then (2) holds for every

$$
0<\gamma<\min\{1,\beta\}.
$$

Indeed the layer-cake formula bounds its left side by

$$
M+\gamma C_*\int_1^\infty t^{\gamma-\beta-1}\,dt
=M+\frac{\gamma C_*}{\beta-\gamma}.
$$

The next criterion measures actual near-bisector incidences at each source separation. Rescale the compact source support once so its diameter is at most one. For dyadic u in (0,1], distinct source points x,x', and retained pins y, write

$$
\theta_{x,x'}=\frac{x-x'}{|x-x'|},\qquad
c_{x,x'}=\frac{|x|^2-|x'|^2}{2|x-x'|}.
$$

For a fixed constant C_0=2b_0, define

$$
Q_{\varepsilon,u}(x,y)
=\frac{1}{\varepsilon u^{s-1}}
 \int_{u/2<|x-x'|\le u}
 a_A(x',y)
 \mathbf1_{\{|y\cdot\theta_{x,x'}-c_{x,x'}|
                   \le C_0\varepsilon/u\}}
 \,d\mu(x').
\tag{7}
$$

This is a dimensionless measure of the source mass whose perpendicular bisectors pass within C_0 epsilon/u of the retained pin. It integrates over source partners, rather than taking a pointwise upper bound for the pin mass associated with each individual source pair.

**Proposition 2.** Suppose there are beta>0, kappa>=0 and C_*>=1 such that, uniformly along resolutions epsilon_j and for every dyadic u>r_epsilon,

$$
\Pi_A\{Q_{\varepsilon,u}>t\}
\le C_*u^{-\kappa}t^{-\beta}
\quad(t\ge1),
\qquad
\frac\kappa\beta<s-1.
\tag{8}
$$

Then the actual selected law has an L^{1+gamma} density for every 0<gamma<min{1,beta}. In particular it has positive mass and produces positive-length pinned distance sets.

**Proof.** A distance collision in the source annulus u/2<|x-x'|<=u satisfies

$$
\begin{aligned}
2|x-x'|\,|c_{x,x'}-y\cdot\theta_{x,x'}|
&=\big||x-y|^2-|x'-y|^2\big|\\
&\le2b_0\varepsilon.
\end{aligned}
$$

Thus it is counted in (7), and

$$
F_\varepsilon(x,y)
\le\sum_{\substack{u\text{ dyadic}\\u>r_\varepsilon}}
 u^{s-1}Q_{\varepsilon,u}(x,y).
\tag{9}
$$

There is no loss of either angular factor in this inequality. Since Pi_A has mass at most one, its level-set measure is also bounded by one. Splitting the layer-cake integral at (C_*u^{-kappa})^{1/beta} gives

$$
\int Q_{\varepsilon,u}^\gamma\,d\Pi_A
\le\frac\beta{\beta-\gamma}
 C_*^{\gamma/\beta}u^{-\kappa\gamma/\beta}.
\tag{10}
$$

Apply subadditivity in (9), then integrate and use (10):

$$
\int F_\varepsilon^\gamma\,d\Pi_A
\le\frac\beta{\beta-\gamma}C_*^{\gamma/\beta}
 \sum_{u\text{ dyadic}\le1}
 u^{\gamma(s-1-\kappa/\beta)}<\infty.
\tag{11}
$$

The sum converges precisely under the strict inequality in (8). Proposition 1 completes the proof.

For finite measures whose mass is distributed equally over source cells, (7) is directly a weighted rich-incidence count: it is the number, or conditional mass, of source cells meeting the indicated approximate-bisector condition, normalized by epsilon u^{s-1}. The threshold distribution in (8) is measured over actual retained source–pin pairs. It is not a bound on a source-only bisector pushforward, and not a bound obtained by replacing the two selected factors by independent angular marginals.

## 3. Why this can be weaker than quadratic collisions

The range beta<=1 is allowed in (6) and (8). Such a tail need not have a uniformly bounded first moment, while every gamma<beta moment is bounded. A simple exact radial-law example shows that this distinction is substantive at the measure-theoretic level.

Fix 0<beta<=1 and let a=1/(1+beta). On (0,1), take the probability density

$$
f(t)=(1-a)t^{-a}.
$$

It is in L^{1+gamma} for every gamma<beta, but not in L^2. For lambda=f(t)dt,

$$
H_\varepsilon(r)
=\varepsilon^{-1}\lambda([r-\varepsilon,r+\varepsilon])
\le C(r+\varepsilon)^{-a},
$$

and therefore

$$
\lambda\{H_\varepsilon>t\}\le C t^{-(1-a)/a}
=Ct^{-\beta}
\quad(t\ge1)
$$

uniformly in epsilon. Nevertheless the first crowding moment diverges as epsilon tends to zero: on r>=2epsilon it dominates a constant times the integral of r^{-2a}. For beta=1 the divergence is logarithmic; for beta<1 it is a power. This example verifies strictness of the fractional crowding condition relative to quadratic collision control. It is not asserted to be a new planar configuration satisfying the dimensional hypotheses of the Falconer problem.

## 4. The exact missing estimate

The hypotheses (6) or (8) have not been proved from dimensions. They identify the additional geometric input, including its normalization and the tolerated loss at source separation u. They avoid the disproved source-only assertion, because the measure of rich incidences retains both factors from one fixed positive source–pin kernel.

For comparison, the estimates already available do not supply (8). Applied on one source annulus, angular domination gives only

$$
\int Q_{\varepsilon,u}\,d\Pi_A
\le C A\left(1+\frac{u^2}{\varepsilon}\right),
\tag{12}
$$

up to fixed changes in the collision-width constant. The near-bisector condition in (7) implies a distance collision with width at most (C_0/a_0)epsilon, so the earlier angular calculation applies with this constant enlargement. If the pin measure is also t-Frostman with 1<t<=2, a direct covering of the bisector strip gives only

$$
\int Q_{\varepsilon,u}\,d\Pi_A
\le C\left(\frac u\varepsilon\right)^{2-t}.
\tag{13}
$$

For (13), the strip width is comparable to epsilon/u, its bounded-length portion has pin mass at most C(epsilon/u)^{t-1}, and the source annulus has mass at most Cu^s. Dividing by epsilon u^{s-1} gives the stated exponent. In the far range u>r_epsilon>=epsilon^alpha with alpha<1, the strip width is small for sufficiently small epsilon; finitely many initial scales can be absorbed in the constant.

For each fixed positive u, both available bounds can diverge as epsilon tends to zero when t<2. Markov's inequality merely transfers that resolution loss to a rich-incidence tail. Taking fractional moments of these bounds does not remove it. A new incidence argument must therefore control how high near-bisector crowding is distributed among retained source–pin pairs; it cannot consist only of interpolating (12) or (13).

The explicit numerical target furnished by Proposition 2 is a tail exponent beta and a source-scale loss kappa with kappa<beta(s-1). No relation between these two incidence exponents and Hausdorff/packing dimensions is supplied in this note. The separate low-crowding compactness criterion being developed in parallel can require even less, because positive distance length needs only a positive absolutely continuous component, not L^{1+gamma} regularity of the full selected law.
