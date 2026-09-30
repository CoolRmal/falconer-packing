# A local GIOW terminal step for the unforced profile iteration

30 September 2026. Analytic proof with an [independent selector audit](2026-09-30-local-terminal-selector-audit.md). This note derives a valid local replacement. The separate [profile comparison](2026-09-30-local-giow-profile-redundancy.md) proves that its optimization gives the existing chain cost exactly, so this construction does not improve the dimension threshold.

The deep input is the planar case of [Guth--Iosevich--Ou--Wang, arXiv version 1](https://arxiv.org/pdf/1808.09346v1), Theorem 4.2 / Corollary 4.3 at exponent six. Its use of a smoothed pin measure and the incidence cancellation is the same as the proof of Proposition 5.3, but the packet norm is bounded by a **local Lebesgue square function**, not by the final global Fourier energy. This distinction permits the older quadratic iteration to continue.

## 1. The local weighted packet estimate

Write r for a large frequency on a unit spatial region, and put rho=r^{-1/2}. Let F_theta have Fourier support in the constant enlargement of the canonical rectangle associated with a circle arc theta of angular length rho: tangential width rho^{-1}, normal width one. Rectangles have bounded overlap. Fixed finite changes of these constants are harmless.

Use a smooth transverse partition of unity eta_{theta,T} at scale rho and a common smooth spatial cutoff chi, equal to one on the pin region. Each

$$
f_T=\chi\eta_{\theta,T}F_\theta
$$

is a usual canonical packet. As in GIOW, its physical tube and frequency rectangle can be enlarged by r^{delta}; the resulting losses below are r^{O(delta)}. Smooth partitions may be chosen nonnegative with sum one, so their selected sums lie in [0,1]. They have bounded overlap, or rapidly decreasing tails with bounded overlap of their majorants. All localization errors below are rapidly decreasing after the standard small-power enlargements. The global input norms and packet counts are assumed polynomially bounded; this is the case in the finite-profile application.

Let lambda be a positive measure of mass at most one. Assume its smoothing at radius r^{-1} has density bounded by D. Let W be the packets retained by the rule

$$
\lambda(C T)\le H\rho,
\qquad H\ge1,
\tag{1}
$$

where C T includes the packet localization enlargement and its adjacent rho-cubes. Then, allowing an arbitrary fixed small positive loss epsilon,

$$
\int\left|\sum_{T\in W}f_T\right|^2d\lambda
\lesssim_\epsilon r^\epsilon H^{2/3}D^{1/3}
\sum_\theta\int_{Q^+}|F_\theta|^2\,dx
+\operatorname{RapDec}(r).
\tag{2}
$$

Here Q^+ is the enlarged unit region used by chi. If its enlargement is a small power, the corresponding area and overlap factors are included in the displayed loss.

**Proof.** The standard local-constancy inequality at scale r^{-1} replaces lambda by its positive smoothing w(x)dx, up to the rapidly decreasing error. A slightly larger C in (1) ensures

$$
0\le w\le C D,\qquad \int_{C'T}w\le C H\rho+\operatorname{RapDec}(r).
\tag{3}
$$

The latter follows by separating the smoothing kernel into its mass inside the enlarged tube and its rapidly decreasing tail. The smoothing radius r^{-1} is smaller than the transverse packet scale rho. The standard enlargements can make that tail smaller than any prescribed inverse power.

Pigeonhole the packet sixth norms. The number of relevant classes is O(log r): discard packets whose norms are smaller than a sufficiently large inverse power, and use the polynomial upper bound for the remaining range. Fix one class containing W_0 packets. Partition the spatial region into rho-cubes and group cubes by a dyadic number M of incident packets. Let Y_M be the union of one such group. Counting incidences with weight w(q) gives

$$
M\,w(Y_M)\lesssim W_0 H\rho.
\tag{4}
$$

Indeed, every packet meeting q has q inside its enlarged tube, and summing w(q) first over the cubes met by a packet is at most C H rho by (3). Packets meeting only through rapidly decreasing tails are handled by the prescribed enlargements. No uniformity assumption on the individual cube masses is needed.

Hölder, the density bound, and refined decoupling yield

$$
\begin{aligned}
\int_{Y_M}|f|^2w
&\le \|f\|_{L^6(Y_M)}^2
       \left(\int_{Y_M}w^{3/2}\right)^{2/3}\\
&\lesssim r^\epsilon
       (M/W_0)^{2/3}
       \sum_{T\in W_0}\|f_T\|_6^2
       D^{1/3}w(Y_M)^{2/3}\\
&\lesssim r^\epsilon (H\rho)^{2/3}D^{1/3}
       \sum_{T\in W_0}\|f_T\|_6^2.
\end{aligned}
\tag{5}
$$

Thus the multiplicity and the mass of Y_M cancel exactly. Summing the finitely many multiplicity and amplitude classes costs only logarithms and the usual small-power losses.

A canonical frequency rectangle has area O(rho^{-1}). Bernstein therefore gives

$$
\|f_T\|_6^2\lesssim\rho^{-2/3}\|f_T\|_2^2,
\tag{6}
$$

again with the permitted small-power loss for microlocal tails. Finally,

$$
\sum_T\|f_T\|_2^2
\lesssim \sum_\theta\int_{Q^+}|F_\theta|^2.
\tag{7}
$$

This follows by bounded overlap of the spatial partition for each theta. The factors rho^{2/3} in (5) and rho^{-2/3} in (6) cancel. This proves (2).

A useful rigorous implementation of the tails is to start with nonnegative Schwartz transverse partitions having compact Fourier support, periodized to sum one, and a common band-limited Schwartz majorant bounded below by a positive constant on the pin region. In this alternative the packet sum equals that majorant times the desired extension; its lower bound controls the latter on the pins, rather than claiming the majorant is identically one. Enlarge the spatial tubes and parent by a small power, truncate the resulting negligible tails, and apply Corollary 4.3 in its usual weighted form. Alternatively one may use GIOW's compact spatial packet cutoffs and their essentially supported Fourier rectangles. Both have the same polynomial counts and arbitrary-order tail bounds. This is the ordinary microlocal localization used in that corollary; it is not an extra estimate for a new oscillatory phase.

## 2. The exact profile exponent

Fix a regularized component sigma and its profile f, and put g(k)=f(k)-k. Let R=2^N, choose a parent depth m, and let

$$
b=2^{-m},\qquad r=Rb=2^{N-m},\qquad
n=\frac{N+m}{2},\qquad
a=2^{-n}=\sqrt{b/R},\qquad
\rho=a/b=r^{-1/2}.
\tag{8}
$$

Round n to an admissible block-grid point when needed; the error is O(T), hence a fixed multiplicative constant. Assume m at most (1-zeta)N for a fixed zeta>0, so the local frequency is at least R^zeta and all localization losses can be made R^{epsilon} uniformly in m.

For an active parent P at depth m, use

$$
\lambda_P=\frac{\sigma|_{P^+}}{\sigma(P^+)}.
$$

The denominator is at least sigma(P), so the regular cube mass bounds imply

$$
\lambda_P(B(x,R^{-1}))
\lesssim_T R^{C\Gamma}2^{f(m)-f(N)}.
\tag{9}
$$

After rescaling P by b^{-1}, convolution at radius r^{-1} thus satisfies

$$
D_P\lesssim_T R^{C\Gamma}
2^{2(N-m)+f(m)-f(N)}
=R^{C\Gamma}2^{(N-m)+g(m)-g(N)}.
\tag{10}
$$

The truncated conditional energy at scale rho is bounded by

$$
J_{\lambda_P}(\rho)
\lesssim_T (N+1)R^{C\Gamma}2^{c_g(m,n)},
\qquad
c_g(m,n)=g(m)-\min_{m\le k\le n}g(k).
\tag{11}
$$

Choose H=R^{D_2h+C Gamma}2^{c_g(m,n)}, exactly as for an ordinary edge. Substituting (10) and this H into (2) produces the terminal multiplier

$$
R^{O(h+\Gamma)+\epsilon}
2^{\mathcal T_g(m)},\qquad
\mathcal T_g(m)
=\frac{2c_g(m,(N+m)/2)+(N-m)+g(m)-g(N)}3.
\tag{12}
$$

There is no initial loss from replacing the measure by a much larger first cube: (9) uses the actual terminal scale R^{-1}.

## 3. Pin-side packets and the source good function

Short **source** packets of dimensions a by b cannot replace the original standard source packets. Their angular aperture is rho=a/b, and their footprint after propagation to the separated source region has width rho, not a. The construction below never makes that replacement.

All angular ancestors, spatial cutoffs, local tube grids, mass marks, and coefficients in this section are chosen once using the shell parameter R. They are independent of the circular radius t as t ranges over the fixed annulus t comparable to R. At a particular t, the local frequency is tb, comparable to Rb by constants depending only on the fixed annular ratio; the same rectangles, with a fixed enlargement, meet the hypotheses of (2). In particular, (15) defines one source function G_{R,y} for the entire shell, as required by the pinned circular identity.

Fix a coarse spatial chain from depth m down to zero, with the old admissibility inequalities. Its marks are unions of whole original standard source-cap labels S of width delta_*=R^{-1/2}. For any parent P at depth m, all these inherited marks are constant on P. Let A_{P,S} in {0,1} record survival of the coarse marks. Partition the standard labels into nominal angular ancestors theta of width rho. Since rho at least delta_*, each theta groups whole S's. Define, at a fixed circle radius comparable to R,

$$
F_{P,\theta}
=\sum_{S\prec\theta}A_{P,S}F_S,
\tag{13}
$$

where F_S is the full standard-cap circular extension, with the same fixed smoothing as in the existing transfer. Hence F_{P,theta} is independent of y inside P and has the canonical local Fourier support required in Section 1.

Use local pin-side packets eta_{theta,T} F_{P,theta}; a packet is good precisely when its enlarged local tube satisfies (1) under lambda_P. Put

$$
c_{P,\theta}(y)=\sum_{T\text{ good}}\eta_{\theta,T}(y),
\qquad 0\le c_{P,\theta}(y)\le1.
\tag{14}
$$

If Schwartz partitions are used, the omitted distant tails are included in the harmless rapidly decreasing remainder. The alternative finite compact partition is exact on the parent. Define the pin-dependent source function by weighting the **original full standard cap source functions**:

$$
G_{R,y}(x)=\sum_S A_{P,S}c_{P,\theta(S)}(y)
\chi(x)(\psi_{R,S}\widehat\mu)^\vee(x),
\qquad y\in P.
\tag{15}
$$

The coefficients do not depend on the distance variable. Consequently they commute with the pinned pushforward for each fixed y, and they also commute with its circular-extension formula. On P, (15) therefore has circular extension equal, up to the existing source-cutoff error, to

$$
\sum_\theta c_{P,\theta}(y)F_{P,\theta}(y)
=\sum_{\theta,T\text{ good}}\eta_{\theta,T}(y)F_{P,\theta}(y).
\tag{16}
$$

Multiplying by the common parent cutoff gives the exact packet sum used in (2). These selectors do **not** multiply unrelated finer Fourier pieces after the local packet decomposition. They select whole local packets of a common parent function, which is the hypothesis required by refined decoupling.

For the discarded first norm, expand each full standard source cap in (15) into its **original unit-length source packets**. Every coefficient has magnitude at most one. A source-pin pair can contribute to at most R^{O(h)} such original packets: their directions must be within O(R^{-1/2+h}) of its connecting line. This bound is independent of the number of standard caps inside theta. Since delta_* at most rho and b rho=a, a bad local theta tube meeting the pin is contained in the standard enlarged heavy tube in the actual source-pin direction. The radial-projection deletion argument therefore gives

$$
\int\|(d_y)_*(P_R\mu-G_{R,y})\|_1\,d\sigma(y)
\lesssim R^{C h}
\left(L^{1-q}BR^\Gamma+
\sum_P\sigma(P^+)\frac{L}{H}J_{\lambda_P}(\rho)
+\text{coarse-chain bad masses}\right)
+\operatorname{RapDec}(R).
\tag{17}
$$

Choose L=R^{D_1h}, and then D_2 sufficiently larger than D_1, exactly as in the previous deletion proof. The right side decays as a fixed negative power. The common coefficient for all original S inside theta is essential here. Applying the old deletion proof to newly created short source packets would be invalid.

## 4. Compatibility with the subsequent quadratic iteration

After (2), the local selectors have completely disappeared. The parent energy is exactly, up to the prescribed enlargements,

$$
\mathcal E_m=
\sum_{P\text{ active at }m}\sigma(P^+)
\sum_{\theta:\,|\theta|=\rho}
\fint_{P^+}|F_{P,\theta}(y)|^2\,dy.
\tag{18}
$$

This is a **local** energy, not the global final circle energy. The old next inflation edge from m to a smaller depth decomposes each theta into angular descendants of width

$$
\delta_m=(Rb)^{-1}=\rho^2\le\rho.
$$

The exact inherited identity applies separately inside every initial parent label theta. All coarse marks in (13) were fixed before the local packet selection, and no coefficient c_{P,theta} remains on the right of (18). Thus the old selected-subset quadratic inflation lemma applies, with one factor H per coarse edge. At depth zero, use precisely the old final circle Cauchy--Schwarz estimate.

If the coarse chain has total cost Phi_g(m), the resulting full cost is

$$
\Phi_g(m)+\mathcal T_g(m)
=\Phi_g(m)+
\frac{2c_g(m,(N+m)/2)+(N-m)+g(m)-g(N)}3.
\tag{19}
$$

All conclusions are subject to the same small positive losses for the block grid, regularization, finite number of edges, and packet enlargements. Consequently a strict uniform cost below (s-1)N would imply the same summable shell estimate and absolute-continuity conclusion as before. This note does not prove such a uniform profile bound.

At m=0, the profile minimum is zero and g(0)=0. Formula (19) is (N-g(N))/3. With g(N) at least (s-1)N, the final shell exponent is at most (5-4s)N/3 plus small losses, agreeing with GIOW's five-quarters threshold. This is a useful normalization check.

## 5. Audit boundary

The mathematical estimate is (2), with its explicit density and tube-mass factors and local square-function right side. Equations (13)--(18) describe the packet-compatible reconstruction needed to use it; they avoid the incorrect short-source-packet argument. The independent selector audit checked this compatibility and the ordinary microlocal tails. The profile comparison and both independent profile audits establish the exact lack of improvement for this construction. No new universal dimension curve, endpoint assertion, or global optimality assertion is made here.
