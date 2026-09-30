# Positive affine comparison at the exact Frostman exponent

Date: 2026-09-30.

This note proves two refinements of the positive coherent-linearization argument: a frequency-band proof removes the logarithmic loss at the source Frostman exponent, and a nonconsecutive comparison preserves the weighted occupied-cell count. Before applying the Frostman estimate, the proof gives an exact positive energy kernel at the curvature scale. These are convergence criteria for the actual positive joint distance law, not signed approximations. The manuscript version is `output/pdf/packing-unforced-band-comparison.tex`.

## 1. Setup and conclusions

Let mu and nu be compactly supported probability measures in the plane with positively separated supports. Assume mu is s-Frostman for a fixed exponent strictly between one and two. Assume the radial pin laws satisfy, for mu-almost every x,

$$
(\Theta_x)_*\nu=\rho_x\sigma,
\qquad \Theta_x(y)=\frac{x-y}{|x-y|},
\qquad B=\int\|\rho_x\|_q^q\,d\mu(x)<\infty,
\qquad q>1.
\tag{1}
$$

Here sigma is normalized arclength. The radial projection theorem supplies this input when both the source and pin Frostman exponents exceed one. The argument below only uses the explicit data in (1).

For each positive-mass dyadic cell Q, let its mass be p_Q and let mu_Q be its normalized restriction. Fix once and for all a center x_Q in Q at which the angular density exists and

$$
F_Q:=\|\rho_{x_Q}\|_q^q
\le\frac2{p_Q}\int_Q\|\rho_x\|_q^q\,d\mu(x).
\tag{2}
$$

Thus the sum of p_Q F_Q over any level is at most 2B. Define

$$
L_Q(x,y)=\Theta_{x_Q}(y)\cdot(x-y).
\tag{3}
$$

At level n these maps push the original positive pair law to a nonnegative joint density f_n relative to nu times Lebesgue measure. Projection densities exist because every mu_Q has finite first energy and each chosen radial pin law is absolutely continuous. Countably many cells give a common full-measure pin set and jointly measurable densities. Every f_n has mass one, and

$$
|L_{Q_n(x)}(x,y)-|x-y||\le C2^{-2n}.
\tag{4}
$$

For an arbitrary pair of sufficiently large integers n<m, put

$$
\mathcal N_m=\left(\sum_{Q\text{ at level }m}\sqrt{p_Q}\right)^2,
\qquad
Z_{n,m}=2^{-m-2n(s-1)}\mathcal N_m.
\tag{5}
$$

The principal comparison is

$$
\|f_m-f_n\|_1\le C(AZ_{n,m})^{1/2}+CB A^{1-q}
\qquad(A\ge1).
\tag{6}
$$

There is no requirement that m be at most twice n. Constants depend on the fixed geometry, separation, s, q and the original Frostman constant, not on n, m, A or an individual cell mass. Cauchy–Schwarz gives the familiar count bound

$$
\mathcal N_m\le N_m.
\tag{7}
$$

For a strictly increasing sequence of levels, write

$$
\eta_q=\frac{q-1}{2q-1}.
$$

Then

$$
\sum_j Z_{n_j,n_{j+1}}^{\eta_q}<\infty
\quad\Longrightarrow\quad
(d_y)_*\mu\ll\mathcal L^1
\quad\text{for nu-almost every }y.
\tag{8}
$$

In particular the consecutive-level criterion is

$$
\sum_n\left[2^{-n(2s-1)}N_{n+1}\right]^{\eta_q}<\infty.
\tag{9}
$$

This removes the factor n from the earlier variable-Sobolev-exponent criterion. A count upper bound by C times the critical exponential times n to power minus a now suffices when a is greater than 1/eta_q. The earlier proof required a greater than 1+1/eta_q.

## 2. The elementary band lemma

Let lambda be a probability supported in a ball of radius C_0 rho about the origin, with Frostman constant K and exponent s. Write F(theta) for its scalar projection density. Let kappa be any finite positive measure on a parameter space carrying measurable angles theta and phi and a real shift v. Assume both angular marginals are bounded by A sigma and

$$
d(\theta,\phi)\le\omega,
\qquad |v|\le v_0.
$$

The claim is

$$
\int\|F(\theta)(\cdot-v)-F(\phi)\|_2^2\,d\kappa
\le C_{s,C_0}AK
\bigl[(\rho\omega)^{s-1}+v_0^{s-1}\bigr].
\tag{10}
$$

All couplings among the angles and the shift are allowed.

### Gaussian energy bounds

For R positive, Gaussian Fourier inversion gives

$$
E_R(\lambda):=\int e^{-|\xi|^2/R^2}|\widehat\lambda(\xi)|^2\,d\xi
=cR^2\iint e^{-c'R^2|x-x'|^2}\,d\lambda(x)d\lambda(x')
\le C_s K R^{2-s}.
\tag{11}
$$

The inequality follows by dyadic spatial annuli of radius at least R inverse. For the signed coordinate measures, the same identity and positivity of the spatial Gaussian kernel give

$$
\int e^{-|\xi|^2/R^2}|\widehat{x_k\lambda}(\xi)|^2\,d\xi
\le C_{C_0}\rho^2 E_R(\lambda)
\le C_{s,C_0}K\rho^2R^{2-s}.
\tag{12}
$$

The bound uses the absolute upper bound for x_k x'_k inside the spatial double integral. It does not assume a corresponding inequality for sharp annular Fourier energies, which need not hold.

### Scalar frequency bands and coupled angles

Choose even smooth multipliers psi_R supported where the absolute scalar frequency is comparable to dyadic R, with bounded overlap and sum of their squares equal to one off zero. Let

$$
U_R(\theta)=\mathcal F^{-1}_\tau
\bigl[\psi_R(\tau)\widehat\lambda(\tau\theta)\bigr].
$$

The maps U_R are smooth as functions from the circle to the Hilbert space L2 of the scalar variable. Polar coordinates and (11)–(12) imply

$$
\int\|U_R(\theta)\|_2^2\,d\sigma(\theta)
\le CK R^{1-s},
\qquad
\int\|\partial_\theta U_R(\theta)\|_2^2\,d\sigma(\theta)
\le CK\rho^2R^{3-s}.
\tag{13}
$$

The derivative of the Fourier restriction is a bounded angular linear combination of tau times the Fourier transforms of the coordinate measures. For two angles separated by at most omega, the fundamental theorem of calculus and Cauchy–Schwarz give

$$
\|U_R(\theta)-U_R(\phi)\|_2^2
\le\omega\int_{d(z,\theta)\le\omega}
                 \|\partial_zU_R(z)\|_2^2\,dz.
\tag{14}
$$

Integrating the first angular marginal and applying Fubini bounds this by C A omega squared times the second quantity in (13). Using both marginal bounds in the trivial squared-difference estimate gives the undifferentiated alternative. Hence

$$
\int\|U_R(\theta)-U_R(\phi)\|_2^2\,d\kappa
\le CAK\min\{1,(\rho\omega R)^2\}R^{1-s}.
\tag{15}
$$

No angular maximal theorem and no pairwise exceptional-set assertion are required: every band function is smooth, and the complete projection densities are evaluated only under absolutely continuous angular marginals.

### Shifts and summation

The scalar Fourier multiplier for translation has squared modulus at most C times the minimum of one and (v_0 R) squared on the band. Thus

$$
\int\|U_R(\theta)(\cdot-v)-U_R(\theta)\|_2^2\,d\kappa
\le CAK\min\{1,(v_0R)^2\}R^{1-s}.
\tag{16}
$$

This estimate is valid before integrating over the arbitrary parameter-dependent shift. For each parameter the scalar-frequency frame identity expresses the squared norm of the complete difference as the sum of its band squared norms. Translation by a parameter-dependent amount preserves these scalar band supports. Therefore Tonelli and the squared triangle inequality reduce (10) to

$$
\sum_{R\in2^{\mathbb Z}}\min\{1,(\delta R)^2\}R^{1-s}
\le C_s\delta^{s-1}.
\tag{17}
$$

Split at R equal to delta inverse. The low-frequency exponent is 3-s, which is positive, and the high-frequency exponent is 1-s, which is negative. Both sums are geometric. This proves (10) without a critical s-energy assumption and without a logarithm.

## 3. Nonconsecutive positive affine maps

Fix n<m and write r=2 to power minus n and h=2 to power minus m. Let Q be a level-m cell with ancestor P at level n. Recenter mu_Q at b=x_Q. Its support radius is at most C h and its Frostman constant at most the original constant divided by p_Q. The two angular directions are theta=Theta_{x_P}(y) and phi=Theta_b(y). Their separation is at most C r. The constant terms of the two affine maps differ by

$$
v(y)=\theta\cdot(b-y)-|b-y|,
\qquad
|v(y)|=|b-y|\,|\theta\cdot\phi-1|\le Cr^2.
\tag{18}
$$

Keep pins for which the two selected radial densities are at most A. Both angular marginals on retained pins are bounded by A sigma; the discarded pin mass is at most A to power 1-q times F_P+F_Q. Applying (10) yields a retained integrated squared L2 difference at most

$$
\frac{CA}{p_Q}\bigl[(hr)^{s-1}+r^{2s-2}\bigr]
\le\frac{CA}{p_Q}r^{2s-2}.
\tag{19}
$$

Each conditional affine density is supported on an interval of length C h. The union of its two supports has length at most 2C h, even when the intervals are separated by a gap much larger than h. This is why no upper restriction on m in terms of n is needed. Cauchy–Schwarz on this union, followed by Cauchy–Schwarz over the retained pins, converts (19) into

$$
CA^{1/2}h^{1/2}r^{s-1}p_Q^{-1/2}.
\tag{20}
$$

Multiply by p_Q and sum the descendants. This preserves the weighted count in (5). On discarded pins each difference has L1 norm at most two. Both sums of the selected radial bounds are at most 2B, because the descendant weights over an ancestor add to its mass. This proves (6).

Optimize (6), after enlarging B to at least one, with

$$
A=(B/\sqrt Z)^{1/(q-1/2)}.
$$

For small Z the resulting bound is C times B to power 1/(2q-1) times Z to power eta_q. Summability in (8) makes the selected positive densities Cauchy in L1. Their limit has mass one. Uniform approximation (4) identifies its joint measure with the raw distance law, and disintegration proves almost-everywhere pinned absolute continuity.

## 4. The exact curvature-scale kernel

For a positive measure of finite first energy, define

$$
J_\delta(\lambda)
=\iint k_\delta(x-x')\,d\lambda(x)d\lambda(x'),
\qquad
k_\delta(z)=\min\{|z|^{-1},\delta^2|z|^{-3}\}.
\tag{21}
$$

The kernel is infinite on the diagonal, whose product mass is zero when the first energy is finite. Before inserting the Frostman bounds, (13) has respective right sides C R inverse E_{cR}(lambda) and C rho squared R E_{cR}(lambda). Consequently the band calculation uses

$$
\sum_{R\in2^{\mathbb Z}}
\min\{1,(\delta R)^2\}R^{-1}E_{cR}(\lambda)
\asymp_c J_\delta(\lambda).
\tag{22}
$$

To verify this, use the positive Gaussian spatial identity and Tonelli. The summed spatial kernel is a constant multiple of

$$
\sum_{R\in2^{\mathbb Z}}R\min\{1,(\delta R)^2\}
                                     e^{-c_cR^2|z|^2}.
$$

For absolute z at most delta, discard the minimum and sum to bound the kernel by C divided by absolute z. For absolute z greater than delta, replace the minimum by delta squared R squared and sum to obtain C delta squared divided by absolute z cubed. Keeping one dyadic R comparable to the reciprocal of absolute z gives the matching lower bound in both cases. This proves (22).

Thus the general band comparison (10) has the exact alternative right side

$$
CA\bigl[J_{\rho\omega}(\lambda)+J_{v_0}(\lambda)\bigr].
\tag{23}
$$

In the nonconsecutive application, both scale parameters are bounded by C r squared. Monotonicity in delta and the elementary inequality J_{C delta} at most max(1,C squared) times J_delta therefore show that (6) holds with Z replaced by

$$
W_{n,m}
=2^{-m}\left[
\sum_{Q\text{ at level }m}p_Q
                 J_{2^{-2n}}(\mu_Q)^{1/2}\right]^2.
\tag{24}
$$

With finite first energy of the original source and the fixed radial data (1), summability of these W coefficients to power eta_q implies the same raw pinned absolute continuity. No Frostman estimate is needed for this exact-energy form. For an s-Frostman source,

$$
J_\delta(\mu_Q)\le \frac{C_sC_\mu}{p_Q}\delta^{s-1},
\tag{25}
$$

by splitting the positive kernel at distance delta and summing dyadic spatial annuli. Hence W is at most C Z, recovering (5).

The exact kernel retains the near-source pair contribution:

$$
J_\delta(\mu_Q)
\ge\delta^{-1}(\mu_Q\times\mu_Q)
                    \{|x-x'|\le\delta\}.
\tag{26}
$$

In particular the refined kernel does not discard concentrated source collisions at the curvature radius. An improvement of a dimension-only theorem requires a new estimate or a selection argument for these coefficients, not merely renaming the energy.

The exact coefficient is stable under a fixed positive source restriction. If mu prime is the normalized restriction of mu to a Borel set S of mass c>0, then

$$
p'_Q J_\delta(\mu'_Q)^{1/2}
=c^{-1}\left[\iint_{(Q\cap S)^2}
                     k_\delta(x-x')\,d\mu(x)d\mu(x')\right]^{1/2}
\le c^{-1}p_Q J_\delta(\mu_Q)^{1/2}.
\tag{27}
$$

Empty restricted cells contribute zero. Therefore the restricted W coefficient is at most c to power minus two times the original W coefficient, at every pair of levels. This follows from positivity of the spatial kernel and does not require any regularity of S. Similarly, a fixed normalized pin restriction preserves the radial exponent and changes its averaged bound only by the corresponding fixed mass factors. Consequently these exact-energy convergence hypotheses survive the positive restrictions needed for the usual countable separated-product localization. The statement here is stability of a given coefficient hypothesis, not an assertion that a restriction automatically acquires that hypothesis.

## 5. Scope and comparison with structured examples

The new proof improves the all-scale endpoint covering summability criterion by a logarithmic factor and permits exact weighted or curvature-energy tests on arbitrary selected levels. It does not by itself prove a bare packing/Hausdorff dimension equality. For homogeneous Moran examples with lower-count levels n<m satisfying N_m at most C times 2 to power d m, and an exact d-Frostman source, (5) gives

$$
Z_{n,m}\le C2^{-(d-1)(2n-m)}.
\tag{28}
$$

Thus the exact sufficient gap condition for these comparisons is summability of 2 to power minus (d-1) eta_q times (2n-m). A fixed proportional gap gives geometric summability; a logarithmic gap has a precise threshold. This sharpens the earlier fixed-Sobolev-exponent rate while leaving its proportional-gap threshold unchanged.

The separate sparse-Moran argument exploits (28) on a specific family of sets. A positive result for that family is not a proof that every set with those two dimensions satisfies the same selected-level condition. Conversely a failure of either sufficient coefficient bound is not a lower bound on the actual affine-density difference and is not a null-distance example.
