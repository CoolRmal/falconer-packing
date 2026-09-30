# A fixed obstruction that survives every positive source restriction

Date: 2026-09-30. Status: complete argument checked in two internal audits; this is not external refereeing. This is an obstruction to a raw measure estimate, not a counterexample to positive-length pinned distances or to the established dimension criterion.

## 1. Statement and scope

There are a compact planar set K and a probability μ on K such that

$$
s=\dim_H K=\frac{11}{10},\qquad
u=\dim_P K=\overline{\dim}_{\rm B}K=\frac{13}{11},
\qquad u<2s-1.
$$

The measure μ is t-Frostman for every 0<t<s. Write T(x)=x+(0,3), and let ν be either μ itself or T_*μ. For every nonzero finite positive measure η supported on K, the joint distance law

$$
\mathcal D_{\eta,\nu}(A)
=\iint 1_A(y,|x-y|)\,d\eta(x)\,d\nu(y)
$$

does not have a density in weak L^q(ν×dt), for any q>9/8. In particular, it does not have an L² density. For ν=μ, the conclusion already holds after restricting the distance coordinate to the fixed interval [1/64,1/16]. Thus the full pin measure can live on the same set K, and the obstruction occurs away from zero distance. Separately, the full joint law with pins T_*η has no weak-L^q density for any q>9/8.

More generally, the L² and weak-L^q conclusions hold for source and pin measures η≤μ, ξ≤T_*μ whenever η and T^{-1}_*ξ have a common nonzero positive submeasure. We make no assertion for arbitrary independently selected, mutually singular source and pin restrictions. We also make no assertion about pin-dependent positive pair restrictions.

As a consequence, for every nonzero positive η supported on K with finite first energy, and every 1<τ<s, the weighted bisector measure of η cannot have a density in

$$
L^2(S^1;L^{2/\tau}(\mathbb R)).
$$

This includes every nonzero η≤μ and every Frostman source measure on K of exponent greater than one. Thus the source-only mixed-norm criterion in the bisector note cannot be deduced merely from the dimension and regularity bounds above, even after changing the source measure.

## 2. Exact block geometry

Put

$$
\alpha=\frac2{11},\qquad \beta=\frac1{20},
\qquad c=2^{-10}.
$$

For an integer L≥10, define

$$
\delta=2^{-40L},\quad
a=2^{-11L},\quad
w=2^{-20L},\quad
h=2^{-22L},\quad
m=2^{-2L}.
$$

Thus w²=δ, h=δ^{s/2}, m=δ^β, and a=δ^{β/α}. The symbols a and m in this note describe geometric scales and track mass, not the dimension/profile parameters in the main manuscript.

Take B=2048 and digit set {0,512,1024,1536}. The horizontal track centers are

$$
c_{\mathbf d}
=\frac18+\frac12\sum_{\ell=1}^{L}d_\ell B^{-\ell},
\qquad \mathbf d\in\{0,512,1024,1536\}^{L}.
$$

There are N_T=4^L=2^{2L}=m^{-1} centers. Their minimum separation is at least 256a. The normalized counting measure on the centers has, uniformly in L, interval mass at most C R^α for R≥a. They can be covered by at most C R^{-α} intervals of length R for R≥a. These facts follow directly by selecting the unique base-B generation with B^{-k-1}<R≤B^{-k}: a radius-R interval meets a bounded number of generation-k cylinders, each of mass 4^{-k}, and there are 4^k such cylinders. The constants absorb the fixed factor 1/2 in the center definition.

Set

$$
N_S=2^{22L-4},\qquad N_X=2^{20L-4}.
$$

For each track i, slat k=0,…,N_S−1, and horizontal index l=0,…,N_X−1, place a child square of side cδ centered at

$$
z_{i,k,l}
=\left(c_i+4\delta\left(l-\frac{N_X-1}{2}\right),
              \frac14+kh\right).
$$

All child squares lie strictly inside [0,1]². They are separated by at least 3δ. The horizontal extent of a track is at most w/4, and its vertical slats have spacing h. The number of children is

$$
M_L=N_TN_SN_X=2^{44L-8}=2^{-8}\delta^{-s}.
$$

Give each child equal probability M_L^{-1}. Every track has probability m, and each of its slats has probability m/N_S. Future descendants can be arbitrarily distributed inside each child square for all estimates below.

## 3. Uniform one-block estimates

For radii cδ≤R≤1, the normalized block measure obeys

$$
\mu_{\rm block}(B(x,R))\le C R^s,
\qquad
N(\operatorname{supp}\mu_{\rm block},R)\le C R^{-u},
\tag{1}
$$

with constants independent of L and of the distributions inside the child squares. Here and below N denotes the number of balls needed for a cover; changing between balls and squares only changes constants.

For δ≤R≤1, the horizontal mass bounds are R^α when R≥a, m when w≤R≤a, and mR/w when δ≤R≤w. The vertical mass bounds are R when R≥h and h when δ≤R≤h. Their products give

$$
\begin{array}{c|c|c}
\text{range}&\text{mass upper bound}&\text{cover upper bound}\\ \hline
a\le R\le1 & C R^{1+\alpha} & C R^{-1-\alpha}\\
w\le R\le a & C\delta^\beta R & C\delta^{-\beta}R^{-1}\\
h\le R\le w & C\delta^{\beta-1/2}R^2
  & C\delta^{1/2-\beta}R^{-2}\\
\delta\le R\le h & C\delta^{s-1}R
  & C\delta^{1-s}R^{-1}.
\end{array}
\tag{2}
$$

The mass bounds are at most CR^s. The cover bounds are at most CR^{-u}: in the middle two ranges the decisive identity is

$$
\frac{s}{2}(2-u)=1-\frac{s}{2}=\frac12-\beta,
\qquad u=3-\frac2s=\frac{13}{11}.
$$

For cδ≤R≤δ, a ball meets only a bounded number of child squares and each square can be covered by a bounded number of radius-R balls. Since c is fixed, (1) follows there too.

At the distinguished radius R=h, the more precise mass estimate is

$$
\mu_{\rm block}(B(x,h))\le C\delta^{3s/2-1}.
\tag{3}
$$

Indeed, the ball meets a bounded number of tracks and slats and O(h/δ) horizontal child squares, each of mass comparable to δ^s.

## 4. The fixed recursive measure and its dimensions

Choose integers

$$
L_j=10+j^2\left(1+\sum_{k<j}L_k\right).
\tag{4}
$$

At stage j insert the above L_j block, with no rotations, inside every stage-(j−1) square, using its affine coordinates. Each child is a similarity of ratio r_j=cδ_j. Let K be the resulting compact intersection, and μ the probability assigning equal conditional weight to each child. Write

$$
\lambda_j=\prod_{k\le j}r_k,\qquad
p_j=\prod_{k\le j}M_{L_k}^{-1},\qquad
P_j=p_j^{-1}.
$$

There are P_j stage-j squares, each of side λ_j and μ-mass p_j. They are separated by at least a fixed large multiple of λ_j. Consequently a ball of radius at most λ_j meets at most a bounded number of stage-j squares. This follows first for siblings from their separation at least 3δ_j before contraction by the parent size, and then for different parents by induction.

If λ_j≤r≤λ_{j−1}, apply (1) inside the bounded number of parents met by a ball:

$$
\mu(B(x,r))\le C p_{j-1}\lambda_{j-1}^{-s}r^s.
\tag{5}
$$

Since M_L^{-1}(cδ)^{-s}=2^8c^{-s} is a fixed constant, the coefficient p_{j−1}λ_{j−1}^{−s} grows at most exponentially in j. For any 0<t<s,

$$
p_{j-1}\lambda_{j-1}^{-s}r^{s-t}
\le (2^8c^{-s})^{j-1}\lambda_{j-1}^{s-t},
$$

which is uniformly bounded. Thus μ is t-Frostman for every 0<t<s, so dim_H K≥s. Conversely,

$$
\frac{\log P_j}{-\log\lambda_j}\longrightarrow s;
$$

the level-j square covers prove dim_H K≤s.

The covering part of (1) gives, for λ_j≤r≤λ_{j−1},

$$
N(K,r)\le C P_{j-1}(r/\lambda_{j-1})^{-u}.
$$

The products P_{j−1}λ_{j−1}^u are bounded, since

$$
M_{L_k}r_k^u=2^{-8}c^u\delta_k^{u-s}<1.
$$

Hence the upper box dimension, and therefore the packing dimension, are at most u.

For the reverse packing inequality put r_j^* = λ_{j−1}h_j. By (3),

$$
\sup_x\mu(B(x,r_j^*))\le
C p_{j-1}\delta_j^{3s/2-1}.
\tag{6}
$$

Every subset A⊂K of positive μ outer measure therefore satisfies

$$
N(A,r_j^*)\ge
\frac{\mu^*(A)}{C p_{j-1}\delta_j^{3s/2-1}}.
$$

Because L_j dominates the sum of earlier depths, taking logarithms proves

$$
\overline{\dim}_{\rm B}A\ge
\frac{3s/2-1}{s/2}=u.
$$

In every countable cover of K at least one member has positive μ outer measure. The countable-cover characterization of packing dimension now gives dim_P K≥u. This also proves the same upper box lower bound in every positive-measure piece.

## 5. The persistent joint collision lower bound

Fix a nonzero finite positive η supported on K, with M=η(K). Set T(x)=x+(0,3) and ν=T_*μ. For a fixed stage j, abbreviate λ=λ_{j−1}, p=p_{j−1}, and δ=δ_j, h=h_j, w=w_j, m=m_j.

Let Q range over stage-(j−1) parents, i over tracks, and k over slats. Put

$$
q_{Q,i,k}=\eta(\text{descendants in slat }(Q,i,k)),\quad
q_{Q,i}=\sum_k q_{Q,i,k},\quad
M_Q=\sum_i q_{Q,i}.
$$

Fix a pin y in the translated track T(Q,i). Any two source points x,x′ in the same source slat (Q,i,k) satisfy

$$
\big||x-y|-|x'-y|\big|
\le C\big(\lambda\delta+\lambda^2w^2\big)
\le C\lambda\delta.
\tag{7}
$$

Indeed their vertical coordinates differ by O(λδ), while each horizontal displacement from y is O(λw). The identity for the difference of squared distances gives (7), because the source and pin sets are separated by a fixed positive distance. The separation between corresponding parent copies is the global distance 3, not a distance proportional to λ; the factor λ² in the horizontal error is therefore correct and favorable.

Choose a nonnegative smooth compactly supported φ of integral one. Its autocorrelation is positive in a neighborhood of zero. With ε_j=C_0λδ and C_0 a sufficiently large fixed constant, (7) implies

$$
\int\left|\phi_{\varepsilon_j}*(d_y)_*\eta(t)\right|^2dt
\ge \frac{c}{\lambda\delta}\sum_k q_{Q,i,k}^2
\quad\text{for }y\in T(Q,i).
$$

Since ν(T(Q,i))=pm, and N_S^{-1}=16h, two Cauchy inequalities yield

$$
\begin{aligned}
\int\|\phi_{\varepsilon_j}*(d_y)_*\eta\|_2^2d\nu(y)
&\ge \frac{cpmh}{\lambda\delta}\sum_{Q,i}q_{Q,i}^2\\
&\ge \frac{cp m^2h}{\lambda\delta}\sum_Q M_Q^2\\
&\ge cM^2p^2\lambda^{-1}\delta^{3s/2-2}.
\end{aligned}
\tag{8}
$$

Here the numbers of tracks and parents are 1/m and 1/p. At s=11/10 the δ exponent is −7/20. More explicitly,

$$
\log_2\!\left(p_{j-1}^2\lambda_{j-1}^{-1}
\delta_j^{-7/20}\right)
=14L_j-48\sum_{k<j}L_k+26(j-1)\longrightarrow+\infty.
\tag{9}
$$

Thus (8) diverges along one fixed sequence of resolutions, for every positive η. An L² joint density would contradict convolution contraction.

For pins T_*η, the pin mass in the translated parent-track is q_{Q,i}; the analogous lower bound is

$$
\frac{ch}{\lambda\delta}\sum_{Q,i}q_{Q,i}^3
\ge c M^3p^2\lambda^{-1}\delta^{3s/2-2},
\tag{10}
$$

by Jensen over the 1/(pm) parent-tracks. This also diverges. If η and T^{-1}_*ξ have a common nonzero positive submeasure ζ, positivity permits restriction to the source ζ and pins T_*ζ. This proves the stated common-submeasure variant.

The calculations (8) and (10) actually require only a positive finite source supported on K; domination by μ is needed for the energy consequence below, not for these collision estimates.

## 6. Weak-Lq obstruction from joint support

For each pin y in T(Q,i), let S_j(y) be the union over source slats k of intervals of length Cλδ centered at the distance from y to the center of that source slat. Enlarge the fixed C if necessary. Equation (7), including the same estimate with the slat center in place of x′, shows that these intervals contain the distances from all source points in the corresponding parent-track. All centers and pieces are Borel, so

$$
S_j=\{(y,t):t\in S_j(y)\}
$$

is measurable. With ω=ν×dt,

$$
\omega(S_j)\le C\lambda N_S\delta
\le C\lambda\delta^{1-s/2},
\tag{11}
$$

and its joint distance mass obeys

$$
\mathcal D_{\eta,\nu}(S_j)\ge
\sum_{Q,i}\eta(Q,i)\nu(T(Q,i))=pmM.
\tag{12}
$$

For q>1 a nonnegative weak-L^q density F satisfies

$$
\int_A F\,d\omega
\le \frac{q}{q-1}\|F\|_{L^{q,\infty}(\omega)}
\omega(A)^{1-1/q}.
$$

Therefore such a density for the joint law would imply

$$
\|F\|_{L^{q,\infty}}
\ge c_q M p\lambda^{-(1-1/q)}
\delta^{\beta-(1-s/2)(1-1/q)}.
\tag{13}
$$

The δ exponent is negative precisely when

$$
q>\frac{2-s}{3-2s}=\frac98.
$$

For every fixed such q, (4) makes the right side tend to infinity: the negative multiple of log δ_j dominates all contributions from earlier stages. Thus there is no weak-L^q density in this range. No conclusion is claimed at q=9/8.

For pins T_*η, the base measure of S_j is at most CMλδ^{1-s/2}, while its joint distance mass is at least

$$
\sum_{Q,i}q_{Q,i}^2\ge M^2pm.
$$

The same exponent and conclusion follow. For arbitrary η,ξ with common submeasure ζ, one can equivalently apply the support lower bound from ζ and its translate; the support has measure at most Cξ(\mathbb R^2)λδ^{1-s/2} under ξ×dt. This proves the common-submeasure weak-L^q assertion without needing a change-of-base-measure assertion for Lorentz spaces.

## 7. The same-set full pin measure

We now prove the primary variant with ν=μ, away from zero distance. The first-stage number N_S is even. Define F:K→K by changing only the first-stage vertical slat digit k to k+N_S/2 modulo N_S, leaving the first track and horizontal-child indices, and all subsequent digits, unchanged. Unique coding makes this a Borel involution. Equal weights show F_*μ=μ.

On each first-stage child, F is an exact vertical translation by either +(0,1/32) or −(0,1/32), since

$$
\frac{N_Sh_1}{2}=\frac1{32}.
\tag{14}
$$

For every j≥2, it maps each stage-(j−1) parent Q onto another parent F(Q) by that same translation, preserving all relative track, slat, and child geometry. In particular μ(F(Q,i))=pm.

For y∈F(Q,i) and x,x′ in source slat (Q,i,k), the proof of (7) applies without change, now using the fixed separation 1/32 instead of 3. Indeed λ≤λ_1 is far smaller than 1/64, and

$$
\left||x-y|-\frac1{32}\right|\le\sqrt2\,\lambda.
$$

Thus all these distances and their Cλδ neighborhoods lie in the fixed interval J=[1/64,1/16], and their oscillation is at most Cλδ.

For y∈F(Q,i), form S_j(y) from the distances to all source slat centers in Q,i, exactly as in Section 6. The parent correspondence is a bijection, so

$$
S_j\subset K\times J,\qquad
(\mu\times dt)(S_j)\le C\lambda\delta^{1-s/2},
\qquad
\mathcal D_{\eta,\mu}(S_j)\ge pmM.
\tag{15}
$$

The same weak-L^q support inequality gives (13), even if only the restriction of the joint law to K×J were assumed to possess the density. This proves the same-set assertion away from the radial diagonal. The L² collision argument (8) likewise applies with F(Q,i) instead of T(Q,i), giving the same divergent lower bound.

This proof does not claim that an arbitrary independently chosen pin restriction retains the requisite matching parent-track masses. The translated matched-pin statement remains separately proved in Sections 5–6.

## 8. Consequence for the bisector mixed-norm target

Fix 1<τ<s and a nonzero source η supported on K with finite first energy. Choose t with τ<t<s. By the Frostman estimate, μ and ν have finite τ-energy. If the weighted bisector measure of η had a density in L²_angle L^{2/τ}_offset, the established bisector criterion would imply that the joint distance law for source η and full pins ν has an L² density. This contradicts (8). The finite-first-energy hypothesis holds in particular for every η≤μ, and for every Frostman source on K of exponent greater than one.

Thus the previously proposed mixed norm is not a regularity consequence of these dimensions, even after an arbitrary positive source restriction. The obstruction does not contradict an L^p density for p sufficiently close to one, absolute continuity, positive-length pinned distances, or a genuinely pin-dependent pair restriction. It identifies precisely a limitation of improving the argument solely by selecting a positive source measure and asking for this raw L² bisector estimate.
