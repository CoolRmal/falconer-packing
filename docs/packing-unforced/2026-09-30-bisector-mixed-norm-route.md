# Source–pin geometry beyond the scale profile: a bisector mixed-norm target

Date: 2026-09-30. This is a bounded literature audit and a proved conditional implication. It does not improve the dimension-only threshold proved in the manuscript.

## 1. What the recent primary results actually supply

- [Orponen–Shmerkin–Wang, Theorem 3.20](https://arxiv.org/html/2209.00348) gives thin tubes for every exponent strictly below the minimum of one and the sum of the two measure dimensions minus one. Thin tubes mean a positive pair restriction with a power upper bound on the mass of tubes through the relevant center. For both dimensions above one, this is angular Frostman control below exponent one. Our existing radial-density selection supplies bounded angular densities on a retained positive pair set, so this result alone is not a stronger input in the present range. It does not state absolute continuity for scalar distances.

- [Ren, *Discretized Radial Projections in R^d*](https://arxiv.org/abs/2309.04097) extends a radial projection and incidence mechanism, including quasi-product tube incidences. The stated output is a discretized projection theorem, not a positive-Lebesgue-distance conclusion. [Csörnyei–Stull](https://arxiv.org/abs/2508.18228) improve the lower bound for the Hausdorff dimension of radial projections to the minimum of one, the source dimension, and half the sum of source and center dimensions. Again, neither dimension one nor angular projection size implies positive length for scalar distances.

- [Liu, v3, Theorem 1.1 and Proposition 1.2](https://arxiv.org/html/2603.15328v3) give a positive-length result with regular pins, and a multiscale weighted extension inequality with a quadratic restriction on neighboring scales. The theorem assumes the pin set has equal Hausdorff and packing dimensions. The scalar profile optimization already uses that multiscale mechanism; merely optimizing its sequence of scales again cannot bypass the sharp profile witnesses.

- [Green–Harris–Ou–Ren–Tammen](https://arxiv.org/html/2502.10686) obtain new circular Furstenberg incidence estimates through local smoothing and trilinear cone restriction. Their main consequences are lower bounds for Hausdorff dimension. A conversion to a uniform integral bound for the actual pinned densities requires more than their stated dimension conclusion.

- [Borges–Ou–Pasquariello, Theorem 1.1](https://arxiv.org/html/2607.10574) use weighted paraboloid restriction for positive-measure pinned configurations. Substitution of ambient dimension two and one distance gives the threshold seven fifths, which is above five quarters.

- [Orponen, *A note on higher integrability of projections*](https://arxiv.org/abs/2509.06474) constructs a t-Frostman measure all of whose orthogonal projections fail to lie in any prescribed Lp space with p greater than two divided by two minus t. This rules out an unrestricted upgrade of the ordinary projection integrability exponent beyond its Sobolev value.

This scan supplies no stronger ready-made source–pin estimate that applies to all sets just outside the current dimension curve. The negative conclusion is limited to these inspected results.

## 2. A geometric quantity that is absent from the scale profile

Let $$\mu,\nu$$ be compactly supported positive measures on the plane, with

$$
I_1(\mu)<\infty,\qquad I_\tau(\nu)<\infty,\qquad 1<\tau<2.
$$

For distinct source points define

$$
\theta(x,x')=\frac{x-x'}{|x-x'|},\qquad
c(x,x')=\frac{|x|^2-|x'|^2}{2|x-x'|}.
$$

The perpendicular bisector is the line with equation $$y\cdot\theta=c$$. Define a finite measure on oriented line space by

$$
\mathcal B_\mu
=(\theta,c)_*\left(|x-x'|^{-1}\,d\mu(x)d\mu(x')\right).
\tag{1}
$$

Its total mass is $$I_1(\mu)$$. Unlike the one-dimensional branching profile, (1) remembers how pairs of points determine reflections in physical space.

The concrete new target is the density estimate

$$
\mathcal B_\mu=b_\mu(\theta,c)\,d\theta\,dc,\qquad
\|b_\mu\|_{L^2_\theta L^{2/\tau}_c}<\infty.
\tag{2}
$$

This is a hypothesis, not a claim about arbitrary Frostman measures. No novelty is claimed for using bisectors in distance problems; the point here is the explicit continuum mixed norm and the implication below.

## 3. Conditional theorem, with exact exponents

**Proposition.** Under (1)–(2), the full joint distance law has an L2 density relative to the pin measure times one-dimensional Lebesgue measure. More precisely, writing

$$
\eta_y=(x\mapsto|x-y|)_*\mu,
$$

one has

$$
\int\|\eta_y\|_{L^2(\mathbb R)}^2\,d\nu(y)
\le C_{\tau,K}\,
\bigl(\nu(\mathbb R^2)^2+I_\tau(\nu)\bigr)^{1/2}
\|b_\mu\|_{L^2_\theta L^{2/\tau}_c}.
\tag{3}
$$

The constant depends on a compact set K containing both supports. In particular, if mu has positive mass, its pinned distance set has positive length for nu-almost every pin.

**Proof.** For almost every angle let

$$
v_\theta(c)\,dc=(y\mapsto y\cdot\theta)_*\nu.
$$

The Fourier projection identity and polar coordinates give

$$
\int_{S^1}\|v_\theta\|_{H^{(\tau-1)/2}(\mathbb R)}^2\,d\theta
\le C_\tau\bigl(\nu(\mathbb R^2)^2+I_\tau(\nu)\bigr).
\tag{4}
$$

Indeed the high-frequency part is a constant times the integral of the squared Fourier transform of nu against the radial weight with exponent tau minus two; the bounded-frequency part is controlled by the mass. The one-dimensional Sobolev embedding, with

$$
q=\frac{2}{2-\tau},\qquad q'=\frac{2}{\tau},
$$

and boundedness of the one-dimensional Hardy–Littlewood maximal operator on Lq imply

$$
\|M v_\theta\|_{L^2_\theta L^q_c}
\le C_\tau\bigl(\nu(\mathbb R^2)^2+I_\tau(\nu)\bigr)^{1/2}.
\tag{5}
$$

Choose a nonnegative compactly supported smooth mollifier of integral one on the real line. The square of the L2 norm of its epsilon-smoothing of eta is bounded by a constant times

$$
\varepsilon^{-1}
\iint
\nu\{y:\bigl||x-y|-|x'-y|\bigr|\le C\varepsilon\}
\,d\mu(x)d\mu(x').
\tag{6}
$$

All source–pin distances are bounded above by a fixed constant. The exact squared-distance identity

$$
|x-y|^2-|x'-y|^2
=2|x-x'|\bigl(c(x,x')-\theta(x,x')\cdot y\bigr)
\tag{7}
$$

therefore places the pins counted in (6) in a band of width at most a constant times epsilon divided by the source separation. For almost every theta,

$$
\varepsilon^{-1}
\nu\{|y\cdot\theta-c|\le C_K\varepsilon/|x-x'|\}
\le C_K |x-x'|^{-1}M v_\theta(c).
\tag{8}
$$

The exceptional set of angles has zero mass for the weighted source pair measure, because (2) implies absolute continuity of its line-space pushforward. Thus (6), (8), and the definition of the bisector measure give the uniform upper bound

$$
C_K\int b_\mu(\theta,c)M v_\theta(c)\,dc\,d\theta.
\tag{9}
$$

Apply Holder with exponents q-prime and q in c, and then Cauchy–Schwarz in theta. Equation (5) proves the asserted bound for every mollification. Weak compactness in the L2 space over nu times Lebesgue measure, followed by testing against continuous compactly supported functions, identifies the weak limit with the actual joint distance law. Disintegration gives (3).

No separation between the two supports is needed in this particular argument; only their boundedness was used in (7). The finite first energy excludes a source diagonal atom.

## 4. Reflection form and a robust finite-resolution test

For a smooth compactly supported source density f, the density in (2) has the especially simple formula

$$
b_\mu(\theta,c)=\int_{\mathbb R^2}f(x)f(\mathcal R_{\theta,c}x)\,dx,
\qquad
\mathcal R_{\theta,c}x=x+2(c-x\cdot\theta)\theta.
\tag{10}
$$

To verify it, write the pair as midpoint plus or minus half a difference vector:

$$
x=z+\tfrac r2\theta,\qquad x'=z-\tfrac r2\theta,\qquad
z=c\theta+u\theta^\perp,\qquad r>0.
$$

The pair Jacobian is r, which cancels the reciprocal separation in (1). Integration in u and r then gives (10), since the product is invariant under reflection and integration over the positive half-space is half its integral over the whole plane.

Consequently a directly testable sufficient missing estimate is

$$
\sup_{0<\delta<1}
\left\|
\int f_\delta(x)f_\delta(\mathcal R_{\theta,c}x)\,dx
\right\|_{L^2_\theta L^{2/\tau}_c}<\infty,
\qquad f_\delta=\mu*\psi_\delta.
\tag{11}
$$

Here psi is a fixed nonnegative compactly supported smooth planar mollifier. If (11) holds, the reflexivity of the mixed-norm space yields a weakly convergent subsequence. Its limit represents (1): away from the source diagonal this follows from weak convergence of the smoothed measures; the near-diagonal contribution is uniformly negligible if, for example, mu is s-Frostman with s greater than one, because the weighted near-diagonal mass is bounded by a constant times the separation cutoff to the power s minus one. Thus (11) implies (2).

For a dimension example outside the manuscript's proved curve, take

$$
d=\frac{23}{20},\qquad D=\frac32,\qquad
\tau=\frac98<d.
$$

The present high branch has

$$
B_H(23/20)=\frac{10}{7}<\frac32.
$$

At this point the exact missing norm is

$$
L^2_\theta L^{16/9}_c,
$$

paired with the pin projection norm

$$
L^2_\theta L^{16/7}_c.
$$

If every such set admitted a positive-mass Frostman restriction satisfying (11) with these exponents, Proposition (3) would cover this point beyond the existing curve. That geometric restriction theorem is not proved here, and no dimension-only implication is being asserted.

## 5. Why existing incidence results do not yet prove the missing estimate

The Euclidean result of [Lund–Petridis, Theorem 2](https://arxiv.org/html/1810.00765) bounds the number of exactly coincident bisectors of an N-point set by a constant times

$$
M N^2+N^{5/2}(\log N)^{1/2},
$$

where M is the maximum number of points on a line or circle. This is concrete evidence that reflection coincidences have additional geometric structure. It is not a bound for approximate bisector coincidences at arbitrary resolution, and it does not provide the mixed norm (11).

Even a schematic approximate L2 bound obtained just by transferring the term with exponent five halves would not be enough below four thirds. For N roughly delta to the negative s and separated source pairs, normalization in two-dimensional line space gives the error scale

$$
\delta^{-2}\frac{N^{5/2}}{N^4}
\asymp\delta^{3s/2-2}.
\tag{12}
$$

At s equal to 23/20 the exponent in (12) is minus 11/40. This is a calculation of the missing size of a power gain, not a discretized theorem. Any approximate incidence argument must also retain the unavoidable background term of size N to the fourth power times delta squared.

The mixed norm in (11) is weaker than the ordinary L2 line-space norm, but extracting this advantage requires control of how approximate reflection coincidences distribute jointly in angle and offset. Angular thin-tube bounds alone do not control the offset variable. Nor may an exact finite-point coincidence theorem be applied to near coincidences without a quantitative stability argument.

There is a further warning: (3) is a raw L2 conclusion. [Guth–Iosevich–Ou–Wang](https://arxiv.org/pdf/1808.09346v1) explicitly identify obstructions to raw L2 methods below four thirds; one cannot assert (11) for arbitrary Frostman measures in that range. A successful use would need an additional geometric dichotomy or a justified positive source restriction, not another estimate depending only on the old branching profile.

## 6. Bounded-task outcome

The literature scan did not yield a new unconditional dimension region. It did yield a precise alternative target: a mixed-norm bound for reflection autocorrelations of an actual positive source restriction, with explicit exponents and a complete implication to positive-length pinned distances. This target retains a source-pair geometry that the existing scale profile discards. Establishing it from Hausdorff and packing dimensions beyond the current curve remains the new missing estimate.
