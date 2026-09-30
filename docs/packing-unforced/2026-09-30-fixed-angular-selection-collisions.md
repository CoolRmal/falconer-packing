# A fixed positive angular selection pays for near-source collisions

30 September 2026. This note proves a geometric estimate for actual positive source--pin restrictions. It is complementary to the signed packet argument and to the reflection mixed-norm target. No stronger dimension theorem is claimed: the far-source collision bound specified below remains unproved.

## 1. Standing hypotheses and one selection for all scales

Let $$\mu,\nu$$ be compactly supported planar probability measures with separated supports. Fix constants

$$
0<a_0\le |x-y|\le b_0<\infty
\quad(x\in\operatorname{supp}\mu,\ y\in\operatorname{supp}\nu).
$$

Assume $$\mu$$ is $$s$$-Frostman for some $$s>1$$:

$$
\mu(B(x,r))\le C_F r^s.
$$

Write $$\Theta_x(y)=(y-x)/|y-x|$$ and suppose that the radial pin projections have angular densities with a finite joint moment:

$$
(\Theta_x)_*\nu=\rho_x(\theta)\,d\theta
\quad\text{for }\mu\text{-almost every }x,
\qquad
B=\int\!\int_{S^1}\rho_x(\theta)^q\,d\theta\,d\mu(x)<\infty,
\qquad q>1.
\tag{1}
$$

The angular measure is ordinary arclength. When both measures have Frostman exponents greater than one, reducing to a common exponent and applying the averaged radial-projection theorem gives (1); see [Guth--Iosevich--Ou--Wang, Theorem 3.7](https://arxiv.org/html/1808.09346#S3). A jointly measurable density can be chosen as the Radon--Nikodym derivative of the law of $$\bigl(x,\Theta_x(y)\bigr)$$ relative to $$\mu\times d\theta$$.

Fix $$A\ge1$$, independently of the resolution, and define

$$
a_A(x,y)=\mathbf1_{\{\rho_x(\Theta_x(y))\le A\}},
\qquad
\eta_y^A(dx)=a_A(x,y)\,d\mu(x).
\tag{2}
$$

The null set of source points where the radial density was not specified may be assigned selection zero. These are positive measurable kernels dominated by the original source probability. Their total deleted mass is bounded by

$$
\begin{aligned}
\iint(1-a_A(x,y))\,d\mu(x)d\nu(y)
&=\int\!\int_{\{\rho_x>A\}}\rho_x\,d\theta\,d\mu(x)\\
&\le B A^{1-q}.
\end{aligned}
\tag{3}
$$

Thus any prescribed fixed loss less than one can be obtained by choosing a sufficiently large finite threshold. The same selected measure is used at every scale; its total loss does not tend to zero with the scale.

For each retained source point, the unnormalized selected pin measure

$$
\nu_x^A(dy)=a_A(x,y)\,d\nu(y)
$$

has the exact angular domination

$$
(\Theta_x)_*\nu_x^A
=\rho_x\mathbf1_{\{\rho_x\le A\}}\,d\theta
\le A\,d\theta.
\tag{4}
$$

This is stronger than merely requiring a subcritical angular Frostman exponent, and it is a statement about original positive pairs.

## 2. The close-source collision bound

For $$0<\varepsilon<r\le1$$, let

$$
\begin{aligned}
\mathcal C_{\varepsilon,\le r}^A
=\varepsilon^{-1}\iiint
&\mathbf1_{\{|x-x'|\le r\}}
\mathbf1_{\{\bigl||x-y|-|x'-y|\bigr|\le\varepsilon\}}\\
&a_A(x,y)a_A(x',y)
\,d\mu(x)d\mu(x')d\nu(y).
\end{aligned}
\tag{5}
$$

**Proposition.** With constants depending only on the standing separation, diameter, Frostman data, and exponent,

$$
\boxed{\quad
\mathcal C_{\varepsilon,\le r}^A
\le C A\bigl(\varepsilon^{-1}r^{s+1}+r^{s-1}\bigr).
\quad}
\tag{6}
$$

**Proof.** First consider source pairs with separation $$u=|x-x'|\le\varepsilon$$. Their contribution is at most

$$
\varepsilon^{-1}\int\mu(B(x,\varepsilon))\,d\mu(x)
\le C_F\varepsilon^{s-1}.
\tag{7}
$$

This includes the entire smallest-separation region and avoids any division by zero. The source diagonal itself has zero product mass because the Frostman measure has no atoms.

For $$\varepsilon<u\le r$$, put $$e=(x'-x)/u$$, $$\ell=|y-x|$$, and $$\theta=\Theta_x(y)$$. The exact squared-distance relation is

$$
|x'-y|^2-|x-y|^2=u^2-2u\ell\,e\cdot\theta.
$$

A collision in (5) therefore implies

$$
|e\cdot\theta|
\le C_{a_0,b_0}\bigl(u+\varepsilon/u\bigr).
\tag{8}
$$

The corresponding set of directions has arclength at most

$$
C\min\{1,u+\varepsilon/u\}.
$$

Drop only the second selection factor, which is at most one, and apply (4) to the first. The selected pin mass for this source pair is consequently at most

$$
C A\bigl(u+\varepsilon/u\bigr).
\tag{9}
$$

Crucially, this step uses a common positive source--pin selection in both factors of (5). It does not replace an arbitrary source-pair selection by a nonexistent conditional source measure.

The Frostman bound gives

$$
\int_{0<|x-x'|\le r}|x-x'|\,d\mu(x')\le C_F r^{s+1},
$$

and, by decomposition into dyadic annuli,

$$
\int_{0<|x-x'|\le r}|x-x'|^{-1}\,d\mu(x')
\le C_s C_F r^{s-1}.
\tag{10}
$$

Integrating (9), dividing by the collision width, and adding (7) proves (6), since $$A\ge1$$ and $$\varepsilon^{s-1}\le r^{s-1}$$.

## 3. The power gain and its limits

Without angular selection, the direct source-mass bound is only

$$
\mathcal C_{\varepsilon,\le r}\lesssim\varepsilon^{-1}r^s.
$$

At the parabolic radius this may diverge. In contrast, (6) gives

$$
\mathcal C_{\varepsilon,\le\sqrt\varepsilon}^A
\le C A\varepsilon^{(s-1)/2}.
\tag{11}
$$

More generally, fix

$$
\frac1{s+1}<\alpha<1,
\qquad
\kappa=\min\{\alpha(s+1)-1,\alpha(s-1)\}>0.
$$

Then

$$
\mathcal C_{\varepsilon,\le\varepsilon^\alpha}^A
\le C A\varepsilon^\kappa.
\tag{12}
$$

Along dyadic resolutions these contributions are summable. Since $$s>1$$, the parameter may even satisfy $$\alpha<1/2$$; the discarded source-pair region then extends to radii larger than the parabolic radius. No optimality claim is made for the first term in (6) or for the resulting cutoff range.

The previously constructed raw off-cluster divergence came from interactions inside increasingly narrow source slats. Estimate (11) shows that this source of divergence is absent after the fixed angular truncation. This observation does not bound the remaining separated-source interactions, and it does not contradict the obstruction to vanishing-total-loss selections: the mass loss in (3) is fixed.

## 4. An exact remaining far-collision criterion

Use the same fixed threshold and both weights from (2). Define

$$
\begin{aligned}
\mathcal C_{\varepsilon,>r}^A
=\varepsilon^{-1}\iiint
&\mathbf1_{\{|x-x'|>r\}}
\mathbf1_{\{\bigl||x-y|-|x'-y|\bigr|\le\varepsilon\}}\\
&a_A(x,y)a_A(x',y)
\,d\mu(x)d\mu(x')d\nu(y).
\end{aligned}
\tag{13}
$$

**Conditional conclusion.** Choose $$A$$ such that

$$
m_0:=1-B A^{1-q}>0.
$$

Fix the parameter in (12). If, for a sequence tending to zero,

$$
\sup_j\mathcal C_{\varepsilon_j,>\varepsilon_j^\alpha}^A<\infty,
\tag{14}
$$

then the selected joint distance law

$$
\Lambda_A(dy,dt)=d\nu(y)\,(d_y)_*\eta_y^A(dt)
$$

has an $$L^2(d\nu\,dt)$$ density and total mass at least $$m_0$$. Consequently a positive-measure set of pins has positive-length distance sets from the source support.

To prove this, take a nonnegative smooth mollifier supported in $$[-1/2,1/2]$$ with integral one. The squared norm of a mollified selected radial law is bounded by the collision integral of width exactly $$\varepsilon$$, times a fixed mollifier constant. Split that integral into (5) and (13); use (12) and (14). Weak compactness of the resulting joint $$L^2$$ densities, and weak convergence of mollifications of the fixed positive measure, identify an $$L^2$$ density for $$\Lambda_A$$. Its mass is at least $$m_0$$ by (3).

If the squared joint norm is at most $$M$$, a quantitative version gives a set of pins of measure at least $$m_0/4$$ for which

$$
|\Delta_y(\operatorname{supp}\mu)|\ge\frac{m_0^3}{16M}.
$$

Indeed, the set of pins with retained source mass at least $$m_0/2$$ has measure at least $$m_0/2$$. The pins whose squared radial norm exceeds $$4M/m_0$$ have measure at most $$m_0/4$$. On the difference, Cauchy--Schwarz gives the displayed length bound.

The geometric task is specifically (14) for an actual fixed positive angular restriction, with source separation exceeding the cutoff in (12). It is not a bound for unrestricted raw collisions, and it is not a signed Haar-child comparison. Angular domination alone gives only an angular band of width comparable to the source separation; to obtain (14), one must also exploit how pin mass is distributed radially inside those angular bands. That radial--angular correlation is absent from both the scalar branching profile and the estimate proved here.

## 5. Independent check of the complementary bisector criterion

The proposition in [the bisector mixed-norm note](2026-09-30-bisector-mixed-norm-route.md) was independently checked. The average projection Sobolev order is $$(\tau-1)/2$$, giving dual offset exponents $$2/(2-\tau)$$ and $$2/\tau$$. The maximal-projection pairing and Cauchy--Schwarz in angle produce exactly its stated bound. The exceptional projection directions have zero bisector mass under the assumed mixed-norm density.

The reflection formula also has the stated normalization. With midpoint coordinate and separation length, the pair Jacobian cancels the reciprocal-separation weight. Substituting half the separation contributes a factor two; symmetry converts twice the half-line integral into the full reflection autocorrelation. There is no missing factor in the formula.

For the finite-resolution criterion, smoothed Frostman measures obey a uniform Frostman bound even below the smoothing scale: the bound follows from their density estimate and $$s\le2$$. Hence their weighted source-pair mass near the diagonal is uniformly $$O(r^{s-1})$$. This validates passage to the limiting bisector measure using mixed-norm reflexivity.

That criterion concerns a source-only reflection density and implies a raw joint $$L^2$$ conclusion. The present criterion instead allows a fixed positive pair restriction and proves a quantitative bound for its near-source part. Neither missing far-collision control nor the reflection norm is deduced here from Hausdorff and packing dimensions beyond the existing theorem.
