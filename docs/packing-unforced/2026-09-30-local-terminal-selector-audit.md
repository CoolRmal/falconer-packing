# Audit of the pin-side local decoupling replacement

30 September 2026. Independent audit of [the local terminal-transfer note](2026-09-30-local-giow-terminal-transfer.md). This note verifies the revised packet geometry and its quantitative local estimate. It does not claim a stronger dimension theorem. The subsequent universal profile comparison proves that this specific terminal replacement is already dominated by ordinary admissible chains; see [the independent redundancy audit](2026-09-30-terminal-redundancy-independent-audit.md).

## 1. Why the source and pin packets must remain different

Fix a shell frequency $$R$$, a parent side $$b$$, and write

$$
r=Rb,\qquad \rho=r^{-1/2},\qquad
a=b\rho=\sqrt{b/R},\qquad \delta_*=R^{-1/2}.
$$

We assume $$R^{-1}\ll b\le1$$. An angular cap of aperture $$\rho$$ has angular uncertainty $$\rho$$. A packet localized initially to a rectangle of transverse width $$a$$ and longitudinal length $$b$$ therefore spreads transversely by order $$\rho$$ after propagation over a distance of order one. It cannot be used as an ordinary unit-length source packet of transverse width $$a$$.

Here is a direct version of the obstruction. Take fixed nonnegative smooth functions $$\chi,\psi$$, supported near zero and positive on smaller intervals, and set

$$
u_R(x_1,x_2)=(ab)^{-1}\chi(x_1/a)\psi(x_2/b)e^{2\pi iRx_2}.
$$

For a small fixed $$c>0$$, use the pin $$y=(c\rho,-1)$$. This pin lies outside any fixed enlargement of the width-$$a$$ vertical source tube when $$b\to0$$. Nevertheless, on the upper branch of the circle centered at $$y$$, write

$$
x_2=h_t(x_1)=-1+\sqrt{t^2-(x_1-c\rho)^2}.
$$

For $$x_1=av$$ in the fixed support of $$\chi$$, $$t\asymp1$$, and $$h_t(0)$$ in a sufficiently small interval of length comparable to $$b$$, Taylor's theorem gives

$$
R|h_t(av)-h_t(0)|\le C(c+b).
$$

Indeed the linear contribution has size $$R(c\rho)a=c$$, and the quadratic contribution has size $$Ra^2=b$$. Also $$|h_t(av)-h_t(0)|=O(R^{-1})=o(b)$$ when $$r\to\infty$$. Choose $$c$$ and then $$b$$ small enough that all phases lie in a fixed open half-plane. The coarea Jacobian $$\sqrt{1+|h_t'|^2}$$ is bounded above and below. It follows that the pinned density has modulus at least $$C^{-1}b^{-1}$$ on an interval of length at least $$C^{-1}b$$. Thus

$$
\|(d_y)_*u_R\|_1\ge C^{-1}.
$$

This defeats a rapid-decay assertion outside the short width-$$a$$ source tube. It does not apply to the revised construction, which keeps the original unit-length source packets and introduces short packets only after taking the circular extension in the pin variable.

## 2. The revised selector has no coarse-cap counting loss

Let $$S$$ be the original standard source-cap labels, of aperture $$\delta_*$$. Partition their nominal labels into angular ancestors $$\theta$$ of aperture $$\rho\ge\delta_*$$. For a parent $$P$$, let $$A_{P,S}\in\{0,1\}$$ describe all inherited coarse selections; these numbers are constant on $$P$$.

For each $$\theta$$, use a nonnegative smooth transverse partition $$\eta_{\theta,T}$$ by pin-side tubes of width $$a$$. A common longitudinal cutoff is one on $$P$$ and supported in its prescribed enlargement. Mark a tube good using the conditional pin measure $$\lambda_P$$:

$$
\lambda_P(CT)\le H\rho.
$$

The dilation $$C$$ here includes the small-power enlargement needed by the iteration; all measures are restricted to the same enlarged parent. On $$P$$ define

$$
c_{P,\theta}(y)=\sum_{T\ {
m good}}\eta_{\theta,T}(y),
\qquad 0\le c_{P,\theta}(y)\le1.
$$

All these objects are fixed using $$R$$ and are independent of the circular radius throughout the $$R$$-shell. Weight the full original source-cap function by the scalar $$A_{P,S}c_{P,\theta(S)}(y)$$. For each fixed pin, the scalar commutes with the pinned pushforward and with the circular-extension identity.

To estimate the discarded first norm, expand back into original standard source packets. For a fixed separated source-pin pair $$(x',y)$$, a packet can contribute only when its enlarged unit-length tube meets both points, up to a rapidly decreasing error. Its direction is then within $$O(R^{-1/2+h})$$ of the connecting line. Consequently at most $$R^{O(h)}$$ standard labels and spatial tubes contribute to this pair.

There is no factor equal to the number $$\rho/\delta_*$$ of standard caps inside $$\theta$$: most of those caps cannot contribute to the fixed pair. Since $$c_{P,\theta}$$ is common to all its standard descendants, selection does not change this pairwise count.

If $$y$$ belongs to a discarded local tube, its direction differs from the actual pair direction by at most $$O(\rho+R^h\delta_*)$$. Across an enlarged parent of length $$R^{O(h)}b$$, the transverse displacement caused by this angular error is at most

$$
R^{O(h)}b\rho=R^{O(h)}a.
$$

Therefore the marked local tube, intersected with the parent, is contained in a permitted enlargement of the conditional test tube based at the actual pair and directed along its connecting line. Here the containing tube is a **conditional $$a$$-by-$$b$$ test tube**, not a width-$$a$$ unit-length source tube. Thus its heaviness is covered by the same radial-projection bad-pair event as in the old deletion argument.

For soft coefficients, use

$$
1-A_{P,S}c_{P,\theta}
\le (1-A_{P,S})+(1-c_{P,\theta}),
\qquad
1-c_{P,\theta}=\sum_{T\ {
m bad}}\eta_{\theta,T}
$$

on $$P$$. The summands are nonnegative and have bounded overlap, so the same pairwise bound applies. This verifies the geometric interface with the existing bad-first-norm estimate, with only the already permitted small-power loss.

## 3. Correct cube scale in refined decoupling

After rescaling the parent by $$b^{-1}$$, the canonical packet width is $$\rho=r^{-1/2}$$. The planar refined estimate in [Guth--Iosevich--Ou--Wang, Theorem 4.2 and Corollary 4.3](https://arxiv.org/html/1808.09346#S4) applies to unions of **$$\rho$$-cubes** in these coordinates. Using cubes of side $$r^{-1}$$ directly would not match that hypothesis.

Let $$w$$ be the smoothed conditional pin density, with $$0\le w\le CD$$, and suppose every retained enlarged packet tube has $$w$$-mass at most $$CH\rho$$. Fix a dyadic class of $$W$$ packets with comparable sixth norms. Group $$\rho$$-cubes by the number $$M$$ of incident enlarged tubes and let $$Y$$ be one resulting union. Enlarge each tested tube enough to contain every cube it meets. Weighted incidence counting gives

$$
M\int_Yw\lesssim WH\rho.
$$

There is no requirement that the individual cube masses be comparable. Hölder and the density bound give

$$
\int_Y|F|^2w
\le \|F\|_{L^6(Y)}^2
       \left(\int_Yw^{3/2}\right)^{2/3}
\le C D^{1/3}\|F\|_{L^6(Y)}^2
       \left(\int_Yw\right)^{2/3}.
$$

Applying refined decoupling and then the incidence bound yields

$$
\int_Y|F|^2w
\lesssim_\epsilon r^\epsilon H^{2/3}\rho^{2/3}D^{1/3}
\sum_{T=1}^{W}\|f_T\|_6^2.
$$

A canonical frequency rectangle has area comparable to $$\rho^{-1}$$, so Bernstein gives

$$
\|f_T\|_6^2\lesssim \rho^{-2/3}\|f_T\|_2^2.
$$

The two powers of $$\rho$$ cancel. Summing logarithmically many amplitude and multiplicity classes, and using the bounded overlap of the transverse partition, gives precisely

$$
\int\left|\sum_{\theta,T\ {
m good}}
\eta_{\theta,T}F_{P,\theta}\right|^2d\lambda_P
\lesssim_\epsilon r^\epsilon H^{2/3}D^{1/3}
\sum_\theta\int_{P^+}|F_{P,\theta}|^2
+\operatorname{RapDec}(r)
$$

in rescaled coordinates. Restoring coordinates changes the integral on the right to the normalized parent average. This calculation verifies the advertised powers independently of any comparability of pin masses on individual cubes.

## 4. Localization implementation and inherited energy

A safe primary implementation uses compact smooth transverse and longitudinal cutoffs. The latter is exactly one on the pin parent. Each product has physical support in the specified local tube. Its Fourier transform is essentially supported in a constant enlargement of the canonical rectangle: transverse derivatives occur at scale $$\rho$$, longitudinal derivatives at scale one. Enlarging the frequency rectangles and physical tube majorants by $$r^\delta$$ makes the omitted Fourier tails smaller than any chosen inverse power, with polynomial input norms and packet counts as in the finite-profile application. Such enlargements incur the permitted $$r^{O(\delta)}$$ loss. The local square-function bound is exact before frequency truncation, and the truncation error can be charged to those rapid tails.

For the smoothing step, a Schwartz approximate identity at scale $$r^{-1}$$ has its significant mass well within the enlarged tube because $$r^{-1}\ll\rho$$. Thus a slightly larger tested tube transfers the $$H\rho$$ mass bound to the smoothed density. Its tails are again controlled by the positive distance supplied by the small-power enlargement. A ball-mass bound at radius $$r^{-1}$$ controls the density everywhere by covering the successive kernel annuli with such balls.

One can instead start with band-limited Schwartz partitions. A common band-limited Schwartz majorant can be bounded below on the pin region, but it cannot equal one on an open region unless it is constant. In that implementation one must use the lower bound to divide out or dominate the common multiplier on pins. The compact-cutoff implementation avoids this minor distinction.

After the local estimate, every terminal coefficient $$c_{P,\theta}$$ has disappeared from its right side. What remains is

$$
\sum_P\sigma(P^+)\sum_{|\theta|=\rho}
\fint_{P^+}|F_{P,\theta}|^2,
\qquad
F_{P,\theta}=\sum_{S\prec\theta}A_{P,S}F_S.
$$

This is local parent energy. Each old next-step angular label has width $$(Rb)^{-1}=\rho^2\le\rho$$, so it refines one of these initial coarse ancestors. The exact inherited identity and selected-subset weighted embedding can be applied separately within each ancestor. No terminal selector remains to spoil those identities, and no global circle-energy estimate has prematurely consumed the remaining coarse iteration.

## 5. Exponent and scope of the result

With $$R=2^N$$, $$b=2^{-m}$$, $$n=(N+m)/2$$, and profile $$g=f-\mathrm{id}$$, the verified factors are

$$
H=2^{g(m)-\min_{[m,n]}g}\,R^{O(h+\Gamma)},
\qquad
D\lesssim 2^{(N-m)+g(m)-g(N)}R^{O(\Gamma)}.
$$

The terminal cost is therefore

$$
\mathcal T_g(m)=
\frac{2\bigl(g(m)-\min_{[m,(N+m)/2]}g\bigr)
      +(N-m)+g(m)-g(N)}3.
$$

The full candidate cost is $$\mathcal T_g(m)+\Phi_g(m)$$, with the old coarse-chain cost $$\Phi_g(m)$$. For a scale-uniform use take $$m\le(1-\zeta)N$$ for fixed $$\zeta>0$$ and absorb block rounding and localization in strict exponent margins.

The audit finds no new selector-compatibility obstruction to this revised terminal step. It verifies a concrete local estimate, not a stronger uniform Hausdorff--packing condition. The subsequent universal profile argument proves that every such terminal cost, even after optimizing its location, is already attained or improved by ordinary admissible chains. This construction therefore gives no improvement in the dimension condition, for any admissible profile; the conclusion concerns this precise construction rather than other possible uses of local decoupling.
