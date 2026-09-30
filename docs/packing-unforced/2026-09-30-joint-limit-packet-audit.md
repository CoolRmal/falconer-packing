# Fresh audit of the assembled unforced analytic transfer

Date: 2026-09-30. Scope: the actual analytic argument in `output/pdf/packing-unforced-finite-profile.tex`, `output/pdf/packing-unforced-transfer.tex`, and `output/pdf/packing-unforced-embedding.tex`. This audit does not reprove, optimize, or certify the separate profile inequalities. It makes no change to the published proof.

The adversarial targets were the pin-dependent quadratic identity, the passage from different good functions at different frequencies to the original measure, the packet/spectral partition interface, and whether the selected-cap embedding silently needs stronger good-tube hypotheses. I found no counterexample or missing hypothesis in those four steps. The concrete checks below are the basis for that conclusion; this is not a claim that a finite audit substitutes for formal verification.

## 1. The pinned identity really permits a different function at every pin

This can be checked directly, without relying on an analogy with the unpinned Mattila integral. Let normalized arclength on the unit circle be denoted by $$d\omega$$, fix a pin $$y$$, and take a complex-valued Schwartz function $$f$$. Its radialization about the pin is

$$
A_y f(z)=\int_{S^1} f(y+|z|\omega)\,d\omega.
$$

Equivalently, radialization is averaging over rotations of the translate $$z\mapsto f(y+z)$$. Fourier transformation commutes with this rotational averaging. The Fourier transform of that translate is $$e^{2\pi i y\cdot\xi}\widehat f(\xi)$$. Consequently the radial Fourier value of $$A_y f$$ at radius $$r$$ is

$$
\int_{S^1} e^{2\pi i r y\cdot\omega}\widehat f(r\omega)\,d\omega
  =(f*\widehat\omega_r)(y).
$$

Planar Plancherel in polar coordinates gives the exact identity

$$
\int_0^\infty
 \left|\int_{S^1}f(y+t\omega)\,d\omega\right|^2 t\,dt
=\int_0^\infty |(f*\widehat\omega_r)(y)|^2 r\,dr.
$$

The density of the distance pushforward is

$$
p_{f,y}(t)=2\pi t\int_{S^1}f(y+t\omega)\,d\omega,
\qquad t>0.
$$

When all source functions are supported in the fixed separated cutoff support, their radial supports lie in one interval $$[c,C]$$ with $$c>0$$. Thus the left-hand side of the pinned identity and the squared unweighted density norm are equivalent, with constants depending only on that interval. For the upper bound needed in the manuscript, the upper endpoint alone would suffice.

Every good shell function is a finite sum of smooth compactly supported standard packets. The identity therefore applies to it. It is a statement universally quantified over a function and a pin separately: substituting $$f=G_{R,y}$$ for each fixed $$y$$ is legitimate. There is no differentiation in the pin variable, and no requirement that the same function be used at every pin.

This matches [Liu's pinned quadratic identity, Theorem 1.9](https://arxiv.org/html/1802.00350). The derivation above additionally checks normalization and the allowance of complex signed shell functions.

## 2. Annular localization needs an integrable tail, and the packet construction supplies one

A pointwise statement “rapidly small outside the annulus” alone would not justify integrating over every circle radius. Here the construction gives the stronger statement that is needed.

The inverse Fourier kernel of a smooth standard annular sector has transverse scale $$R^{-1/2}$$ and longitudinal scale $$R^{-1}$$, with arbitrary decay in the corresponding rescaled coordinates. Fixed annular ratios depending on $$T$$ alter constants, not the powers in these localization scales. For every prescribed derivative order and decay order, the usual rescaling and integration-by-parts argument supplies a bound of the form

$$
|\partial^\alpha K_{R,S}(z)|
 \le C_{A,\alpha,T}R^{3/2+|\alpha|}
 \bigl(1+R^{1/2}|z\cdot v_S^\perp|
          +R|z\cdot v_S|\bigr)^{-A}.
$$

The support of $$1-\chi$$ is a positive fixed distance from the support of the original source measure whenever $$1-\chi$$ is nonzero. Integrating this estimate against the finite source measure and then in the spatial variable proves, for every $$A,m$$,

$$
\bigl\|(1-\chi)(\psi_{R,S}\widehat\mu)^\vee\bigr\|_{W^{m,1}}
 \le C_{A,m,T} R^{-A}.
$$

In this display the derivatives of $$1-\chi$$ are included by the product rule. Far from both compact supports the same kernel decay makes the norms integrable. This establishes the cutoff removal used for the circular reconstruction. Using the derivative bounds as well as the first norm gives arbitrary decay in the frequency variable for that error, so it is harmless after the radial integral too.

For the compactly supported packet itself, multiplication by $$\chi\eta_T$$ convolves the original annular Fourier support with a rapidly decreasing transform. Its transverse derivative scale is at most $$R^{1/2+O(h)}$$, while its longitudinal and fixed source cutoff derivatives are smaller than $$R$$. Outside a fixed enlargement of the original annulus, the frequency separation from its support is comparable to $$R$$ (and comparable to $$|\xi|$$ further away). Integration by parts to arbitrary order therefore gives, for any prescribed $$A,M$$,

$$
|\widehat G_{R,y}(\xi)|
 \le C_{A,M,T,h} R^{-A}(1+|\xi|/R)^{-M}
$$

there, uniformly in the pin and in the retained packet subset. The polynomial number of packets is absorbed by choosing more derivatives. A sufficiently small fixed $$h$$ is already required elsewhere and makes the separation between the derivative and annular scales positive.

Since circle extension is bounded by the supremum of this Fourier transform, its squared tail integrated against $$r\,dr$$ is bounded by a constant times $$R^{2-2A}$$. This is rapidly decreasing to arbitrary order. Thus no nonintegrable uniform error is being inserted into the pinned identity.

## 3. Exact finite reconstruction is sufficient for the joint limit

Write the shell densities as

$$
g_R(y,t)=\frac{d(d_y)_*G_{R,y}}{dt},\qquad
b_R(y,t)=\frac{d(d_y)_*(P_R\mu-G_{R,y})}{dt}.
$$

They are measurable joint functions: each frequency has finitely many components, cubes, caps, and packets, and all marks can be assigned by a fixed deterministic convention. The pin dependence is piecewise specified on Borel sets. For each shell, the exact identity is

$$
g_R(y,t)+b_R(y,t)
=\frac{d(d_y)_*P_R\mu}{dt}.
$$

No compatibility of the good parts at different frequencies is asserted or needed.

The established shell bounds have strictly negative powers of the geometric shell parameter. Taking square roots in the good estimate gives

$$
\sum_R\|g_R\|_{L^2(d\nu\,dt)}<\infty,
\qquad
\sum_R\|b_R\|_{L^1(d\nu\,dt)}<\infty.
$$

All their radial supports lie in the common bounded interval $$[c,C]$$. Hence the good series also converges absolutely in the first norm, using Cauchy--Schwarz in this finite product measure space. The sum, including the smooth low-frequency term, defines an integrable joint density $$h$$.

For a smooth compactly supported test function $$\Phi(y,t)$$, the finite shell sum can be evaluated against the smooth spatial test

$$
\Psi(x)=\chi(x)\int\Phi(y,|x-y|)\,d\nu(y).
$$

The source cutoff and pin support are separated. Every derivative in $$x$$ can therefore be taken under the integral with a uniform bound, and $$\Psi$$ is smooth and compactly supported. Distributional frequency reconstruction gives convergence to

$$
\iint\Phi(y,|x-y|)\,d\mu(x)\,d\nu(y).
$$

The first-norm convergence of the densities gives convergence to the same test against $$h(y,t)\,d\nu(y)\,dt$$. This identifies the two finite Borel measures, first on smooth tests and hence on all Borel sets. Although intermediate shells are complex signed functions, their limit is the positive joint distance law. It follows in particular that $$h$$ is real and nonnegative almost everywhere.

Uniqueness of disintegration on these standard Borel spaces now gives

$$
(d_y)_*\mu=h(y,\cdot)\,dt
\quad\text{for }\nu\text{-almost every }y.
$$

The pin remainder at each frequency causes no extra issue: its error uses the uniform first norm of the whole annular multiplier times its discarded mass. Estimating that remainder by all absolute packet norms would be insufficient, but the manuscript explicitly avoids doing that.

### Collision stress test

The fixed train-track examples in `research/2026-09-30-off-cluster-collision-obstruction.md` have divergent raw averaged squared collision quantities. They do **not** contradict this argument. Only the good shell sum is shown to have a joint square-integrable density; the bad shell sum is controlled in the first norm. The resulting raw joint density need not belong to the second-norm space. Any attempt to strengthen the actual conclusion to raw joint square integrability without an additional argument would encounter those examples.

## 4. Finer spectral labels do not require finer spatial packets

The order of operations in the manuscript matters and is mathematically sufficient:

1. Choose smooth standard annular multipliers first. Their fixed smooth edges supply the standard spatial packet estimates.
2. Make coarse labels by grouping whole standard labels. Once the spectral width is below the standard width, use separate labels $$(S,I)$$ and the spectral multiplier $$\psi_{R,S}\mathbf1_I$$. The intervals partition the **entire** support of each smooth standard multiplier, including overlap beyond its nominal arc.
3. For all such fine labels, assign their standard parent's mark. Every decision to retain a source packet is therefore a decision on a whole standard label.
4. At a fixed initial pin cube, sum standard packets before passing to finer spectral pieces. Remote packets from a removed standard label contribute only rapidly decreasing circular extension there. The complete standard sum is the full standard-cap function, after the cutoff error checked above.
5. Only then partition the circular spectral measure into fine pieces. These pieces are used solely for quadratic estimates. No claim is made that an individually fine-filtered spatial packet stays inside its standard tube.

The elementary inequalities guaranteeing the geometry are

$$
\delta_j\le\rho_j,
\qquad
\delta_*\le\rho_j.
$$

The first is the curvature/admissibility inequality. For the second,

$$
n_j-n_{j+1}\le\min\{n_j,N-n_j\}\le N/2.
$$

Thus the actual direction of a fine spectral interval differs from its standard marking direction by at most a constant times the aspect ratio of the required dual tube. Enlarging its marking tube by the prescribed small power accommodates this mismatch and the standard packet uncertainty.

The inherited identity is exact because future marks come from the fixed spatial parent. For that parent and a label, the function on the right is independent of its child cube; only the current child's selection coefficient varies. Smooth support overlap causes multiple labels, not an ambiguous parent relation, because the labels retain their standard index. The overlap remains bounded at every level.

The spatial tubes may and should be chosen of a fixed longitudinal length covering the common normalized source and pin region, with the longitudinal cutoff supported outside that region. This is the usual bounded-region packet convention. Otherwise a finite tube's longitudinal endpoint, rather than its transverse distance, could accidentally be used in the remote-packet assertion. This is a choice of the standard packet decomposition, not a new estimate or a hypothesis on the measures.

The primary source checks are [Liu's Lemma 3.1, Lemma 4.2, and Section 4.2](https://arxiv.org/html/2603.15328v3). These provide the standard-packet first-norm and remote-extension estimates used here, and apply the pinned identity to the shell construction. The fine-label step above is checked separately; it is not attributed to a statement in that paper that already proves the new unforced construction.

## 5. The weighted embedding matches the actual marks

The embedding proposition allows an arbitrary finite positive pin measure, including atomic test measures, and arbitrary child-dependent subsets of labels. Its assumption on a retained label is exactly the upper bound for the enlarged test tube intersected with the same enlarged parent. It does not ask for a uniform bound on tubes of the omitted labels.

Three points exclude the candidate counterexamples from arbitrary destructive/constructive cap interference:

- Local Plancherel is applied to the **selected subset** for that child. Multiplication by a spatial cutoff only expands equal-scale Fourier balls by a bounded factor, preserving bounded overlap. The inequality therefore has no unselected cap in its main term.
- For a fixed label, the spectral function is independent of the child. This is exactly what the inherited identity supplies. Child-dependent marks do not turn into child-dependent Fourier functions.
- If a dual tube meets several selected enlarged children, choose just one selected child. The enlarged marking tube centered there contains all the contributing child enlargements, because the effective direction differs from the actual one by at most the tube aspect ratio. The overlap bound converts its single selected mass test into the required sum of positive child weights.

In the notation of the embedding appendix, this yields

$$
\tau_\theta(U)\le\Lambda H(a/b)M
$$

for every dual rectangle $$U$$, where $$\tau_\theta$$ is the sum of the selected enlarged-child averages, $$M=\sigma(P^+)$$, and $$\Lambda$$ is the overlap multiplicity. The anisotropic reproducing kernel has size $$1/(ab)$$ with summable decay on the dual-rectangle lattice. Its convolution against this positive averaging measure is bounded by

$$
C\frac1{ab}\Lambda H\frac ab M
=C\frac{\Lambda HM}{b^2}.
$$

This displays exactly one threshold factor. The margin from the averaging supports to the outside of the enlarged parent supplies arbitrary-order global-norm tails. All the required Fourier rectangles, fixed frequency smoothings, direction mismatches, and enlarged-parent normalizations agree with the transfer construction. The later small-power factors absorb their fixed-step overlap constants.

## 6. Other hypothesis checks and the scope of the conclusion

The radial projection input is used only to discard source-heavy pairs in the first-norm estimate. Both original measures are separated and have a common Frostman exponent strictly greater than one, so [GIOW Theorem 3.7](https://arxiv.org/pdf/1808.09346) supplies precisely the averaged radial-projection integrability assumed in the manuscript. Restricting the pin measure to a regularized component multiplies the integral by at most the reciprocal component mass; this is already included in the displayed small-power loss.

The conditional-energy bounds use original pin restrictions and normalize by the same enlarged parents as the good-tube tests. The lower mass bound of the active original parent controls the denominator. No bound on an arbitrary thin intersection with an enlarged-cube boundary is required.

The parameter order is consistent. First fix the chain start and hence the finite edge bound, then the deletion constants, then the small geometric exponent, and finally the regularization depth and discarded mass parameter. Constants depending on the resulting annular ratio are fixed before frequency tends to infinity. The localization derivatives and tail orders can be increased after these choices; their constants do not change the frequency exponents.

**Audit outcome:** the four targeted analytic interfaces are consistent under the manuscript's actual hypotheses. In particular, the loss of a fixed forced midpoint is not contradicted by packet tails, selection-dependent cap sums, or the pin-dependent distributional limit. This note neither certifies the separate chain/profile optimization nor proves that any resulting sufficient dimension condition is the weakest possible one.
