# Generic small metric changes and fixed profile witnesses

30 September 2026. Positivity of distances for almost every elliptic metric is established context; see [Hofmann--Iosevich, *Falconer conjecture in the plane for random metrics*](https://arxiv.org/abs/math/0305132). No novelty for that general phenomenon is claimed here. The purpose of this note is a complete quantitative joint pinned estimate and its application to the fixed profile witnesses in this project. The original Euclidean metric is not covered by an almost-everywhere parameter conclusion.

## 1. The quantitative estimate

Let $$\mu$$ be a compactly supported probability in the plane with

$$
I_1(\mu)=\iint |x-x'|^{-1}\,d\mu(x)d\mu(x')<\infty.
$$

Let $$\nu$$ be any fixed compactly supported pin probability. It is chosen independently of the metric parameter, and may equal the source measure. No source--pin separation hypothesis is needed in this theorem.

Equip the three-dimensional space of real symmetric two-by-two matrices with its Frobenius norm. For $$0<\eta<1/2$$, let $$\mathbb P_\eta$$ be normalized Lebesgue measure on

$$
\mathcal M_\eta=\{M:\|M-I\|_F<\eta\}.
$$

Every such matrix is positive definite. Define

$$
d_{M,y}(x)=\sqrt{(x-y)^{\mathsf T}M(x-y)}.
$$

**Theorem 2.** For almost every matrix in this ball, the full joint pinned distance law has a density in the corresponding joint second-norm space. Quantitatively,

$$
\boxed{\quad
\int_{\mathcal M_\eta}\int
\|(d_{M,y})_*\mu\|_{L^2(\mathbb R)}^2
\,d\nu(y)\,d\mathbb P_\eta(M)
\le C\eta^{-1}I_1(\mu).
\quad}
\tag{1}
$$

The left side is interpreted through the densities provided by the conclusion. The constant is absolute up to the choice of matrix norm and a fixed mollifier normalization.

### Proof of matrix transversality

For a source pair and a pin, put

$$
v=x-x',\qquad z=\frac{x+x'}2-y,
\qquad Q=zv^{\mathsf T}+vz^{\mathsf T}.
$$

The squared-distance difference is exactly $$\operatorname{tr}(MQ)$$. Moreover,

$$
\|Q\|_F^2
=2|z|^2|v|^2+2(z\cdot v)^2,
\tag{2}
$$

so its norm is comparable to the product of the two lengths. The eigenvalues of all matrices in the parameter ball are between one half and three halves, and therefore

$$
d_{M,y}(x)+d_{M,y}(x')
\le C(|v|+|z|).
$$

If the two distances differ by at most $$\varepsilon$$, then

$$
|\operatorname{tr}(MQ)|
\le C\varepsilon(|v|+|z|).
$$

A linear slab in a three-dimensional ball of radius $$\eta$$ occupies at most a constant times its width divided by $$\eta$$. Consequently, whenever neither vector vanishes,

$$
\frac1\varepsilon\mathbb P_\eta
\{|d_{M,y}(x)-d_{M,y}(x')|\le\varepsilon\}
\le C\eta^{-1}\left(\frac1{|v|}+\frac1{|z|}\right).
\tag{3}
$$

Keeping the distance-sum factor in this calculation is essential. Merely replacing it by the diameter would instead leave a product of reciprocal lengths and an additional midpoint potential. Also, separation of the source and pin supports by itself would not exclude a pin near a source-pair midpoint.

### The midpoint term is bounded by the source energy

For a fixed pin let $$R_y(x)=2y-x$$ be reflection through that point. Then

$$
\iint\left|\frac{x+x'}2-y\right|^{-1}\,d\mu(x)d\mu(x')
=2I_1(\mu,(R_y)_*\mu)
\le2I_1(\mu).
\tag{4}
$$

The last step is Cauchy--Schwarz for the positive Riesz-energy form. For completeness, its Fourier expression has the positive weight proportional to the reciprocal frequency length. The two factors have identical self-energy because translation and reflection preserve energy, so their cross-energy is at most that common value. This reasoning may first be applied to smoothed measures and then passed to the limit, or proved through the positive Gaussian representation of the Riesz kernel.

Finite source energy also implies that the source probability has no atoms. The diagonal and, for each fixed pin, the reflected diagonal therefore have zero source-pair mass. This justifies ignoring the zero-vector exceptions in (3), even when the pin measure has atoms.

### Passing from collisions to the joint density

Choose a nonnegative smooth probability mollifier supported in the interval from minus one half to one half. Its self-correlation is bounded and supported in the interval from minus one to one. The squared second norm of the mollified radial law is therefore bounded by a fixed constant times the collision probability of width $$\varepsilon$$ divided by that width.

Integrating (3) in the source pair and pin and using (4) yields the uniform estimate

$$
\int\!\int
\|\varphi_\varepsilon*(d_{M,y})_*\mu\|_2^2
\,d\nu(y)\,d\mathbb P_\eta(M)
\le C\eta^{-1}I_1(\mu).
\tag{5}
$$

All mollified laws have a common bounded radial support. Weak compactness in the fixed space with reference measure $$d\mathbb P_\eta\,d\nu\,dt$$ and weak convergence of mollifications identify an actual joint density. Lower semicontinuity gives (1). Disintegration then gives the stated almost-everywhere assertion for the individual metric and pin parameters.

## 2. One fixed Euclidean image, arbitrarily close to the original set

For every admissible matrix put $$L_M=M^{1/2}$$. Then

$$
d_{M,y}(x)=|L_Mx-L_My|.
$$

Thus (1) is a statement about ordinary Euclidean distances between the simultaneously transformed source and pin measures. Almost every matrix in any prescribed sufficiently small ball yields a **single fixed pair of measures** whose full joint pinned distance law has finite squared second norm. For example some matrix in the ball has joint squared norm at most

$$
2C\eta^{-1}I_1(\mu).
$$

For almost every such matrix, almost every transformed pin has a positive-length distance set from the transformed source support. Hausdorff and packing dimensions are preserved by the invertible linear map, as are Frostman exponents up to constants. The map differs from the identity in operator norm by at most a constant times the parameter radius.

This permits a fixed small deformation of a previously constructed Moran witness with dimension greater than one, retaining its dimensions while giving the full raw pinned second norm. It is a statement about a suitable deformed witness, not about every orientation or the undeformed witness. No persistent deletion is required for this generic image, so there is no conflict with the obstruction to vanishing-total-loss selections for a different fixed raw law.

The quantitative bound deteriorates as the reciprocal parameter radius. Taking good matrices successively closer to the identity therefore does not give a uniform second-norm bound and cannot pass this conclusion to the identity metric. The original metric may lie in the exceptional parameter set.

## 3. What happens to the dyadic profile

Dimensions alone do not specify the intermediate-scale profile, so that point must be checked separately. Suppose the original compact support at depth $$n$$ occupies exactly $$2^{F(n)}$$ dyadic squares, each of source mass $$2^{-F(n)}$$, as in the homogeneous dyadic construction used earlier.

Fix an invertible linear map. There is a constant $$C_L$$, independent of depth, such that the image of any source square meets at most $$C_L$$ target squares of the same side length, and the inverse image of any target square meets at most $$C_L$$ source squares. Therefore the transformed support and probability satisfy

$$
N_n(L\operatorname{supp}\mu)\le C_L2^{F(n)},
\qquad
\sup_{Q\in\mathcal D_n}(L_*\mu)(Q)\le C_L2^{-F(n)}.
\tag{6}
$$

This does not assert equal masses for the transformed cubes: a boundary may cut off arbitrarily small mass. It is the pair of global bounds (6) that survives.

Suppose a positive restriction of the transformed probability has mass $$w$$, and its normalized regularized component has positive depth-$$n$$ cube masses between

$$
2^{-f(n)-eN}\quad\text{and}\quad2^{-f(n)}
$$

for all depths under consideration up to $$N$$. Its mass upper bound from (6) and its occupied-cube count imply respectively

$$
F(n)+\log_2w-eN-\log_2C_L
\le f(n)
\le F(n)+\log_2C_L.
\tag{7}
$$

For the lower inequality, compare the asserted lower regularized cube mass with the transformed mass upper bound divided by the retained mass. For the upper inequality, sum the asserted upper regularized masses over at most the number of squares in (6).

Hence large regularized components have the same normalized limiting profiles, up to their already permitted regularization and mass errors. In particular, choosing the metric from the full-measure good set does not erase the profile witness merely through a change of grid.

One can also check the global quadratic mass profile directly: the source and transformed depth partitions have a common refinement with uniformly bounded row and column overlap. Cauchy--Schwarz on that finite overlap gives

$$
C_L^{-1}\sum_{Q\in\mathcal D_n}\mu(Q)^2
\le\sum_{Q\in\mathcal D_n}(L_*\mu)(Q)^2
\le C_L\sum_{Q\in\mathcal D_n}\mu(Q)^2,
$$

after enlarging the map-dependent constant if necessary.

## 4. Interpretation for the research goal

The inherited-slat obstruction shows why the finite arithmetic averaging argument cannot simply be applied anew at every stage of a fixed singular construction. The present result shows that one fixed geometric modification can nevertheless produce full pinned absolute continuity while preserving the dimension data and the normalized profile witness.

The two observations distinguish an obstruction to a profile-based estimate from a Euclidean null-distance example. A worst profile can occur for a fixed set whose raw joint pinned laws are perfectly square integrable after a suitable arbitrarily small common deformation. What remains unproved is a mechanism forcing comparable transversality for the original Euclidean geometry of every set in a larger Hausdorff--packing region.
