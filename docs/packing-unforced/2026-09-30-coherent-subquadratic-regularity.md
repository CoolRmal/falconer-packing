# Strong integrability from the coherent positive approximations

30 September 2026. This is a natural-language proof supplement. It uses the coherent angular comparison and the chosen-center construction already proved in `output/pdf/packing-bound-original-branch.tex`. No new formalization or improvement of the dimensional cutoff is asserted.

Let the source probability have Frostman exponent $$1<s\le2$$ and occupied dyadic square count at scale $$r$$ at most $$Cr^{-u}$$, with

$$
s\le u<2s-1.
$$

Let the pin probability have a Frostman exponent greater than one. Both supports are compact and positively separated. Write $$q>1$$ for the averaged radial-projection exponent used to choose the source centers, and set

$$
v=2-\frac1q,\qquad
\eta=\frac{q-1}{2q-1},\qquad
\delta=2s-1-u>0.
$$

**Theorem.** The raw joint pinned distance law has a density in every space

$$
L^p(d\nu(y)\,dt),\qquad
1<p<\left(1-\eta\frac{\delta}{s}\right)^{-1}.
\tag{1}
$$

In particular, the coherent branch also yields a density with some exponent strictly greater than one. The claimed range is strictly below $$v$$ because $$0<\delta<s$$ and $$\eta=1-1/v$$.

## Polynomial higher-norm control of the positive approximations

Use the centers from the coherent proof. At each occupied source square $$Q$$ of side $$r=2^{-n}$$ put

$$
p_Q=\mu(Q),\qquad \mu_Q=p_Q^{-1}\mu|_Q,
\qquad F_Q=\|\rho_{x_Q}\|_{L^q(S^1)}^q,
\qquad \sum_Qp_QF_Q\le2B<\infty.
$$

Here the angular law of the pin seen from the center has density $$\rho_{x_Q}$$. This is one fixed, countable family of center choices. Let $$a_Q(y,t)$$ be the nonnegative density obtained by pushing $$\mu_Q$$ through the affine distance approximation based at this center. It has mass one in the distance variable for almost every pin. Let $$h_Q(\theta,t)$$ be the density of its scalar orthogonal projection, before the pin-dependent translation in the distance variable. For almost every angle, probability interpolation gives

$$
\int |h_Q(\theta,t)|^v\,dt
\le \left(\int |h_Q(\theta,t)|^2\,dt\right)^{v-1}.
\tag{2}
$$

This follows directly from Hölder applied to the powers $$h_Q^{2(v-1)}$$ and $$h_Q^{2-v}$$. Both exponents are between zero and one after the appropriate Hölder normalization. The first norm is one.

Write $$q'=q/(q-1)$$, so $$v-1=1/q'$$. Translating a density does not change its norm. Integrating (2) against the angular pin law and using Hölder in the angle gives

$$
\|a_Q\|_{L^v(d\nu\,dt)}^v
\le F_Q^{1/q}
\left(\int_{S^1}\|h_Q(\theta,\cdot)\|_2^2\,d\theta\right)^{1/q'}
\le C F_Q^{1/q} I_1(\mu_Q)^{1/q'}.
\tag{3}
$$

The last step is the projection-energy identity; normalized versus unnormalized angular measure only changes the fixed constant. The exceptional angular null set is avoided by the absolutely continuous angular pin law.

The source Frostman estimate, integrated over a square of diameter at most a constant times $$r$$, gives

$$
I_1(\mu_Q)\le C r^{s-1}/p_Q.
\tag{4}
$$

The coherent approximation is $$f_n=\sum_Qp_Qa_Q$$. Convexity, (3), and (4) show

$$
\|f_n\|_v^v
\le C r^{(s-1)/q'}\sum_Q(p_QF_Q)^{1/q}
\le C B^{1/q}r^{(s-1-u)/q'}.
\tag{5}
$$

For the last inequality apply Hölder to the finite sum and use its number of terms, at most $$Cr^{-u}$$. Consequently, with $$A=u+1-s>0$$,

$$
\|f_n\|_v\le C r^{-A\eta}.
\tag{6}
$$

No lower bound on an individual occupied-square mass is needed.

## Interpolate differences and sum them

Choose

$$
0<\gamma<\min\{1/2,(s-1)/2\},\qquad
\tau=s-u+2\gamma>0.
$$

The coherent comparison, optimized in its angular truncation parameter, gives

$$
\|f_{n+1}-f_n\|_1\le C r^{\tau\eta}.
\tag{7}
$$

Its proof uses $$Z_n\le Cr^{\tau}$$ and the exponent $$\eta=(q-1)/(2q-1)$$. Meanwhile (6) and the triangle inequality imply

$$
\|f_{n+1}-f_n\|_v\le C r^{-A\eta}.
\tag{8}
$$

For any $$1<p<v$$ define

$$
\vartheta=\frac{v-p}{p(v-1)},\qquad
\frac1p=\vartheta+\frac{1-\vartheta}{v}.
$$

Hölder interpolation between (7) and (8) yields

$$
\|f_{n+1}-f_n\|_p
\le C r^{\eta[\tau\vartheta-A(1-\vartheta)]}.
\tag{9}
$$

The exponent is positive exactly when

$$
p<\frac{v(\tau+A)}{\tau+vA}
=\frac{v(1+2\gamma)}{s-u+2\gamma+v(u+1-s)}.
\tag{10}
$$

As $$\gamma$$ increases to $$(s-1)/2$$ from below, the right side tends to

$$
\frac{vs}{\delta+v(s-\delta)}
=\left(1-\eta\frac\delta s\right)^{-1}.
$$

Thus every exponent in (1) admits a legal fixed choice of $$\gamma$$ for which (9) has a positive exponent. The dyadic sum of these norms converges. An initial approximation has finite $$v$$-norm by (5), and hence finite $$p$$-norm because the common pin-distance region has finite measure. It follows that $$f_n$$ converges in strong $$L^p$$ and also in $$L^1$$.

The existing uniform affine approximation to the distance function identifies the weak limit of the positive joint measures with the raw joint distance law. Therefore this law has the strong density just constructed. This proves the theorem.

## Consequence for the full currently proved dimension curve

The separate finite-profile argument now also gives a strong exponent greater than one, as proved in `2026-09-30-subquadratic-profile-transfer.md`. Combining the two upgrades with the same compact-set and Borel reductions proves: every set covered by the current strict curve has two separated compact subsets carrying source and pin probabilities for which the raw joint distance law has a density in some strong space $$L^p$$, with $$p>1$$. The exponent is not asserted uniform as the dimensional margin tends to zero.

For almost every pin the pinned probability density belongs to that same space. If its joint integral satisfies

$$
M=\int\int f(y,t)^p\,dt\,d\nu(y)<\infty,
$$

then pins in a set of probability at least one half satisfy

$$
|\Delta_y(E)|\ge(2M)^{-1/(p-1)}>0.
$$

Indeed Markov bounds the individual integral by $$2M$$ on such a pin set; Hölder applied to a density of mass one gives the displayed length bound.

This regularity gain retains the strict dimensional conditions. It provides no endpoint conclusion and no weaker Hausdorff–packing cutoff by itself.
