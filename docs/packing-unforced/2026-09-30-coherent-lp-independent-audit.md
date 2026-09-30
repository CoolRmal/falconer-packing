# Independent audit of the coherent strong-integrability supplement

Date: 2026-09-30.

Files checked: research/2026-09-30-coherent-subquadratic-regularity.md, output/pdf/packing-unforced-coherent-lp.tex, and the center construction and coherent comparison in output/pdf/packing-bound-original-branch.tex. I also checked that output/pdf/packing-unforced-subquadratic.tex faithfully converts the independently corrected frequency argument.

**Conclusion:** the coherent supplement's stated strong range and its full-curve corollary follow from the existing coherent comparison. No new gap was found. This is a mathematical audit of the deduction, not a replacement proof of the underlying angular comparison.

## Projection interpolation and the angular law

Put

$$
v=2-\frac1q,\qquad q'=\frac q{q-1},\qquad
\eta=\frac{q-1}{2q-1}.
$$

Then

$$
1<v<2,\qquad v-1=\frac1{q'},\qquad
\frac{v-1}{v}=\eta.
$$

For a nonnegative scalar density of mass one, Hölder gives

$$
\int h^v\le
\left(\int h^2\right)^{v-1}
\left(\int h\right)^{2-v}
=\left(\int h^2\right)^{v-1}.
$$

For a fixed source square, the affine scalar density at a pin is a translate of the projection density in the direction from its chosen center to that pin. The translation may depend on the full pin position, but it disappears after integration of the scalar power. Thus integrating against the pin probability is exactly integrating the scalar projection norm against the center's angular law. No independence between pin angle and radius is needed.

Hölder in angle, using the equality above between exponents, gives precisely

$$
\|a_Q\|_{L^v(d\nu\,dt)}^v
\le F_Q^{1/q}
\left(\int\|h_Q(\theta,\cdot)\|_2^2\,d\theta\right)^{1/q'}
\le C F_Q^{1/q}I_1(\mu_Q)^{1/q'}.
$$

The projection-energy identity applies because the conditional source has finite first energy. Its exceptional angular set is avoided by the absolutely continuous angular pin law. There are only countably many selected centers and source squares, so the almost-everywhere assertions can be imposed simultaneously.

## Small square masses do not cause a missing factor

Integrating the original source Frostman estimate inside a square of diameter comparable to its side gives

$$
I_1(\mu_Q)\le C r^{s-1}/p_Q.
$$

This requires no lower bound for the square mass. Convexity applied to the positive mixture and then the preceding estimate give

$$
\begin{aligned}
\|f_n\|_v^v
&\le\sum_Qp_Q\|a_Q\|_v^v\\
&\le C r^{(s-1)/q'}\sum_Q
p_Q^{1-1/q'}F_Q^{1/q}\\
&=C r^{(s-1)/q'}\sum_Q(p_QF_Q)^{1/q}.
\end{aligned}
$$

The center choice supplies the bounded sum of the quantities inside the last powers. Hölder over at most the covering-number count of squares therefore gives

$$
\|f_n\|_v^v\le C r^{(s-1-u)/q'},
\qquad
\|f_n\|_v\le C r^{-(u+1-s)\eta}.
$$

The small-mass power has exactly canceled. In particular there is no unaccounted sum of reciprocal square masses.

## The stated range is the exact result of the difference interpolation

Write

$$
A=u+1-s,\qquad
\tau=s-u+2\gamma,\qquad
\delta=2s-1-u.
$$

The existing coherent comparison and the covering bound give

$$
\|f_{n+1}-f_n\|_1\le C r^{\tau\eta}.
$$

The two growth estimates at adjacent dyadic scales give

$$
\|f_{n+1}-f_n\|_v\le C r^{-A\eta};
$$

their different side lengths change only a fixed multiplicative constant. If

$$
\vartheta=\frac{v-p}{p(v-1)},
$$

then interpolation gives the exponent

$$
\eta[\tau\vartheta-A(1-\vartheta)].
$$

It is positive exactly when

$$
p<\frac{v(\tau+A)}{\tau+vA}.
$$

As the allowed parameter approaches its upper endpoint from below, the last bound tends to

$$
\frac{vs}{\delta+v(s-\delta)}
=\left(1-\eta\frac{\delta}{s}\right)^{-1}.
$$

Every strictly smaller exponent above one is achieved by one fixed legal parameter, with a strictly positive summation exponent. This includes the source endpoint exponent two: the parameter still approaches one half only from below.

The assumptions imply

$$
0<\delta\le s-1<s,
$$

so the displayed upper bound is strictly between one and the higher control exponent. The interpolation is always within its legal range.

## Limit and full-curve consequence

The affine densities have one common bounded scalar support. An initial density has finite higher norm, and the difference norms are summable in the stated strong space. The resulting limit also exists in the first norm. The uniform quadratic approximation of the affine maps to distance identifies its positive joint measure with the original distance law, exactly as in the coherent proof.

For the full dimension curve, the corollary only selects two separated compact subsets and their probabilities. Such subsets can be obtained after the same strict Frostman and covering parameter choices in the coherent Borel reduction. Thus the stronger conclusion does not require patching infinitely many separated pieces while retaining a single uniform strong norm. The profile branch is supplied separately by the corrected subquadratic frequency proof. The two branches cover the same union as the original dimension theorem.

Fubini gives the asserted strong density for almost every selected pin. If the joint power integral is denoted by its finite value, Markov bounds the individual integral by twice that value on a pin set of probability at least one half. Hölder for a density of mass one then gives exactly the lower length bound stated in the supplement.

Finally, the TeX conversion of the frequency upgrade retains the necessary split between the regularized pin region and its discarded complement, its precise strong exponent restriction, the decay of the full shell, and distributional identification. I found no mismatch between that conversion and the corrected research proof.
