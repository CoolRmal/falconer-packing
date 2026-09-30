# Independent audit of the frequency-band comparison and sparse Moran application

Date: 2026-09-30. Audited sources: `output/pdf/packing-unforced-band-comparison.tex`, `output/pdf/packing-unforced-sparse-moran.tex`, and their fixed-center and radial-projection dependencies in `output/pdf/packing-bound-original-branch.tex`. The audit found no analytic gap in the current arguments. This records what is verified and its exact scope; it is not a claim that the examples imply a universal dimension-only inequality.

## 1. Gaussian bounds require no critical energy

For a probability supported in a ball of radius comparable to rho, with Frostman exponent s strictly between one and two and Frostman constant K, the Gaussian identity gives

$$
E_R(\lambda)=cR^2\iint e^{-c'R^2|x-x'|^2}\,d\lambda(x)d\lambda(x')
\le C_sKR^{2-s}.
$$

The dyadic spatial shells prove this for every positive frequency radius, including radii below one. No finiteness of the energy at exponent s is required. Finite first energy, needed for almost-everywhere projected second-norm densities, follows separately from the Frostman bound and s greater than one.

The signed-coordinate estimate is valid in precisely its Gaussian form:

$$
\int e^{-|\xi|^2/R^2}|\widehat{x_k\lambda}(\xi)|^2\,d\xi
\le C\rho^2E_R(\lambda).
$$

To check this, express its left side as the spatial Gaussian double integral with the additional signed factor consisting of the two kth coordinates. Its absolute value is at most a constant times rho squared. The remaining spatial kernel is nonnegative. This proves the comparison despite the signed coordinate measure. It would not justify an analogous comparison of two sharp annular energies, and the manuscript does not assert one.

For the scalar frequency band of size R, polar coordinates consequently give

$$
\int\|U_R(\theta)\|_2^2\,d\sigma(\theta)
\le C_sKR^{1-s},
\qquad
\int\|\partial_\theta U_R(\theta)\|_2^2\,d\sigma(\theta)
\le C_sK\rho^2R^{3-s}.
$$

The radial Jacobian contributes the inverse frequency factor to both estimates, and the angular derivative contributes two frequency powers to the second. These powers are correct.

## 2. Correlated angular pairs and arbitrary shifts

If the two angular marginals are bounded by A times arclength and their pointwise separation is at most omega, the fundamental theorem of calculus along the shorter arc gives

$$
\|U_R(\theta)-U_R(\phi)\|_2^2
\le\omega\int_{d(z,\theta)\le\omega}
\|\partial_zU_R(z)\|_2^2\,dz.
$$

Integrating the right side needs only the first marginal. Fubini contributes another factor omega. The trivial squared-difference estimate uses both marginals. Taking the smaller bound yields

$$
\int\|U_R(\theta)-U_R(\phi)\|_2^2\,d\kappa
\le CAK\min\{1,(\rho\omega R)^2\}R^{1-s}.
$$

Thus no independence of the angles is used. For a shift of absolute value at most v, the scalar Fourier multiplier is bounded pointwise by a constant times the minimum of one and vR. This remains valid when the shift is an arbitrary measurable function of the parameter. Scalar frequency localization is preserved by such a shift at each fixed parameter.

The partition of scalar frequency has squared functions summing to one. Therefore the squared second norm of the full shifted difference equals the sum of the localized squared norms; this is a frame identity, not an assertion that the shifted bands have disjoint support. Nonnegativity permits the parameter integral and band sum to be interchanged. The resulting scalar sum is

$$
\sum_{R\in2^{\mathbb Z}}
\min\{1,(\delta R)^2\}R^{1-s}
\le C_s\delta^{s-1}.
$$

The powers on the two sides of the splitting frequency are respectively three minus s and one minus s. Both sums are geometric. In particular there is no borderline summation producing a logarithm and no hidden appeal to critical energy. The constants can be fixed on any compact subinterval of the permitted source exponent range.

## 3. Arbitrary levels, common centers, and the correct mass factor

At parent depth n and descendant depth m greater than n, let their side lengths be r and h. The fixed centers chosen by the original radial-projection argument give angular separation of order r and scalar shift of order r squared after recentering at the descendant center. The conditional source has diameter of order h and Frostman constant at most the original constant divided by its mass. The new lemma therefore gives, for each descendant Q, the retained integrated squared second-norm error

$$
\frac{CA}{p_Q}\bigl((hr)^{s-1}+r^{2s-2}\bigr)
\le\frac{CA}{p_Q}r^{2s-2}.
$$

For each pin, each affine conditional density is supported on an interval of length of order h. The union of the two intervals has length of order h even if the gap between them is much larger. Cauchy–Schwarz uses this union, not a single containing interval. This is why no restriction that m be at most twice n is needed for the comparison itself.

After the pin Cauchy–Schwarz step, multiplication by the descendant mass and summation give exactly

$$
CA^{1/2}h^{1/2}r^{s-1}\sum_Q\sqrt{p_Q}.
$$

Consequently the correct weighted count is

$$
\mathcal N_m=\left(\sum_Q\sqrt{p_Q}\right)^2\le N_m,
\qquad
Z_{n,m}=2^{-m-2n(s-1)}\mathcal N_m.
$$

The discarded pin mass sums correctly at both selected levels: all descendants of a parent have total mass equal to that parent's mass. The radial exponent q, radial moment bound, and all selected centers are fixed once for this source–pin pair. No independence or re-selection across scales is used. Optimizing the truncation height gives the first-norm error bounded by a constant times

$$
Z_{n,m}^{\eta_q},\qquad \eta_q=\frac{q-1}{2q-1}>0.
$$

Summability makes a subsequence of the same positive probability densities converge in first norm. Uniform approximation of distance identifies the limit as the raw joint distance law. This establishes full absolute continuity of that law, rather than only a nonzero absolutely continuous component or convergence of separately chosen good parts.

For consecutive levels, replacing the weighted count by the occupied count yields the asserted sufficient series

$$
\sum_n\left[2^{-n(2s-1)}N_{n+1}\right]^{\eta_q}<\infty.
$$

The factor of one half from the successor scale is a harmless fixed constant. There is no additional factor n.

## 4. Sparse stopping scales and the logarithmic boundary

The sparse fragment also gives a valid proof from the earlier fixed-gamma comparison. Its translation estimate for shifts up to the square of the parent side length follows from the same Plancherel proof with arbitrary shift range; the fragment now states this explicitly. The newer frequency-band theorem gives the sharper rate when the count at the selected depth is at most a constant times the exponential of d times that depth:

$$
Z_{n,m}\le C2^{-(d-1)(2n-m)}.
$$

Both comparisons require the same qualitative summability of positive curvature gaps. For the homogeneous branching construction with lower barrier dn and upper barrier Dn minus a sublinear function ell, write a for a lower stop, b for the next upper stop, and m for the following lower stop. The stopping identities give

$$
(2-D)b=(2-d)a-\ell(b)+O(1),\qquad
dm=Db-\ell(b)+O(1).
$$

Elimination gives the exact asymptotic recurrence

$$
m=\kappa a-\frac{2\ell(b)}{d(2-D)}+O(1),
\qquad \kappa=\frac{D(2-d)}{d(2-D)}.
$$

When D is strictly below four d divided by d plus two, this ratio is strictly between one and two. At equality the ratio is two. The choice

$$
\ell(b)=A\log_2(b+1),\qquad A>0,
$$

then gives

$$
2a-m=\frac{2A}{d(2-D)}\log_2(a+1)+O(1).
$$

The stopping depths grow geometrically. Thus any fixed positive power of their reciprocal is summable over the stopping index. Every positive choice of A suffices; no lower threshold depending on q is missing.

## 5. Construction, hereditary obstruction, and scope

The first-crossing and first-catching construction terminates because the upper slope is strictly below two. Its lower barrier proves the d-Frostman bound; lower-stop covers prove finite positive critical Hausdorff measure. Common forced-zero digit levels remove dyadic endpoint ambiguity. The peak counts and equal cylinder masses force every positive-mass subset to have upper box dimension at least D, proving packing dimension D by the countable-cover characterization.

There is no branching from an upper stop to the following lower stop, whose depth ratio tends to D divided by d. Covers at the upper stop transfer with the same number of cells to the lower stop. This proves for every subset, without a measurability restriction,

$$
\dim_H S\le\frac dD\dim_P S.
$$

All construction and exponent statements in the sparse fragment follow from these facts. Restrictions to compact balls preserve the count upper bounds and Frostman properties up to constants. A countable family of separated products covers all unequal source–pin pairs, and the diagonal has zero pair mass. This justifies the stated arbitrary prescribed Frostman pin probability, including natural self-pins.

At the explicit pair

$$
d=\frac{21}{20},\qquad D=\frac65,
$$

the stopping ratio is nineteen fourteenths and the sparse threshold is eighty-four sixty-firsts. These numbers are consistent. For every subset with Hausdorff dimension greater than one, the hereditary inequality excludes the manuscript's previous strict low-branch condition. The logarithmic construction also reaches the sparse boundary at the same Hausdorff dimension.

This is a geometric class with a favorable recurrence of covering scales. It does not show that the dimension pair alone forces that recurrence. The zero-gauge construction can simultaneously have finite positive critical Hausdorff and packing measures and fail every all-scale critical covering extraction, as shown in `research/2026-09-30-critical-measure-gauge-extraction-obstruction.md`. The positive sparse conclusion and that extraction obstruction are compatible. The boundary logarithmic construction is not being assigned the zero-gauge construction's finite positive critical packing-measure conclusion.

## 6. The exact positive kernel and arbitrary-level energy criterion

The subsequently appended spatial refinement also passes independently. Inserting the Gaussian identity before the Frostman estimate gives a positive spatial kernel comparable to

$$
\sum_{R\in2^{\mathbb Z}}
R\min\{1,(\delta R)^2\}e^{-cR^2u^2},
\qquad u=|x-x'|>0.
$$

For u at most delta, dropping the minimum gives an upper bound of order the reciprocal of u. For u larger than delta, replacing the minimum by the squared product gives an upper bound of order delta squared divided by u cubed. Both estimates follow from rescaling the corresponding dyadic Gaussian sum. A single dyadic frequency comparable to the reciprocal of u gives the matching lower bound in both regimes. Therefore the exact positive kernel is, up to fixed multiplicative constants,

$$
k_\delta(x-x')=
\min\{|x-x'|^{-1},\delta^2|x-x'|^{-3}\}.
$$

Finite first energy removes the product-measure diagonal and dominates this kernel, making the Gaussian integral and all required conditional energies finite. Positivity permits Tonelli without cancellation concerns. The coordinate estimate uses only the first Gaussian inequality from Section 1, so no Frostman assumption re-enters this refinement.

With the notation

$$
J_\delta(\lambda)=\iint k_\delta(x-x')\,d\lambda(x)d\lambda(x'),
$$

the band proof yields the retained conditional squared second-norm error bounded by a constant times A times the sum of the energies at scales rho omega and the shift range. For the coherent maps these scales are at most a constant times the square of the parent side length. Monotonicity and the elementary inequality

$$
J_{C\delta}(\lambda)\le\max\{1,C^2\}J_\delta(\lambda)
$$

then give the coefficient stated in the manuscript:

$$
W_{n,m}=2^{-m}
\left[\sum_{Q\text{ at level }m}
p_QJ_{2^{-2n}}(\mu_Q)^{1/2}\right]^2.
$$

The support-union estimate, conditional mass weights, and bad-pin aggregation are the same as in Section 3. Thus summability of a fixed positive power of these coefficients along selected levels gives the claimed raw absolute continuity. The proposition explicitly assumes the fixed radial exponent, moments, and centers; it does not incorrectly infer these data from finite first energy alone.

For a source Frostman exponent between one and two, direct spatial integration gives

$$
J_\delta(\mu_Q)\le\frac{C_sC_\mu}{p_Q}\delta^{s-1}.
$$

The inner integral converges because s exceeds one, while the outer kernel integral converges because s is below three. Substitution recovers the preceding weighted count bound. The lower bound from source pairs at separation at most delta is also correct, since the kernel there is the reciprocal-distance kernel and is at least the reciprocal of delta. This refinement retains close pairs; the manuscript properly leaves open any further deduction from dimensions alone.
