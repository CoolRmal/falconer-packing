# Variable-exponent coherent endpoint: independent analytic audit

Date: 2026-09-30. This note checks the proposed endpoint use of `output/pdf/packing-bound-original-branch.tex`. It proves a quantitative covering criterion under an ordinary critical Frostman bound. It does not replace a strict dimension inequality by a non-strict inequality without further hypotheses.

## 1. Precise statement

Let the source probability and pin probability be compactly supported and positively separated in the plane. Assume the source satisfies the ordinary estimate

$$
\mu(B(x,r))\le C_\mu r^d,
\qquad 1<d<2,
$$

and the pin probability has a Frostman exponent greater than one. Let the number of source dyadic squares of positive mass at depth n be the following quantity, and put

$$
N_n=\#\{Q\in\mathcal D_{2^{-n}}:\mu(Q)>0\},
\qquad D=2d-1.
$$

Fix an available averaged radial-projection exponent and the exponent from the existing coherent comparison:

$$
q>1,\qquad
\eta_q=\frac{q-1}{2q-1}>0.
$$

Then

$$
\boxed{\quad
\sum_{n\ge n_0}
\left(n\,2^{-nD}N_{n+1}\right)^{\eta_q}<\infty
\quad}
\tag{1}
$$

implies absolute continuity of the actual joint law of pin and distance relative to the product of pin measure and radial Lebesgue measure. In particular the original source pinned law is absolutely continuous for almost every pin.

This conclusion concerns the original positive source probability. No microlocal source modification or source logarithmic Frostman improvement is used.

## 2. The approximation does not depend on the analytic exponent

Use the existing radial moment

$$
B=\int\|\rho_x\|_q^q\,d\mu(x)<\infty,
\qquad (\Theta_x)_*\nu=\rho_x\,d\theta.
$$

For every occupied dyadic node choose a source center with

$$
F_Q:=\|\rho_{x_Q}\|_q^q
\le\frac2{\mu(Q)}\int_Q\|\rho_x\|_q^q\,d\mu(x).
$$

These choices depend only on the measures and this fixed radial exponent. They do not use the angular Sobolev exponent. The positive affine maps

$$
L_Q(x,y)=\Theta_{x_Q}(y)\cdot(x-y)
$$

and their joint densities at each source depth are consequently fixed once and for all. Varying the analytic exponent in the estimate for consecutive densities does not vary either density being compared.

The conditional source probabilities have finite first energy. Their affine projections have densities for almost every angle, and each chosen center's angular pin law is absolutely continuous. All exceptional sets can be removed simultaneously over countably many nodes and the countable sequence of analytic exponents. The Radon–Nikodym densities of the affine laws may be chosen independently of those exponents.

## 3. Uniformity of the angular constants

For sufficiently large n set

$$
a_n=d-\frac1n,
\qquad
\gamma_n=\frac{a_n-1}{2}.
$$

For example, once n is at least two divided by d minus one,

$$
\frac{d-1}{4}\le\gamma_n<\frac{d-1}{2}<\frac12.
$$

Thus the exponents lie in a fixed compact subinterval of the permitted open interval. Inspecting the angular comparison proof gives uniform constants:

- The Riesz Fourier identity constants are continuous and bounded when the energy exponent stays in a compact subinterval of the interval from one to two.
- Angular Sobolev interpolation has constant one in the Fourier-series formulation.
- The fractional difference integral is uniformly bounded by the relevant angular Fourier weight on the same compact exponent interval; its small and large increment integrals are bounded by constants depending only on that interval.
- Averaging the two-angle triangle inequality and the elementary translation multiplier estimate have uniformly bounded constants there.
- The fixed geometry and separation constants raised to these exponents remain bounded.

No constant proportional to n is introduced by this angular part. The only necessary n factor in the ensuing estimate comes from approaching the source energy exponent d.

## 4. Conditional energy at the varying exponent

Let a child square have diameter at most a fixed multiple of the parent scale

$$
r=2^{-n},\qquad p_Q=\mu(Q),\qquad \mu_Q=p_Q^{-1}\mu|_Q.
$$

Layer cake and the source Frostman estimate, for every source point in that square, give

$$
\begin{aligned}
\int_Q|x-x'|^{-a_n}\,d\mu(x')
&\le C r^{d-a_n}
 +C a_n\int_0^{Cr}t^{d-a_n-1}\,dt\\
&\le C n r^{1/n}.
\end{aligned}
$$

All fixed diameter constants raised to these bounded exponents are absorbed uniformly. Integrating over the first source point and dividing by the square of the node mass yields

$$
p_Q I_{a_n}(\mu_Q)\le C n r^{1/n}.
\tag{2}
$$

Define the energy expression in the coherent comparison using the varying exponent:

$$
Z_n=r^{1+4\gamma_n}
\sum_{Q\text{ at depth }n+1}p_QI_{a_n}(\mu_Q).
$$

Since

$$
1+4\gamma_n=2a_n-1,
\qquad
r^{2a_n-1+1/n}
=r^{2d-1-1/n}=2\,2^{-nD},
$$

equation (2) proves the required quantitative bound

$$
\boxed{Z_n\le C n\,2^{-nD}N_{n+1}.}
\tag{3}
$$

## 5. Telescoping remains valid

The uniform angular comparison supplies, for the same positive affine densities and every cutoff level at least one,

$$
\|f_{n+1}-f_n\|_1
\le C(AZ_n)^{1/2}+CB A^{1-q},
$$

with one constant independent of n. Enlarge B to at least one. Under (1), equation (3) tends to zero, so for all sufficiently large n the usual optimized choice is legal:

$$
A_n=(B/\sqrt{Z_n})^{1/(q-1/2)}\ge1.
$$

It gives

$$
\|f_{n+1}-f_n\|_1
\le C B^{1/(2q-1)}Z_n^{\eta_q}.
$$

The right side is summable by (1). An initial affine density is integrable and all have mass one, so the sequence converges in the first norm to a positive density of mass one. Uniform affine approximation to distance identifies the weak measure limit with the original joint law. This proves the statement.

## 6. Consequences and exact scope of the endpoint gain

The covering margin

$$
N_n\le C2^{nD}\exp(-c\sqrt n),\qquad c>0,
\tag{4}
$$

satisfies (1) for every positive exponent. Indeed the harmless shift by one in depth gives

$$
n2^{-nD}N_{n+1}
\le C' n\exp(-c\sqrt{n+1}),
$$

whose every positive power is summable. More generally a polynomial margin with exponent strictly greater than one plus the reciprocal of the coherent summability exponent suffices.

Condition (4) is compatible with upper box and packing dimension equal to D: its logarithmic correction is negligible after division by depth. It is nevertheless strictly stronger than the assertion that packing dimension equals D. Packing dimension alone does not even imply this upper box count, much less its negative subpower margin.

If a compact set has exact dimensions

$$
\dim_H E=d,\qquad\dim_P E=D=2d-1,
\qquad
1<d\le d_\alpha:=\frac{7-\sqrt7}{4},
$$

then its dimension pair lies on the excluded boundary of the manuscript's current curve, because in this range

$$
B_{\rm H}(d)=2d-1=D.
$$

The witness separately constructed in `research/2026-09-30-critical-covering-moran-examples.md` satisfies the ordinary critical Frostman estimate and (4), and therefore provides an additional endpoint class. Its construction and hereditary subset property are independently verified in Section 7 below. The latter check excludes applying the existing strict condition or regular-pin theorem to a better subset of these examples.

In particular, the verified witness property

$$
\dim_H A\le\frac dD\dim_P A
\qquad\text{for every }A\subset E
\tag{5}
$$

gives the intended comparison. For any subset of Hausdorff dimension a greater than one, it implies

$$
\dim_P A\ge\frac Dd a
=2a-\frac ad\ge2a-1=B_{\rm H}(a),
$$

because a is at most d and hence remains in the low branch. It also rules out positive-dimensional subsets with equal Hausdorff and packing dimensions. These consequences use the separately verified construction; they are not needed in the analytic criterion itself.

No pure non-strict packing-dimension theorem and no endpoint strong integrability exponent above one are established by this criterion.

## 7. Independent check of the fixed Moran witness

The construction is now supplied in `research/2026-09-30-critical-covering-moran-examples.md`. I independently checked it, including its all-subsets assertion. The following records the substantive points of that check; the construction itself remains in the companion note.

For the relevant parameter range, its upper and lower barriers are

$$
1<d\le\frac32,\qquad D=2d-1,\qquad
U(n)=Dn-A\sqrt{n+1},
$$

and the integer branching count has increments zero or two. Starting near the lower line, it grows at slope two until first crossing the upper barrier, then stays constant until the lower line catches it. The difference between the growing line and the upper barrier tends to infinity, even when D equals two: in that case the difference is a constant plus the positive square-root term. Thus every growing phase terminates. For large enough starting depth the barriers are separated by more than ten, so both phase types have positive length.

The first-crossing overshoot is less than two. The lower-line catch overshoot is less than d. These facts prove throughout all later depths

$$
dn-2\le F(n)\le Dn-A\sqrt{n+1}+2.
$$

At consecutive growing and flat endpoints,

$$
F(a_j)=F(b_j),\qquad
da_j=Db_j-A\sqrt{b_j+1}+O(1),\qquad
\frac{a_j}{b_j}\longrightarrow\frac Dd.
$$

The planar dyadic construction keeps all four children when the increment is two, otherwise only the lower-left child. Infinitely many common forced-zero depths occur after every fixed depth. This excludes any admissible binary coordinate tail consisting entirely of ones, which is exactly the ambiguity that could place a symbolic cell's endpoint in the wrong half-open dyadic cell. Each cell therefore has the claimed probability mass

$$
2^{-F(n)},
$$

and there are precisely the claimed number of occupied cells. A ball meets only boundedly many cells at comparable depth. The lower barrier proves the ordinary d-Frostman bound. The low-endpoint covers have bounded d-dimensional Hausdorff cost, proving finite positive critical Hausdorff measure. The high-endpoint ball mass bound proves upper box dimension D for every subset of positive measure outer mass; a countable-cover argument then proves packing dimension D for the full set.

For completeness, the hereditary inequality has a short proof. Cover an arbitrary subset S by sets whose upper box dimensions are at most its packing dimension plus a fixed tolerance. At depth b_j, each such cover piece needs at most

$$
C2^{(\dim_P S+2\epsilon)b_j}
$$

dyadic cells. Between b_j and a_j there is no branching, so exactly the same number of cells at the much smaller final scale covers it. Its Hausdorff dimension is therefore at most

$$
\frac dD(\dim_P S+2\epsilon).
$$

Countable stability and letting the tolerance tend to zero establish (5), without a measurability restriction on S. Consequently the subset exclusions proved in Section 6 genuinely apply to these examples.

Finally, normalized positive restrictions to compact separated patches preserve both the ordinary Frostman estimate and the covering margin, with patch-dependent constants. Countably many separated rational-ball products cover the complement of the diagonal, whose pair mass is zero. Applying the endpoint criterion on every positive-mass product proves absolute continuity of the full raw self-pinned joint law. Thus the witness obtains positive-length pinned distances for almost every natural-measure pin, with no assumed logarithmic improvement of the source ball bound.

**Witness audit result:** no substantive defect found. Together with the analytic criterion, these examples provide a verified additional boundary class below the first branch transition; they do not settle the boundary for arbitrary sets having the same two dimensions.

## 8. Audit of the actual TeX criterion

I also checked `output/pdf/packing-unforced-critical-covering.tex` directly after its preparation. Its statements and proof agree with the verified argument above. In particular:

- The varying exponent is used only in estimating the same affine densities, with the countable exceptional-set issue explicitly addressed.
- Its layer-cake estimate includes both the finite-diameter boundary term and the critical denominator, and its displayed factor of two from the variable exponent is correct.
- The optimized angular cutoff gives the existing coherent summability exponent; it makes no claim that this exponent is optimal.
- The subpower covering margin works for every positive radial summability exponent. This is what allows separated restrictions to have different angular exponents in the removal of separation.
- Its theorem concerns the entire raw joint law, using countably many separated restrictions and the zero mass of the diagonal. The positive self-pinned conclusion then follows from probability disintegration.
- Its final paragraph explicitly distinguishes the covering information from equality of dimensions alone.

**TeX audit result:** no substantive error found. No manuscript or TeX source was edited in carrying out this audit.
