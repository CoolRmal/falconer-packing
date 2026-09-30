# Subquadratic norms for the profile decomposition: a regularity gain and a threshold obstruction

Date: 2026-09-30. This note studies the actual good/bad threshold tradeoff in the finite-profile argument. It proves an elementary weak-norm interpolation lemma, derives a stronger integrability conclusion under the already established strict criterion, and shows why this interpolation does not weaken that criterion. It also calculates the exact train-track obstruction for raw joint weak norms. No new sufficient dimension curve is claimed.

## 1. An elementary parameterized decomposition lemma

Let a measurable function F on a measure space satisfy

$$
\|F\|_1\le1.
$$

Suppose that for every parameter Λ at least one there is a decomposition into measurable functions satisfying

$$
F=G_\Lambda+B_\Lambda,
\qquad \|B_\Lambda\|_1\le\Lambda^{-\gamma},
\qquad \|G_\Lambda\|_2^2\le A\Lambda^K,
\tag{1}
$$

where A and γ are positive and K is positive. Set

$$
\theta=\frac\gamma{K+\gamma},\qquad
p=1+\theta=\frac{K+2\gamma}{K+\gamma}.
\tag{2}
$$

Then

$$
\sup_{t>0}t^p\,m\{|F|>t\}\le C_{K,\gamma}A^\theta.
\tag{3}
$$

In particular the usual weak Lebesgue quasinorm obeys

$$
\|F\|_{L^{p,\infty}}\le C_{K,\gamma}A^{\gamma/(K+2\gamma)}.
\tag{4}
$$

**Proof.** If t is at most A, Markov's inequality gives

$$
t^pm\{|F|>t\}\le t^{p-1}\le A^\theta.
$$

If t is larger than A, choose

$$
\Lambda=(t/A)^{1/(K+\gamma)}.
$$

Chebyshev for the two pieces, with the threshold t/2, gives

$$
m\{|F|>t\}\le4A\Lambda^Kt^{-2}+2\Lambda^{-\gamma}t^{-1}
=6A^\theta t^{-p}.
$$

This proves (3). No positivity, nesting of the good parts, Fourier multiplier theorem, or reverse Hausdorff--Young inequality is used. Fixed multiplicative constants in the assumptions merely change the conclusion's constant.

The same proof works with parameters only in the interval from one to a finite upper bound, provided that upper bound is at least

$$
\max\{1,(\|F\|_\infty/A)^{1/(K+\gamma)}\}.
\tag{5}
$$

This finite version is useful when the decomposition has rapidly decreasing localization errors.

For the one-threshold estimate

$$
\|B_H\|_1\le J/H,\qquad \|G_H\|_2^2\le HE,
\qquad H\ge J,
$$

put Λ equal to H/J. Then γ and K both equal one, A equals JE, and the conclusion is weak membership at exponent three halves, with quasinorm at most a constant times the cube root of JE. The decisive frequency power is the product JE.

## 2. Radial projection tails and the actual finite-profile estimates

Let q be the exponent greater than one supplied by the radial-projection input in the existing finite-profile proof. Fix its regularized pin components, their spatial chains, and a common upper bound K for their numbers of edges. These are fixed at each frequency before varying the thresholds.

The two deletion estimates before choosing their thresholds have the schematic but explicit form

$$
\mathrm{BadMass}\lesssim B L^{1-q}+L\sum_{j<K}\frac{J_j}{H_j},
\tag{6}
$$

apart from the already specified regularization and geometric enlargement powers. Here B is the averaged qth angular norm and J_j is the conditional pair-energy bound. Multiplying every pin threshold by Λ and the source angular threshold by Λ to the power one over q changes both terms by the same factor

$$
\Lambda^{-\gamma},\qquad \gamma=\frac{q-1}{q}>0.
\tag{7}
$$

Indeed the first term changes by Λ to the power (1−q)/q; the second changes by Λ to the power 1/q−1. This uses only the two deletion estimates already proved in the manuscript. Source-heavy directions remain an auxiliary device for estimating deletion; no new non-smooth spatial cutoff is introduced.

At each Fourier inflation step there is one pin-threshold factor. Multiplying at most K such factors changes the squared good norm by at most Λ to the power K. Consequently, if the chain cost is strictly less than the source-energy allowance, write

$$
\mathcal C<s-1,
$$

and choose the existing small parameters so that all fixed power losses leave a number κ greater than zero. For the full annular pinned density F_R and its modified good density one obtains

$$
F_R=G_{R,\Lambda}+B_{R,\Lambda},
\quad
\|G_{R,\Lambda}\|_2^2\le C R^{-\kappa}\Lambda^K,
\quad
\|B_{R,\Lambda}\|_1\le C R^{-c}\Lambda^{-\gamma}
 +C R^{-\epsilon_{\rm reg}}+\operatorname{RapDec}(R).
\tag{8}
$$

Here the positive number ε_reg is the exponent of the discarded pin mass in finite regularization. On that remainder the good function is zero at every threshold, so its contribution has no Λ decay. It must be retained explicitly. All norms here are over the joint pin and distance variables. Constants are uniform for Λ in any fixed polynomial range in R, after choosing the localization error orders sufficiently large. The component weights sum to one, as in the original proof, so no component-count factor appears.

Here is why that stated uniformity is enough and why it does not impose a new analytic assumption. Increasing the thresholds only changes which of the fixed standard packets are retained. Their number and global derivative bounds are polynomial in R uniformly over every subset. The Fourier identities and selected-label inflation estimate are valid at each such threshold. Multiplying the finitely many inflation factors by parameters in a fixed polynomial range merely increases the polynomial multiplying an error term. Choosing more integration-by-parts decay absorbs this. The same fixed source packet decomposition and the same regularized spatial chains are used for all these parameters.

The full annular density has

$$
\sup_y\|F_R(y,\cdot)\|_1\le C_T,\qquad \|F_R\|_1\le C_T,\qquad \|F_R\|_\infty\le C_T R^2.
\tag{9}
$$

The first estimate follows from the annular kernel's first norm and contraction of total variation under pushforward. For the last, the spatial annular kernel is bounded by a constant times R squared; integrating its bounded density over a circle in the fixed bounded source-pin region gives the same upper bound for the scalar radial density. The fixed spatial cutoff does not change these estimates.

Let Ω_R be the union of the retained regularization components in the pin variable, and split the whole annular density as

$$
F_R=F_R^{\rm reg}+F_R^{\rm rem},\qquad
F_R^{\rm reg}=\mathbf1_{\Omega_R}(y)F_R,
\quad
F_R^{\rm rem}=\mathbf1_{\Omega_R^c}(y)F_R.
$$

On Ω_R the discarded-mass term in (8) is absent. Choose a polynomial range Λ at most R to the power M, with

$$
M>\frac{2+\kappa}{K+\gamma}+1.
$$

It contains every parameter needed by (5) and (9) for the regular-region function. Choose all localization error orders large enough that their first-norm contribution is at most R to the power minus Mγ minus one on that range. Their contribution is then bounded by Λ to the power minus γ. The decaying first term of the bad bound has the same property. Applying (1), with fixed multiplicative constants absorbed, gives

$$
p_0=\frac{K+2\gamma}{K+\gamma}>1,
\qquad
\|F_R^{\rm reg}\|_{L^{p_0,\infty}}
\le C R^{-\kappa\gamma/(K+2\gamma)}.
\tag{10}
$$

The omitted region must be handled separately. Its pin measure is at most a constant times R to the power minus ε_reg. The full annular first norm and supremum in (9) imply

$$
\|F_R^{\rm rem}\|_1\le C R^{-\epsilon_{\rm reg}},
\qquad
\|F_R^{\rm rem}\|_\infty\le C R^2.
$$

Consequently, for every p greater than one,

$$
\|F_R^{\rm rem}\|_p
\le C_p R^{[2(p-1)-\epsilon_{\rm reg}]/p}.
\tag{11}
$$

This is the direct inequality obtained by bounding p−1 powers of the integrand by its supremum and integrating the remaining factor.

### A genuine regularity consequence

Under the existing strict finite-profile measure criterion, the actual joint pinned distance law has a density in every strong Lebesgue space with exponent

$$
1<p<\min\left\{p_0,1+\frac{\epsilon_{\rm reg}}2\right\}.
\tag{12}
$$

In particular at least one exponent greater than one is available. The exponent depends on the chosen regularization loss as well as on the radial-projection exponent and the number of chain edges.

To verify summation explicitly, let V be the finite measure of the common pin-distance region. If a function has weak p_0 quasinorm Q, then integrating the bound

$$
m\{|F|>t\}\le\min\{V,Q^{p_0}t^{-p_0}\}
$$

gives, for p strictly below p_0,

$$
\|F\|_p\le
\left(\frac{p_0}{p_0-p}\right)^{1/p}
V^{1/p-1/p_0}Q.
\tag{13}
$$

Thus (10), (11), and (12) give

$$
\|F_R\|_p\le C_p R^{-c_p},\qquad
c_p=\min\left\{
\frac{\kappa\gamma}{K+2\gamma},
\frac{\epsilon_{\rm reg}-2(p-1)}p
\right\}>0.
\tag{14}
$$

The geometric annular sequence makes the right side summable. The shell series therefore converges in the strong pth norm and, by Hölder on the bounded product region, also in the first norm. The original distributional reconstruction identifies its limit, after adding the smooth low-frequency density, with the positive joint distance law. Fubini then gives a pth-power integrable pinned density for almost every pin.

For later use, the same elementary layer-cake argument also gives the restricted-set inequality

$$
\int_A|F|\le\frac{p_0}{p_0-1}
\|F\|_{L^{p_0,\infty}}\,m(A)^{1-1/p_0}.
\tag{15}
$$

An earlier draft mistakenly dropped the fixed discarded-pin term in (8) and asserted weak p_0 for the entire shell series. The independent audit identified that omission. Only (10) for the regularized region and the complete strong range (12) for the full law are established here.

This strengthens the integrability conclusion of the finite-profile branch but does not improve its dimension threshold. It is compatible with the failure of a raw quadratic bound for some prescribed source probabilities.

## 3. Why interpolation retains the old threshold

Before using strictness, the squared good estimate's leading factor is

$$
A_R=R^{\mathcal C-(s-1)+\eta},
\tag{16}
$$

where η is an arbitrarily small fixed positive loss. Formula (4) raises this factor to a strictly positive power. Its sign is unchanged. Thus the resulting shell norms decay precisely when the same strict condition can absorb η.

This limitation is sharp for the abstract data (1). For any A at least one, on a unit interval take

$$
F_A=A\mathbf1_{[0,1/A]}.
$$

It has first norm one and squared second norm A. Taking the entire function as the good part and zero as the bad part satisfies (1) for every Λ. But

$$
\|F_A\|_{L^{p,\infty}}^p=A^{p-1}=A^\theta
$$

for the exponent (2), exactly matching the power in (3). As A grows, no uniform weak norm of any fixed exponent greater than one follows from (1). At a zero shell exponent, the earlier compact null-support example with uniformly bounded orthogonal increments still prevents a conclusion from shell bounds alone.

This is a limitation of these stated estimates. It is not a theorem excluding a different subquadratic argument.

## 4. Higher pin-tube moments using only maximum mass cannot reduce the profile cost

Consider one ideal regular edge with depth endpoints m less than n, put

$$
\ell=n-m,\qquad \rho=2^{-\ell},\qquad
c=g(m)-\min_{[m,n]}g.
$$

Let λ be the normalized conditional pin probability in its parent cube, and let the tubes have width equal to the child scale and length equal to the parent scale. Suppose the usual tube-pair bound is

$$
J_2=\sum_T\lambda(T)^2\lesssim2^c.
$$

A tube can be covered by a constant times the reciprocal of ρ child-scale cubes. Their masses are controlled by regularity. Along with the trivial mass bound this gives

$$
\frac{\max_T\lambda(T)}\rho\lesssim2^{d_*},
\qquad
d_*=\min\{\ell,\ \ell+g(m)-g(n)\}.
\tag{17}
$$

The regularization and enlargement errors in the actual proof only add its already accounted small powers.

For any moment exponent r at least two, writing the maximum tube mass as M gives

$$
\sum_T\lambda(T)^r\le M^{r-2}J_2.
$$

On tubes with mass larger than Hρ, the retained source mass is at most a constant times Lρ. Therefore the heavy-pair estimate obtained from this higher moment is

$$
\mathrm{BadMass}\lesssim
L\rho(H\rho)^{1-r}\sum_T\lambda(T)^r
\lesssim L H^{-(r-1)}2^{c+(r-2)d_*}.
\tag{18}
$$

The effective base threshold exponent is consequently

$$
c_r=\frac{c+(r-2)d_*}{r-1}.
\tag{19}
$$

Both entries in the minimum defining d_* are at least c. The first comparison follows from the Lipschitz bound on the drop. For the second, if z minimizes g on the edge, then

$$
\ell+g(m)-g(n)-c
=\ell+g(z)-g(n)\ge\ell-(n-z)\ge0.
$$

Thus d_* is at least c and c_r is at least c. The improvement in the tail's power is paid for by a base threshold no smaller than the original one. Applying the radial-projection optimization after this step changes the weak integrability exponent, not this inequality. A genuine higher-moment gain must therefore use more than the second moment and the deterministic maximum-mass bound.

## 5. The train-track obstruction at general weak exponents

Use the finite-scale configuration proved in `2026-09-30-off-cluster-collision-obstruction.md`, with

$$
1<s<4/3,\qquad 3-2/s\le u\le2.
$$

At width δ, every pin has a same-track source submeasure of mass comparable to

$$
\beta_\delta=\delta^{(s-1)/2}.
$$

Its pinned distances are contained in a union of a constant times δ to the power minus s over two intervals, each of length a constant times δ. After convolution at a fixed multiple of δ with a compactly supported probability mollifier, this submeasure is still supported on a set of length at most

$$
V_\delta=C\delta^{1-s/2}.
$$

The pin-dependent unions can be chosen Borel: there are only finitely many track and slat labels at each scale. On the joint pin-distance space they therefore give a measurable set of measure at most V_δ carrying mass at least a constant times β_δ of the full positive mollified law.

For any exponent p greater than one, the restricted-set estimate (15), used in reverse, gives

$$
\|h_\delta\|_{L^{p,\infty}}^p
\gtrsim_p\frac{\beta_\delta^p}{V_\delta^{p-1}}
\asymp
\delta^{\,1-s/2+p(s-3/2)}.
\tag{20}
$$

The same lower bound holds for the strong pth moment by Hölder. Hence the finite-scale raw weak norm diverges whenever

$$
p>p_{\rm track}(s):=\frac{2-s}{3-2s}.
\tag{21}
$$

For s strictly between one and four thirds this critical exponent lies strictly between one and two. At p equal to two, (20) reduces to the previously proved exponent three s over two minus two. For p below (21), this particular track term no longer forces divergence; this is not an upper bound for the other interactions.

### A fixed-measure obstruction

Use the fixed gluing from the cited note: block scale λ_j proportional to two to the power minus j, block mass w_j proportional to λ_j to the power s, and internal track resolution δ_j equal to two to the power minus a quadratic polynomial in j. At smoothing width a fixed multiple of λ_jδ_j, restrict pins and source points to corresponding translated blocks.

The joint mass captured by the corresponding track-distance unions is at least a constant times

$$
w_j^2\delta_j^{(s-1)/2},
$$

whereas their measure in the joint reference space is at most a constant times

$$
w_j\lambda_j\delta_j^{1-s/2}.
$$

Thus

$$
\|h_j\|_{L^{p,\infty}}^p
\gtrsim_p
w_j^{p+1}\lambda_j^{1-p}
\delta_j^{\,1-s/2+p(s-3/2)}.
\tag{22}
$$

For p satisfying (21), the negative δ exponent dominates the fixed exponential block factors. These norms tend to infinity. The actual fixed joint law therefore has no weak density of that exponent: if it did, convolution in the distance variable with a probability mollifier would preserve its restricted-set bound uniformly. To check this last statement directly, translate a test set in the distance variable, apply (15) to each translate, and average against the mollifier. Its reference measure is unchanged by translation.

The fixed construction still has the Frostman and covering properties proved in the original note; its source and pin supports are separated. Radial projection therefore supplies some exponent greater than one as in the existing analytic proof. This demonstrates that merely adding qualitative angular integrability does not eliminate all raw weak-norm obstructions. It does not rule out an exponent closer to one, a positive good-part selection, or another source probability supported on the same set.

## Scope

The proved new gain is higher-than-first-power integrability of the raw joint distance density under the already certified strict finite-profile condition. The exact threshold tradeoff, deterministic higher-moment calculation, and fixed train-track lower bounds identify why the presently available estimates do not yield a weaker Hausdorff–packing inequality through this interpolation alone. A new estimate must alter the frequency power or supply cancellation/nonconcentration not encoded in these inputs.
