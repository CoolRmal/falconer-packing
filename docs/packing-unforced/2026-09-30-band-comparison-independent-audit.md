# Independent audit of the frequency-band positive comparison

30 September 2026. Read-only audit of [packing-unforced-band-comparison.tex](packing-unforced-band-comparison.tex), including its selected-level theorem, consecutive-level corollary, and subsequently appended positive-kernel criterion. This audit checks the new estimate rather than assuming earlier internal audits certify it. No substantive defect was found in these statements.

## Gaussian estimates and angular coupling

For a probability λ with s-Frostman constant K, 1<s<2, the Gaussian Fourier identity gives

$$
E_R(\lambda)\le C_s K R^{2-s}\qquad(R>0).
$$

This uses the Frostman estimate at every spatial radius, including the low-frequency case. For each signed coordinate measure x_kλ the spatial Gaussian kernel remains nonnegative, so taking the absolute value of x_kx'_k before integration proves

$$
E_R(x_k\lambda)\le C\rho^2 E_R(\lambda).
$$

This does not use a false comparison of sharp-annular Fourier energies. A fixed multiple of the Gaussian radius dominates the sharp annulus used in the band estimate.

Polar coordinates give the R^{1-s} angular band energy and the Kρ²R^{3-s} angular derivative energy. The angular derivative contributes one factor R before squaring. For a coupled angular law with first marginal bounded by A times arclength, the fundamental theorem of calculus gives

$$
\int\|U_R(\theta)-U_R(\phi)\|_2^2\,d\kappa
 \le CA\omega^2\|\partial_\theta U_R\|_2^2.
$$

Indeed the first pointwise factor is ω, and after Fubini the set of angular starting points whose ω-neighborhood contains a fixed point has length O(ω). The alternative energy bound uses both marginals. Thus their minimum is valid without angle independence:

$$
CAK\min\{1,(\rho\omega R)^2\}R^{1-s}.
$$

Likewise the scalar shift can depend arbitrarily on the same pin: its Fourier multiplier bound is pointwise in that pin and only requires |v|≤v₀.

## Summing bands

The scalar multipliers have sum of squares one away from frequency zero. Therefore the squared norm of the complete difference is exactly the sum of the band squared norms, although different bands need not have disjoint supports. This is a Plancherel identity and does not require orthogonality of a sum of band outputs. A pin-dependent scalar translation preserves each scalar frequency localization.

The geometric sum

$$
\sum_{R\in2^{\mathbb Z}}\min\{1,(\delta R)^2\}R^{1-s}
 \le C_s\delta^{s-1}
$$

has positive low-frequency exponent 3−s and negative high-frequency exponent 1−s. It is finite without a logarithm. Zero angular or scalar displacement contributes zero directly. Finite I₁ follows from s>1; thus the needed projection densities and single marginal null sets exist.

These checks establish the printed bound

$$
\int\|F(\theta)(\cdot-v)-F(\phi)\|_2^2\,d\kappa
 \le CAK\big((\rho\omega)^{s-1}+v_0^{s-1}\big).
$$

## Arbitrary-level application and mass weights

For levels n<m, put r=2^{-n}, h=2^{-m}. The common conditional source in a depth-m square has support diameter Ch and Frostman constant C/p_Q. The two parent/child directions differ by Cr, and their recentered scalar constants differ by Cr². This agrees with the actual positive affine maps from the coherent source proof.

After angular clipping, the integrated squared conditional difference is therefore bounded by

$$
CAp_Q^{-1}\big((hr)^{s-1}+r^{2s-2}\big)
 \le CAp_Q^{-1}r^{2s-2}.
$$

For each pin the two affine-density supports lie in two intervals, each of length Ch. Their union has measure at most 2Ch even when their gap is much larger than h. Thus first-norm Cauchy–Schwarz contributes h^{1/2}, with no condition m≤2n.

After multiplying by p_Q and summing, the retained contribution is exactly bounded by

$$
CA^{1/2}h^{1/2}r^{s-1}\sum_Q\sqrt{p_Q}.
$$

The discarded pin mass is handled before this summation. Fine angular costs sum with p_Q, and all descendant weights of one coarse parent sum to that parent's weight. Both costs are bounded by the same fixed averaged radial moment B. The resulting bound is

$$
\|f_m-f_n\|_1\le C(AZ_{n,m})^{1/2}+CB A^{1-q},
\quad
Z_{n,m}=2^{-m-2n(s-1)}
 \left(\sum_{\text{depth }m}\sqrt{p_Q}\right)^2.
$$

Cauchy–Schwarz gives the stated occupied-square upper bound, since the p_Q sum to one.

## Limit and scope

For η_q=(q−1)/(2q−1), optimizing A gives a constant times Z^{η_q}. The selected-level summability makes the same fixed sequence of positive mass-one affine densities Cauchy in the joint first norm. Uniform Taylor error identifies its limit with the actual joint law; disintegration then gives raw pinned absolute continuity for almost every prescribed pin.

At consecutive levels m=n+1 the constant factor 2^{-1} is harmless, and the sufficient occupied-count summand is

$$
\left[2^{-n(2s-1)}N_{n+1}\right]^{\eta_q}.
$$

There is no factor n. The polynomial covering deficit condition aη_q>1 is correct after shifting n to n+1. This genuinely weakens the earlier variable-exponent covering test. It does not establish a new sufficient condition in terms of the two dimensions alone.

## Addendum: exact positive kernel

The subsequently appended Gaussian kernel sum is comparable to

$$
k_\delta(z)=\min\{|z|^{-1},\delta^2|z|^{-3}\}.
$$

For |z|≤δ, dropping the cutoff gives the upper bound C/|z|. For |z|>δ, replacing the cutoff by (δR)² gives Cδ²/|z|³. In either case one dyadic R comparable to |z|^{-1} gives the matching lower bound. Positivity justifies Tonelli, and finite first energy removes the diagonal.

Before applying Frostman estimates, the bandwise angular and translation arguments use precisely this positive Gaussian sum. Thus the refinement to J_δ holds, including arbitrary dependent angles and shifts. In the arbitrary-level comparison both scale parameters are bounded by Cr², and monotonicity plus J_{Cδ}≤max(1,C²)J_δ permits the displayed coefficient

$$
W_{n,m}=2^{-m}\left(\sum_Qp_Q\sqrt{J_{2^{-2n}}(\mu_Q)}\right)^2.
$$

The first-norm convergence proof is unchanged. The near-pair lower bound and the Frostman estimate J_δ(μ_Q)≤C_s C_μ p_Q^{-1}δ^{s−1} are also correct. These additions introduce no defect found in this audit.
