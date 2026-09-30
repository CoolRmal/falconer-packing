# Independent audit of the assembled unforced proof

30 September 2026. This audit freshly reads the complete assembled mathematical sources, rather than only the proposed auxiliary-cap modification:

- `output/pdf/packing-unforced-proof.tex`;
- `output/pdf/packing-unforced-finite-profile.tex`;
- `output/pdf/packing-unforced-profile.tex`;
- `output/pdf/packing-unforced-transfer.tex`;
- `output/pdf/packing-unforced-obstruction.tex`;
- the imported `output/pdf/packing-bound-original-branch.tex`.

The final check includes the explicit assignment $\mathcal C=C(s,u)$ in the transfer, matching its exponent to the profile estimate and the summation argument.

## Verdict and scope

I found no mathematical gap or incompatible hypothesis in the assembled argument, using the established analytic inputs explicitly named in the manuscript. In particular, the earlier need to integrate the auxiliary-cap proposal into a complete proof has now been met in the sources reviewed here. The profile cost, finite regularization, conditional energy, deletion thresholds, packet reconstruction, inflation, terminal estimate, shell summation, and Borel reduction use compatible parameters and objects.

This is an internal mathematical audit, not a Lean certificate or external refereeing. It does not establish optimality for distance sets. The manuscript correctly confines its sharpness claim to the high-slope profile problem.

## New low-slope unforced estimate

For $0<a\le b\le1/2$, the definitions

$$
q=\frac b{2b-a},\qquad r=2q-1=\frac a{2b-a}
$$

are legitimate since $2b-a\ge a>0$. They give $1/2<q\le1$ and $0<r\le1$.

The asserted zero-cost region follows from the exact implication

$$
n\le q
\quad\Longrightarrow\quad
b(2n-1)\le an\le g(n).
$$

Thus a leftmost minimum on the maximal admissible interval gives a strict decrease of the endpoint at zero cost. If $a=b$, the whole profile is linear and the stated cost is zero; if the initial endpoint lies below $q$, no paid initial segment is needed.

On $[r,1]$, the affine function

$$
H(z)=\frac z2+\left(b-\frac12\right)r
$$

majorizes $bz$. Its potential $\Lambda(x)=H(2x-1)-g(x)$ is nondecreasing for $x\ge q$, with $\Lambda(q)\le0$. The derivative inequality

$$
(-g')_+\le\frac{1-g'}2
$$

holds for every derivative value in $[-1,1]$. Therefore the paid part costs at most $\Lambda(1)/2$. The subsequent zero-cost construction either stays above $q$, where the affine majorant applies, or enters the already verified zero-cost region below $q$.

The final algebra is correct:

$$
\frac{H(1)-a}{2}
=\frac{(b-a)(1-a)}{2(2b-a)}.
$$

The high-slope estimate, the uniform logarithmic edge bound, zero-cost merging, continuous compactness limit, and grid perturbations are compatible with this argument. Repeated endpoints arising in a compactness limit can be removed. Uniform perturbation by $\epsilon N$ changes each edge cost by at most $2\epsilon N$, so the stated $O(K\epsilon N+KT)$ allowance is appropriate.

## Exact connection between profile and regularization

The component profiles satisfy $g_i=f_i-\mathrm{id}$ with slopes in $[-1,1]$. Their approximate barriers are $(s-1)k$ and $(u-1)k$, so the substitution

$$
a=s-1,\qquad b=u-1
$$

matches the profile lemma. The selected chain starts on the block grid near $(1-\zeta)N$ and has $K\le K_0$ independent of $N$ and the component. All profile rounding and barrier losses fit the existing $CK\Gamma N+C_{T,K}$ allowance.

The conditional-energy estimate uses the actual original restricted component, not the terminal-cube-smoothed measure. Coarser cube masses agree, which is exactly the information required. Intermediate radii can be estimated at adjacent block-grid radii with a factor depending on the fixed block size $T$; this does not add a frequency exponent.

The denominator in the conditional probability on $Q^+$ is bounded below by the mass of the original active cube $Q$. Consequently the enlargement introduces only the recorded small-power geometric losses, not a hidden regularity assumption about mass near an enlarged boundary.

A harmless normalization clarification is available if desired: place the compact supports inside one fixed unit dyadic cube by a similarity before regularization. This makes $f_i(0)=0$ and the root-scale convention literal. The current normalization into a fixed bounded region can be implemented this way without changing the theorem or its dimensions.

## Auxiliary caps and packet compatibility

I rechecked the complete auxiliary-cap construction, including the choices that matter for the proof:

1. Smooth standard annular multipliers are fixed before any finer partition. Thus the ordinary standard-packet localization inputs retain their hypotheses.
2. Fine labels are spectral pairs $(S,I)$ retaining the standard root $S$. Their hard interval indicators partition circular spectral measures only; they are not applied to individual spatially truncated packets.
3. Every mark removes a union of whole standard labels at the initial spatial cube. Remote packets from a bad label have rapidly small extension there, so whole-cap reconstruction precedes the exact fine spectral partition.
4. The inherited identity sums functions depending only on the parent cube and angular label. The common mark on several fine descendants preserves this identity.
5. Admissibility gives both
   $$
   \delta_j\le\rho_j,\qquad R^{-1/2}\le\rho_j.
   $$
   The latter follows from $n_j-n_{j+1}\le\min(n_j,N-n_j)\le N/2$. Hence effective standard directions can control the fine dual tubes without a forced midpoint.
6. Fixed frequency convolution is harmless because $R/r_j\ge1$ and $R/r_{j+1}\ge1$. Support overlap and terminal Cauchy--Schwarz bounds do not acquire the number of fine descendants.

The fixed source cutoff preserves compact support and separation for the pinned identity. Its removal in the circular cap reconstruction is justified by rapid decay of the smooth standard multiplier kernel away from the original source. These are different uses of the cutoff and are compatible.

## Inflation and threshold bookkeeping

The same enlarged parent appears in the conditional energy, the mark, and the averaging energy. For a fine angular label, a dual tube meeting good children lies inside the enlarged test tube of one such child because its angular discrepancy is at most a constant times $\rho_j$. The sum of the corresponding child weights is therefore bounded by

$$
R^{O_{K_0}(h)}H_{i,j}\rho_j\sigma_i(P^+).
$$

The tube-to-parent area comparison contributes $1/\rho_j$, giving exactly one threshold factor $H_{i,j}$ per edge. No factor counting fine caps or regularized components is introduced.

The stated choices of enlarged cubes provide room for the child averages and the further smooth localizations inside the enlarged parent. One may cover the union of enlarged children, rather than the entire outer enlarged parent, when implementing this standard local-constancy comparison. The available dilation gap is more than sufficient.

The bad-part estimate sums physical standard packets only. Its pair multiplicity remains $R^{O(h)}$. The source-heavy and pin-heavy estimates can therefore dominate all the prescribed geometric losses by choosing the threshold exponents first, then $h$, and finally $T$ and $\epsilon$.

The terminal angular width is at most $R^{-1/2}$ because the last admissible edge has $n_{K-1}\le N/2$. The final sum of squared norms retains the normalized-circle factor $R^{-1}$. Its proof uses bounded overlap and a fixed-radius circle-mass bound; it is valid for strictly finer terminal caps too.

## Summation and identification of the positive law

The substitution $\mathcal C=C(s,u)$ makes the shell second-norm estimate

$$
\int\|(d_y)_*G_{R,y}\|_2^2\,d\nu(y)
\lesssim R^{1-s+C(s,u)+\eta}I_s(\mu).
$$

Strict $C(s,u)+\eta<s-1$ gives a summable series even after taking square roots. The bad first-norm estimates are summable as well. The common compact source support gives a fixed bounded radial interval, so the sum defines an integrable joint density.

Although the good and bad shell functions are signed or complex and depend on the pin, their finite sums reconstruct the original source distribution. The test function obtained by integrating a smooth radial test against the pin measure is smooth after multiplication by the separated source cutoff. Thus the joint limit is the actual positive pushforward of $\mu\times\nu$. Disintegration yields absolute continuity of the raw pinned probability for almost every selected pin; no positivity of individual Fourier shells is assumed.

## Strict dimension exponents and endpoints

For the finite-profile theorem, the function $C(s,u)$ is continuous on its domain, including $u=3/2$. If

$$
C(d,D)<d-1,
$$

strictness allows $s<d$ sufficiently close to $d$ and $u>D$ sufficiently close to $D$ so that $C(s,u)<s-1$ still holds. Choose a Frostman exponent $t$ strictly between $s$ and $d$. Because $D\ge d$, these choices also give $u\ge s$, as required by the profile lemma. When $D<2$, one can retain $u<2$; the case $D=2$ would use $u=2$, though it never satisfies this strict criterion when $d\le5/4$.

The compact positive-mass restriction obtained from the packing cover preserves the $t$-Frostman estimate. Splitting it into two separated compact positive-mass pieces preserves both that estimate and the pin covering bound. Both source and pin sets remain subsets of the original Borel set.

At $d=5/4$, every $D<2$ has genuine slack, so exponents can be decreased and increased as above. Equality $D=2$ has zero slack and is correctly excluded. At $d=7/6$, strict $D<3/2$ supplies slack on the low-slope side. At $d=8/7$, the manuscript uses the coherent branch with its strict condition $D<2d-1$.

The imported coherent argument was freshly checked: its angular estimate has a single exceptional set, so the coupled angle laws are legitimate; its conditional sources are the same in each parent-child comparison; the scalar translation error is quadratic after recentering; and the covering estimate gives a summable positive-density comparison. Its countable separated-product argument removes source-pin overlap without changing the chosen source probability.

## Algebra and profile sharpness

The two pieces of $U(a,b)$ agree at $b=1/2$ and increase in $b$ with the derivatives displayed in the manuscript. The low-slope strict inequality is exactly

$$
b(1-5a)<a(1-3a).
$$

In the range $1/7<a\le1/6$, its cutoff is at most $1/2$ and strictly exceeds $2a$. The high-slope strict inequality is exactly

$$
b<\frac{2a}{1-2a}.
$$

These yield the stated joins at $d=8/7$ and $d=7/6$. The example $d=23/20$, $D=33/25$ has cost $289/1960$ and margin $1/392$, as stated. At $d=31/25$, the high-slope cutoff is $25/13$.

The single-collapse obstruction $g(x)=\min\{bx,1+a-x\}$ is admissible. Its crossing-edge lower bound and the attaining chain both give exactly $(b-a)/(1+2b)-\zeta$. The claimed sharpness applies only to the high-slope profile cost; the text correctly does not promote this profile example to a planar distance-set counterexample or a necessity result.
