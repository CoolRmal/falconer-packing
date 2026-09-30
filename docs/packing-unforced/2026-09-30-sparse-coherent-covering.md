# Sparse coherent comparisons: integration and logarithmic endpoint

30 September 2026. This note records the complete manuscript integration at [packing-unforced-sparse-moran.tex](../output/pdf/packing-unforced-sparse-moran.tex). It is an internal mathematical proof, not an external verification or novelty claim.

## Provenance

The arbitrary-block coherent comparison and selected-scale criterion were already present in Sections 8–9 of [source_condition_fresh_audit.md](source_condition_fresh_audit.md). The open constructed family and hereditary dimension calculation were already reviewed in [sparse_scale_literature_audit.md](sparse_scale_literature_audit.md), building on [liu_comparison.md](liu_comparison.md). Section 9 of the source-condition audit already includes the closed boundary, with square-root slack.

Accordingly the integration does **not** claim discovery of a new dimension-only theorem or of that sparse family. It supplies the full proof in the main manuscript, exhibits examples outside the current strict curve, and replaces square-root endpoint slack by an arbitrarily small positive multiple of a logarithm.

## Fixed-exponent criterion

Let the source probability be d-Frostman, with 1<d<2, and let the pin probability have a Frostman exponent above one. Fix a legal angular exponent q>1 and

$$
\eta_q=\frac{q-1}{2q-1},\qquad 0<\gamma<\frac{d-1}{2}.
$$

For selected depths satisfying

$$
N_{n_j}\le C2^{dn_j},
$$

the raw joint distance law is absolutely continuous provided

$$
\sum_j 2^{-2\gamma\eta_q(2n_j-n_{j+1})}<\infty.
$$

This proof does not depend on the new critical frequency-band argument. For a block n<m, write r=2^{-n} and δ=2^{-m}. Comparing the same fine conditional source in the two affine maps gives

$$
\|f_m-f_n\|_1
 \le C(AZ_{n,m})^{1/2}+CBA^{1-q},
\qquad
Z_{n,m}=\delta r^{4\gamma}
 \sum_{Q\text{ at depth }m}p_Q I_{1+2\gamma}(\mu_Q).
$$

Each affine density has support in an interval of length O(δ). Their union has total measure O(δ), even if the scalar shifts differ by much more than δ. Thus the estimate has no restriction m≤2n. The translation component of the angular lemma is valid for every shift bound h>0 by the same Plancherel estimate; here h=Cr².

Conditional Frostman energy and the selected covering count give

$$
Z_{n_j,n_{j+1}}\le C2^{-2\gamma(2n_j-n_{j+1})}.
$$

Angular clipping raises the right-hand quantity to the power η_q. Convergence in the joint first norm along the selected subsequence identifies the raw law because the same fixed affine approximation sequence converges weakly to it.

## Fixed Moran examples and the boundary

For every

$$
1<d<D\le\frac{4d}{d+2},
$$

the manuscript constructs a compact K with a d-Frostman probability μ such that

$$
0<\mathcal H^d(K)<\infty,\qquad
\dim_H K=d,\qquad \dim_P K=D,
$$

and

$$
\dim_H S\le\frac dD\dim_P S\qquad(S\subset K).
$$

The raw joint distance law is absolutely continuous against any compactly supported pin Frostman probability of exponent greater than one, including μ itself.

The construction uses homogeneous increments 0 or 2 in the base-two logarithm F(n) of the occupied-square count. Starting near the lower line dn, grow with slope two until first reaching

$$
U(n)=Dn-\ell(n),
$$

then keep F constant until the lower line catches it. In the strict interior take ℓ=0; at the boundary take

$$
\ell(n)=A\log_2(n+1),\qquad A>0.
$$

Writing a for one low endpoint, b for the following peak, and m for the next low endpoint gives

$$
(2-D)b=(2-d)a-\ell(b)+O(1),
\qquad
dm=Db-\ell(b)+O(1),
$$

and therefore

$$
m=\kappa a-\frac{2}{d(2-D)}\ell(b)+O(1),
\qquad
\kappa=\frac{D(2-d)}{d(2-D)}.
$$

The strict interior has κ<2. At D=4d/(d+2), κ=2 and

$$
2a-m=\frac{2A}{d(2-D)}\log_2(a+1)+O(1).
$$

The low endpoints grow geometrically. Every positive power of their reciprocal is summable, so every A>0 is enough, regardless of how close the fixed angular exponent is to one.

The flat intervals satisfy m/b→D/d and transfer every cover at a peak to a cover at the following trough without adding cells. The countable upper-box characterization of packing dimension then gives the hereditary inequality for every subset, including nonmeasurable ones.

## Scope and explicit example

At

$$
d=\frac{21}{20},\qquad D=\frac65,
$$

the low-endpoint ratio is 19/14, the old strict cutoff is 11/10, and the maximal constructed packing dimension at this d is 84/61.

If d≤(7−√7)/4 and D≥2d−1, any subset S with h=dim_H S>1 satisfies

$$
\dim_P S\ge (D/d)h\ge2h-1=B_H(h).
$$

Thus the positive result is not obtained by extracting a subset satisfying the previous strict dimension criterion. There is also no positive-dimensional subset with equal Hausdorff and packing dimensions.

The favorable timing of covering scales is extra information. The theorem does not assert that arbitrary Borel sets with the same two dimensions have absolutely continuous distance laws. In the zero-gauge interior examples with D≥2d−1, the all-scale covering summands fail to tend to zero at the peaks; the sparse proof shows that this numerical failure need not obstruct the actual law.
