# Independent audit: local terminal profile redundancy

30 September 2026. Reviewed `2026-09-30-local-giow-profile-redundancy.md`, Sections 1–5, independently of its author. The profile argument passes. This audit concerns the specified terminal multiplier and its weighted family; it does not exclude different uses of decoupling or prove a necessary dimension condition for distance sets.

The key potential is

$$P(t)=(t-2f(t))/3.$$

Across a hard component of length ell and drop delta, its increase is `(ell+2 delta)/3`, at least delta because delta is at most ell. Across a gap with hard endpoints v<u and positive rise Delta, hardness at u forces v<u/2 and Delta at most u/2-v. Thus the potential does not decrease. A nonpositive gap rise is even easier. Summing through the last hard point r bounds the hard-component total drop by P(r). If r is below one half, the necessary endpoint comparison is

$$f(r)\ge\min_{[1/2,1]}f-1/2+r,$$

which yields the same bound as the case r at least one half. The proof does not silently assume that one is hard.

Reversal has the correct endpoint correction: for f(t)=h(1-t)-h(1), the original limiting chain cost is total drop minus h(1). Consequently the universal bound becomes

$$
\Phi_h(1)\le\frac{1-h(1)-2\min_{[0,1/2]}h}{3}.
$$

Rescaling the interval [m,1] preserves `2n-m≤1` exactly and gives the proposed terminal cost. Concatenation with a coarse chain therefore proves its redundancy. The reverse infimum inequality follows by letting m approach one, since the terminal cost lies between zero and 1-m.

The finite formulation is also sound. Truncation makes optimal costs monotone in their starting point. Bridging two starts with admissible edges costs at most their distance. Merging admissible consecutive edges never increases cost; after all such merges, every pair of edges more than doubles the complementary distance from one. This gives the uniform logarithmic edge bound needed for the compact endpoint argument and polygonal approximation. Downward rounding to a grid containing zero and one preserves admissibility, and the per-edge perturbation errors stated in the note are valid.

Finally, the weighted exponent comparison has the correct sign:

$$
T_p-T_6=
\left(\frac2p-\frac13\right)
\left(\frac L2-g(n)+\min_{[m,n]}g\right)\ge0,
\qquad 2\le p\le6.
$$

The second factor is nonnegative by the Lipschitz bound over an interval of length L/2. This calculation agrees with the independently checked large-coordinate application of Du--Ou--Ren--Zhang Theorem 1.1(b) in the local-transfer fragment. No numerical optimization is used in this conclusion.
