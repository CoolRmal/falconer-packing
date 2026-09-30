# Independent audit: local and weighted terminal costs are redundant

30 September 2026. The proof in [the profile-redundancy note](2026-09-30-local-giow-profile-redundancy.md) passes independent audit, including arbitrary Lipschitz profiles and finite approximation. The scaling in [the weighted-decoupling comparison](2026-09-30-weighted-decoupling-profile-comparison.md) also passes. Thus the revised local packet construction is mathematically meaningful but provides **no smaller optimized profile cost** than ordinary admissible chains. This is a limitation of that construction, not a necessary condition for positive-length distance sets.

## 1. The potential proof is valid without dimension barriers

Let $$f:[0,1]\to\mathbb R$$ be 1-Lipschitz with $$f(0)=0$$, initially piecewise affine with finitely many pieces. Its hard set is

$$
H=\{t:f(t)=\min_{[t/2,t]}f\}.
$$

Use the hard-component formula for total drop from [Keleti--Shmerkin, Lemma 5.4](https://arxiv.org/html/1801.08745#S5): total drop is the sum of the decreases on the components of this set. Adding the degenerate point zero to the hard set does not affect that formula. The finite piecewise-affine hypothesis ensures finitely many hard components.

The new potential

$$
P(t)=\frac{t-2f(t)}3
$$

pays for each component decrease. Indeed, on a hard component with endpoints $$u\le v$$ and decrease $$\delta=f(u)-f(v)\ge0$$,

$$
P(v)-P(u)=\frac{v-u+2\delta}3\ge\delta
$$

because $$\delta\le v-u$$. Across a complementary interval with hard endpoints $$v<u$$, set $$\Delta=f(u)-f(v)$$. If $$\Delta\le0$$, the potential increases. If $$\Delta>0$$, hardness at the right endpoint forces $$v<u/2$$ and $$f(u/2)\ge f(u)$$, whence

$$
0<\Delta\le u/2-v,
\qquad P(u)-P(v)\ge v/3\ge0.
$$

No unsupported monotonicity claim about the function on the complementary gap is used. In particular the proof would still work without separately establishing a sign for the net change across each gap.

Let $$r=\max H$$. Summing all components and gaps from zero to the last hard point yields

$$
\mathbf T(f)\le\frac{r-2f(r)}3.
$$

Put $$\beta=\min_{[1/2,1]}f$$. If $$r\ge1/2$$ then $$f(r)\ge\beta$$. If $$r<1/2$$, Lipschitz continuity gives $$f(r)\ge\beta-1/2+r$$. Both cases give

$$
\mathbf T(f)\le\frac{1-2\beta}3.
$$

The cases of an empty positive hard set, isolated hard points, zero-length components, and the last hard point equal to zero cause no exception.

## 2. Endpoint reversal and approximation retain the exact constant

For a normalized profile $$h(0)=0$$ with endpoint $$e=h(1)$$, set

$$
f(t)=h(1-t)-e.
$$

Reversing an edge changes its cost by an endpoint increment of this last function. Over a chain these increments telescope. A chain starting at $$1-\zeta$$ leaves the correction

$$
-e-f(\zeta),
$$

which tends to $$-e$$. Completing or truncating ratio-two partitions at scale $$\zeta$$ changes the total-drop sum by at most a constant times $$\zeta$$, since every summand is bounded by its interval length. Therefore

$$
\Phi_h(1)=\mathbf T(f)-e
\le\frac{1-e-2\min_{[0,1/2]}h}3.
$$

There is no reversal sign error.

For general Lipschitz profiles, approximate by linear interpolants on finer finite meshes. Their Lipschitz constants and endpoint values are preserved. For each fixed starting point below one, consecutive admissible edges may be merged without increasing cost: the inequality

$$
c_g(l,n)\le c_g(l,m)+c_g(m,n),\qquad l<m<n,
$$

follows directly by comparing the two interval minima. In a chain admitting no further merger, every two successive edges more than double the complementary distance to one. Starting at $$1-\zeta$$ therefore needs only $$O(1+\log(1/\zeta))$$ edges. Compactness of these bounded endpoint lists passes both the cost and admissibility to the uniform limit. Repeated limiting endpoints have zero cost and may be removed.

Finally, the optimal finite-start cost is monotone and 1-Lipschitz in its starting point. Shortening the first crossing edge proves monotonicity; adding maximal admissible edges costs at most their total length and proves the other inequality. Hence

$$
0\le\Phi_g(1)-\Phi_g(1-\zeta)\le\zeta.
$$

This justifies the endpoint limit without assuming continuity of an infimum over arbitrary infinite chains. It also makes the general Lipschitz extension independent of an unproved general hard-set formula.

## 3. Exact terminal comparison

At a parent position $$m<1$$ put $$L=1-m$$ and rescale

$$
h(x)=\frac{g(m+Lx)-g(m)}L.
$$

The edge condition transforms exactly:

$$
2(m+Ly)-(m+Lx)\le1
\quad\Longleftrightarrow\quad2y-x\le1.
$$

The preceding bound gives a tail-chain cost at most

$$
T_6(g;m)=
\frac{L-g(1)+g(m)+2\bigl(g(m)-\min_{[m,(1+m)/2]}g\bigr)}3.
$$

After concatenation with the coarse chain,

$$
\Phi_g(1)\le\Phi_g(m)+T_6(g;m)
$$

for every 1-Lipschitz profile and every parent. No lower or upper dimension barrier is needed. Conversely $$0\le T_6(g;m)\le1-m$$ by Lipschitz continuity, so letting $$m\uparrow1$$ proves the stronger identity

$$
\inf_{0\le m<1}\bigl(\Phi_g(m)+T_6(g;m)\bigr)=\Phi_g(1).
$$

For finite-grid implementation, simultaneous rounding down of endpoints preserves admissibility when one is a grid point: the rounded quantity $$2n'-m'$$ lies on the grid and is strictly below one plus one mesh length, hence is at most one. Each edge cost changes by at most twice the mesh. These errors remain bounded by the compressed chain length.

## 4. Weighted decoupling: scaling and exponent audit

The source theorem is [Du--Ou--Ren--Zhang, Theorem 1.1(b)](https://arxiv.org/html/2309.04501v1#S1.SS1). Its weight is bounded by one and has an upper mass condition only on the natural packet-scale cubes. The stated exponent parameter may be any real number at most two; no additional nonnegative lower bound is required.

Normalize the spatial parent to unit size and frequency $$r$$. Let the smoothed pin density obey $$w\le A$$ and natural-square mass be at most $$v$$. Under $$X=rx$$, the weight

$$
W(X)=w(X/r)/A
$$

has natural-square mass at most $$r^2v/A$$. Choosing

$$
\alpha=2\log_r(r^2v/A),\qquad Q=rv/A
$$

makes the squared weighted-decoupling gain exactly

$$
r^{(\alpha-2)(1/p-1/6)}=Q^{2/p-1/3}.
$$

The condition $$\alpha\le2$$ is exactly $$Q\le1$$. Coordinate Jacobians cancel: the factor $$r^{-4/p}$$ from converting the weighted norm back is cancelled by the factor $$r^{4/p}$$ from the packet norms. Thus there is no missing dimensional scale factor.

For a comparable packet class, Hölder with respect to the pin measure, weighted incidence counting, and packet Bernstein give the multiplier

$$
A^{2/p}Q^{2/p-1/3}H^{1-2/p},\qquad 2\le p\le6.
$$

Here weighted incidence uses natural squares of side $$r^{-1/2}$$ and cancels multiplicity against their total pin mass; it needs no assumption of equal square masses. The local packet construction and radius-independent scalar selectors are still required, as stated in the parent note.

At profile depth $$N$$, with $$L=N-m$$ and $$n=(N+m)/2$$, define

$$
I=L+g(m)-g(N),\quad
J=-L/2+g(N)-g(n),\quad
c=g(m)-\min_{[m,n]}g.
$$

These are the leading exponents of $$A,Q,H$$. The inequality $$J\le0$$ follows from Lipschitz continuity, so the theorem's range is respected; regularization losses require the usual harmless small-power adjustment. The resulting terminal exponent satisfies

$$
T_p-T_6=
\left(\frac2p-\frac13\right)
\left(\frac L2-g(n)+\min_{[m,n]}g\right)\ge0.
$$

Both factors are nonnegative. For the second, choose a minimizing point in the half-interval and apply the 1-Lipschitz bound over an interval of length at most $$L/2$$. Thus the whole weighted family is dominated by its exponent-six member, which is itself dominated by ordinary profile chains.

The combined conclusion excludes a dimensional improvement from this precise family of terminal replacements. It does not exclude refinements that use additional geometric information absent from the one-dimensional profile, different source/pin selectors, or a different analytic multiplier.
