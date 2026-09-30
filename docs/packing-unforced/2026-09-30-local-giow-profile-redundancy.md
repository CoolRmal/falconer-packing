# The proposed local GIOW terminal cost is already attained by profile chains

Date: 2026-09-30. Status: proved profile statement, independent of the still-separate analytic local-decoupling transfer. This note does not assert a new distance-set theorem.

## 1. Definitions and conclusion

Let $$g:[0,1]\to\mathbb R$$ be any 1-Lipschitz function. No Hausdorff or packing barriers, sign condition, or endpoint normalization are needed. An admissible edge $$n\to m<n$$ satisfies $$2n-m\le1$$ and has cost

$$
c_g(m,n)=g(m)-\min_{[m,n]}g.
$$

Write $$\Phi_g(n)$$ for the infimum over finite admissible chains from $$n<1$$ to zero. The endpoint limit exists; denote it by

$$
\Phi_g(1)=\lim_{n\uparrow1}\Phi_g(n).
$$

For $$0\le m<1$$ put $$L=1-m$$, $$n=(1+m)/2$$, and

$$
T_g(m)=\frac{2c_g(m,n)+L-g(1)+g(m)}3.
$$

**Theorem.** For every such profile and every $$m<1$$,

$$
\boxed{\quad \Phi_g(1)\le\Phi_g(m)+T_g(m).\quad}
$$

Consequently the proposed terminal optimization satisfies the exact identity

$$
\inf_{0\le m<1}\bigl(\Phi_g(m)+T_g(m)\bigr)=\Phi_g(1).
$$

Thus even a fully valid analytic transfer with exactly this terminal cost cannot improve a dimension condition obtained by optimizing all admissible profile chains. This is a limitation of this specific proposed replacement, not of all possible uses of local decoupling.

## 2. A universal total-drop inequality

For a 1-Lipschitz function $$f:[0,1]\to\mathbb R$$ with $$f(0)=0$$, let $$\mathbf T(f)$$ be the infimum of

$$
\sum_{j\ge1}\left(f(t_j)-\min_{[t_j,t_{j-1}]}f\right)
$$

over sequences $$1=t_0>t_1>\cdots\to0$$ with $$t_{j-1}\le2t_j$$. Define

$$
\beta=\min_{[1/2,1]}f.
$$

We prove

$$
\boxed{\qquad \mathbf T(f)\le\frac{1-2\beta}3.\qquad} \tag{1}
$$

First suppose that $$f$$ is piecewise affine with finitely many pieces. Its hard-point set is

$$
H=\left\{t\in[0,1]:f(t)=\min_{[t/2,t]}f\right\}.
$$

It is a finite union of closed interval components. The point zero belongs to it, and $$f$$ is nonincreasing on each component. The hard-point identity of [Keleti–Shmerkin, Lemma 5.4](https://arxiv.org/html/1801.08745) gives

$$
\mathbf T(f)=\sum_{[u,v]\text{ component of }H}\bigl(f(u)-f(v)\bigr). \tag{2}
$$

Consider the potential

$$
P(t)=\frac{t-2f(t)}3.
$$

On a hard component $$[u,v]$$, put $$\delta=f(u)-f(v)\ge0$$. The Lipschitz bound gives $$\delta\le v-u$$, and therefore

$$
P(v)-P(u)=\frac{v-u+2\delta}3\ge\delta. \tag{3}
$$

Across a complementary interval with hard endpoints $$v<u$$, put $$\Delta=f(u)-f(v)$$. If $$\Delta\le0$$, then $$P(u)\ge P(v)$$ immediately. If $$\Delta>0$$, hardness at $$u$$ implies $$v<u/2$$: otherwise $$v\in[u/2,u]$$ would give $$f(v)\ge f(u)$$. Moreover $$f(u/2)\ge f(u)$$, so

$$
0<\Delta\le f(u/2)-f(v)\le\frac u2-v.
$$

Hence in this case also,

$$
P(u)-P(v)=\frac{u-v-2\Delta}3\ge\frac v3\ge0. \tag{4}
$$

Let $$r=\max H$$. Summing (3) over the hard components and (4) over the intervening gaps, using $$P(0)=0$$, proves

$$
\mathbf T(f)\le P(r)=\frac{r-2f(r)}3. \tag{5}
$$

If $$r\ge1/2$$, then $$f(r)\ge\beta$$, and thus $$r-2f(r)\le1-2\beta$$. If $$r<1/2$$, then

$$
f(r)\ge f(1/2)-(1/2-r)\ge\beta-1/2+r,
$$

so $$r-2f(r)\le1-2\beta-r\le1-2\beta$$. This proves (1) for piecewise affine functions. The finite-chain argument below proves the general case without assuming continuity of an infimum over infinite partitions.

## 3. Reversal and the local tail bound

Let $$h:[0,1]\to\mathbb R$$ be 1-Lipschitz, $$h(0)=0$$, and $$e=h(1)$$. Set

$$
f(t)=h(1-t)-e.
$$

Under reversal, an admissible edge $$y\to x$$ becomes a ratio-at-most-two interval $$[1-y,1-x]$$. Its original cost differs from the usual total-drop summand by the change in $$f$$ between the two endpoints. The changes telescope. Passing from starts $$1-\zeta$$ to their limit gives

$$
\Phi_h(1)=\mathbf T(f)-e. \tag{6}
$$

One may justify this limit directly: extending a finite ratio-two partition below $$\zeta$$ by successive halvings adds at most $$\zeta$$ to total drop, while truncating an infinite partition at $$\zeta$$ changes its crossing cost by at most $$2\zeta$$. The additional endpoint correction tends to $$-e$$.

Since

$$
\min_{[1/2,1]}f=\min_{[0,1/2]}h-e,
$$

(1) and (6) yield

$$
\Phi_h(1)\le\frac{1-e-2\min_{[0,1/2]}h}3. \tag{7}
$$

Now take

$$
h(x)=\frac{g(m+Lx)-g(m)}L,\qquad L=1-m.
$$

The admissibility condition rescales exactly: if $$x<y$$, then

$$
2(m+Ly)-(m+Lx)\le1\quad\Longleftrightarrow\quad2y-x\le1.
$$

Multiplying (7) by $$L$$ gives a chain from a limiting start at one to $$m$$ with cost at most

$$
\frac{L-g(1)+g(m)+2c_g(m,(1+m)/2)}3=T_g(m).
$$

Concatenating with an optimal chain from $$m$$ to zero proves the theorem. For a finite start below $$m$$, monotonicity of the optimal chain cost suffices; $$T_g(m)\ge0$$ follows directly from the Lipschitz bound. Conversely, the same Lipschitz bound gives $$0\le T_g(m)\le1-m$$. Letting $$m\uparrow1$$ proves the asserted equality for the infimum itself.

## 4. Finite chains, approximation, and perturbation

These arguments supply actual chains with the same bounded-length property used in the finite-profile transfer.

First, for any 1-Lipschitz profile the finite-start costs are monotone in the start. To lower the start, truncate a chain at its first crossing and shorten that edge. Its cost and admissibility can only improve. In the other direction, a finite sequence of maximal admissible edges bridges any two starts less than one, with cost at most their distance. Thus

$$
0\le\Phi_g(1)-\Phi_g(1-\zeta)\le\zeta. \tag{8}
$$

Second, whenever $$l<m<n$$, direct comparison of the interval minima gives

$$
c_g(l,n)\le c_g(l,m)+c_g(m,n). \tag{9}
$$

Merge adjacent edges whenever their union is admissible. In the remaining chain, every pair of successive edges more than doubles the complementary distance to one. A chain starting at $$1-\zeta$$ therefore has at most

$$
K\le2\lceil\log_2(1/\zeta)\rceil+O(1)
$$

edges, with no increase in cost. Compactness of the bounded endpoint lists shows that the finite-start infimum is attained. Repeated limiting endpoints are simply deleted.

For a general 1-Lipschitz $$h$$, approximate uniformly by its piecewise affine interpolants, preserving the Lipschitz constant and endpoint values. At any fixed finite start, the preceding piecewise affine proof supplies chains of uniformly bounded length. Their endpoint lists have a convergent subsequence. Interval minima and edge costs pass to the limit, as does admissibility. This proves (7) for every finite start, and then (8) gives its limiting version. It also proves (1) in general through (6).

For the rescaled tail, the corresponding bound is

$$
K_{\rm tail}\le2\left\lceil\log_2\frac{1-m}{1-n_0}\right\rceil+O(1),\qquad m<n_0<1.
$$

After concatenation with the coarse chain, compress once more using (9); the final bound depends only on $$1-n_0$$. A uniform perturbation of the profile by $$\varepsilon$$ changes the cost of each fixed edge by at most $$2\varepsilon$$. Grid rounding at mesh $$\rho$$, with zero and one on the grid, preserves admissibility when all endpoints are rounded down and changes each cost by at most $$2\rho$$. Therefore the result is stable with error $$O(K(\varepsilon+\rho))$$, exactly at the level needed for finite regular profiles.

## 5. Weighted decoupling exponents do not remove this obstruction

The further conditional proposal coming from weighted refined decoupling, for $$2\le p\le6$$, is

$$
T_p=\frac2p I+\left(\frac2p-\frac13\right)W+\left(1-\frac2p\right)c,
$$

where

$$
I=L+g(m)-g(1),\qquad
W=-\frac L2+g(1)-g(n),\qquad
c=g(m)-\min_{[m,n]}g,\qquad n=\frac{1+m}2.
$$

At $$p=6$$ this is exactly $$T_g(m)$$. Moreover

$$
T_p-T_6=\left(\frac2p-\frac13\right)(I+W-c)
=\left(\frac2p-\frac13\right)\left(\frac L2-g(n)+\min_{[m,n]}g\right)\ge0.
$$

The last inequality is the 1-Lipschitz bound on an interval of length $$L/2$$. Thus this whole exponent family is dominated by $$p=6$$, and the latter is already dominated by ordinary admissible chains.

The original numerical observations on the single- and double-collapse witnesses are therefore consequences of a universal exact inequality; no numerical optimization is needed for this conclusion.
