# Endpoint normalization and the Keleti–Shmerkin profile problem

30 September 2026. This note records a useful exact reduction of the current profile minimax. It does not give a new closed-form low-slope optimum.

The relevant comparison is [Keleti–Shmerkin, Proposition 5.2, Lemma 5.4 and Section 7](https://arxiv.org/html/1801.08745). Their doubling-partition total-drop problem has sharp bounds for barriers through the origin. Reversing our coordinate produces different, affine barriers and a nonzero endpoint correction. Consequently their stated sharp formula cannot be substituted directly.

## 1. The worst profile may be assumed to end on its lower barrier

Suppose $g:[0,1]\to\mathbb R$ is 1-Lipschitz and $ax\le g(x)\le bx$, with $0<a\le b\le1$. Define

$$
h(x)=\min\{g(x),1+a-x\}.
$$

Then $h$ is 1-Lipschitz, satisfies the same barriers, and has $h(1)=a$. The lower barrier is preserved because

$$
1+a-x-ax=(1+a)(1-x)\ge0.
$$

More strongly, for every interval $[m,n]$,

$$
c_h(m,n)\ge c_g(m,n),
\qquad c_g(m,n)=g(m)-\min_{[m,n]}g.
\tag{1}
$$

If $g(m)\le1+a-m$, the left endpoint is unchanged and the interval minimum can only decrease. If $g(m)>1+a-m$, then

$$
c_h(m,n)\ge(1+a-m)-(1+a-n)=n-m\ge c_g(m,n),
$$

where the final inequality is Lipschitz continuity. Thus (1) holds edge by edge, not merely after optimization.

In particular, the supremum over profiles of the optimal cost of admissible chains is unchanged if one imposes $g(1)=a$. This applies to every fixed starting point $n_0<1$ and every fixed upper bound on chain length: the clipping does not alter the chain constraints.

## 2. Exact reversal of the cost

After the preceding normalization, put

$$
F(t)=g(1-t)-a.
$$

Then

$$
F(0)=0,\qquad F(1)=-a,
$$

and the two barriers are

$$
-at\le F(t)\le(b-a)-bt.
\tag{2}
$$

The Lipschitz condition also gives $|F(t)|\le t$, so the available upper envelope is $\min\{t,(b-a)-bt\}$.

Let $\delta=1-n_0$ and write a reversed chain as

$$
1=t_0>t_1>\cdots>t_M=\delta,
\qquad t_{i-1}\le2t_i.
$$

If $T_\delta(F)$ denotes the infimum of the left-endpoint drop

$$
\sum_i\left(F(t_i)-\min_{[t_i,t_{i-1}]}F\right)
$$

over these finite doubling partitions, then the original chain infimum is exactly

$$
\inf\sum_j c_g(n_{j+1},n_j)
=T_\delta(F)-g(1-\delta).
\tag{3}
$$

Indeed, the original edge cost is the right-endpoint drop of $F$. Its difference from the left-endpoint drop is $F(t_{i-1})-F(t_i)$; summing telescopes to $F(1)-F(\delta)=-g(1-\delta)$.

Let $T(F)$ be the infimum over infinite doubling partitions tending to zero. One has

$$
|T_\delta(F)-T(F)|\le C\delta.
$$

For one direction, extend a finite partition below $\delta$ by dyadic halving; its extra cost is at most $\delta$ by Lipschitz continuity. For the other, truncate an almost optimal infinite partition at the interval crossing $\delta$, replacing its lower endpoint by $\delta$; the ratio constraint is preserved and the changed cost is at most $C\delta$.

Thus

$$
\lim_{n_0\uparrow1}\inf\sum_j c_g(n_{j+1},n_j)
=T(F)-a.
\tag{4}
$$

This is an exact bridge to the published problem, with the endpoint correction exposed.

## 3. The hard-point description in the original coordinate

For piecewise-linear profiles, define

$$
H_g=\left\{x:\min_{[x,(1+x)/2]}g=g(x)\right\}.
$$

It is the reflected set of hard points for $F$. If its nondegenerate interval components are $[p_j,q_j]$, the hard-point characterization gives

$$
T(F)=\sum_j\bigl(g(q_j)-g(p_j)\bigr).
$$

Together with (4), this represents the limiting optimized original cost as

$$
\sum_j\bigl(g(q_j)-g(p_j)\bigr)-a.
\tag{5}
$$

For the single-collapse profile $g(x)=\min\{bx,1+a-x\}$, the nontrivial hard component is

$$
[0,q],\qquad q=\frac{1+2a}{1+2b}.
$$

Formula (5) recovers

$$
bq-a=\frac{b-a}{1+2b}.
$$

The same formula indicates what a genuinely sharp low-slope analysis must control: the total increase on several separated hard components, subject to the affine cap in (2).

## 4. Why the published sharp formula does not yet settle the low-slope case

The barriers (2) have a shared endpoint at $t=1$, whereas the standard proposition assumes two rays from $t=0$. Replacing them by those rays changes the admissible family. For example, using $C=b$ and $D=a$ directly would predict zero published total drop when $b=2a$, while the original single-collapse profile already has positive cost $(b-a)/(1+2b)$.

The affine-cap extension therefore remains an additional optimization problem. The endpoint-normalization lemma and equations (3)–(5) are rigorous reductions that can be used to derive or test it. They do not establish that the existing low-slope bound is sharp, nor supply a stronger distance-set condition by themselves.
