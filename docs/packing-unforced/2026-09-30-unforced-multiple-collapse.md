# Multiple collapses obstruct the single-collapse low-slope conjecture

30 September 2026. This is a rigorous lower-bound construction for the unforced profile optimization. It does not give a distance-set counterexample, a necessary Hausdorff–packing condition, or the sharp profile upper bound. No published manuscript is changed by this note.

The hard-point description used here is [Keleti–Shmerkin, Lemma 5.4](https://arxiv.org/html/1801.08745). The coordinate reversal and endpoint correction are recorded in `2026-09-30-ks-affine-barrier-reduction.md`. All profiles below are piecewise affine with finitely many pieces, so the hard-point formula applies directly.

## 1. Setup and the conclusion

For a 1-Lipschitz function on the unit interval satisfying

$$
ax\le g(x)\le bx,\qquad g(1)=a,
$$

an edge from $n$ to $m<n$ is admissible if $2n-m\le1$, and has cost

$$
c_g(m,n)=g(m)-\min_{[m,n]}g.
$$

Let $\Phi_\zeta(g)$ be the infimum of chain costs from $1-\zeta$ to zero. The limit $\Phi_0(g)=\lim_{\zeta\downarrow0}\Phi_\zeta(g)$ exists, as also follows from the hard-point formula below.

Assume

$$
0<a<b<\frac{1+2a}{4+2a}.
\tag{1}
$$

Then an explicit two-collapse profile has exact limiting cost

$$
C_2(a,b)=\frac{(b-a)(2+a-2b-4ab)}{(1-a)(1+2b)^2}.
\tag{2}
$$

This strictly exceeds the single-collapse value:

$$
C_2(a,b)-\frac{b-a}{1+2b}
=\frac{(b-a)(1+2a-4b-2ab)}{(1-a)(1+2b)^2}>0.
\tag{3}
$$

Thus the high-slope sharp formula cannot extend unchanged throughout the low-slope range. For example, at $a=1/8,b=1/4$, the new lower bound is $2/21$, while the single-collapse value is $1/12$.

Along the baseline $b=2a$, the two-collapse cost satisfies

$$
C_2(a,2a)-a
=\frac{a(1+2a)(8a^2-12a+1)}{(1-a)(1+4a)^2}.
$$

In particular, this difference is strictly positive for

$$
0<a<\frac{3-\sqrt7}{4}=0.0885621722\ldots.
$$

These parameters satisfy (1). Hence in this whole range the universal unforced profile cost cannot be less than $a$ even on the line $b=2a$. This is a precise obstruction to that sufficient *method*, not to pinned distance positivity itself. The separate argument giving the strict inequality $D<2d-1$ remains unaffected.

## 2. Two collapses, with an exact hard-point calculation

Put

$$
k=2b-a,\qquad q_0=\frac b{k},\qquad
Q(t)=\frac{2(1+a)t-1}{1+2b},\qquad
c=\frac{1-b}{1-a}.
$$

Set

$$
q=Q(1)=\frac{1+2a}{1+2b},\qquad
t=cq=\frac{(1+2a)(1-b)}{(1-a)(1+2b)},\qquad r=Q(t).
$$

Condition (1) gives $q_0<t<q<1$. Indeed, $t<1$ follows from $b>a$, and $t>q_0$ is equivalent to $1+2a-4b-2ab>0$. Define

$$
g(x)=\min\{bx,\ at+|x-t|,\ 1+a-x\}.
\tag{4}
$$

This is 1-Lipschitz. Each entry in the minimum majorizes $ax$: for the middle entry this follows separately from $(1+a)(t-x)\ge0$ when $x\le t$ and $(1-a)(x-t)\ge0$ when $x\ge t$. The last entry majorizes $ax$ because its difference is $(1+a)(1-x)$. Thus (4) has both barriers and the asserted endpoint value.

Let

$$
L=\frac{(1+a)t}{1+b},\qquad P=\frac{1+a}{1+b}.
$$

The profile has the following consecutive pieces:

$$
g(x)=
\begin{cases}
bx,&0\le x\le L,\\
(1+a)t-x,&L\le x\le t,\\
x-(1-a)t,&t\le x\le q,\\
bx,&q\le x\le P,\\
1+a-x,&P\le x\le1.
\end{cases}
\tag{5}
$$

The rise after $t$ meets the upper barrier precisely at $q$, since $t=cq$. All listed intervals are correctly ordered: $L<t<q<P<1$; the weak versions also follow immediately from the formulas.

Define the original-coordinate hard set by

$$
H_g=\{x:\min_{[x,(1+x)/2]}g=g(x)\}.
$$

Its nondegenerate components for (4) are exactly

$$
[0,r]\quad\text{and}\quad[t,q].
\tag{6}
$$

Here are details identifying all components, so that (6) is a certificate rather than a plotted observation.

First, $r<L$ and $(1+r)/2\le t$. The first inequality follows from

$$
Q(t)-\frac{(1+a)t}{1+b}
=\frac{(1+a)t-(1+b)}{(1+b)(1+2b)}<0,
$$

and the second is equivalent to $t\ge q_0$. At $x=r$,

$$
br=(1+a)t-\frac{1+r}{2}.
$$

For $x\le r$, the interval from $x$ to $(1+x)/2$ either stays on the initial increasing portion, or enters its following descent and has right endpoint value at least $bx$. Hence every such $x$ is hard. For $r<x<t$, before the window reaches $t$ its right endpoint is lower than $g(x)$; once the window reaches $t$, the value $g(t)=at$ is lower than $g(x)$. The latter comparison uses

$$
br-at=\frac{kt-b}{1+2b}>0.
$$

Thus there are no hard points in $(r,t)$.

For $t\le x\le q$, the profile initially rises from $g(x)$ and can then enter the final descent. Its final-descent value at the window endpoint is

$$
1+a-\frac{1+x}{2}.
$$

The difference from $g(x)=x-(1-a)t$ equals $3(q-x)/2\ge0$. Therefore these points are hard. For $q<x\le P$, the same endpoint is strictly below $bx$, so these points are not hard. For $P<x<1$, strict decrease rules out hardness. The isolated endpoint $1$ is hard and contributes zero increment. This proves (6).

The reversed total-drop formula, including its endpoint correction, now gives

$$
\Phi_0(g)=br+(bq-at)-a.
$$

Substitution simplifies this to (2). At the nonstrict boundary $b=(1+2a)/(4+2a)$, the formulas remain valid and yield no gain over the single collapse.

## 3. An iterated family with finitely many exact collapses

The two-collapse construction iterates. Assume (1), and put

$$
\rho=\frac{2(1+a)(1-b)}{(1-a)(1+2b)},\qquad
\eta=\frac{1-b}{(1-a)(1+2b)}.
$$

Starting from $v_0=1$, define

$$
v_{j+1}=cQ(v_j)=\rho v_j-\eta.
\tag{7}
$$

Retain precisely the terms $v_1,\ldots,v_K$ for which $v_j>q_0$. They form a finite strictly decreasing sequence. To see this, $v_1<1$ because $b>a$, while

$$
\rho-1=\frac{1+3a-4b}{(1-a)(1+2b)}>0.
$$

The last sign follows from $b<(1+2a)/(4+2a)<(1+3a)/4$. Thus successive differences in (7) are negative and increase geometrically in magnitude; the sequence eventually crosses $q_0$.

Consider

$$
g_K(x)=\min\left\{bx,\ 1+a-x,\ \min_{1\le j\le K}\bigl(av_j+|x-v_j|\bigr)\right\}.
\tag{8}
$$

It has the same Lipschitz and barrier properties as (4). Between two consecutive valleys $v_j<v_{j-1}$, only those two valley cones can be the smallest cone. The earlier cones have larger increasing branches, and the later cones have larger decreasing branches. The upper-barrier intersection of the increasing branch from $v_j$ is

$$
\frac{(1-a)v_j}{1-b}=Q(v_{j-1}),
$$

by (7). The decreasing branch into $v_{j-1}$ begins at $(1+a)v_{j-1}/(1+b)\ge Q(v_{j-1})$.

Repeating the window comparison from (6), the nondegenerate hard components are exactly

$$
[0,Q(v_K)]\quad\text{and}\quad
[v_j,Q(v_{j-1})]\quad(1\le j\le K).
\tag{9}
$$

For completeness, the decisive comparison at each right endpoint $Q(v_{j-1})$ uses the decreasing cone into $v_{j-1}$; its window endpoint is at most $v_{j-1}$ because $v_{j-1}\ge q_0$. After that endpoint, the future window either has a strictly smaller value on that descent or contains the valley itself. Values at still later valleys increase with their coordinates, so they cannot create an additional obstruction inside the claimed hard component. The initial component is treated exactly as before, and the final descent leaves only the isolated endpoint $1$.

Consequently (8) has the exact limiting cost

$$
\boxed{\displaystyle
\Phi_0(g_K)=\sum_{j=0}^K\frac{(2b-a)v_j-b}{1+2b}.}
\tag{10}
$$

The term for $j=0$ is the single-collapse value. Each additional term is strictly positive by the stopping rule. This is an explicit rigorous lower bound on the universal profile minimax. It is not an asserted upper bound.

The recurrence can also be evaluated without iteration. With

$$
v_* = \frac{1-b}{1+3a-4b}>1,
$$

one has

$$
v_j=v_*-(v_*-1)\rho^j,
$$

and $K$ is the largest nonnegative integer with $v_K>q_0$. Thus the finite sum (10) is an elementary geometric sum.

Some exact examples are:

| $a$ | $b$ | Number of inserted valleys $K$ | Exact limiting cost |
|---|---|---|---|
| $1/8$ | $1/4$ | $1$ | $2/21$ |
| $1/20$ | $1/10$ | $1$ | $61/912$ |
| $1/100$ | $1/50$ | $3$ | $5833382519/197068158144$ |

For the last example the cost is approximately $0.02960084$, almost three times $a$. Thus even the line $b=2a$ can encounter a real obstruction to the criterion “universal profile cost $<a$” within this particular analytic method. This says nothing against the original separate argument proving the strict dimension inequality $D<2d-1$.

## 4. Bounded chains and the limiting start

There is no unbounded-chain loophole in these lower bounds. In fact arbitrary finite admissible chains can be compressed without increasing cost. For $l<m<n$,

$$
c_g(l,n)\le c_g(l,m)+c_g(m,n).
\tag{11}
$$

To prove this, let $A=\min_{[l,m]}g$, $B=\min_{[m,n]}g$ and use $g(m)\ge\max(A,B)$. Subtracting the left side of (11) from the right side leaves $g(m)-\max(A,B)\ge0$.

Merge adjacent edges whenever their union is admissible. After no further merges are possible, any three consecutive endpoints obey $2n_i-n_{i+2}>1$. Hence the complementary depth more than doubles every two edges. A chain starting at $1-\zeta$ therefore compresses to at most

$$
2\left\lceil\log_2(1/\zeta)\right\rceil+2
$$

edges. A near-optimal chain can consequently always be chosen with this length bound, independently of the number of affine pieces.

The limiting costs also control starts uniformly. The function $\Phi_\zeta(g)$ is nondecreasing as $\zeta\downarrow0$: truncate a chain at its first crossing of an earlier start, replacing the crossing edge by its subinterval. This preserves admissibility and can only decrease cost. Conversely, from a later start one can reach the earlier start using maximal admissible jumps; their total cost is at most the distance between the starts. Therefore

$$
0\le\Phi_0(g)-\Phi_\zeta(g)\le\zeta.
\tag{12}
$$

The reflected total-drop formula supplies the same limit. In particular, for a strict margin $\Phi_0(g)>a$, the obstruction already holds for every sufficiently small positive $\zeta$, even with unrestricted finite chains and hence also with bounded chains.

## 5. Remaining question

The construction strongly suggests examining a Bellman optimization in the successive valley positions and heights. A useful local inequality is already exact: if a hard-component endpoint $q$ of height $u$ is followed by a valley at $p$ of height $v<u$, then hardness and Lipschitz continuity imply

$$
u-v\le p-\frac{1+q}{2},\qquad u-v\le bq-ap.
$$

Optimizing these two bounds in $q$ gives

$$
u-v\le\frac{(2b-a)p-b}{1+2b}.
$$

The constructed profiles saturate these inequalities. What is still missing for a matching universal upper bound is a rigorous reduction showing that all intervening hard rises can simultaneously be replaced by rises from the lower barrier to the upper barrier with the recurrence (7), without decreasing the total hard increment. The present note makes no such reduction claim.
