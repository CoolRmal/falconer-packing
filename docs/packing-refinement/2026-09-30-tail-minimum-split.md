# A universal chain bound from the location of a tail minimum

30 September 2026. This is an elementary profile theorem. Its consequences for distance sets are conditional on a separately valid analytic transfer. No optimality of the profile theorem or the distance-set condition is asserted.

## The bound

Let $0<a\le b\le1$, and let $g:[0,1]\to\mathbb R$ be 1-Lipschitz with $ax\le g(x)\le bx$. For $m<n$, define

$$
c_g(m,n)=g(m)-\min_{[m,n]}g.
$$

An edge from $n$ to $m$ is admissible when $2n-m\le1$. Fix $3/4\le n_0<1$. There is an admissible chain from $n_0$ to $1/2$, then to zero, with at most $C(1+\log(1/(1-n_0)))$ edges and cost at most

$$
\boxed{\max\{E(a,b),L(a,b)\},}
\tag{1}
$$

where

$$
E(a,b)=\frac{1-2a-2a^2+(2+a)b}{6(1+a)},
$$

$$
L(a,b)=
\begin{cases}
\displaystyle\frac18+\frac{3b}{4}-\frac{5a}{4},&b\le\frac12,\\[6pt]
\displaystyle\frac{b-a}{1+2b}+\frac b2-\frac{3a}{4},&b\ge\frac12.
\end{cases}
$$

The two formulas for $L$ agree at $b=1/2$. A grid version has additive $O(T)$ cost error on mesh $T$. Approximate barriers with error $\epsilon$ have an additional $O(K\epsilon+KT)$ cost error, where $K$ is the chain-length bound.

## The elementary chain construction used below

Suppose an affine function $H(z)=hz+\alpha$, with $h\ge1/2$, majorizes $g(z)$ on $[q,1]$. Assume $H(q)\le g((1+q)/2)$ when that endpoint is used. Put

$$
\Lambda(x)=H(2x-1)-g(x),\qquad x\ge(1+q)/2.
$$

The function $\Lambda$ is nondecreasing. On its positive region,

$$
(-g')_+\le\frac{2h-g'}{1+2h}
=\frac{\Lambda'}{1+2h}.
\tag{2}
$$

Take maximal admissible downward jumps through that region. Their costs sum to at most $\Lambda(1)_+/(1+2h)$. In the region $\Lambda(n)\le0$, put $m_0=2n-1$. Provided $m_0\ge q$, we have

$$
g(m_0)\le H(m_0)\le g(n).
$$

Choosing a leftmost minimum on $[m_0,n]$ gives an admissible zero-cost edge. Continue until the stopping threshold is reached. On a grid this is finite. Consecutive zero-cost edges can be merged whenever their union is admissible; every pair of unmergeable consecutive edges more than doubles the complementary depth $1-n$. Thus all retained chains have the stated logarithmic length bound. A crossing of a sign-change location or stopping threshold costs $O(T)$ when grid rounding is required. Passing to arbitrarily fine grids and extracting a convergent subsequence of bounded-length endpoint lists proves the continuous version.

For the late case below, the starting endpoint condition is unnecessary: one simply stops the positive-cost construction at the specified stopping threshold if it has not yet reached $\{\Lambda\le0\}$. The same upper bound for the positive cost remains valid.

## Split at the location of the global tail minimum

Choose a global minimum $t$ of $g$ on $[1/2,1]$, and write

$$
m=g(t),\qquad v=g(1/2),\qquad e=g(1).
$$

### An early minimum

Suppose $t\le3/4$. Lipschitz continuity gives the affine upper envelope

$$
g(z)\le H(z):=m+z-t\qquad(z\ge t).
$$

Use the preceding construction with $q=t$, $h=1$, and $\alpha=m-t$. Its lower endpoint satisfies

$$
\Lambda((1+t)/2)=m-g((1+t)/2)\le0.
$$

The resulting chain reaches $n\le(1+t)/2$ with cost at most

$$
\frac{1-t+m-e}{3}.
$$

Its jump to $t$ is admissible and has zero cost, since $t$ is a global tail minimum. The jump $t\to1/2$ is admissible because $t\le3/4$, and costs $v-m$. Hence the total cost is bounded by

$$
v-m+\frac{1-t+m-a}{3}.
\tag{3}
$$

We now maximize this expression under the weaker scalar constraints

$$
m\ge at,\qquad
v\le\min\{b/2,m+t-1/2\},\qquad 1/2\le t\le1.
$$

Put $t_*=(1+b)/(2(1+a))$. For $t\le t_*$, the maximum in $m$ occurs at $m=b/2-t+1/2$, and the resulting expression increases with $t$. For $t\ge t_*$, the maximum occurs at $m=at$, and the resulting expression decreases with $t$. Therefore (3) is at most its value at $t=t_*$, namely

$$
\frac{b-a}{2(1+a)}
+\frac{(1-a)(1-t_*)}{3}
=E(a,b).
$$

We maximized over the larger interval $[1/2,1]$, so no extra assumption $t_*\le3/4$ is required for this upper bound.

### A late minimum

Suppose $t>3/4$. Then every $x\in[1/2,1]$ satisfies

$$
g(x)\ge m\ge at>3a/4.
\tag{4}
$$

When $b\ge1/2$, use the envelope $H(z)=bz$ and stop the chain construction as soon as $n\le3/4$. The cost before that point is at most

$$
\frac{b-e}{1+2b}\le\frac{b-a}{1+2b}.
$$

When $b\le1/2$, use instead

$$
H(z)=\frac z2+\frac{b-1/2}{2},\qquad z\ge1/2.
$$

This is an upper envelope because $(b-1/2)z\le(b-1/2)/2$. Stop again at $n\le3/4$. The positive-region cost is bounded by

$$
\frac{H(1)-e}{2}\le\frac{1+2b-4a}{8}.
$$

The terminal jump $n\to1/2$ is admissible in both cases and, by (4), costs at most

$$
v-m\le\frac b2-\frac{3a}{4}.
$$

Adding the corresponding bounds gives $L(a,b)$. If this terminal bound is negative, the late-minimum case is impossible, since $v\ge m$. Finally $1/2\to0$ costs zero. This proves (1).

## Parameter consequences

For $s=1+a$ and $u=1+b$, the early condition $E(a,b)<a$ is equivalent to

$$
u<\frac{s(8s-7)}{s+1}.
\tag{5}
$$

For $u\le3/2$, the late condition is

$$
u<3s-\frac{13}{6}.
\tag{6}
$$

The smaller of the two right sides in (5)–(6) first exceeds $2s-1$ at

$$
s_A=\frac{4+\sqrt{10}}6\approx1.193712943,
$$

and the two right sides cross at

$$
s_B=\frac{47+\sqrt{649}}{60}.
$$

The line in (6) reaches $3/2$ at $s=11/9$.

For $u\ge3/2$, the late condition is equivalent to

$$
4b^2+(6-14a)b-11a<0,
$$

or

$$
u<\frac{7s-6+\sqrt{49s^2-96s+56}}4.
\tag{7}
$$

For $2/9\le a\le1/4$, condition (7) already implies the early condition. To check this algebraically, let

$$
b_E=\frac{8a^2+8a-1}{a+2},\qquad
P_a(b)=4b^2+(6-14a)b-11a.
$$

The polynomial $P_a$ is strictly increasing for $b\ge0$ in this range. Direct expansion gives

$$
(a+2)^2P_a(b_E)
=144a^4+213a^3+82a^2+10a-8.
$$

This last expression is strictly increasing for $a>0$ and equals $700/729>0$ at $a=2/9$. Thus the positive root of $P_a$ is strictly below $b_E$, as claimed. The root is at least $1/2$ exactly when $a\ge2/9$, because $P_a(1/2)=4-18a$.

Combining only these elementary facts with the separate criterion $u<2s-1$ produces the following **conditional candidate cutoff for the distance theorem**:

$$
\widetilde B(s)=
\begin{cases}
2s-1,&1<s\le s_A,\\[3pt]
\displaystyle\frac{s(8s-7)}{s+1},&s_A<s\le s_B,\\[6pt]
\displaystyle3s-\frac{13}{6},&s_B<s\le\frac{11}{9},\\[6pt]
\displaystyle\frac{7s-6+\sqrt{49s^2-96s+56}}4,
&\frac{11}{9}<s\le\frac54.
\end{cases}
$$

All displayed joins agree exactly. In particular, at $s=1.24$ the new profile cutoff is approximately $1.546869432$. This is an improvement of the sufficient profile estimate, not a proof that the cutoff is optimal and not by itself a proof of the corresponding pinned-distance assertion.
