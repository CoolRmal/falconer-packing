# A sharp two-gap bound for the unforced profile problem

30 September 2026. This note proves a new universal upper bound by reducing arbitrary hard components to two gaps and a controlled tail. It matches the two-collapse profile exactly on an explicit parameter domain. In particular, the exact profile minimax at $a=1/10,b=1/5$ is $9/98<1/10$.

This is a theorem about the profile model. Its application to pinned distances uses the separately established analytic transfer. It is not an assertion of the weakest possible dimension criterion or a distance-set counterexample.

## 1. Statement

Let

$$
0<a<b<\frac12,\qquad
b\le\frac{1+2a}{4+2a},
$$

and assume

$$
R(a,b):=4(1+a)b^2-4(a+2)b+1+3a\le0.
\tag{1}
$$

Define

$$
C_2(a,b)=\frac{(b-a)(2+a-2b-4ab)}{(1-a)(1+2b)^2}.
\tag{2}
$$

For every 1-Lipschitz $g:[0,1]\to\mathbb R$ satisfying $ax\le g(x)\le bx$, and every $n_0<1$, there is an admissible chain from $n_0$ to zero of cost at most $C_2(a,b)$. Here an edge $n\to m<n$ is admissible when $2n-m\le1$, and its cost is $g(m)-\min_{[m,n]}g$.

The chain may be chosen with at most $2\lceil\log_2(1/(1-n_0))\rceil+O(1)$ edges. The usual $O(KT)$ grid error and $O(K\epsilon)$ additive barrier error hold. The limiting optimal cost as $n_0\uparrow1$, maximized over all profiles, is exactly (2).

The proof of the upper bound follows below. The matching two-collapse profile and its exact hard components are proved in `2026-09-30-unforced-multiple-collapse.md`.

## 2. Normalization and the hard-component identity

One may assume $g(1)=a$. Indeed, clipping $g$ from above by $1+a-x$ preserves the barriers and Lipschitz property and increases every edge cost. The edgewise argument is given in the endpoint-normalization note and the independent supporting-line audit.

First assume $g$ is piecewise affine with finitely many pieces. Define

$$
H_g=\{x\in[0,1]:g(x)=\min_{[x,(1+x)/2]}g\}.
$$

The endpoints $0$ and $1$ belong to $H_g$. Write its finitely many closed interval components in increasing order, allowing degenerate components. On each component $g$ is nondecreasing. By [Keleti–Shmerkin, Lemma 5.4](https://arxiv.org/html/1801.08745), applied after the substitution $F(t)=g(1-t)-a$, the limiting optimal original cost is

$$
\Phi_0(g)=\sum_{[p,q]\text{ component of }H_g}\bigl(g(q)-g(p)\bigr)-a.
\tag{3}
$$

The endpoint correction is essential: reversing an original edge changes its cost from the smaller-coordinate endpoint drop to the larger-coordinate endpoint drop, whose total difference telescopes to $-g(1)=-a$ in the limit.

The formula (3) can be rewritten entirely in terms of the complementary gaps of $H_g$. This requires the next elementary fact.

### Gap lemma

Suppose $(q,p)$ is a gap between consecutive hard components. Then

$$
g(x)\ge g(p)\quad(q<x<p),\qquad g(q)\ge g(p).
\tag{4}
$$

To prove the first assertion, suppose $g(x)<g(p)$ for some $x\in(q,p)$. A minimum of $g$ on $[x,p]$ is attained at a point $z<p$, and $g(z)<g(p)$. On $[z,p]$ the profile is at least $g(z)$. On the portion of $[z,(1+z)/2]$ lying after $p$, hardness of $p$ gives

$$
g(y)\ge g(p)>g(z),
$$

since $(1+z)/2\le(1+p)/2$. Thus $z$ itself is hard, contradicting $z\in(q,p)$. Continuity proves the endpoint assertion.

Let $u=g(q)$, $v=g(p)$, and $\delta=u-v\ge0$. If $\delta>0$, hardness of $q$ forces $p>(1+q)/2$. Lipschitz continuity then gives

$$
\delta\le p-\frac{1+q}{2}.
\tag{5}
$$

Indeed, $g((1+q)/2)\ge u$, and its decrease by the time $p$ is at most the distance between these two points.

Telescoping the hard-component increases and the intervening gaps in (3), using $g(0)=0$, gives

$$
\Phi_0(g)=\sum_{\text{gaps}}\delta.
\tag{6}
$$

Gaps with zero drop may now be omitted. They contribute nothing to (6), and the remaining gaps preserve their order and disjointness. Lipschitz bounds between endpoints of two retained gaps continue to hold, regardless of how many zero-drop gaps were omitted.

## 3. Two uniform estimates for the tail after a gap

Consider the positive-drop gaps lying entirely after a point $p$, where $g(p)=v$. Let their total drop be $T$. Formula (5) implies, for each such gap $(q_j,p_j)$,

$$
\delta_j\le\frac{p_j-q_j}{2}-\frac{1-p_j}{2}
\le\frac{p_j-q_j}{2}.
$$

The gap intervals are disjoint and contained in $[p,1]$, so

$$
T\le\frac{1-p}{2}.
\tag{7}
$$

Independently, each drop is at most the negative variation on its gap. Summing and using the total-variation bound of a 1-Lipschitz function gives

$$
T\le\operatorname{Var}^-(g;[p,1])
\le\frac{1-p+v-a}{2}.
\tag{8}
$$

Both right sides are valid even when there are no later gaps. For any $0\le\chi\le1/2$, taking the convex combination of (7) and (8), with weights $1-2\chi$ and $2\chi$, yields

$$
T\le\frac{1-p}{2}+\chi(v-a).
\tag{9}
$$

This interpolation of the two tail bounds is what extends the exact two-gap estimate below $a=1/10$.

## 4. An exact nonnegative-weight certificate

Write

$$
s=1+2b,\qquad D=(1-a)s^2,\qquad
\chi=\frac{1+a-4ab+4b^2-2b}{D}.
\tag{10}
$$

The numerator is $1-2b+a+4b(b-a)>0$. Moreover,

$$
\chi-\frac12=\frac{R(a,b)}{2D}\le0.
$$

Hence the tail interpolation (9) applies with this choice.

If there are at least two positive-drop gaps, denote the first two by $(q_i,p_i)$, with endpoint values $u_i=g(q_i)$, $v_i=g(p_i)$ and drops $\delta_i=u_i-v_i$, for $i=1,2$. The following inequalities hold:

$$
\begin{aligned}
u_1-bq_1&\le0,\\
ap_1-v_1&\le0,\\
q_1-2p_1+2\delta_1&\le-1,\\
u_2-v_1-q_2+p_1&\le0,\\
u_2-bq_2&\le0,\\
q_2-2p_2+2\delta_2&\le-1,\\
p_2&\le1.
\end{aligned}
\tag{11}
$$

The fourth inequality is simply the Lipschitz bound between $p_1$ and $q_2$; it remains valid if intervening zero-drop gaps were omitted.

Multiply these seven inequalities, in the displayed order, by

$$
\begin{aligned}
w_1&=\frac1s,&
w_2&=\frac{1-2b}{(1-a)s},&
w_3&=\frac b{s},\\
w_4&=\frac{2b-a}{(1-a)s},&
w_5&=\frac{1+2a-4b-2ab}{D},&
w_7&=\frac{1-\chi}{2},\\
w_8&=\frac12-\chi.&&&
\end{aligned}
\tag{12}
$$

Every weight is nonnegative under the theorem's assumptions. For $w_5$, the required sign is exactly $b\le(1+2a)/(4+2a)$. The other signs follow from $a<b<1/2$ and $0<\chi\le1/2$.

The weighted left side simplifies to

$$
\delta_1+\delta_2-\frac{p_2}{2}+\chi v_2.
$$

For a check of every coefficient, the identities needed for the cancellation are

$$
w_3=bw_1,\quad w_1+2w_3=1,\quad
aw_2-2w_3+w_4=0,
$$

$$
w_2+2w_3+w_4=1,\quad
w_7=w_4+bw_5,\quad
w_4+w_5=\chi,\quad
2w_7=1-\chi.
$$

The weighted right side is $-w_3-w_7+w_8=-w_3-\chi/2$. Thus (11) proves the exact inequality

$$
\delta_1+\delta_2-\frac{p_2}{2}+\chi v_2
\le-\frac b{1+2b}-\frac\chi2.
\tag{13}
$$

Apply (9) to all remaining gaps after $p_2$. Equations (6), (9), and (13) give

$$
\begin{aligned}
\Phi_0(g)
&\le\delta_1+\delta_2+\frac{1-p_2}{2}+\chi(v_2-a)\\
&\le\frac12-\frac b{1+2b}-\left(a+\frac12\right)\chi\\
&=\frac{(b-a)(2+a-2b-4ab)}{(1-a)(1+2b)^2}.
\end{aligned}
\tag{14}
$$

This is an algebraic certificate for an arbitrary number of gaps. Its validity does not rest on a finite numerical linear program.

If there is only one positive-drop gap, (5) and the barriers give

$$
\delta\le\min\left\{p-\frac{1+q}{2},\ bq-ap\right\}
\le\frac{(2b-a)p-b}{1+2b}
\le\frac{b-a}{1+2b}.
$$

The middle inequality follows by eliminating $q$, or by intersecting the decreasing and increasing affine bounds in $q$. The single-gap value is at most $C_2$, because

$$
C_2-\frac{b-a}{1+2b}
=\frac{(b-a)(1+2a-4b-2ab)}{D}\ge0.
$$

If there are no positive-drop gaps, the cost is zero. This completes the piecewise affine upper bound.

## 5. Sharpness and the size of the verified region

The explicit profile

$$
g(x)=\min\{bx,\ at+|x-t|,\ 1+a-x\},
\qquad
t=\frac{(1+2a)(1-b)}{(1-a)(1+2b)},
$$

has cost exactly $C_2$ whenever $a<b\le(1+2a)/(4+2a)$. Its complete hard-point calculation is in the multiple-collapse note. Thus the universal upper bound (14) is sharp on the domain (1).

At $a=1/10,b=1/5$ this gives

$$
\sup_g\Phi_0(g)=\frac9{98},\qquad
\frac1{10}-\frac9{98}=\frac2{245}>0.
$$

The parameter conditions are strict at that point, so the estimate persists on a neighborhood. For another exact pair,

$$
a=\frac1{10},\quad b=\frac{21}{100},\quad
C_2=\frac{1463}{15123},\quad a-C_2=\frac{493}{151230}>0.
$$

It also reaches below the former onset:

$$
a=\frac9{100},\quad b=\frac{181}{1000},\quad
C_2=\frac{4619}{51529},\quad a-C_2=\frac{1861}{5152900}>0.
$$

Here $b>2a$, so this is an actual improvement beyond the original packing line, subject to analytic transfer and its usual strict parameter slack.

Set

$$
\alpha=\frac{3-\sqrt7}{4}.
$$

The certificate remains valid in a neighborhood of $(\alpha,2\alpha)$, since

$$
R(\alpha,2\alpha)=\frac{87-33\sqrt7}{4}<0,
$$

and

$$
1+2\alpha-4(2\alpha)-2\alpha(2\alpha)
=3\sqrt7-\frac{15}{2}>0.
$$

On the baseline, exact subtraction gives

$$
C_2(a,2a)-a
=\frac{a(1+2a)(8a^2-12a+1)}{(1-a)(1+4a)^2}.
$$

Therefore the sharp two-gap profile cost first drops below $a$ at $a>\alpha$ near this point. The matching lower construction shows why the same criterion cannot improve the baseline immediately below $\alpha$. This is sharpness of this unforced profile criterion in the certified region, not optimality of the distance theorem.

## 6. Finite starts, bounded chains, and continuous profiles

For any profile, the optimal finite-start cost $\Phi_\zeta$ is nondecreasing as $\zeta\downarrow0$. Truncate a chain at its first crossing of an earlier start to prove monotonicity: the crossing subinterval remains admissible and has no greater cost. Conversely, maximal admissible edges bridge two starts with total cost at most their distance. Hence

$$
0\le\Phi_0(g)-\Phi_\zeta(g)\le\zeta.
$$

Thus (14) bounds the infimum of costs at every finite start. Near-optimal finite chains can always be compressed without increasing cost, because

$$
c_g(l,n)\le c_g(l,m)+c_g(m,n)\qquad(l<m<n).
$$

Indeed, if $A$ and $B$ are the minima on $[l,m]$ and $[m,n]$, the difference between the right and left sides is $g(m)-\max(A,B)\ge0$. Merge adjacent edges whenever their union is admissible. When no merge is possible, $2n_i-n_{i+2}>1$, so the complementary depth more than doubles every two edges. This gives the stated uniform logarithmic length bound. Taking limits of near-optimal endpoint lists of this bounded length produces an actual chain with the asserted upper cost.

For a general continuous 1-Lipschitz profile, first normalize its endpoint, then interpolate on finer partitions containing $0,n_0,1$. Both barriers, the endpoint value, and the Lipschitz constant are preserved. The interpolants satisfy the proved upper bound and have chains of uniformly bounded length. Uniform convergence and a convergent subsequence of the endpoint lists pass admissibility and interval-minimum costs to the limit. This proves the continuous assertion.

Finally, downward grid rounding preserves $2n-m\le1$ when the terminal scale lies on the grid and changes every cost by at most twice the mesh. For approximate barriers, clamp first; the uniform profile change increases each edge cost by at most twice its size. Endpoint normalization then only increases edge costs. These steps give the same bounded-chain and perturbation guarantees required by the previously established analytic transfer.

## 7. A matching sharp single-collapse bound on the high side

The root agent supplied a second dual certificate, independently verified here coefficient by coefficient. It proves the following complementary statement:

$$
0<a<b\le\frac12,\qquad b\ge\frac{1+2a}{4+2a}
\quad\Longrightarrow\quad
\sup_g\Phi_0(g)=C_1(a,b):=\frac{b-a}{1+2b}.
\tag{15}
$$

No condition $R(a,b)\le0$ is required for this branch. The same finite-chain, perturbation, and continuous-profile conclusions hold by Section 6.

Keep the first two positive gaps and the notation of Section 4. There is now one additional inequality:

$$
v_1\le u_2.
\tag{16}
$$

To justify it even when zero-drop gaps were omitted, pass along the profile from $p_1$ to $q_2$. On each hard component the endpoint increase is nonnegative. Every intervening gap has zero drop, since these are the first two positive gaps. Telescoping shows $u_2-v_1\ge0$. No assertion of pointwise monotonicity throughout this whole interval is needed.

Use the following eight inequalities in the displayed order:

$$
\begin{aligned}
u_1-bq_1&\le0,\\
\delta_1-p_1+q_1/2&\le-1/2,\\
ap_1-v_1&\le0,\\
\delta_2-p_2+q_2/2&\le-1/2,\\
ap_2-v_2&\le0,\\
u_2-v_1-q_2+p_1&\le0,\\
p_2&\le1,\\
v_1-u_2&\le0.
\end{aligned}
\tag{17}
$$

Let $D_1=(1+2a)(1+2b)$ and multiply (17) by

$$
\begin{aligned}
\omega_1&=\frac1{1+2b},&
\omega_2&=\frac{2b}{1+2b},&
\omega_3&=\frac{2b}{D_1},\\
\omega_4&=\frac{4b(1+a)}{D_1},&
\omega_5&=\frac{1+2a-2b}{D_1},&
\omega_6&=\frac{2b(1+a)}{D_1},\\
\omega_7&=\frac{(6+8a)b-(1+2a)^2}{2D_1},&
\omega_8&=\frac{(2a+4)b-(2a+1)}{D_1}.&&
\end{aligned}
\tag{18}
$$

These weights are all nonnegative. The last one has exactly the required threshold $b\ge(1+2a)/(4+2a)$. The numerator of the penultimate one is increasing in $b$; at that threshold it equals

$$
\frac{(1+a)(1-2a)(1+2a)}{a+2}>0.
$$

The remaining signs follow from $0<a<b\le1/2$.

The weighted left side of (17) is exactly

$$
\delta_1+\delta_2-\frac{p_2}{2}.
$$

Using the half-length tail bound (7), one obtains

$$
\begin{aligned}
\Phi_0(g)
&\le\delta_1+\delta_2+\frac{1-p_2}{2}\\
&\le\frac12-\frac{\omega_2}{2}-\frac{\omega_4}{2}+\omega_7\\
&=\frac{b-a}{1+2b}.
\end{aligned}
\tag{19}
$$

The zero- and one-positive-gap cases were already bounded by this same quantity in Section 4. Therefore (19) proves the full upper statement (15).

Sharpness follows from the single-collapse profile $g(x)=\min\{bx,1+a-x\}$. Its only nondegenerate hard component is $[0,(1+2a)/(1+2b)]$. Formula (3) gives exactly $(b-a)/(1+2b)$. Thus both sides of the transition are sharp profile formulas on their respective certified domains, and they agree at $b=(1+2a)/(4+2a)$.
