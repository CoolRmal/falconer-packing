# Independent audit of the normalized supporting-line estimate

30 September 2026. This audits `2026-09-30-normalized-adaptive-head-audit.md` independently of its author. The supporting-line chain, the normalized late estimate, and the proposed universal bound pass the audit. No PDF source is edited here.

## Verified statement

Assume

$$
\frac1{10}\le a\le\frac16,\qquad 2a\le b\le\frac12.
$$

For a 1-Lipschitz profile satisfying $ax\le g(x)\le bx$, and a starting point $15/16\le n_0<1$, an unforced admissible chain to zero exists of cost at most

$$
N(a,b)=\max\{F(a,b),E(a,b),P(a,b)\},
$$

where

$$
F=\frac{(1-a)(b-a)}{4(2b-a)(1-b)},\qquad
E=\frac{(b-a)(1+6b-a)}{3(4b-a)},
$$

and

$$
P=\begin{cases}
\dfrac{(1+3b)(b-a)}{8b},&b\le1/3,\\[6pt]
\dfrac{(b-a)(2+a-9ab)}{2(4b+3a-13ab)},&b\ge1/3.
\end{cases}
$$

The two expressions for $P$ agree at $b=1/3$. The same logarithmic chain-length and grid/barrier perturbation bounds as in the earlier profile lemmas hold. This is a sufficient profile estimate; global optimality is not established.

## 1. Normalization really permits an upper bound for every profile

Replace $g$ by

$$
\widetilde g(x)=\min\{g(x),1+a-x\}.
$$

The new profile has the same barriers and Lipschitz constant, and endpoint value $a$. For an edge $n\to v$, if $g(v)\le1+a-v$, its lower-endpoint value is unchanged and the interval minimum can only decrease. Thus its cost cannot decrease. If $g(v)>1+a-v$, then

$$
c_{\widetilde g}(v,n)\ge(1+a-v)-(1+a-n)=n-v\ge c_g(v,n).
$$

Consequently every chain produced for the normalized profile gives at most the same cost for the original profile. There is no change in admissibility or chain length. In the remaining proof write $g$ for the normalized profile.

## 2. Supporting-line majorization and the initial potential

Let $t$ be a minimum point on $[q,1]$, where

$$
q=\frac b{2b-a},\qquad m=g(t),\qquad g(1)=a.
$$

Then $t\ge q$ and $m\le a$. On $[t,1]$ the two affine bounds are

$$
g(z)\le bz,\qquad g(z)\le m+z-t.
$$

Their intersection is $z_*=(t-m)/(1-b)$. Define

$$
H(z)=\frac z2+\left(b-\frac12\right)z_*.
$$

This majorizes their minimum for every real $z$, not only when $z_*$ lies in $[t,1]$. Indeed, the increasing-slope-one line is the smaller line for $z\le z_*$, and

$$
H(z)-(m+z-t)=\frac{z_*-z}{2}\ge0.
$$

For $z\ge z_*$, the smaller line is $bz$, and

$$
H(z)-bz=\left(\frac12-b\right)(z-z_*)\ge0.
$$

Thus $H$ majorizes $g$ on $[t,1]$. In particular $H(1)\ge g(1)=a$. There is no missing positive-part correction at the endpoint.

Put $s=(1+t)/2$ and

$$
\Lambda(x)=H(2x-1)-g(x),\qquad x\in[s,1].
$$

It is nondecreasing, and almost everywhere

$$
(-g')_+\le\frac{1-g'}2=\frac{\Lambda'}2.
$$

This potential is used only at endpoints $x\ge s$, so that $2x-1\ge t$ and the majorization just proved is available at every required point.

## 3. Both possible stopping geometries are valid

If $n_0\le s$, the jump directly to $t$ is admissible and free, provided $n_0\ge t$. The latter holds in the early case where this chain is used: $t\le H_m\le11/12<n_0$.

Otherwise start above $s$. There are two possibilities.

- If the potential is positive all the way down to $s$, use maximal admissible edges, shortening the last edge to end at $s$. Their total cost is at most $(\Lambda(n_0)-\Lambda(s))/2\le\Lambda(n_0)/2$. Discarding the nonnegative residual potential is legitimate. Then jump freely to $t$.
- If the potential reaches zero before $s$, use maximal edges through the positive region and stop at its boundary. Thereafter, for a current endpoint $n\ge s$ with $\Lambda(n)\le0$, one has $g(2n-1)\le H(2n-1)\le g(n)$. A leftmost interval minimum yields a free admissible edge. Its lower endpoint is at least $t$. Continue until the endpoint lies in $[t,s]$, and then jump freely to $t$.

If the initial potential is already nonpositive, only the second procedure's free steps are needed. Because $\Lambda$ is nondecreasing and $\Lambda(1)=H(1)-a\ge0$, all possibilities give cost at most

$$
\frac{H(1)-a}{2}
=\frac{1/2-a-\kappa(t-m)}2,
\qquad \kappa=\frac{1/2-b}{1-b}\ge0.
$$

The jump to $t$ is free because $g(t)$ is a minimum on $[t,1]$. This argument does not require $H(t)=m$ or $\Lambda(s)\le0$.

Since $t-m\ge q-a$, the resulting bound is at most

$$
\frac{1/2-a-\kappa(q-a)}2
=\frac{(1-a)(b-a)}{4(2b-a)(1-b)}=F.
$$

It applies precisely when the continuation after $t$ is free: either $t\le Q_m$, or the positive-part terminal cost in the range $Q_m<t\le H_m$ vanishes. Thus it replaces the former $E_1$ case without altering the positive-terminal or late cases.

## 4. The adaptive positive-terminal estimate remains valid at the new endpoint

Set

$$
Q_m=\frac{1+m/b}{2},\qquad H_m=\frac{3+m/b}{4},\qquad
m_0=\frac{3ab}{4b-a}.
$$

The early positive-terminal cost is bounded by

$$
A(t,m)=\frac{1-a-3b+(6b-1)t-2m}{3},
\qquad t\le\min\{m/a,H_m\}.
$$

For $m\le m_0$, substitution of $t\le m/a$ gives an affine function with slope $(6b-1-2a)/(3a)\ge0$. For $m\ge m_0$, substitution of $t\le H_m$ gives an affine function with slope $-(2b+1)/(12b)<0$. Their common value at $m_0$ is exactly $E$. The nonnegative first slope is enough: at $a=1/10,b=1/5$ it vanishes, but the maximum remains the same intersection value.

In the late reflected case, the expression after telescoping the running-minimum correction is

$$
\frac{1-a-3b+(6b-1)u-2m}{3},
\qquad u\le H_m,\quad m>m_0.
$$

The same decreasing affine bound gives $E$. The earlier reflection proof uses only Lipschitz continuity on the reflected portion and the unchanged original profile on the terminal free portion, so normalization creates no new barrier requirement.

## 5. The normalized late free-terminal estimate

The variation construction, including the possibility that $t>n_0$ and its nonnegative cone allowance is omitted, gives

$$
\text{cost}\le S(m)=\frac{-1-8a+9b}{24}
+\frac{4b-3a-ab}{24ab}m.
$$

Its slope is positive because $4b-3a-ab\ge a(5-2a)>0$. The alternative floor chain gives

$$
L(m)=\frac{1-2a}{4}-\frac{1-2b}{4b}m.
$$

Normalization supplies the crucial additional restriction $m\le a$. Direct calculation gives

$$
S(a)=\frac{(1+3b)(b-a)}{8b},\qquad
S(a)-L(a)=\frac{(b-a)(3b-1)}{8b}.
$$

When $b\le1/3$, monotonicity alone yields $S(m)\le S(a)$, proving the first branch of $P$. When $b\ge1/3$, the intersection of $S$ and $L$ yields the second branch:

$$
\min\{L(m),S(m)\}
\le\frac{(b-a)(2+a-9ab)}{2(4b+3a-13ab)}.
$$

At $b=1/3$ the intersection occurs at $m=a$, so the branches agree. The denominator is positive throughout the domain, since $4b+3a-13ab=b(4-13a)+3a>0$. At $b=1/2$, the floor is constant and the same expression gives its value $(1-2a)/4$.

Together these cases prove the universal maximum $N$ stated above.

## 6. Strict improvement starts above $a=1/10$

On $b=2a$, one has

$$
F=\frac{1-a}{12(1-2a)},\qquad
E=\frac{1+11a}{21},\qquad
P=\frac{1+6a}{16}.
$$

The first is strictly below $a$ on the entire closed interval $[1/10,1/6]$: the equivalent polynomial $24a^2-13a+1$ is decreasing there and is already negative at $1/10$. Furthermore,

$$
a-E=\frac{10a-1}{21},\qquad
a-P=\frac{10a-1}{16}.
$$

Hence $N(1/10,1/5)=1/10$ and $N(a,2a)<a$ whenever $a>1/10$. Continuity gives a nonempty interval of $b>2a$ with $N(a,b)<a$ for every such $a$. In the distance parameters, this supplies improvement beyond the coherent packing line for every $d>11/10$ in the relevant low-dimensional range. The exact endpoint $a=1/10$ is not included in that strict improvement.

## 7. Bounded chains and perturbations

For a piecewise affine profile, the maximal-edge and leftmost-minimum procedures terminate. The supporting line adds only a fixed number of such portions. Alternatively, arbitrary finite admissible chains can be compressed without increasing cost: whenever their union remains admissible,

$$
c_g(l,n)\le c_g(l,m)+c_g(m,n)\qquad(l<m<n).
$$

After all possible adjacent merges, complementary depth more than doubles every two edges, giving an absolute logarithmic bound in $1/(1-n_0)$.

For continuous profiles, interpolate while retaining the endpoint value $a$, both barriers, and the Lipschitz constant. Pass to a limit of chains of uniformly bounded length. The admissibility condition is closed, and interval minima are continuous under these limits. Downward rounding to a prescribed grid preserves admissibility and changes each edge cost by at most twice the mesh. For approximate barriers, clamp first, normalize second, and use the edgewise monotonicity of normalization. The standard $O(K\epsilon+KT)$ error remains valid.

No unresolved geometric or algebraic issue was found in the proposed estimate. The exact global minimax, and the weakest possible dimension condition, remain separate open optimization questions.

## 8. The full interpolated family also passes the audit

The root agent subsequently proposed interpolation between the original fixed head interval and the adaptive one, retaining both the length and variation estimates. This stronger family is valid as well.

Fix $0\le\theta\le1$, and define

$$
h_\theta=\frac{1+q}{2}-\frac{\theta a}{4(2b-a)},\qquad
r_\theta=\frac{\theta}{4b},\qquad
H_\theta(m)=h_\theta+r_\theta m.
$$

The actual head is

$$
H_\theta(m)=(1-\theta)\frac{1+q}{2}+\theta\frac{3+m/b}{4}.
$$

Its left endpoint is $Q_\theta(m)=2H_\theta(m)-1$. Since $aq\le m$, the enlarged free endpoint $Q_m$ is at least $q$, and therefore

$$
q\le Q_\theta(m)\le Q_m,\qquad
H_\theta(m)\le H_m\le11/12<n_0.
$$

Thus every geometric construction continues to apply with the head interval $[Q_\theta,H_\theta]$. In particular, the terminal interval is free below $Q_\theta$, and the reflection leaves it unchanged.

Write

$$
A_0=\frac{1-a-3b}{3},\qquad
\gamma=\frac{6b-1-2a}{3a}\ge0,\qquad
L_0=\frac{1-2a}{4},\qquad \lambda=\frac{1-2b}{4b}\ge0,
$$

and put

$$
m_\theta=\frac{a h_\theta}{1-a r_\theta},\qquad
E_\theta=A_0+\gamma m_\theta,\qquad
J_E=\frac{\gamma L_0+\lambda A_0}{\gamma+\lambda}.
$$

All denominators are positive. In particular, $a r_\theta\le1/8$. Although $\gamma$ can vanish at $a=1/10,b=1/5$, at that point $\lambda>0$. If $\lambda=0$, then $b=1/2$ and $\gamma>0$.

For the early positive-terminal case, the two substitutions for $t$ give

$$
A(t,m)\le A_0+\gamma m,
$$

and

$$
A(t,m)\le A_0+\frac{6b-1}{3}h_\theta
+\frac{(6b-1)r_\theta-2}{3}m.
$$

The first is nondecreasing, while the second has strictly negative slope, since

$$
\frac{(6b-1)r_\theta-2}{3}
\le-\frac{2b+1}{12b}<0.
$$

Their intersection is $m=m_\theta$, so the cheaper bound is at most $E_\theta$. Comparing the first line with the floor line $L_0-\lambda m$ separately gives $J_E$. Hence the early positive case costs at most $\min(E_\theta,J_E)$.

In the late reflected case, $t>H_\theta(m)$ and $m\ge at$ imply $m>m_\theta$. The reflected cost is bounded by the second, decreasing line, so is at most $E_\theta$. The floor line is at most its value at $m_\theta$. Comparing both lines at that point with their intersection value shows

$$
\min\{E_\theta,L_0-\lambda m_\theta\}\le J_E.
$$

Thus the same bound applies. At the corner $\gamma=0$, these statements remain valid because $J_E=A_0$, and a constant line already gives that bound.

The early zero-terminal cost is bounded by both $(1-q)/3$ and the supporting-line estimate $F$. Thus set

$$
Z=\min\left\{\frac{1-q}{3},F\right\}.
$$

For the late free-terminal case, the variation and length constructions give the two affine bounds $A_i+\sigma_i m$, where

$$
A_v=\frac{1-a}{3}-\frac{1-b}{2}h_\theta,
\qquad
\sigma_v=\frac{1-a}{6a}-\frac{1-b}{2}r_\theta,
$$

and

$$
A_l=\frac{1-a}{3}-h_\theta,
\qquad
\sigma_l=\frac{a+2}{3a}-r_\theta.
$$

Their slopes are positive uniformly in the domain. For example,

$$
\sigma_v\ge\frac{5-2a}{48a}>0,
\qquad
\sigma_l\ge\frac{8a+13}{24a}>0.
$$

Consequently $m\le a$ gives the endpoint bounds $P_i=A_i+a\sigma_i$. Comparing each line with the floor also gives

$$
J_i=\frac{\sigma_iL_0+\lambda A_i}{\sigma_i+\lambda}.
$$

All four are upper bounds obtainable by the available chains. The normalized family therefore satisfies

$$
\boxed{\displaystyle
C_\theta(a,b)=\max\left\{
Z,\ \min(E_\theta,J_E),\ \min(P_v,J_v,P_l,J_l)
\right\}.}
$$

This is a valid universal cost for each fixed $\theta\in[0,1]$. The constructions have the same bounded number of portions independently of $\theta$. The earlier compactness, downward rounding, and barrier-clamping arguments therefore apply uniformly, with no new perturbation issue. One may also minimize this continuous expression over the compact interval $[0,1]$; its minimum is attained and depends continuously on $(a,b)$. The minimizing interpolation depends only on the two parameters, and does not introduce an additional profile assumption.

## 9. Independent monotonicity and root audit

Let $C_*(a,b)=\min_{0\le\theta\le1}C_\theta(a,b)$. For fixed $a$, this function is strictly increasing in $b$ on $[2a,1/2]$. The following checks prove strictness, including the interpolation minimum.

First, factor the early value as

$$
E_\theta=\frac{b-a}{3(2b-a)}T_\theta,
\qquad
T_\theta=\frac{12b^2+(2-8a)b-a(1-a)\theta}{4b-a\theta}.
$$

The first factor is positive and strictly increasing. Also

$$
T_\theta(2a)=\frac{(32+\theta)a+4-\theta}{8-\theta}>0,
$$

and

$$
\partial_bT_\theta
=\frac{48b^2-24ab\theta+2a\theta+4a^2\theta}{(4b-a\theta)^2}>0.
$$

For the last sign, $a\le b/2$ gives $48b^2-24ab\theta\ge36b^2$. Thus $E_\theta$ is strictly increasing.

The previously computed derivative of $J_E$ remains positive on the enlarged range $a\ge1/10$:

$$
\partial_bJ_E
=\frac{a(1-a)(60b^2-12b+1-4a)}{(24b^2-14ab+3a-4b)^2}>0.
$$

Indeed the quadratic in $b$ is increasing for $b\ge2a\ge1/5$, and its value at $b=2a$ is $240a^2-28a+1\ge3/5$ for $a\ge1/10$. All denominators remain positive as already checked.

For the late lines, retain a fixed real $m>0$ while varying $b$. Direct differentiation gives

$$
\partial_bH_\theta(m)
=-\frac{a(1-\theta)}{2(2b-a)^2}-\frac{\theta m}{4b^2}<0.
$$

Consequently both $S_i(m)=A_i+\sigma_i m$ increase strictly in $b$: the length expression contains $-H_\theta(m)$, while the variation derivative is

$$
\frac{H_\theta(m)}2-rac{1-b}{2}\partial_bH_\theta(m)>0.
$$

Here $H_\theta(m)>0$. In particular, the endpoint values $P_i=S_i(a)$ increase strictly. The floor line also increases strictly for $m>0$:

$$
\partial_b(L_0-\lambda m)=\frac{m}{4b^2}>0.
$$

To apply this observation to the intersection values $J_i$, their intersection points must be positive. In fact they are larger than $aq$. At $m=aq$, the head $H_\theta(aq)=(1+q)/2$ is independent of $\theta$, and direct subtraction gives

$$
L(aq)-S_v(aq)=\frac{(b-a)(5-2a-9b)}{12(2b-a)}>0,
$$

$$
L(aq)-S_l(aq)=\frac{(4-a)(b-a)}{6(2b-a)}>0.
$$

Both increasing lines meet the decreasing floor strictly to the right of $aq>0$. Now fix $b_1<b_2$ and evaluate the two lines for $b_2$ at their intersection point for $b_1$. Both values strictly increase, so their minimum is strictly greater than $J_i(a,b_1)$. Since the intersection value for $b_2$ is the supremum over $m$ of that minimum, $J_i(a,b_2)>J_i(a,b_1)$. This argument includes $b_2=1/2$, when the floor becomes constant.

Finally, both terms forming $Z$ increase strictly: $(1-q)/3=(b-a)/(3(2b-a))$ does, and

$$
F=\frac{1-a}{4}\frac{b-a}{2b-a}\frac1{1-b}
$$

is a product of positive strictly increasing factors. Finite minima and maxima of strictly increasing functions are strictly increasing. It follows that $C_\theta$ is strictly increasing for every fixed $\theta$.

This property passes to $C_*$ without a uniform derivative estimate. Given $b_1<b_2$, take a minimizer $\theta_2$ at $b_2$. Then

$$
C_*(a,b_2)=C_{\theta_2}(a,b_2)
>C_{\theta_2}(a,b_1)\ge C_*(a,b_1).
$$

The endpoint checks are also exact. At $b=1/2$, $\lambda=0$, so $J_E=J_v=J_l=L_0$. Moreover $E_\theta\ge E_0=(1-2a)/3>L_0$; the inequality follows from the already computed nonnegative derivative of $m_\theta$ in $\theta$. Also $Z\le F=L_0$. Therefore

$$
C_\theta(a,1/2)=C_*(a,1/2)=\frac{1-2a}{4}.
$$

At $b=2a$, the choice $\theta=1$ is bounded by the estimate $N$ audited above. Thus $C_*(a,2a)<a$ for $a>1/10$. At $a=1/10,b=1/5$, $\gamma=0$ gives $E_\theta=J_E=a$ for every $\theta$, so every $C_\theta\ge a$; the choice $\theta=1$ attains $a$.

The intermediate value theorem and strict monotonicity consequently give a unique root $\beta(a)\in[2a,1/2]$ of $C_*(a,\beta(a))=a$, with

$$
\beta(1/10)=1/5,\qquad \beta(1/6)=1/2.
$$

The root lies strictly inside its interval for $1/10<a<1/6$. Its continuity follows by taking convergent subsequences of roots, using joint continuity of the compact minimum $C_*$, and invoking uniqueness at the limiting parameter. Hence the proposed root-envelope dimension statement has no numerical uniqueness or continuity assumption.

On the domain of the published bound $V$, namely $1/8\le a\le1/6$, the new curve is never worse. At $\theta=0$, the early expressions are exactly the earlier $E_2,J_E$ and the late intersection expressions are exactly the earlier $J_F,J_V$, with the extra endpoint and length alternatives only lowering the cost. The zero term is harmless because

$$
Z\le E_1\le\min(E_2,J_E),
$$

as proved in the published redundant-term calculation. Thus $C_*\le C_0\le V$ throughout that domain.
