# Interpolating the free head endpoint

30 September 2026. This extends the complete construction in `research/2026-09-30-adaptive-free-head.md`. It gives a continuous one-parameter family of sufficient profile bounds, sometimes strictly stronger than both the published bound $V$ and the fully adaptive bound $W$. It does not assert that this family solves the profile minimax.

## A rational one-parameter bound

Retain the domain

$$
\frac19\le a\le\frac16,\qquad 2a\le b\le\frac12,
$$

the normalized profile $g$, the starting condition $n_0\ge15/16$, and the notation

$$
k=2b-a,\quad q=\frac b{k},\quad h=\frac{1+q}{2},
\quad m=\min_{[q,1]}g,\quad e=g(1).
$$

For a fixed $\theta\in[0,1]$, define

$$
P_\theta=(1-\theta)q+\theta\frac{1+m/b}{2},
\qquad H_\theta=\frac{1+P_\theta}{2}=h_\theta+r_\theta m,
$$

where

$$
h_\theta=h-\frac{\theta a}{4k},
\qquad r_\theta=\frac{\theta}{4b}.
\tag{1}
$$

Every point below $P_\theta$ has a free continuation, since $q\le P_\theta\le Q_m$. Moreover $H_\theta\le11/12<n_0$.

Set

$$
m_\theta=\frac{a h_\theta}{1-a r_\theta},
\qquad A_0=\frac{1-a-3b}{3},
\qquad \gamma=\frac{6b-1-2a}{3a}>0,
$$

and define

$$
E_\theta=A_0+\gamma m_\theta.
\tag{2}
$$

For the late estimate put

$$
\beta=\frac1{4b},
\qquad S_\theta=\frac13-\frac{(1-b)h_\theta}{2},
\qquad
\sigma_\theta=\frac{1-3a}{6a}-\frac{(1-b)r_\theta}{2}>0,
$$

and

$$
J_\theta=\frac{\sigma_\theta/4+\beta S_\theta}{\sigma_\theta+\beta}.
\tag{3}
$$

Then there is a chain with the same bounded-length and perturbation properties as in the adaptive-head note, whose cost is at most

$$
W_\theta(a,b)=\max(E_\theta,J_\theta).
\tag{4}
$$

All expressions are rational in $a,b,\theta$, with positive denominators throughout the stated domain. In particular, $1-a r_\theta\ge7/8$, and

$$
\sigma_\theta\ge\frac{5-18a}{48a}>0.
$$

## Proof of the bound

Use exactly the four chain constructions in the adaptive-head note, replacing $Q$ by $P_\theta$ and $H$ by $H_\theta$.

If the global tail minimum $t$ lies below $P_\theta$, the cone followed by the free continuation has cost at most $(1-q)/3$. If $P_\theta<t\le H_\theta$, the positive-terminal part of the cone construction is bounded by

$$
\frac{1-a-3b+(6b-1)t-2m}{3},
\qquad t\le\min\{m/a,h_\theta+r_\theta m\}.
$$

For $m\le m_\theta$, this is bounded by the increasing line $A_0+\gamma m$. For $m\ge m_\theta$, it is bounded by a decreasing line of slope $((6b-1)r_\theta-2)/3<0$. The two lines intersect at $m_\theta$, so their common upper envelope is $E_\theta$.

If $t>H_\theta$, let $u$ minimize on $[P_\theta,H_\theta]$, with value $w$. When $w\le b(2u-1)$, apply the same reflected-minimum construction. It has the same positive-terminal expression, with $u$ in place of $t$. Now $u\le H_\theta$ and $m\ge at>aH_\theta$, hence $m>m_\theta$. The decreasing line again bounds the cost by $E_\theta$.

When $w\ge b(2u-1)$, the terminal interval is free. The cone and middle negative variation give

$$
\frac{1-e}{3}-\frac{(1-b)H_\theta}{2}+\frac{t-m}{6}
\le S_\theta+\sigma_\theta m,
$$

using $e\ge m$, $t\le m/a$, and (1). This remains valid when $t>n_0$, by omitting the cone and using monotonicity of negative variation on subintervals. Intersect with the always available floor bound $1/4-\beta m$ to obtain (3).

It remains to remove the extra term $(1-q)/3$. The following monotonicity check proves $J_\theta\ge J_1$. At $m=aq$, every line $S_\theta+\sigma_\theta m$ has the same value. The floor exceeds that value by

$$
\frac{(b-a)(5-9b)}{12(2b-a)}>0.
\tag{5}
$$

Its intersection with each increasing line therefore occurs strictly to the right of $aq$. Increasing $\theta$ lowers the increasing line at every such point, because

$$
\frac{\partial}{\partial\theta}(S_\theta+\sigma_\theta m)
=\frac{1-b}{8b}(aq-m)<0.
$$

The intersection moves right and its value decreases. Thus $J_\theta\ge J_1$. The adaptive-head note proves $(1-q)/3\le J_1$, so (4) follows.

There remain only a bounded number of cone, maximal-edge and free portions, with $H_\theta\le11/12$ uniformly in $\theta$. The edge-count, compactness, grid-rounding and barrier-clamping proofs apply without change. This finishes the profile estimate, including its finite-scale transfer requirements.

## Optimizing within this family

For fixed $a,b$, the function $E_\theta$ increases strictly with $\theta$, since

$$
\frac{d m_\theta}{d\theta}
=\frac{a^2(b-a)}{8b(2b-a)(1-a r_\theta)^2}>0.
$$

The proof of (5) shows that $J_\theta$ decreases strictly. Consequently

$$
W_{\mathrm{int}}(a,b)=\min_{0\le\theta\le1}\max(E_\theta,J_\theta)
\tag{6}
$$

is attained. Its minimizer is $0$ if $E_0\ge J_0$, is $1$ if $E_1\le J_1$, and otherwise is the unique intersection $E_\theta=J_\theta$. Here the subscripts refer to the parameter $\theta$, not to the separately used zero-terminal cost. Clearing the positive denominators makes the intersection a polynomial equation of degree at most two in $\theta$.

Equation (6) is an exact, unambiguous continuous sufficient profile cost. Continuity follows from joint continuity of (4) and minimization over the fixed compact interval $[0,1]$. It may be combined with the earlier estimates by taking their minimum. This optimization concerns only this family of chain constructions.

## A strict example beyond both previous bounds

Take

$$
a=\frac7{50},\qquad b=\frac5{16},\qquad \theta=\frac12.
$$

Exact substitution yields

$$
E_{1/2}=\frac{1275741}{9156800},\qquad
J_{1/2}=\frac{123027}{881924},
$$

and the positive margins are

$$
\frac7{50}-E_{1/2}=\frac{6211}{9156800},\qquad
\frac7{50}-J_{1/2}=\frac{11059}{22048100}.
$$

The fully adaptive estimate does not prove this pair: its early term exceeds $a$ by $149/88800$. Neither does the published estimate $V$: its two late intersection values satisfy

$$
J_F-a=\frac{2363}{10990100}>0,
\qquad J_V-a=\frac{10861}{86291200}>0.
$$

Thus (4) is strictly stronger than simply taking the minimum of those two available bounds. Under the established transfer argument, this supplies the dimension pair

$$
d=\frac{57}{50}=1.14,\qquad D=\frac{21}{16}=1.3125.
$$

These exact inequalities, rather than numerical optimization, establish the strict improvement.
