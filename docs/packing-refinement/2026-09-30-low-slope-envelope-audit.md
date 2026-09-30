# Audit of the low-slope early-minimum envelope

30 September 2026. Independent verification of the profile-minimax agent's proposed early-case improvement. This is an elementary profile audit, with no assertion about the analytic transfer to distance sets.

## Outcome

The proposed envelope, the truncated affine-potential construction, and the scalar maximization are valid. A possibly positive potential at the stopping threshold is harmless: stopping discards nonnegative remaining potential rather than requiring a zero-cost continuation through that positive region.

Let $0<a\le b\le1/2$. Suppose $g$ is 1-Lipschitz with $ax\le g(x)\le bx$, and a global minimum on $[1/2,1]$ occurs at $t\in[1/2,3/4]$. Put $m=g(t)$, $v=g(1/2)$, and $e=g(1)$. Then a bounded-length admissible chain forced through $1/2$ has cost at most

$$
\min\{E(a,b),F(a,b)\},
$$

where $E$ is the previously proved cone bound and

$$
F(a,b)=\frac{b-a}{2(1+a)}+\frac{1-2a}{4}
-\frac{(1-2b)(1-a)(1+b)}{8(1-b)(1+a)}.
$$

## Envelope and stopping-potential check

The two available upper bounds on $g(z)$, for $z\ge t$, are

$$
g(z)\le bz,\qquad g(z)\le m+z-t.
$$

Their intersection is at

$$
z_*:=\frac{t-m}{1-b}.
$$

Since $m\le bt$, one has $z_*\ge t$. The line

$$
H(z):=\frac z2+(b-1/2)z_*
$$

passes through this intersection and has slope between $b$ and $1$. To the left of $z_*$ it lies above the slope-one line; to the right it lies above the slope-$b$ line. Therefore

$$
H(z)\ge\min\{bz,m+z-t\}\ge g(z)
\qquad(z\ge t).
$$

In particular $H(1)\ge e\ge a$. Write

$$
\kappa:=\frac{1/2-b}{1-b}\in[0,1/2].
$$

Then $H(1)=1/2-\kappa(t-m)$, and the initial potential budget is

$$
\frac{H(1)-e}{2}\le
P_H:=\frac{1/2-a-\kappa(t-m)}2.
$$

Both the actual initial budget and this relaxed bound are nonnegative for the actual profile.

The relevant potential is

$$
\Lambda(x)=H(2x-1)-g(x).
$$

It is nondecreasing, since its almost-everywhere derivative is $1-g'(x)\ge0$. On its positive region,

$$
(-g')_+\le\frac{1-g'}2=\frac{\Lambda'}2.
$$

Run maximal admissible jumps downward, stopping at $x=(1+t)/2$ if the positive region has not yet ended. Their cost is at most the initial positive potential divided by two; the remaining positive potential is simply omitted. If the construction instead enters $\Lambda\le0$, use zero-cost minimum edges until the current endpoint lies in $[t,(1+t)/2]$. Such zero-cost edges stay above $t$ while their starting point is greater than $(1+t)/2$, because their maximal admissible predecessor is then greater than $t$.

The edge to $t$ is admissible and has zero cost, independently of the sign of the potential at $(1+t)/2$. Thus the objection that $H(t)$ can exceed $m$ does not invalidate the construction. The final edge $t\to1/2$ is admissible and costs $v-m$.

The usual slope-one cone separately gives the initial cost bound $(1-t+m-e)/3$. Hence the total cost is at most

$$
v-m+\min\left\{\frac{1-t+m-a}{3},\;
\frac{1/2-a-\kappa(t-m)}2\right\}.
\tag{1}
$$

The same logarithmic edge bound, mesh error, and approximate-barrier stability as the existing affine-envelope construction apply. No dependence on the location of the intersection $z_*$ relative to $1$ is needed.

## Scalar maximization

For the second term in (1), it suffices to maximize

$$
T(t,m,v)=v-m+\frac{1/2-a-\kappa(t-m)}2
$$

under the relaxed constraints

$$
m\ge at,\qquad
v\le\min\{b/2,m+t-1/2\},\qquad
1/2\le t\le3/4.
$$

It increases with $v$, so take $v$ at its displayed upper bound. Put $c=(1+b)/2$.

For $m\le c-t$, the active bound is $v=m+t-1/2$, and $T$ has slope $\kappa/2\ge0$ in $m$. For $m\ge c-t$, the active bound is $v=b/2$, and $T$ has slope $-1+\kappa/2<0$ in $m$. Thus an optimal choice is

$$
m=\max\{at,c-t\}.
$$

The two branches meet at

$$
t_*:=\frac{c}{1+a}=\frac{1+b}{2(1+a)}\in[1/2,3/4].
$$

Below $t_*$, substitution gives

$$
T=(1-\kappa)t-\frac14-\frac a2+\frac{\kappa c}{2},
$$

which is increasing in $t$. Above $t_*$, it gives

$$
T=\frac b2+\frac14-\frac a2
-\left(a+\frac{\kappa(1-a)}2\right)t,
$$

which is decreasing. Consequently its maximum is attained at $t=t_*$, $m=at_*$, $v=b/2$, and equals $F(a,b)$.

The previously proved cone expression has its maximum $E(a,b)$ at the same point. In particular, (1) is bounded by $\min\{E,F\}$. The argument only requires an upper bound, so the use of relaxed scalar constraints introduces no additional hypothesis.

## Algebraic checks

An exact expansion gives

$$
8(1-b)(1+a)(F(a,b)-a)
=-2(1+a)b^2+(3+13a+12a^2)b+1-13a-12a^2.
$$

The multiplier is positive on the stated range, verifying the proposed polynomial criterion.

For locating possible joins with the earlier conditions, define the polynomial on the right as $Q_a(b)$ and set

$$
b_E=\frac{8a^2+8a-1}{a+2},\qquad
b_M=\frac{28a-3}{6}.
$$

The following exact identities were independently checked:

$$
Q_a(2a)=16a^3+6a^2-7a+1,
$$

$$
(a+2)^2Q_a(b_E)
=-(a+1)(32a^4-28a^3-75a^2-5a+4),
$$

$$
18Q_a(b_M)=2(112a^3+76a^2+30a-9).
$$

The relevant numerical roots are approximately $0.188783591161368$, $0.195322470968635$, and $0.186999504998433$, respectively. These locate candidate joins; a final piecewise statement should use exact root definitions and sign proofs rather than rounded decimal comparisons.
