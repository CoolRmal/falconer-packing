# Exact algebra for the normalized-minimum bound

30 September 2026. This note audits the proposed scalar bounds. It does not
assert the new profile estimate: that geometric argument requires a separate
proof. No published proof file was changed.

## 1. Definitions and a pointwise simplification

Assume

$$
\frac1{10}\le a\le\frac16,\qquad 2a\le b\le\frac12.
$$

Write

$$
F=\frac{(1-a)(b-a)}{4(2b-a)(1-b)},\qquad
E=\frac{(b-a)(1+6b-a)}{3(4b-a)},
$$

$$
P=\begin{cases}
P_1=\dfrac{(1+3b)(b-a)}{8b},&b\le1/3,\\[4pt]
P_2=\dfrac{(b-a)(2+a-9ab)}{2(4b+3a-13ab)},&b\ge1/3,
\end{cases}
$$

and retain the earlier intersection

$$
J=\frac{(1-a)(b-a)(6b-1)}{24b^2-14ab+3a-4b}.
$$

All displayed denominators are positive. For the last one, use

$$
24b^2-14ab+3a-4b\ge b(17b-5/2)>0,
$$

since $$a\le b/2$$, $$3-14b<0$$, and $$b\ge1/5$$.
The two definitions of $$P$$ agree at $$b=1/3$$, where both are
$$(1-3a)/4$$.

There are two useful pointwise comparisons throughout the full range:

$$F\le P\le E.\tag{1}$$

For $$P_1-F$$, cancel the positive common factors. Its sign is the sign of

$$
H=4b^2-6b^3+a(3b^2-1).
$$

For $$1/5\le b\le1/3$$, using $$a\le b/2$$ gives

$$
H\ge\frac b2(-1+8b-9b^2)>0.
$$

For $$P_2-F$$, the corresponding numerator factors as

$$
(1-2b)Q,\qquad
Q=4b-7a+11ab-18ab^2+a^2+9a^2b.
$$

Here $$\partial_b Q=4+11a-36ab+9a^2>0$$ on the range, and

$$Q(a,1/3)=\frac43(1-a)(1-3a)>0.$$

Thus $$F<P$$ unless $$b=1/2$$, where equality holds.

To prove the other comparison, the sign of $$E-P_1$$ is that of

$$
12b^2-4b+ab+3a
\ge12(b-1/5)(b-1/8)\ge0.
$$

For $$b\ge1/3$$, the sign of $$P_2-P_1$$ is that of

$$
(3b-1)\bigl(a(b+3)-4b\bigr)\le0.
$$

This proves (1). Consequently the original proposed expression has the
exact simplification

$$N=\max(F,E,P)=E.\tag{2}$$

If the earlier intersection is retained, the refined expression is exactly

$$
W=\max\{F,\min(E,J),P\}
=\max\{\min(E,J),P\}.
\tag{3}
$$

In particular, $$F$$ is redundant as a function, not only at the threshold.

## 2. Monotonicity and the individual roots

For fixed $$a$$, all of $$E,J,P$$ are strictly increasing in $$b$$.
For $$E$$, both positive factors $$(b-a)/(4b-a)$$ and $$1+6b-a$$
are strictly increasing. For $$J$$, differentiation gives

$$
\partial_bJ=
\frac{a(1-a)(60b^2-12b+1-4a)}
 {(24b^2-14ab+3a-4b)^2}>0.
$$

The bracket is increasing for $$b\ge1/5$$ and, at $$b=2a$$, is
$$240a^2-28a+1\ge3/5$$ for $$a\ge1/10$$.
The derivative of $$P_1$$ is plainly positive. For $$P_2$$, its derivative
numerator before dividing by the squared displayed denominator is

$$
28a-72ab^2-38a^2-108a^2b+234a^2b^2+28a^3.
$$

This decreases in $$b\ge0$$ on the parameter range. At $$b=1/2$$ it is

$$\frac a2(20-67a+56a^2)>0.$$

Together with continuity at $$b=1/3$$, this proves strict monotonicity of
$$P$$ and hence of $$W$$.

The equation $$E=a$$ has the unique relevant root

$$
e(a)=\frac{19a-1+\sqrt{265a^2-14a+1}}{12}.
\tag{4}
$$

Indeed its level polynomial is

$$6b^2+(1-19a)b+4a^2-a,$$

which has a negative constant term and positive leading coefficient. On the
whole parameter range,

$$N<a\quad\Longleftrightarrow\quad b<e(a).\tag{5}$$

The root is $$2a$$ at $$a=1/10$$ and strictly larger when $$a>1/10$$.

The larger root of the level equation for $$J=a$$ is

$$
j(a)=\frac{1+a-20a^2+
\sqrt{400a^4-520a^3+177a^2-22a+1}}
 {12(1-5a)}.
\tag{6}
$$

The level polynomial is

$$
6(1-5a)b^2+(20a^2-a-1)b+a-4a^2.
\tag{7}
$$

Its smaller root is below $$a$$ for $$a>1/10$$: its value at $$b=a$$
is $$-a^2(10a-1)<0$$. At $$a=1/10$$ the two roots are $$a$$ and
$$2a$$. Thus, in the domain $$b\ge2a$$, the inequality $$J<a$$ is
equivalent to $$b<j(a)$$. This remains correct when $$j(a)<2a$$;
then the inequality has no solution in the domain.

The relevant root of $$P=a$$ is

$$
p(a)=\begin{cases}
\dfrac{11a-1+\sqrt{121a^2-10a+1}}6,&a\le1/7,\\[7pt]
\dfrac{C(a)-\sqrt{C(a)^2-36a^2(2+7a)}}{18a},&a\ge1/7,
\end{cases}
\tag{8}
$$

where $$C(a)=2-7a+35a^2$$. The corresponding level polynomials are

$$
3b^2+(1-11a)b-a,
\qquad
-9ab^2+(2-7a+35a^2)b-2a-7a^2.
$$

Both give the root $$b=1/3$$ at $$a=1/7$$. On $$b\le1/2$$ the
second level polynomial is strictly increasing, since its derivative is at
least $$2-16a+35a^2=(5a-1)(7a-2)>0$$. This selects the smaller
quadratic root in (8).

By (1), $$e(a)\le p(a)$$. Therefore the exact cutoff of (3) is

$$
W<a\quad\Longleftrightarrow\quad
b<\beta(a),\qquad
\beta(a)=\min\{p(a),\max(e(a),j(a))\}.
\tag{9}
$$

Existence and uniqueness can also be read directly from the cost. At
$$b=2a$$, both $$E-a=(1-10a)/21$$ and $$P-a=(1-10a)/16$$ are
nonpositive, strictly negative for $$a>1/10$$. At $$b=1/2$$,
$$W=(1-2a)/4\ge a$$, with equality only at $$a=1/6$$.

## 3. The active branches of the refined cutoff

Define

$$
\kappa=\frac{31-\sqrt{601}}{45}
=0.144104414571943\ldots,
$$

and let $$\gamma$$ be the unique root in $$[1/7,1/6]$$ of

$$
T(a)=986a^3-1127a^2+256a-16.
\tag{10}
$$

Then

$$
\gamma=0.164620336615410\ldots,
\qquad
\beta(a)=\begin{cases}
e(a),&1/10\le a\le\kappa,\\
j(a),&\kappa\le a\le\gamma,\\
p(a),&\gamma\le a\le1/6.
\end{cases}
\tag{11}
$$

Here the last branch uses the second formula in (8).

The following exact resultant identities verify all possible interior
crossings. Write $$H_E,H_J,H_{P_2}$$ for the level polynomials above.
Direct polynomial expansion gives

$$
\operatorname{Res}_b(H_E,H_J)
=-12a^2(10a-1)(4a-1)(45a^2-62a+8),
$$

$$
\operatorname{Res}_b(H_J,H_{P_2})
=-9a^2(6a-1)T(a).
$$

The only interior crossing of $$e,j$$ in $$[1/10,1/6]$$ is $$\kappa$$.
Their order is fixed by exact sign witnesses: at $$a=7/50,b=61/200$$,
$$E-a=-13/4320<0$$ while $$J-a=181/166960>0$$; at
$$a=3/20,b=7/20$$ the signs are reversed.

The polynomial $$T$$ is strictly decreasing on $$[1/7,1/6]$$. Indeed
its derivative is negative at $$1/7$$ and its second derivative is negative
throughout that interval. Also

$$T(4/25)=2304/15625>0,\qquad T(33/200)=-53359/4000000<0.$$

Thus $$\gamma$$ exists uniquely. The actual root order is checked by:
at $$a=4/25,b=43/100$$, $$J-a=1/2660>0$$ and
$$P_2-a=-37/54400<0$$; at $$a=33/200,b=959/2000$$,
$$J-a=-1079/238995280<0$$ and
$$P_2-a=59593/2215156000>0$$. These witnesses and the resultant
identity prove (11), including the endpoint equality at $$a=1/6$$.

The three active root branches increase with $$a$$. For $$e$$ this follows
by implicit differentiation of $$H_E$$: $$\partial_aH_E<0$$ and
$$\partial_bH_E>0$$. For $$j$$ in its active range, $$b=j(a)\ge2a$$
implies $$\partial_aH_J\le1-10a-40a^2<0$$, while the derivative in
$$b$$ is positive at the larger root. For $$p$$ the same conclusion
follows from the two level polynomials; for the second one
$$\partial_aH_{P_2}<0$$ follows, for example, from the uniform upper
bound $$7/3-17/5<0$$. Hence the cutoff is continuous and increasing.

## 4. Exact comparison with the previously published cost

Use $$V$$ and $$b_*$$ as in the preceding minimum appendix. The new
expression $$W$$ does not dominate the old result everywhere. In fact,
when the two results are combined, the only new interval is governed by
the simple root $$e$$; the other two branches in (11) add no further gain.

Define

$$
Q(a)=100-1724a+16495a^2-83494a^3+126464a^4-43504a^5.
\tag{12}
$$

It has exactly one root $$\theta$$ in $$[1/8,1/6]$$, and

$$
0.138<\theta<0.139,\qquad
\theta=0.138689025873107\ldots.
\tag{13}
$$

The exact comparison is

$$
e(a)>b_*(a)\quad(1/8\le a<\theta),\qquad
e(\theta)=b_*(\theta),\qquad
e(a)<b_*(a)\quad(\theta<a\le1/6).
\tag{14}
$$

Here are explicit algebraic certificates, avoiding numerical root assumptions.
The difference of the new and old early bounds has sign

$$
E-E_{\rm old}quad\text{has sign}\quad
3a(b-a)(6b-2a-1),
$$

and is strictly positive on the comparison range. Thus at $$b=e(a)$$ the
old early term is strictly below $$a$$. The resultant of $$H_E$$ with the
old $$J_V=a$$ level polynomial is exactly $$6a^3Q(a)$$.

For a polynomial of degree $$n$$ on an interval, express it in the Bernstein
basis $$\binom ni t^i(1-t)^{n-i}$$ after linear rescaling to $$0\le t\le1$$.
All basis functions are nonnegative and their sum is one. The Bernstein
coefficients of $$Q'$$ on $$[1/8,1/6]$$ are

$$
\left(-\frac{148259}{256},-\frac{63215}{96},
-\frac{438527}{576},-\frac{23773}{27},-\frac{163525}{162}\right).
$$

They prove strict decrease. Exact evaluation gives $$Q(138/1000)>0$$
and $$Q(139/1000)<0$$, proving (13). At $$a=1/8$$, the old $$J_V$$
at $$e(a)$$ is above $$a$$; at $$a=1/6$$ it is below $$a$$. Therefore
the unique resultant zero is the actual crossing, with the asserted signs.

One must also check the old $$J_F$$ before this crossing. Its level resultant
with $$H_E$$ is $$2a^3Q_F(a)$$, where

$$
Q_F=164-1786a+9287a^2-36740a^3+9904a^4-512a^5.
$$

The Bernstein coefficients of $$Q_F'$$ on $$[1/8,1/6]$$ are

$$
\left(-\frac{17755}{16},-\frac{56837}{48},
-\frac{370421}{288},-\frac{611381}{432},-\frac{127216}{81}\right).
$$

They are negative, and $$Q_F(139/1000)>0$$. Thus there is no crossing
before $$\theta$$. At $$a=1/8$$, the old $$J_F$$ is already above
$$a$$ at $$b=2a$$, so it remains above at $$b=e(a)$$ throughout this
interval. Together these facts prove (14) for the old maximum of minima.

Finally, $$b_*(a)\ge j(a)$$ for $$\kappa\le a\le1/6$$. It suffices
to check that the old $$J_F$$ at $$b=j(a)$$ is below $$a$$. The relevant
resultant, apart from the nonzero factor $$12a^3(6a-1)(a-1)$$, is

$$R_F=80a^4-376a^3-209a^2+110a-10.$$

Its Bernstein coefficients on $$[7/50,1/6]$$ are

$$
\left(\frac{94559}{312500},\frac{94547}{187500},
\frac{44789}{67500},\frac{701}{900},\frac{275}{324}\right)>0.
$$

There is therefore no interior crossing there. The sign at $$a=3/20$$
is negative: $$j(a)=(7+\sqrt{13})/30<9/25$$ and the old
$$J_F(3/20,9/25)-3/20=-136/51015$$. At the right endpoint both roots
are $$1/2$$. Since $$\beta\le j$$ in this part of (11), the refined
intersection does not improve the old cutoff there.

## 5. Consequence for a combined sufficient curve

Conditional only on the new profile argument proving the proposed cost,
the best combination with the old manuscript is

$$
B_{\rm combined}(d)=
\begin{cases}
2d-1,&1<d\le11/10,\\[5pt]
\dfrac{19d-8+\sqrt{265d^2-544d+280}}{12},
 &11/10<d<1+\theta,\\[7pt]
B_{\rm M}(d),&1+\theta\le d\le5/4.
\end{cases}
\tag{15}
$$

The first join is exact because $$e(1/10)=1/5$$, and the second is exact
by (14). The new inequality improves the old coherent condition already
for every $$11/10<d\le9/8$$. At the old join $$a=1/8$$, the new packing cutoff is
$$1+e(1/8)=1.268030415236\ldots$$, whereas the old one is $$1.25$$.

A useful fully rational example is

$$
d=\frac{28}{25}=1.12,\qquad D=\frac54=1.25.
$$

Here $$a=3/25$$, $$b=1/4$$, and exact arithmetic gives

$$
N(a,b)=E(a,b)=a-\frac{37}{13200}<a.
\tag{16}
$$

The old cutoff at this Hausdorff dimension was $$31/25=1.24$$.
No decimal value in this note is used to prove a cutoff or branch comparison.
