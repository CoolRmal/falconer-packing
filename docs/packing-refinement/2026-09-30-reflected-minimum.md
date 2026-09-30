# A running-minimum reflection improves the late case

30 September 2026. This note proves a profile-chain estimate. Its conversion
to a distance-set theorem requires the separately justified analytic transfer.

For a 1-Lipschitz profile on $$[0,1]$$ satisfying $$ax\leq g(x)\leq bx$$,
let

$$
E(a,b)=\frac{1-2a-2a^2+(2+a)b}{6(1+a)},\qquad
M(a,b)=\frac{3b}{8}+\frac3{16}-\frac{3a}{4}.
$$

If $$0<a\leq1/4$$ and $$a\leq b\leq1$$, every initial point
$$3/4\leq n_0<1$$ has an admissible decreasing chain through $$1/2$$ to zero
whose cost is at most

$$\max\{E(a,b),M(a,b)\}.$$

The number of edges is $$O(1+\log(1/(1-n_0)))$$. On a grid of mesh $$T$$
in normalized coordinates add $$O(KT)$$. Additive barrier errors of size
$$e_0$$ add $$O(Ke_0)$$. A detailed manuscript proof is in
`output/pdf/packing-refinement-reflection-lemma.tex`.

## Reflection identity

Let $$u\in[1/2,3/4]$$ minimize the profile on that interval, and let
$$t\in[1/2,1]$$ minimize it on the full upper half. Write

$$
v=g(1/2),\qquad w=g(u),\qquad m=g(t),\qquad e=g(1).
$$

Set the running deficit to zero before $$u$$ and to

$$r(x)=w-\min_{z\in[u,x]}g(z)$$

after $$u$$. It is nondecreasing and nonnegative. The reflected function
$$h=g+r$$ is 1-Lipschitz and has an early global minimum at $$u$$. To verify
the Lipschitz claim, consider $$u\leq x<y$$. If the running deficit is
unchanged, the increment is exactly that of the original function. Otherwise
a new minimum is attained at some $$z\in[x,y]$$, and

$$
h(y)=g(y)+w-g(z),\qquad h(x)\geq w,
$$

so $$h(y)-h(x)\leq y-x$$. The other inequality follows from the monotonicity
of the deficit. Gluing at $$u$$ extends this to the whole interval.

For every edge $$p<q$$,

$$
c_g(p,q)\leq c_h(p,q)+r(q)-r(p).
$$

Indeed, the minimum of $$g+r$$ is at most the minimum of $$g$$ plus $$r(q)$$.
The added terms telescope across any chain, with total at most $$w-m$$.

The upper cone from the reflected early minimum gives a chain cost at most

$$v-w+\frac{1-u+w-h(1)}3.$$

Since $$h(1)=e+w-m$$, its transfer back to the original profile gives

$$R_0=v+\frac{1-u-e-2m}{3}.$$

This does not require the reflected function to satisfy the original upper
linear barrier. The cone argument uses only its Lipschitz constant, its early
global minimum and its endpoint value.

## A second chain and cancellation

Suppose the global minimum is late: $$t>3/4$$. First reach $$t$$ with the
cone construction, costing at most $$ (1-t+m-e)/3 $$. From $$t$$ make
maximal admissible jumps toward $$3/4$$, clipping the last one. Their total
cost is at most their total length $$t-3/4$$. The last edge from $$3/4$$ to
$$1/2$$ costs exactly $$v-w$$, not just the looser bound $$v-m$$. Therefore

$$S_0=v-w+\frac{2t+m-e-5/4}{3}.$$

If $$t>n_0$$, skip reaching $$t$$ and make those jumps directly from $$n_0$$.
The same bound holds since $$n_0-3/4\leq t-3/4$$ and the omitted cone bound
is nonnegative by Lipschitz continuity.

The prefix minimum obeys $$w\geq v-u+1/2$$. Thus

$$
\begin{aligned}
\min\{R_0,S_0\}
&\leq\frac34R_0+\frac14S_0\\
&\leq\frac{3v}{4}+\frac1{48}-\frac e3+\frac t6-\frac{5m}{12}\\
&\leq\frac{3b}{8}+\frac1{48}-\frac a3+\frac{2-5a}{12}t\\
&\leq M(a,b).
\end{aligned}
$$

The early-global-minimum case retains the previously proved bound $$E(a,b)$$.
This proves the maximum of the two bounds uniformly, without a remaining
location hypothesis.

## Why this is enough for the useful early bound

The strict inequality $$E(a,b)<a$$ is equivalent to

$$b<b_E(a):=\frac{8a^2+8a-1}{a+2}.$$

At this boundary,

$$M(a,b_E(a))-a=\frac{5a(4a-1)}{16(a+2)}\leq0$$

for $$0<a\leq1/4$$. Since the late bound increases strictly with $$b$$,
the strict inequality $$E(a,b)<a$$ also implies $$M(a,b)<a$$ throughout
this range. It is therefore sufficient without separately imposing the old
late-case inequality. The region with $$b\geq a$$ is nonempty precisely
when $$a>1/7$$.

In the distance notation $$a=s-1$$ and $$b=u-1$$, this is the profile
condition

$$u<\frac{s(8s-7)}{s+1},\qquad\frac87<s\leq\frac54.$$

For illustration, at $$s=31/25$$ the right side is $$2263/1400$$, which is
approximately $$1.616428571$$. At $$s=5/4$$ it is $$5/3$$. These scalar
computations do not prove a distance-set theorem independently of the analytic
transfer.

## Scope of the universal early-bound question

The argument proves a universal bound by $$E(a,b)$$ whenever $$M(a,b)\leq
E(a,b)$$, namely

$$b\leq\frac{20a^2+11a-1}{2+10a}.$$

This includes the entire useful strict region $$E(a,b)<a$$ for
$$0<a\leq1/4$$, because the difference between the two boundary functions
has numerator $$15a(4a-1)(a+1)$$ over a positive denominator.

It does **not** prove the universal early bound for all larger parameters,
nor supply a counterexample there. No claim of a globally weakest
dimension condition or minimax optimality follows from this lemma.
