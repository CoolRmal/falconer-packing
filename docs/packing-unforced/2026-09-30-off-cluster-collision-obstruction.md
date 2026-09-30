# A fixed-measure obstruction to the raw off-cluster collision target

30 September 2026.

The positive collision target (14) in
`2026-09-30-synchronized-profile-energy-obstruction.md` cannot hold for every
prescribed source and pin measure under the indicated dimension controls.
Removing microscopic self-pairs does not cure the train-track obstruction.
The construction below has uniform Frostman and covering constants, and can
be assembled into one fixed pair of separated measures. It does not obstruct
choosing a better source probability, deleting bad interactions, or proving
positive-length pinned distances.

The geometric starting point is the train-track configuration in
[Guth–Iosevich–Ou–Wang, Section 6](https://arxiv.org/html/1808.09346#S6).
The additional points here are a covering exponent below two, a positive
off-cluster lower bound, and a fixed-measure gluing argument with controlled
dimensions. All estimates needed for those points are proved below.

## 1. Statement

Fix

$$
1<s<\frac43,\qquad 3-\frac2s\le u\le2.
\tag{1}
$$

There are compact sets and probabilities

$$
\operatorname{supp}\mu=K,\qquad
\nu=(x\mapsto x+(0,3))_*\mu,
$$

with the following properties:

$$
\dim_H K=\dim_P K=s,
\qquad N(K,r)\le C r^{-u},
\tag{2}
$$

$$
\mu(B(x,r))+\nu(B(x,r))\le C r^s,
\qquad
\operatorname{dist}(\operatorname{supp}\mu,\operatorname{supp}\nu)>2.
\tag{3}
$$

Let a nonnegative smooth compactly supported mollifier have integral one,
and set $$K_0=\varphi*\widetilde\varphi$$. There is a sequence
$$\varepsilon_j\downarrow0$$ such that the nonnegative collision integral

$$
\mathcal C_\varepsilon=
\iiint \varepsilon^{-1}K_0\left(
 \frac{|x-y|-|x'-y|}{\varepsilon}\right)
\,d\mu(x)\,d\mu(x')\,d\nu(y)
\tag{4}
$$

goes to infinity along this sequence. For the partition into squares of
side $$\varepsilon_j$$, the same-square contribution tends to zero. Thus
the contribution from different squares tends to infinity. More generally,
no sequence of measurable source partitions can make both hypotheses in
the earlier positive collision criterion hold for these measures.

Notice that $$3-2/s>s$$ for $$1<s<2$$. No inconsistency is asserted between
the packing dimension in (2) and the larger uniform covering exponent.
Countable unions preserve packing dimension, while their upper box dimension
can be larger.

## 2. A family of finite-scale source measures

Write

$$
\alpha=u-1,\qquad p=\frac{s-1}{2\alpha},\qquad
a=\delta^p,\quad w=\delta^{1/2},\quad h=\delta^{s/2}.
\tag{5}
$$

The assumptions imply

$$
0<p\le s/4<1/2<s/2<1,
\qquad a\gg w\gg h\gg\delta.
$$

Choose an $$\alpha$$-Ahlfors regular compact subset of $$[0,1/2]$$.
Take a maximal $$3a$$-separated net of horizontal track centers in this set.
Its cardinality $$N_T$$ satisfies

$$N_T\asymp a^{-\alpha}.$$

The uniform probability on the centers assigns mass at most
$$C(r^\alpha+a^\alpha)$$ to any interval of length $$r$$. Its covering
number at scales $$r\ge a$$ is at most $$Cr^{-\alpha}$$. These facts
follow by comparing disjoint balls of radius comparable to $$a$$ with
the regular measure. Such a regular compact set exists for every
$$0<\alpha\le1$$: for $$\alpha<1$$ use the two-interval Cantor construction
with contraction $$2^{-1/\alpha}$$, and for $$\alpha=1$$ use an interval.

Within every track place

$$N_S\asymp h^{-1}$$

horizontal slats at heights $$kh$$ in $$[0,1]$$. Within each slat place

$$N_X\asymp w/\delta$$

small cells with horizontal centers spaced $$4\delta$$ across an interval
of length comparable to $$w$$. In each cell place a translate of a
$$\delta/100$$-scaled copy of one fixed $$s$$-Ahlfors regular compact set
and its regular probability. One may take the product of an interval with
an $$(s-1)$$-regular Cantor set. Let $$\mu_\delta$$ give equal mass to all
the cells. The support lies in a fixed bounded square.

The total number of cells and the mass of a cell satisfy

$$
N_TN_SN_X\asymp
 a^{-\alpha}h^{-1}w/\delta=\delta^{-s},
\qquad \mu_\delta(\text{cell})\asymp\delta^s.
\tag{6}
$$

The mass of one complete slat in one specified track is

$$
m_\delta=(N_TN_S)^{-1}\asymp a^\alpha h
=\delta^{s-1/2}.
\tag{7}
$$

All implicit constants below depend on $$s,u$$ and the fixed regular sets,
not on $$\delta$$.

### Uniform Frostman bound

For $$r\ge\delta$$, count the cells whose centers lie in the coordinate
projections of a ball. The horizontal and vertical center indices are
independent and uniformly weighted. This gives

$$
\mu_\delta(B(x,r))\lesssim
\begin{cases}
r^u,&a\le r\le1,\\
a^\alpha r,&w\le r\le a,\\
a^\alpha w^{-1}r^2,&h\le r\le w,\\
a^\alpha h w^{-1}r,&\delta\le r\le h.
\end{cases}
\tag{8}
$$

Fixed changes in interval lengths absorb the diameter of the tiny cell
copies. Since $$a^\alpha=\delta^{(s-1)/2}$$, each line in (8) is at most
$$Cr^s$$. For the second line use $$r\ge w$$; for the third use
$$r\le w$$ and $$s<2$$; for the fourth use $$r\ge\delta$$.
The first follows from $$u\ge s$$.

When $$r<\delta$$, a ball meets a bounded number of cells. A cell has
mass at most $$C\delta^s$$ and its normalized tail measure is
$$s$$-regular at scale $$\delta$$, so again its contribution is at most
$$Cr^s$$. Thus

$$\mu_\delta(B(x,r))\le Cr^s\quad\text{for every }r>0.$$

### Uniform covering bound

The same elementary counts give

$$
N(\operatorname{supp}\mu_\delta,r)\lesssim
\begin{cases}
r^{-u},&a\le r\le1,\\
a^{-\alpha}r^{-1},&w\le r\le a,\\
a^{-\alpha}wr^{-2},&h\le r\le w,\\
a^{-\alpha}h^{-1}wr^{-1},&\delta\le r\le h,\\
r^{-s},&0<r\le\delta.
\end{cases}
\tag{9}
$$

The second line is at most $$Cr^{-u}$$ because $$r\le a$$. In the third
and fourth ranges, comparison with $$r^{-u}$$ is hardest at $$r=h$$;
there the ratio is

$$
\delta^{(2-3s+su)/2}\le1.
\tag{10}
$$

This is precisely where $$u\ge3-2/s$$ is used. The final line follows
from (6) and the covering number of the fixed regular tail:

$$
\delta^{-s}(r/\delta)^{-s}=r^{-s}\le r^{-u}.
$$

Therefore the covering constant is independent of $$\delta$$. Each of
these finite-scale supports is a finite union of scaled copies of the fixed
regular tail, and has Hausdorff and packing dimension exactly $$s$$.

## 3. Positive collisions from distinct cells in one slat

First place pins in the vertical translate of the finite-scale source by
$$(0,3)$$. A pin belongs to a particular track. Every source point in the
same track has horizontal difference from that pin at most $$Cw$$.
For any two source points in one slat of that track, their vertical
coordinates differ by at most $$C\delta$$. Their vertical distances to
the pin are bounded above and below by positive constants. Consequently

$$
\bigl||x-y|-|x'-y|\bigr|\le C\delta+Cw^2\le C'\delta.
\tag{11}
$$

For completeness, subtract the squares of the two distances. The difference
of the vertical squares is $$O(\delta)$$; each horizontal square is
$$O(w^2)$$. Divide by the sum of the distances, which is bounded below.

The function $$K_0$$ is continuous and $$K_0(0)>0$$. Fix $$L$$ so large
that the kernel at smoothing width $$L\delta$$ is at least
$$c/\delta$$ on every pair satisfying (11). For every pin in the translated
source support, the contribution from all slats in its own track is at least

$$
c\delta^{-1}N_Sm_\delta^2
\asymp \delta^{3s/2-2}.
\tag{12}
$$

This tends to infinity when $$s<4/3$$. The conclusion uses a nonnegative
collision count, not a signed Fourier expansion.

The same-cell part of the full source pair integral, uniformly in the pin,
is at most

$$
C\delta^{-1}\sum_A\mu_\delta(A)^2
\lesssim\delta^{s-1}\longrightarrow0.
\tag{13}
$$

Thus almost all of the growing contribution in (12) comes from distinct
microscopic cells. Their common macroscopic slat has transverse width
$$\delta^{1/2}$$, so treating all problematic pairs as microscopic
self-clusters misses this obstruction.

## 4. One fixed source and one fixed pin measure

Choose a small constant $$c>0$$, for instance $$c=10^{-4}$$, and set

$$
\lambda_j=c2^{-j},\qquad z_j=(2^{-j},0),\qquad
\delta_j=2^{-(j+j_0)^2}.
$$

Choose the fixed integer $$j_0$$ large enough for all the finite-scale
comparisons above. Put

$$
\mu=\sum_{j\ge1}w_j(T_{z_j}\circ D_{\lambda_j})_*\mu_{\delta_j},
\qquad w_j=Z^{-1}\lambda_j^s,\qquad
Z=\sum_{j\ge1}\lambda_j^s,
\tag{14}
$$

and let $$\nu$$ be its translate by $$(0,3)$$. The source support is the
union of the compact blocks and their only possible accumulation point,
the origin. Taking $$c$$ small makes the source and pin supports separated
by more than two.

The Frostman constant is finite. Indeed, components with $$\lambda_j>r$$
have horizontal separations much larger than $$r$$, so a ball of radius
$$r$$ meets at most a bounded number of them. Each contributes at most

$$Cw_j(r/\lambda_j)^s\le C' r^s.$$

The total mass of all components with $$\lambda_j\le r$$ is at most
$$C r^s$$, by the geometric series. This proves (3).

For the covering estimate, the components with $$\lambda_j\ge r$$ need
at most

$$
C\sum_{\lambda_j\ge r}(\lambda_j/r)^u\le C' r^{-u}
$$

balls. All the remaining components lie in a ball of radius $$C_c r$$
about the origin, and hence need only a fixed number of additional
$$r$$-balls. This proves the uniform estimate in (2). Countable stability
of Hausdorff and packing dimension, applied to the blocks and the origin,
gives the two dimension equalities in (2).

Now take

$$\varepsilon_j=L\lambda_j\delta_j.$$

Restrict both source variables to block $$j$$ and the pin variable to its
translate. The horizontal squared difference in (11) is now
$$O(\lambda_j^2\delta_j)$$, and the vertical squared difference is
$$O(\lambda_j\delta_j)$$. All source-pin distances remain bounded below.
Thus the same kernel lower bound holds at width $$\varepsilon_j$$.
Accounting for the three block masses gives

$$
\mathcal C_{\varepsilon_j}
\ge c\,w_j^3\lambda_j^{-1}\delta_j^{3s/2-2}
\asymp
\lambda_j^{3s-1}\delta_j^{3s/2-2}
\longrightarrow\infty.
\tag{15}
$$

The negative exponent of $$\delta_j$$ wins over every fixed exponential
in $$j$$, because $$\log(1/\delta_j)$$ grows quadratically.

For any partition into squares of side $$\varepsilon_j$$, the Frostman
bound gives

$$
\varepsilon_j^{-1}\sum_A\mu(A)^2
\le \varepsilon_j^{-1}\sup_A\mu(A)
\lesssim\varepsilon_j^{s-1}\longrightarrow0.
\tag{16}
$$

Subtract this bounded nonnegative same-part contribution from (15).
The off-cluster part diverges. More generally, if any chosen partition
sequence satisfies the first hypothesis in the earlier collision criterion,
its same-part contribution is bounded by that hypothesis and
$$\|K_0\|_\infty$$. It cannot absorb the divergence in (15), so its
off-part contribution cannot satisfy (14) of that criterion.

The measures have finite $$I_t$$ for every $$t<s$$, by their Frostman bound.
Thus this obstruction also allows a strict finite-energy margin if the
Frostman exponent required by an attempted estimate is chosen below the
construction parameter $$s$$.

### Variant with finite energy at the stated Frostman exponent

If the attempted estimate requires $$I_s(\mu)<\infty$$ itself, choose
$$s<v\le u$$ and use a $$v$$-Ahlfors regular set for every microscopic
tail. This changes neither the number and masses of cells nor the lower
bound (15). The Frostman estimate below scale $$\delta$$ becomes

$$
\mu_\delta(B(x,r))\lesssim\delta^s(r/\delta)^v
\le r^s,\qquad r<\delta.
$$

The covering bound there becomes

$$
N(\operatorname{supp}\mu_\delta,r)
\lesssim\delta^{v-s}r^{-v}\le r^{-u}.
$$

The layer-cake formula for energy, using (8) above scale $$\delta$$ and
the improved small-scale mass bound below it, gives

$$I_s(\mu_\delta)\lesssim1+\log(1/\delta).$$

In the fixed glued measure the within-block energies are bounded by

$$
\sum_j w_j^2\lambda_j^{-s}I_s(\mu_{\delta_j})
\lesssim\sum_j\lambda_j^s(1+j^2)<\infty.
$$

The distance between distinct blocks $$i<j$$ is comparable to $$2^{-i}$$,
so their cross energies have sum at most

$$
C\sum_{i<j}2^{is}w_iw_j
\lesssim\sum_j j2^{-js}<\infty.
$$

Thus the same obstruction holds with finite $$I_s(\mu)$$ and
$$I_s(\nu)$$. Its support now has Hausdorff and packing dimension $$v$$.
For example one may take $$s=6/5$$, $$u=4/3$$, and $$v=5/4$$. The
independent geometry check by the other audit agent also confirmed the
track/slat exponent and suggested this finite-energy variant.

## 5. What an elementary unrestricted estimate actually gives

There is a simple uniform bound, but it loses a power. Suppose the source
and pin supports are bounded, the pin measure is $$t$$-Frostman with
$$1<t\le2$$, and $$I_{t-1}(\mu)<\infty$$. For a fixed source pair at
separation $$r=|x-x'|>0$$, the collision condition implies that the pin
lies in a strip of width $$C\varepsilon/r$$ about the perpendicular
bisector. This follows from the exact squared-distance identity

$$
|x-y|^2-|x'-y|^2
=2(x-x')\cdot\left(\frac{x+x'}2-y\right).
$$

A strip of bounded length and width $$q\le1$$ is covered by $$O(q^{-1})$$
balls of radius $$q$$. Its pin mass is therefore at most $$Cq^{t-1}$$.
Using the trivial mass bound when $$q>1$$, then integrating the source
pair, yields

$$
\mathcal C_\varepsilon
\le C\varepsilon^{t-2}I_{t-1}(\mu).
\tag{17}
$$

All off-cluster subintegrals satisfy the same upper bound by positivity.
For equal exponents $$t=s<2$$ this is not a uniform bound. The covering
condition alone does not justify replacing its right side by a constant:
(15) rules out that replacement in the range (1).

The new conclusion is an obstruction to the proposed raw positive-collision
route, not an improved sufficient packing curve. A useful bilinear refinement
must retain enough selection to remove the same-track/same-slat interactions,
or change the source law before demanding uniform joint $$L^2$$ control.
The published good-part proof is unchanged.

This obstruction already occurs with an upper covering exponent below the
original coherent cutoff, since

$$
2s-1-\left(3-\frac2s\right)=\frac{2(s-1)^2}{s}>0.
$$

It therefore distinguishes the desired distance-set conclusion from the
stronger claim that an arbitrary prescribed source law has a uniformly
bounded averaged $$L^2$$ norm. At a single finite scale, the offending source
track has mass only $$N_T^{-1}\asymp\delta^{(s-1)/2}$$ for each pin, even
though its collision contribution diverges. This is exactly the kind of
small-mass, large-$$L^2$$ interaction that a retained good-part selection can
remove.
