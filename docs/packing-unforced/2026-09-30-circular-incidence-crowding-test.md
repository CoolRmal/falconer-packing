# Testing circular local smoothing and broad incidence bounds on crowding tails

30 September 2026. This is a calculation for a specific attempted insertion of published approximate-circle incidence bounds into the fixed positive crowding criterion. It does not prove that the true crowding tails fail. The calculation gives no new dimension region: even the favorable broad-incidence substitution retains a fixed loss throughout the range of interest.

## 1. The primary input and the finite model

The input is [Green–Harris–Ou–Ren–Tammen, arXiv:2502.10686, Theorems 2.1 and 2.3](https://arxiv.org/html/2502.10686). For delta-neighborhoods of circles P and delta-discs X, their local-smoothing estimate, in the range 3a+b<=7, is

$$
I(P,X)\lesssim_\eta
\delta^{-3/4-\eta}
K_{b,P}^{1/4}K_{a,X}^{3/4}|P|^{3/4}|X|^{1/4}.
\tag{1}
$$

For their broad incidence count, in the range 3a+2b<=9, they prove

$$
I^{\mathrm{broad}}_{L,R}(P,X)
\lesssim_\eta R^{100}\delta^{-1/2-\eta}
K_{b,P}^{1/3}K_{a,X}^{1/2}|P|^{2/3}|X|^{1/2},
\qquad L\ge |\log\delta|.
\tag{2}
$$

Here K_{a,X} means the least constant in the count bound K_{a,X}(r/delta)^a for balls of radius r>=delta; the circle parameter space is the three-dimensional space (center,radius). The radii are in [1,2]. A fixed bounded interval of positive radii can be treated by finitely many rescalings; its endpoints enter only fixed constants. We retain the broadness factor rather than assuming that all incidences counted by (1) are broad.

Take delta-separated source centers X and pin centers Y with uniform probabilities

$$
\mu_\delta=w\sum_{x\in X}\delta_x,
\qquad
\nu_\delta=v\sum_{y\in Y}\delta_y,
\qquad
w|X|=v|Y|=1.
$$

Assume, for r>=delta,

$$
\mu_\delta(B(z,r))\le C_\mu r^s,
\qquad
\nu_\delta(B(z,r))\le C_\nu r^t,
\qquad 1<s,t<2.
\tag{3}
$$

These are scale-truncated Frostman hypotheses. No small-scale Frostman claim is made for atomic measures. All source–pin distances are in a fixed compact subinterval of positive radii. The cell masses w and v remain arbitrary; in particular they are not replaced by delta^s or delta^t.

At each pin y, put circle radii on a delta grid. Enlarge the annuli by a fixed constant so that rounding the distance |x-y| to this grid, and a collision of width delta, both lead to incidences with the same annulus. Equivalently, use delta-discs at source centers and fixed dilates of the annuli. All these fixed dilations affect only constants in (1)–(3).

For a circle C let M(C) be w times its incidence count with X. Thus M(C) is its source mass at resolution delta, with finite overlap of the radial windows. Let P_h be the circles with

$$
h\le M(C)<2h,
\tag{4}
$$

where h ranges over dyadic numbers. The following estimates are for the full raw law and therefore majorize the law from any positive source–pin selection bounded by one. They remain valid for the fixed angular selection after such a selection is supplied at the finite resolution; no angular regularity of the atomic model is asserted.

## 2. Keeping every cell-mass and Frostman factor

The source disc family has

$$
K_{s,X}\lesssim C_\mu\frac{\delta^s}{w}.
\tag{5}
$$

For a ball of radius r in circle parameter space, there are at most C_nu r^t/v eligible pin centers and at most Cr/delta possible radii for each center. Hence

$$
K_{t+1,P_h}\lesssim C_\nu\frac{\delta^t}{v}.
\tag{6}
$$

Suppose 3s+t<=6, so (1) applies with a=s and b=t+1. Substituting (5), (6), and |X|=1/w into (1) gives

$$
I(P_h,X)
\lesssim_\eta C_\nu^{1/4}C_\mu^{3/4}
\delta^{(t+3s-3)/4-\eta}
v^{-1/4}w^{-1}|P_h|^{3/4}.
\tag{7}
$$

On the other hand, (4) gives I(P_h,X)>=h|P_h|/w. Therefore

$$
|P_h|
\lesssim_\eta C_\nu C_\mu^3
\delta^{t+3s-3-4\eta}v^{-1}h^{-4}.
\tag{8}
$$

The source–pin product mass whose distance belongs to one of these windows is at most 2vh|P_h|. If the normalized annular crowding exceeds lambda, then its corresponding circle has mass at least c lambda delta. Summing (8) over the dyadic h above this threshold is geometric, and yields

$$
(\mu_\delta\times\nu_\delta)
 \{H_\delta>\lambda\}
\lesssim_\eta C_\nu C_\mu^3
\delta^{3s+t-6-4\eta}\lambda^{-3}
\qquad(\lambda\ge1).
\tag{9}
$$

Fixed enlargements of the crowding window and constants in lambda are understood; they do not alter any exponent. The same upper bound applies to retained pair mass for any positive selection, because its crowding is bounded by raw crowding and its pair measure is dominated by the raw product measure.

The cell masses w and v cancel exactly. Adding upper box-counting bounds |X|<=C delta^{-D_source} and |Y|<=C delta^{-D_pin} therefore supplies no additional power in this particular insertion. This is not an assertion that every use of packing dimension must cancel: it is a calculation for (1), (5), and (6).

## 3. The most favorable broad-incidence substitution

Let P_h^b be any subfamily on which the broad count satisfies

$$
I^{\mathrm{broad}}_{L,R}(P_h^b,X)
\ge b\,\frac{h}{w}|P_h^b|,
\qquad b>0.
\tag{10}
$$

This is an additional hypothesis, not a consequence of fixed angular truncation. In particular, the truncation bounds pin directions viewed from each source point; it does not directly give broad source directions on every rich circle. A two-cluster configuration is another reason not to substitute (10) without proof.

When 3s+2t<=7, substituting (5)–(6) into (2) and using (10) gives

$$
|P_h^b|
\lesssim_\eta R^{300}b^{-3} C_\nu C_\mu^{3/2}
\delta^{t+3s/2-3/2-3\eta}v^{-1}h^{-3}.
$$

Consequently the pair mass associated to these broad rich circles satisfies

$$
\operatorname{Mass}_{\mathrm{broad}}\{H_\delta>\lambda\}
\lesssim_\eta
R^{300}b^{-3}C_\nu C_\mu^{3/2}
\delta^{3s/2+t-7/2-3\eta}\lambda^{-2}.
\tag{11}
$$

Both R and b have been retained. Since L>=|log delta|, one cannot take R fixed and simultaneously assume a nontrivial broad lower bound at all small scales. Permitting R and b^{-1} to grow only logarithmically would give only logarithmic extra losses. Even if one optimistically deletes their entire factor from (11), its resolution exponent is still negative throughout the target self-pinned range:

$$
s,t\le d\le\frac54
\quad\Longrightarrow\quad
\frac32s+t-\frac72\le-\frac38.
\tag{12}
$$

Thus the numerical threshold furnished by this optimistic broad substitution would require 3s/2+t>7/2, or d>7/5 when s=t=d. The ordinary local-smoothing substitution instead requires 3s+t>6, or d>3/2. These are limitations of the displayed bounds, not newly proved distance thresholds.

In fact the corresponding first-branch hypotheses stop exactly at these zero-deficit boundaries. Beyond the local-smoothing boundary one must use the second branch of Theorem 2.1, treated below. Thus these inequalities identify where the negative powers disappear in the printed formulas, rather than asserting that these incidence theorems prove a uniform tail above the stated values.

At the specific point d=23/20, D=3/2, which lies beyond the present manuscript curve, (11) retains the loss delta^{-5/8}, even before the arbitrary small-power and broadness losses. At d=5/4 it retains delta^{-3/8}.

## 4. A richness-based circle parameter estimate does not repair the loss

There is a second available count bound for P_h. For fixed pin y, a radius interval of length r corresponds to a width-O(r) annulus in the source region. Covering that annulus by O(r^{-1}) balls of radius O(r) and using (3) gives source mass at most C C_mu r^{s-1}. Since the windows in (4) overlap boundedly, the number of h-rich radii in this interval is at most C C_mu r^{s-1}/h. Together with the radius grid bound, this gives

$$
\#(P_h\cap B((y_0,r_0),r))
\lesssim\frac{C_\nu r^t}{v}
\min\left\{\frac r\delta,
                  \frac{C_\mu r^{s-1}}h\right\}.
\tag{13}
$$

For 0<=theta<=1, interpolating these two elementary counts gives a valid circle parameter exponent and constant

$$
b_\theta=t+1-\theta(2-s),
\qquad
K_{b_\theta,P_h}
\lesssim\frac{C_\nu C_\mu^\theta}{v}
 \delta^{t+\theta(s-1)}h^{-\theta}.
\tag{14}
$$

Substituting (14) into the same two theorems gives the tail powers

$$
\begin{array}{c|c|c}
\text{input}&\text{power of delta}&\text{power of lambda}\\ \hline
\text{local smoothing}&
3s+t-6-\theta(2-s)-4\eta&-(3+\theta)\\
\text{broad incidence}&
3s/2+t-7/2-\theta(2-s)-3\eta&-(2+\theta).
\end{array}
\tag{15}
$$

The fixed constants are respectively C_nu C_mu^{3+theta} and R^{300}b^{-3}C_nu C_mu^{3/2+theta}. Thus a larger level-set tail exponent is obtained at the expense of a worse resolution loss.

This trade does not help fractional moments. Ignore the arbitrarily small losses, set

$$
\begin{aligned}
\zeta_{\rm loc}(\theta)&=6-t-3s+\theta(2-s),
&p_{\rm loc}(\theta)&=3+\theta,\\
\zeta_{\rm br}(\theta)&=\frac72-t-\frac32s+\theta(2-s),
&p_{\rm br}(\theta)&=2+\theta.
\end{aligned}
$$

A tail bounded by min{1,C delta^{-zeta}lambda^{-p}} gives, for 0<gamma<p, a gamma moment bounded at best by a constant times delta^{-gamma zeta/p} through layer cake. Direct differentiation shows

$$
\frac{d}{d\theta}\frac{\zeta_{\rm loc}(\theta)}{p_{\rm loc}(\theta)}
=\frac{t}{(3+\theta)^2}>0,
\qquad
\frac{d}{d\theta}\frac{\zeta_{\rm br}(\theta)}{p_{\rm br}(\theta)}
=\frac{t+(1-s)/2}{(2+\theta)^2}>0.
\tag{16}
$$

So among the circle parameter counts (13)–(14), the original product count theta=0 is already the best one for this fractional-moment route. This tests the natural richness-dependent bootstrap rather than simply stopping at (9).

## 5. Optimizing ambient counting and the packing cardinality as well

One might improve (5)–(6) by using the ambient separation bounds at small scales, and the upper box count to constrain the cell weights. This optimization can also be done explicitly. Write d for the common Frostman exponent in this calculation, with

$$
1<d\le\frac54,\qquad d\le D<2.
$$

Suppose the finite source and pin cardinalities are at most a constant times delta^{-D}. Uniform weights therefore satisfy w,v>=c delta^D. The most favorable values for the following scalar incidence bounds are w,v comparable to delta^D: all uncancelled powers of w,v in the bounds are nonnegative. We compute in that favorable case. Larger cell weights only increase the numerical upper bounds supplied by this substitution.

Interpolate the source d-Frostman count with its ambient two-dimensional separation count. If 0<=q<=1, set

$$
a=2-(2-d)q,
\qquad
K_{a,X}\lesssim
\left(C_\mu\frac{\delta^d}{w}\right)^q.
\tag{17}
$$

For the circle family, combine its ambient three-dimensional count with (14). If 0<=r<=1, then

$$
b=3-(2-d)(1+\theta)r,
\qquad
K_{b,P_h}\lesssim
\left(
 \frac{C_\nu C_\mu^\theta}{v}
 \delta^{d+\theta(d-1)}h^{-\theta}
\right)^r.
\tag{18}
$$

Both inequalities follow by taking geometric means of the two pointwise count bounds, so no unproved interpolation theorem is being used. Put z=theta r. In the first local-smoothing branch let Z=3q+(1+theta)r. Its hypothesis is Z>=2/(2-d). Substitution gives a tail of the form delta^{-zeta}lambda^{-p}, apart from the arbitrarily small losses, with

$$
p=3+z,
\qquad
\zeta=6-4D+(D-d)Z+(2-D)z.
\tag{19}
$$

The fixed Frostman multiplier is C_nu^r C_mu^{3q+theta r}. Since D>=d, (19) yields

$$
\zeta\ge
\frac{(6-4d)(2-D)}{2-d}+(2-D)z.
\tag{20}
$$

The ratio of the right side to 3+z strictly increases with z, because its derivative has the sign of d/(2-d). Equality at z=0 is attainable at the parameter boundary Z=2/(2-d). Thus neither the ambient interpolation nor the richness parameter removes the deficit; the best first-branch loss-to-tail ratio is

$$
\frac{(6-4d)(2-D)}{3(2-d)}.
\tag{21}
$$

For completeness, the second branch of Theorem 2.1 has parameter ell=4/(3a+b-3)<1 and reads

$$
I(P,X)\lesssim_\eta
\delta^{-3\ell/4-\eta}
K_{b,P}^{\ell/4}K_{a,X}^{3\ell/4}
|P|^{1-\ell/4}|X|^{1-3\ell/4}.
$$

Solving the rich-circle inequality now gives, for Z<2/(2-d),

$$
p=5-(2-d)Z+z,
\qquad
\zeta=(2-D)(4-Z+z).
\tag{22}
$$

For fixed Z, zeta/p increases with z, because the derivative has the sign of 1+(d-1)Z. At z=0 it decreases with Z, because the derivative has the sign of 3-4d<0. Its infimum is therefore again (21), at the common boundary of the two branches. The small-power loss in the primary theorem becomes 4eta/ell after solving for cardinality and remains adverse.

For broad incidences set Z=3q/2+(1+theta)r. The theorem's range is Z>=3/[2(2-d)]. The tail powers are

$$
p=2+z,
\qquad
\zeta=\frac72-\frac52D+(D-d)Z+(2-D)z
\ge
\frac{(7-5d)(2-D)}{2(2-d)}+(2-D)z.
\tag{23}
$$

The Frostman multiplier is C_nu^r C_mu^{3q/2+theta r}, and the factor R^{300}b^{-3} from the broadness hypothesis is still present. The ratio of the right side of (23) to 2+z increases with z, its derivative having the sign of (1+d)/[2(2-d)]. The best optimistic broad loss-to-tail ratio is consequently

$$
\frac{(7-5d)(2-D)}{4(2-d)}.
\tag{24}
$$

All these quantities are strictly positive for d<=5/4 and D<2. The best tails in this tested family have powers p=3 and p=2, with resolution deficits respectively

$$
\boxed{
\zeta_{\rm loc}^{\rm opt}=
\frac{(6-4d)(2-D)}{2-d},
\qquad
\zeta_{\rm br}^{\rm opt}=
\frac{(7-5d)(2-D)}{2(2-d)}.
}
\tag{25}
$$

At (d,D)=(23/20,3/2), even the favorable broad substitution retains delta^{-25/68}. At D=2 the optimized fixed-power deficit reaches zero, but the primary theorem still loses delta^{-eta}; this does not establish a uniform finite-threshold bound. These computations concern what the displayed incidence estimates supply, not lower bounds for the actual crowding.

In a set-dimensional application, the Frostman exponent is taken slightly below the Hausdorff dimension and the box exponent slightly above the relevant packing dimension after the usual reduction. The strictly positive deficits above persist under these arbitrarily small changes; no endpoint Frostman measure has been assumed.

## 6. Retaining source separation and the exact scope of failure

Let u be a dyadic source separation and Q_{delta,u} the normalized near-bisector partner mass from `2026-09-30-fractional-far-bisector-crowding.md`. The squared-distance identity and source–pin separation imply

$$
Q_{\delta,u}(x,y)
\le C u^{-(s-1)}H_{C\delta}(x,y).
\tag{26}
$$

Using a global circle tail without any extra localization therefore gives

$$
\Pi_A\{Q_{\delta,u}>\lambda\}
\lesssim
\min\{1,
C\delta^{-\zeta}\lambda^{-p}u^{-p(s-1)}\}.
\tag{27}
$$

It has both an unwanted resolution loss and the borderline source-scale loss kappa=p(s-1), whereas the proved fractional criterion needs kappa<p(s-1). More decisively, at any fixed macroscopic u the resolution loss remains, even after the ambient and packing-cardinality optimization in (25). Consequently improving only the very small source-separation contribution cannot repair this specific insertion.

Localizing source arcs and then rescaling is not free: unit circles become circles of radius comparable to 1/u, so (1) or (2), stated for radii in a fixed interval, cannot be reapplied with unchanged constants. The note makes no such rescaling claim. Equation (27) is the valid separation-dependent consequence actually obtained from the cited global estimates.

For a fixed threshold T, the right side of the tail bound tends to the trivial upper bound one in the target range. It therefore gives no positive lower bound for the mass with crowding at most T. Taking any fixed positive fractional moment merely multiplies the negative resolution exponent by gamma/p; it does not remove it.

The logarithmic criterion is not supplied either. Integrating the same tail against (1+lambda)^{-1} gives only a bound of size

$$
C+\frac\zeta p\log\frac1\delta
$$

for the crowding logarithmic moment. Thus the optimized positive ratio in (21) or (24) survives at that endpoint as logarithmic growth. Choosing a moment exponent tending to zero with the resolution would not be the fixed positive fractional-moment or uniform entropy hypothesis previously proved.

This bounded attempt rules out a concrete shortcut: insert these published approximate-circle bounds through the global rich-circle count, with either of the natural parameter-space nonconcentration estimates above, and hope that fractional moments or packing cell cardinalities produce a new dimension region. The numerical substitution does not do so. The result leaves open estimates retaining source-pair structure before the global circle count, an effective treatment of narrow configurations, or a genuinely stronger localized incidence theorem.
