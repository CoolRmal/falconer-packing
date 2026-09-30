# Positive good-part selection for train tracks: an exact cure and a remaining obstruction

Date: 2026-09-30.

This note starts from the finite train-track family and the fixed glued measures in [the off-cluster collision obstruction](2026-09-30-off-cluster-collision-obstruction.md). It addresses actual positive source–pin interaction deletion, rather than repeating the failure of the unmodified joint $L^2$ estimate.

Three new statements are proved:

1. A pin-dependent transverse deletion of summably small mass gives a uniformly bounded mollified pinned density for the entire finite train-track configuration.
2. Deleting only the pin's own source track does **not** suffice when the covering exponent is below $4/3$: nearby tracks still force divergent off-cell collisions.
3. There is a quantitative necessary deletion budget. In particular, pin-independent source thinning retaining fixed positive mass cannot replace interaction selection, and overly fast power decay of the allowed deletion fails even for one fixed glued pair of measures.

These are finite-configuration estimates and method obstructions. No improved dimension-only distance theorem follows yet.

## 1. Geometric data

Fix

$$
1<s<4/3,\qquad 3-2/s\le u\le2,
$$

and write

$$
\alpha=u-1,\qquad \beta=(s-1)/2,\qquad p=\beta/\alpha,
$$

$$
a=\delta^p,\qquad w=\delta^{1/2},\qquad h=\delta^{s/2}.
\tag{1}
$$

The hypotheses imply

$$
0<\beta\le p<1/2<s/2<1,
\qquad a\gg w\gg h\gg\delta.
$$

Choose track centers $c_i$ from a maximal $3a$-separated net of an $\alpha$-Ahlfors regular compact set in a fixed horizontal interval. There are $N_T\asymp a^{-\alpha}$ tracks, with common mass

$$
m=N_T^{-1}\asymp a^\alpha=\delta^\beta.
\tag{2}
$$

The normalized track-center counting measure obeys

$$
N_T^{-1}\#\{i:c_i\in J\}\le C(|J|^\alpha+a^\alpha)
\tag{3}
$$

for every interval $J$.

Each track has $N_S\asymp h^{-1}$ slats at heights $v_k=kh$ in a bounded interval. A slat contains $N_X\asymp w/\delta$ pairwise disjoint microscopic cells, with horizontal centers $c_i+z_\ell$ spaced by $4\delta$ across an interval of length comparable to $w$. Every cell is contained in a ball of radius $C\delta$ about its center, and has the same mass

$$
m_{\rm cell}=(N_TN_SN_X)^{-1}\asymp m h\delta/w\asymp\delta^s.
\tag{4}
$$

The microscopic cell probabilities can be the regular tails used in the earlier construction. Their internal structure is irrelevant to the new upper bound. Let $\mu_\delta$ denote the resulting source probability and $\nu_\delta$ its translate by $(0,3)$. Source–pin vertical distances are bounded above and below by positive constants. The earlier note proves the uniform $s$-Frostman and $u$-covering estimates for this family.

Fix a nonnegative compactly supported smooth probability mollifier $\varphi$. For a positive source measure $\eta_y$ depending on the pin, define

$$
f_{y,\varepsilon}(t)=\int\varepsilon^{-1}\varphi\left(\frac{t-|x-y|}{\varepsilon}\right)\,d\eta_y(x).
\tag{5}
$$

All estimates below allow any fixed ratio $\varepsilon/\delta$ bounded above and below by positive constants. For collision lower bounds, choose $\varepsilon=L\delta$ with a sufficiently large fixed $L$, as in the earlier note.

## 2. A positive deletion that gives uniform $L^\infty$

Put

$$
r_0=h/w=\delta^\beta.
\tag{6}
$$

Notice $r_0\ge a$ and $r_0/w\to\infty$. For each pin $y$, delete every source track whose center satisfies

$$
|c_i-y_1|<A r_0,
\tag{7}
$$

where $A$ is a sufficiently large fixed constant. Let $\eta_y$ be the restriction of $\mu_\delta$ to the remaining tracks.

**Proposition 1.** Uniformly in sufficiently small $\delta$ and in every pin in the translated source region,

$$
\mu_\delta(\mathbb R^2)-\eta_y(\mathbb R^2)
\le C\delta^{\alpha\beta},
\qquad
\|f_{y,\varepsilon}\|_\infty\le C.
\tag{8}
$$

Consequently

$$
\int\|f_{y,\varepsilon}\|_2^2\,d\nu_\delta(y)\le C.
\tag{9}
$$

The bound includes all source pairs, so it also controls every positive cross-cluster subintegral.

**Proof.** By (3), the removed mass is at most

$$
C(r_0^\alpha+a^\alpha)\le C r_0^\alpha=C\delta^{\alpha\beta}.
$$

Fix a retained track and write $r=|c_i-y_1|\ge A r_0$. Since $r_0\gg w$, horizontal source–pin separation throughout this track is comparable to $r$. Source–pin distances are bounded above and below, so the derivative of the distance with respect to the horizontal source coordinate has magnitude comparable to $r$ and constant sign on the track.

Consider one slat. If any point of a microscopic cell contributes to (5) at the radial location $t$, its center has distance within $C\delta$ of $t$. Along the horizontal sequence of cell centers, successive distances differ by at least $cr\delta$. Thus at most $C(1+1/r)\le C'/r$ cells can contribute. By (4), the density contributed by this slat is at most

$$
C\delta^{-1}\frac1r\,m_{\rm cell}
\le C\frac{m h}{r w}.
\tag{10}
$$

The entire distance image of that slat, including mollification, lies within $Crw+C\delta$ of the distance of its center $(c_i,v_k)$ from $y$. Here the horizontal variation is at most $Crw$, because $r\gg w$, and the microscopic vertical variation is $O(\delta)$. Since $rw\ge A h\gg\delta$, the interval length is at most $Crw$.

As $k$ varies, the central distances $|(c_i,v_k)-y|$ are monotone with successive gaps at least $ch$, because the vertical separation is bounded away from zero. Therefore at most $C(1+rw/h)$ slats can contribute at any $t$. Multiplying (10) by this number bounds the whole track's density by

$$
C m\left(1+\frac{h}{rw}\right)\le C'm.
\tag{11}
$$

Summing over the retained tracks gives $\|f_{y,\varepsilon}\|_\infty\le C$ because their total source mass is at most one. Since $f_{y,\varepsilon}\ge0$ and has first norm at most one, its squared second norm is at most the same constant. This proves (8)--(9).

The numerical deletion bound $C\delta^{\alpha\beta}$ is summable on dyadic sequences of $\delta$. The finite family here varies with $\delta$; this observation does not by itself construct a consistent all-scale good part for an arbitrary fixed measure.

## 3. Deleting only the own track is insufficient

The successful deletion (7) removes a neighborhood of the pin's track. Removing only the track containing the pin leaves a further obstruction.

**Proposition 2.** Suppose in addition that $u<4/3$; this is possible under the stated hypotheses precisely when $s<6/5$. Let $\eta_y$ be $\mu_\delta$ with only the pin's own track removed. Then

$$
\|f_{y,\varepsilon}\|_2^2\ge c\delta^{3\beta-p}
\quad\text{for every pin in the translated source support},
\tag{12}
$$

where

$$
3\beta-p=\beta(3-1/\alpha)<0.
$$

The same averaged divergence comes from pairs in distinct microscopic cells, up to a term tending to zero.

**Proof.** Every net center has another center at distance between $3a$ and $Ca$, with $C$ independent of $a$. To justify this, use the lower Ahlfors bound on a ball of radius $Ca$ and the upper bound on a ball of radius $6a$. For sufficiently large fixed $C$, there is a point of the regular set in the larger ball outside the smaller one. Maximality of the $3a$-net gives a different center within $3a$ of that point, yielding the claimed distance bounds after enlarging $C$.

For a pin in its own track, its horizontal displacement from that track center is $O(w)=o(a)$. Hence one remaining neighboring source track is at horizontal distance comparable to $a$ from the pin. A source slat in this track has radial image, after smoothing, of length at most

$$
C(aw+\delta)\le C'aw,
$$

because $p<1/2$ implies $aw\gg\delta$. The whole neighboring track therefore has mollified radial support of length at most $CN_Saw$. Its source mass is $m$. Cauchy–Schwarz gives

$$
\|f^{\rm neighbor}_{y,\varepsilon}\|_2^2
\ge\frac{m^2}{CN_Saw}
\ge c\frac{m^2h}{aw}
\asymp\delta^{2\beta+s/2-p-1/2}
=\delta^{3\beta-p}.
$$

The retained full density dominates this nonnegative neighboring-track density, proving (12).

For the microscopic-cell partition, every positive restriction $\eta_y\le\mu_\delta$ has same-cell collision contribution at most

$$
C\delta^{-1}\sum_{A\text{ cell}}\mu_\delta(A)^2
\le C\delta^{s-1}\longrightarrow0.
\tag{13}
$$

Subtract (13) from the positive collision identity for (12). The divergent remainder comes from distinct cells.

For example,

$$
s=11/10,\qquad u=13/11,
\qquad \beta=1/20,\quad p=11/40,
$$

gives the lower bound $c\delta^{-1/8}$ after the own-track deletion. Proposition 1 nevertheless obtains a bounded density after a wider deletion of mass at most $C\delta^{1/110}$.

## 4. A necessary deletion budget

Consider any measurable positive interaction selection

$$
d\eta_y(x)=\theta(x,y)\,d\mu_\delta(x),\qquad 0\le\theta\le1.
$$

Write

$$
r_y=1-\eta_y(\mathbb R^2),\qquad
e=\int r_y\,d\nu_\delta(y).
$$

**Proposition 3.** For the sufficiently large fixed smoothing ratio $\varepsilon=L\delta$,

$$
\int\|f_{y,\varepsilon}\|_2^2\,d\nu_\delta(y)
\ge c\delta^{s/2-1}(m-e)_+^2.
\tag{14}
$$

The off-cell contribution is at least the right side minus $C\delta^{s-1}$. In particular, a uniformly bounded retained averaged second norm forces

$$
e\ge m-C\delta^{(2-s)/4}
=m\left(1-O\!\left(\delta^{(4-3s)/4}\right)\right).
\tag{15}
$$

**Proof.** Fix a pin and consider its own source track. Points in one slat of that track have mutual pinned-distance difference at most $C\delta$, because the horizontal offsets are $O(w)$ and $w^2=\delta$, while vertical variation within a slat is $O(\delta)$. For $K=\varphi*\widetilde\varphi$, continuity and $K(0)>0$ show that the collision kernel at scale $L\delta$ is at least $c\delta^{-1}$ on these pairs when $L$ is a large enough fixed constant.

Let $q_k$ be the retained source mass in the $k$th slat of that track. Its total retained mass is at least $(m-r_y)_+$. The positive collision identity and Cauchy–Schwarz over $N_S$ slats give

$$
\|f_{y,\varepsilon}\|_2^2
\ge c\delta^{-1}\sum_k q_k^2
\ge\frac{c}{\delta N_S}(m-r_y)_+^2.
$$

Average and apply Jensen to the convex function $(m-r)_+^2$. This proves (14), since $N_S\asymp\delta^{-s/2}$. Equation (13) gives its off-cell version. Taking square roots of (14) under a uniform second-norm bound gives (15), and $(2-s)/4-\beta=(4-3s)/4>0$.

Thus a deletion budget $e=O(\delta^\gamma)$ with $\gamma>\beta$ is too small to bound the retained collision. When $u=2$, one has $\alpha=1$, so Proposition 1 achieves the necessary deletion exponent $\beta$. For $u<2$, the upper bound $\delta^{\alpha\beta}$ and this necessary lower bound $\delta^\beta$ leave a quantitative gap; optimal deletion rates are not claimed there.

### Pin-independent thinning cannot substitute for interaction selection

If $\eta$ is any fixed positive measure on the finite source support with total mass $M$, independent of $y$, then

$$
\int\|\varphi_\varepsilon*(d_y)_*\eta\|_2^2\,d\nu_\delta(y)
\ge c\delta^{3s/2-2}M^2.
\tag{16}
$$

Indeed, let $q_i$ be its mass in source track $i$. Pins in track $i$ have total probability $m=1/N_T$. The preceding within-track slat argument gives, after averaging the pins in that track, a contribution at least $cm\delta^{-1}q_i^2/N_S$. Sum over tracks and use

$$
\sum_i q_i^2\ge M^2/N_T=mM^2.
$$

This gives (16). If $\eta\le\mu_\delta$, its same-cell term is still bounded by (13), so the divergence persists off-cell whenever $M$ is bounded below. Unlike Proposition 1, merely choosing one large source subset does not cure this finite-scale example.

## 5. Overly fast deletion fails for one fixed pair of measures

The power restriction from Proposition 3 can be transferred to the fixed glued example in the earlier off-cluster note. Recall its notation:

$$
\lambda_j=c2^{-j},\qquad
\delta_j=2^{-(j+j_0)^2},\qquad
w_j=Z^{-1}\lambda_j^s,\qquad
\varepsilon_j=L\lambda_j\delta_j.
$$

The source and pin block probabilities are both $w_j$. Their conditional train tracks have $N_{S,j}\asymp\delta_j^{-s/2}$ slats and track mass $m_j\asymp\delta_j^\beta$.

Let an arbitrary positive selection $\eta_{j,y}\le\mu$ have averaged deleted mass $e_j=\int(1-\eta_{j,y}(\mathbb R^2))\,d\nu(y)$. Restrict the collision to source block $j$ and pin block $j$. The same slat argument, followed by Jensen on the pin block of mass $w_j$, gives

$$
\mathcal C^{\rm retained}_{\varepsilon_j}
\ge\frac{c}{\varepsilon_jN_{S,j}w_j}
\left(w_j^2m_j-e_j\right)_+^2.
\tag{17}
$$

For clarity, each pin in that block initially sees source mass $w_jm_j$ in its corresponding track. If $r_y$ is the total deleted source mass, integrate $(w_jm_j-r_y)_+^2$ over that pin block. Jensen bounds it below by $w_j^{-1}(w_j^2m_j-e_j)_+^2$, which is (17).

If $e_j\le C\varepsilon_j^\gamma$ for any fixed $\gamma>\beta$, then

$$
\frac{e_j}{w_j^2m_j}
\lesssim\lambda_j^{\gamma-2s}\delta_j^{\gamma-\beta}
\longrightarrow0.
$$

Consequently (17) is bounded below by

$$
c\lambda_j^{3s-1}\delta_j^{3s/2-2}\longrightarrow\infty.
\tag{18}
$$

The exponent $3s/2-2$ is negative, and the quadratic decay in $\log\delta_j$ dominates every fixed exponential factor from $\lambda_j$. The fixed measure is $s$-Frostman, so its same-square contribution at side length $\varepsilon_j$ is at most $C\varepsilon_j^{s-1}\to0$. Thus the retained off-square collision still diverges.

The same argument applies to the finite-$I_s$ variant in the earlier note, because it only uses the unchanged macroscopic track/slat masses and the Frostman bound. This obstruction allows arbitrary positive pin-dependent selection subject to that deletion budget. It does not prohibit slower positive-power deletion, such as that in Proposition 1, and it does not apply directly to signed frequency-dependent wave-packet modifications.

## 6. Implication for the next analytic step

For the principal counterexample family, a positive pin-dependent selection genuinely restores a bounded bilinear collision integral. The necessary deletion is wider than the most obvious own-track removal: nearby tracks matter when $u<4/3$. The gain in (11) comes from explicit transversality and overlapping radial images of successive slats once $rw\ge h$.

A general improvement would need an analogue of this argument for arbitrary measures and multiple directions, with a summable deletion cost and a quantitative retained cross-cluster estimate. The proofs above do not supply such a general estimate or improve the published packing curve. They provide a concrete, verified test for a proposed refinement: it should survive the neighboring-track obstruction, allow pin-dependent selection, and account for the tradeoff between deletion rate and collision growth.
