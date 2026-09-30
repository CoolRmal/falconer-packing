# Fresh adversarial audit of the unforced Fourier transfer

Date: 2026-09-30. Files checked: `output/pdf/packing-unforced-transfer.tex`, `output/pdf/packing-unforced-embedding.tex`, and the regularization, deletion, and summation interfaces in `output/pdf/packing-unforced-finite-profile.tex`. This is a written mathematical audit, not a formal verification. No published source was changed.

**Verdict:** I found no analytic gap in the checked implication from an admissible bounded-length profile chain to the stated shell estimates. In particular, fine angular splitting does not introduce a missing cap-count factor, and the inherited selections have the constancy required by the embedding. This audit does not independently prove the profile minimax or optimality of the resulting dimension condition.

## 1. The two angular inequalities have separate jobs

For one edge let

$$
a=2^{-n},\qquad b=2^{-m},\qquad
0\le m<n,\qquad 2n-m\le N,\qquad R=2^N.
$$

The auxiliary angular width, standard source width, and tube aspect ratio are

$$
\delta=(Ra)^{-1},\qquad\delta_*=R^{-1/2},\qquad\rho=a/b.
$$

Admissibility gives both

$$
\delta\le\rho,
\qquad
\delta_*\le\rho.
$$

The first is equivalent to

$$
b\le Ra^2.
$$

It says that curvature of an auxiliary circular arc fits inside a frequency rectangle with tangential width comparable to the reciprocal child scale and normal width comparable to the reciprocal parent scale. The second follows because

$$
n-m\le\min\{n,N-n\}\le N/2.
$$

It controls the difference between a fine auxiliary direction and the coarser standard source direction used for its mark. These are separate conditions. The proof checks both, so it does not wrongly identify a fine Fourier piece with a thinner source packet.

## 2. Fine labels and the exact inherited identity

The smooth standard source multipliers are fixed first. A finer label keeps both its standard label and its dyadic angular interval. Each standard multiplier is partitioned across its entire support, including the portion outside its nominal interval. Therefore summing its terminal pieces recovers the original standard multiplier exactly.

Every standard label belongs to one coarse nominal ancestor, even when neighboring smooth supports overlap. A terminal label has a unique ancestry as a label. At each direction there are only boundedly many active standard multipliers. Consequently duplicated intervals coming from overlapping standard multipliers have bounded multiplicity.

At a fixed auxiliary level the circular centers are separated at scale

$$
r\delta\asymp_T a^{-1},\qquad r\asymp_T R.
$$

Their supports thus lie in balls of radius comparable to the reciprocal child scale with bounded overlap. Fixed frequency smoothing adds only bounded radius. Since all auxiliary widths are at least the reciprocal full frequency, it cannot create growing overlap.

For a fixed spatial parent P, the function assigned to an angular label contains precisely those terminal descendants surviving marks at P and its ancestors. It does not depend on the child Q. The current mark is constant for all descendants of that label. Hence the identity really is

$$
F_{Q,\alpha}=\sum_{\theta\prec\alpha}
\varepsilon_{Q,\theta}F_{P,\theta},
\qquad \varepsilon_{Q,\theta}\in\{0,1\}.
$$

The coefficients are constants on the entire averaging integral, even though different children select different subsets. Overlaps between enlarged child cubes do not change this algebra: the objects assigned to two different cubes need not agree on their overlap.

After crossing the standard angular scale, the fine descendants of a standard label have identical mark decisions. This permits the later fine splitting while preserving standard-cap reconstruction. The proof never uses localization of an individual hard-truncated source packet.

## 3. Initial reconstruction uses only standard packets

The primary comparison is [Liu v3, Lemmas 4.2–4.4](https://arxiv.org/html/2603.15328v3). Lemma 4.2 gives rapid smallness of a standard packet's circular extension on a pin cube disjoint from twice its tube. Lemma 4.3 provides the inherited cap identity, and Lemma 4.4 applies local orthogonality before tube-mass control.

The manuscript follows that order. For each standard label, sum its spatial packet partition first. On the initial cube, remote packets have a rapid circular-extension error. For a bad label all nonremote packets were removed, so its retained remote remainder contributes only that error. A surviving label reconstructs the full standard cap. Only then is its circular spectral measure subdivided into fine intervals.

The fixed source cutoff causes no extra power loss. The smooth annular-cap kernel decays rapidly outside transverse scale

$$
R^{-1/2}
$$

and longitudinal scale

$$
R^{-1}.
$$

Outside a fixed neighborhood of the source support, multiplying by the omitted part of that cutoff therefore leaves an integrably rapid error, including any fixed number of derivatives. This error bounds its circular extension uniformly on the annulus. All actual source functions retain the cutoff, which ensures compact support and separation for the pinned quadratic identity.

The packet tube length must cover the normalized source–pin region; the printed convention does this. Thus remoteness means transverse remoteness. The integration-by-parts argument is not being applied merely because a pin lies beyond an artificial tube endpoint.

Initial localization also checks. A globally band-limited reconstructed function has a pointwise quadratic bound by a rapidly weighted average at scale equal to the reciprocal frequency. Enlarging to the initial cube costs the area ratio

$$
R^{2\zeta+O(T/N)+O_K(h)}.
$$

It is an upper bound for the same globally defined reconstructed function. Equality between that function and the selected source extension is needed only at the original pin, not outside its pin cube. The enlargement creates no unproved equality across neighboring masks.

## 4. The selected-cap embedding is valid with arbitrary child subsets

Let the child and parent side lengths be a and b. In the embedding proposition,

$$
Q^+=L^{2j+2}Q,\qquad
\widetilde Q=LQ^+,\qquad
P^+=L^{2j+4}P,
$$

and

$$
w_Q=\sigma(Q^+),\qquad M=\sigma(P^+),\qquad
\Lambda\lesssim L^{4j+4}.
$$

The selected test bounds the mass of a sufficiently enlarged child-centered tube by

$$
H\frac ab M.
$$

For any translate U of an actual dual rectangle, choose one selected enlarged child meeting U. Every smaller averaging cube whose further enlargement meets U lies inside the chosen child's marked tube. The direction error contributes at most a constant times the child width to the transverse displacement, because the mismatch is at most a constant times the aspect ratio. The prescribed large dilation absorbs all child enlargements. Thus

$$
\sum_{\substack{Q:\varepsilon_{Q,\theta}=1\\
                  \widetilde Q\cap U\ne\varnothing}}w_Q
\le\Lambda H\frac ab M.
$$

All cubes are also inside the same enlarged parent. Therefore the conditional normalization used in deletion is exactly the one required here.

For a fixed child, multiply by a Schwartz cutoff whose Fourier support is a small ball. Enlarging the original equal-radius containing balls by a factor two multiplies their overlap by at most nine in the plane: integrate their original overlap over the ball of triple radius about any point of multiple membership. Plancherel therefore controls the selected sum by the selected sum of squares, uniformly in the subset and its size. No deleted label is restored before its tube test is used.

The averaging measure for one label is

$$
\tau_\theta=\sum_{Q:\varepsilon_{Q,\theta}=1}w_Qm_{\widetilde Q}.
$$

Its mass on every dual rectangle obeys the preceding estimate. A reproducing kernel for the frequency rectangle satisfies

$$
|k_\theta(z)|\lesssim_p\frac1{ab}
\left(1+\frac{|z\cdot u_\theta^\perp|}{a}
          +\frac{|z\cdot u_\theta|}{b}\right)^{-p}.
$$

Summation over a lattice of dual rectangles gives

$$
\int|k_\theta(x-y)|\,d\tau_\theta(x)
\lesssim\frac1{ab}\Lambda H\frac ab M
=\frac{\Lambda HM}{b^2}.
$$

This is the precise cancellation of the aspect ratio. The single threshold factor is correct. The support of the averaging measure has a margin at least Lb inside the parent enlargement, so the kernel gives arbitrary decay outside that parent. The main factor after converting averages is

$$
L^2\Lambda\frac{|P^+|}{b^2}
\lesssim L^{8j+14}.
$$

The errors have the printed form

$$
C_mMa^{-2}L^{-m}\sum_\theta\|f_\theta\|_2^2.
$$

Because the actual functions have compact smoothed frequency support, all belong to quadratic integrability even when their underlying circular densities have hard angular endpoints. No derivative of a hard indicator occurs in the argument.

## 5. Terminal estimate and shell identification

The normalized mass of a radius-r circle in a fixed-radius frequency ball is bounded by a constant times the reciprocal frequency. Cauchy–Schwarz inside each smoothing convolution therefore gives

$$
\sum_\ell\|F_\ell\|_2^2
\lesssim_T R^{-1}\int_{S^1}|\widehat\mu(r\omega)|^2\,d\omega.
$$

The squared terminal multipliers sum to a uniformly bounded function. This estimate is independent of the number of fine labels. The final admissible edge places their width between the reciprocal frequency and its inverse square root, as required by the overlap analysis.

Combining the iterated estimate with the source energy bound gives the squared shell norm power

$$
R^{-1+\mathcal C+o(1)}R^{2-s}
=R^{1-s+\mathcal C+o(1)}.
$$

The notation for the small losses means fixed positive losses that can be chosen arbitrarily small before the frequency grows. It is not a uniform vanishing quantity along a fixed proof.

The off-annulus derivative estimate is applied to standard source packets only, and is uniform over their retained subsets. Arbitrary-order decay absorbs the polynomial numbers of packets, cubes, and labels. Each normalized component has the same uniform shell bound; multiplying by its mass and summing creates no component-count factor.

The pin-dependent functions are inserted into the pinned identity separately at each pin. The later identification of the full joint law tests against a smooth function integrated over pins; separation and the fixed source cutoff make this a smooth compactly supported source test. Hence the dependence of masks on pins does not invalidate distributional reconstruction.

## 6. A sharp stress test for the threshold power

The abstract embedding cannot replace its factor H by any fixed smaller power while retaining arbitrary-order errors. This is an obstruction to that specific improvement, not a planar dimension counterexample.

Use one child and one label, with

$$
j=0,\quad K=1,\quad b=1,\quad a=q^{-1},\quad
P=[-1/2,1/2]^2,\quad Q=[-a/2,a/2]^2,
$$

and take the pin measure to be the unit atom at zero. Both child and parent weights equal one. Put

$$
u=v=(0,1),\qquad H=q.
$$

The selected test holds exactly since its tube contains the atom and

$$
H\frac ab=1.
$$

Choose a Schwartz function with compact Fourier support, positive near zero, and let

$$
f(x_1,x_2)=\varphi(x_1/a)\varphi(x_2).
$$

Its Fourier support satisfies the required rectangle hypothesis. Fix any hypothetical power

$$
0\le\gamma<1.
$$

Choose

$$
L=q^\varepsilon,
\qquad
0<\varepsilon<\frac{1-\gamma}{8}.
$$

As q tends to infinity, the child average is bounded below by a constant times

$$
L^{-2},
$$

because the transverse integration captures width comparable to a while the longitudinal child length is much smaller than one. The parent average is bounded above by

$$
CL^{-8}q^{-1},
$$

using the global squared norm, which is comparable to a. Replacing H by its power gamma in the printed main term would therefore give at most

$$
CL^6q^{\gamma-1}.
$$

Its ratio to the lower bound is at most

$$
CL^8q^{\gamma-1}\longrightarrow0.
$$

The printed error divided by the same lower bound is at most

$$
C_m qL^{2-m}.
$$

Choose a fixed decay order greater than two plus the reciprocal of epsilon. This ratio also tends to zero, a contradiction. All constants and that decay order are fixed before q grows.

This example uses an atomic pin measure, which the abstract embedding expressly permits. It does not rule out better estimates exploiting additional Frostman, pair-incidence, or angular structure beyond the embedding hypotheses.

## 7. What could and could not change the cutoff

The enlargement powers, bounded overlaps, grid constants, and initial localization loss are already allowed to be arbitrarily small in the exponent when the final inequality is strict. Reducing those constants would not move the limiting strict curve.

The terminal reciprocal-frequency factor is also sharp for arbitrary circular data: constant data on one arc, smoothed at fixed frequency width, has squared norm comparable to arc mass divided by frequency. An improvement requires information about the actual Fourier data or its alignment with the retained pin geometry, not a correction to Cauchy–Schwarz alone.

At the equality boundary, the existing proof has no positive summability margin. Merely making positive losses small does not make them negative or summable. A legitimate endpoint theorem would need new quantitative control of these losses and the shell contributions. None is obtained by this audit.
