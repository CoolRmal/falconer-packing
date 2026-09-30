# Independent audit of the recursive source obstruction

30 September 2026. Reviewed `2026-09-30-nonremovable-bisector-source-obstruction.md`, Sections 1–7. The construction and claimed obstructions pass. The scope is a raw joint density estimate for specified source/pin measures, not positive-length distances or pin-dependent positive pair selections.

## Geometry and dimensions

The exact block counts give M_L=2^{44L-8}=2^{-8}delta^{-11/10}. Child squares have fixed ratio c delta, uniform separation much larger than their side, and lie inside the parent. The track center construction has the required separation and uniform truncated Cantor estimates. The four mass and cover ranges in the block table check, including the critical cover identity u=3-2/s. Arbitrary probabilities inside child squares do not affect these estimates: they follow from cell counts and equal cell masses at radii at least c delta.

At recursive scales, the factor p_j lambda_j^{-s} grows only exponentially in the stage count. For every t<s it is absorbed by lambda_j^{s-t}, proving a global t-Frostman bound. The endpoint covers give Hausdorff dimension s. The upper box bound follows directly from the uniform one-block cover estimate and boundedness of P_j lambda_j^u; it does not accumulate an uncontrolled cover constant through all levels.

At the intermediate scale lambda_{j-1}h_j, the mass bound is

$$
\sup_x\mu(B(x,\lambda_{j-1}h_j))
\le C p_{j-1}\delta_j^{3s/2-1}.
$$

Here a ball meets boundedly many tracks and slats, and O(h_j/delta_j) horizontal cells. Since each new L_j dominates all preceding depths, the resulting lower covering exponent for every positive-outer-mass subset is (3s/2-1)/(s/2)=13/11. The countable-cover characterization then gives packing dimension 13/11, also for every positive-measure subset of K. The level separation justifies using the same bound for arbitrary balls, not only parent-centered balls.

## Collision and measure quantifiers

Pins are translated globally by three; matched parent separation is not scaled by lambda. This is handled correctly: within one source slat, vertical variation is O(lambda delta) and squared horizontal variation is O(lambda^2 w^2), which is smaller than the former because w^2=delta and lambda≤1. A fixed sufficiently large mollification ratio therefore gives the required positive collision lower bound uniformly in the pin.

A parent has natural measure mass p and matched natural pin-track mass pm; its mass under the arbitrary source eta need not equal p. Cauchy–Schwarz over slats, tracks, and the 1/p parents gives exactly

$$
c M^2p^2\lambda^{-1}\delta^{3s/2-2}.
$$

For s=11/10 the exact base-two logarithm is

$$
14L_j-48\sum_{k<j}L_k+26(j-1),
$$

which tends to positive infinity under the explicit recursive choice. The proof uses only that the source is a finite positive measure supported on K. Source domination by mu is not needed for the fixed full-pin statement.

For matched pins T_*eta, the extra pin-track mass factor replaces the quadratic sum by a cubic one and gives M^3 instead of M^2. The common-submeasure extension follows by positivity. It does not cover unrelated source and pin restrictions with no common pulled-back part.

## Weak norms and bisectors

The measurable joint support S_j has base measure at most C lambda delta^{1-s/2} under the full pin law, while it carries joint distance mass at least pmM. The weak-norm set inequality produces the exponent

$$
\beta-(1-s/2)(1-1/q),
$$

negative exactly for q>9/8. The new block depth dominates all old prefactors for every fixed q in that range. The matched and common-submeasure variants use the actual pin base measure and do not make an invalid change-of-measure assertion for weak norms.

Finally, the natural translated pin law has finite I_tau for every tau<s. Thus the mixed bisector criterion would contradict the fixed-pin L2 obstruction for any nonzero source measure on K having finite I_1 and the claimed finite bisector mixed norm. The finite-first-energy hypothesis must remain explicit when strengthening beyond dominated restrictions: an atom has zero off-diagonal bisector pushforward but infinite first energy. The collision lower bound itself needs no energy assumption. The example remains compatible with weaker Lp conclusions near one and with the established dimension criterion, since 13/11<2(11/10)-1.

## Final TeX check

The complete conversion in `output/pdf/packing-unforced-source-restriction-obstruction.tex` preserves these estimates and quantifiers. Its main statement explicitly retains finite first energy for the bisector consequence, allows every nonzero finite positive source measure supported on K for the collision and weak-norm obstruction, and limits the independent pin restriction variant to a common nonzero pulled-back submeasure. The matched-pin weak-norm argument uses the correct additional total-mass factor in the base measure. No conversion issue was found.

## Stronger same-set full-pin variant

The full natural pin measure can also be mu itself, with no translation. In a fixed parent and track, for a pin in slat ell use source slats k with |k-ell| at least N_S/4. For every source slat, at least N_S/2 pin slats are eligible. Since N_S h=1/16, eligible source and pin points have vertical separation at least a fixed constant times lambda. Within one source slat, the difference-of-squares identity therefore bounds distance oscillation by

$$
C\lambda\delta+C\frac{\lambda^2w^2}{\lambda}
\le C'\lambda\delta.
$$

The measurable union of all eligible slat distance intervals has mu-times-Lebesgue measure at most C lambda delta N_S. For every finite positive eta supported on K, its joint distance law assigns this union mass at least c p m eta(K), since each source slat sees at least half the equal-mass natural pin slats in its parent-track. The preceding weak-norm calculation is unchanged, and rules out a weak-Lq density for q>9/8 with pins mu on the same K. No claim is made for arbitrary same-set matched pins eta: the eligible pin slats need not carry any eta mass. The translated matched-pin assertion proved above remains a separate valid statement.

The root's sharper first-digit involution gives a cleaner proof with every support window bounded away from distance zero. At the first stage replace the slat index k by k+N_S/2 modulo N_S, keeping the track, horizontal child, and all later digits fixed. This is a measure-preserving involution F of K. On every first-generation child it is exactly vertical translation by either +1/32 or -1/32, because N_S h=1/16. Hence for j at least two every parent Q, together with all its descendants, is translated by one fixed vector to F(Q).

For a pin in F(Q,i), the original fixed-separation slat-width proof applies. All such distances lie in [1/64,1/16], since lambda is at most the extremely small first-generation side length. The disjoint pin tracks F(Q,i) have natural mass pm. The joint support therefore has law mass at least pm eta(K), base measure at most C lambda delta N_S, and lies in that one fixed compact interval of positive distances. The same weak-Lq failure holds even after restricting the joint law to this interval. No near-zero singularity is used. This sharper involution proof independently passes and can replace the eligible-slat proof in the manuscript.

The final TeX conversion now uses this involution proof; its sourceobs:samepins support estimate and its application to the finite-energy bisector consequence have been checked directly. The interval assertion is specific to full same-set pins mu. For translated matched pins T_*eta, the conclusion concerns the full joint law instead.
