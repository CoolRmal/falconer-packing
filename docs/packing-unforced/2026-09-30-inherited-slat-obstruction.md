# Why the finite slat average cannot be reused literally at infinitely many scales

30 September 2026. This note identifies a precise obstruction to transferring [the sharp finite train-track estimate](2026-09-30-sharp-finite-train-track-deletion.md) to a fixed nested measure. It does not disprove such a transfer with additional arguments. In particular, it does not exclude compensation between conditional source masses, pin masses, and the inherited geometry.

## 1. No fixed measure has the uniform global slat model at arbitrarily fine scales

Let $$\sigma$$ be a probability on a fixed bounded interval. Suppose there are scales

$$
h_j\to0,\qquad \delta_j/h_j\to0
$$

and families of intervals $$I_{j,k}$$, each of length at most $$C_0\delta_j$$, centered at distinct positions on an arithmetic grid of spacing $$h_j$$. Assume the number of relevant grid positions is at most $$C_0/h_j$$, and that

$$
\sigma\left(\bigcup_k I_{j,k}\right)=1,
\qquad
\sigma(I_{j,k})\le C_1 h_j
\tag{1}
$$

for constants independent of the scale. For sufficiently large indices the intervals are disjoint.

**Proposition 1.** No fixed probability satisfies these hypotheses.

**Proof.** A bounded interval $$J$$ meets at most

$$
C\bigl(|J|/h_j+1\bigr)
$$

of the slats. The support and mass assumptions imply

$$
\sigma(J)\le C C_1(|J|+h_j).
$$

Letting the scale tend to zero shows that $$\sigma(J)\le C C_1|J|$$ for every interval. Consequently $$\sigma$$ is absolutely continuous with an essentially bounded density. But the union of slats has length at most

$$
C_0^2\delta_j/h_j\to0.
$$

The bounded density then forces its mass to tend to zero, contradicting (1).

In the finite train-track model, the vertical projection has equal mass on each of the full arithmetic slats, with their number comparable to the reciprocal spacing. Moreover its slat thickness divided by spacing tends to zero. Thus the precise global model used in that finite proof cannot describe one fixed source or pin probability at infinitely many resolutions, with uniform constants. This obstruction is already one-dimensional and does not concern the choice of horizontal track centers.

## 2. A version allowing fixed positive retained mass

The preceding issue is not repaired merely by retaining a fixed positive amount of pin mass at each scale while leaving the same globally uniform slat bound.

Suppose $$\sigma_j\le\sigma$$ are positive submeasures of a fixed finite measure, their masses are bounded below by a fixed positive number, and they are supported on the same kinds of slat unions. Assume

$$
\sigma_j(I_{j,k})\le C_1h_j.
\tag{2}
$$

These hypotheses are also impossible. To see this, pass to a weakly convergent subsequence on the common compact support. The interval estimate from the preceding proof, or continuous interval majorants, gives an absolutely continuous weak limit with bounded density and positive mass.

Write the fixed measure as its absolutely continuous and singular parts. The absolutely continuous part gives mass tending to zero to the slat unions, because their lengths tend to zero. Hence the weak limit is also dominated by the fixed singular part: test nonnegative continuous functions against the submeasures after removing the negligible absolutely continuous contribution. This contradicts its positive mass and absolute continuity.

This is a statement about domination by one fixed measure and uniform full-grid counting. It is not the earlier vanishing-total-loss compactness argument, and it does not require the deleted mass to tend to zero.

## 3. The inherited gap has an explicit cost

Let the old vertical support be contained in a union of finitely many intervals

$$
K=\bigcup_{i=1}^{J}P_i,
\qquad
L=\sum_{i=1}^{J}|P_i|.
$$

Suppose a positive measure $$\tau$$ supported on this union has mass at least $$m_0>0$$. If a fine-scale counting estimate has the form

$$
\tau(I)\le C\bigl(|I|+h\bigr)
\quad\text{for every interval }I,
\tag{3}
$$

then summing (3) over the old parent intervals gives

$$
\boxed{\qquad C\ge\frac{m_0}{L+Jh}.\qquad}
\tag{4}
$$

In particular, at sufficiently fine fresh scales, the constant is at least a fixed multiple of the reciprocal inherited occupied length. A fixed positive retained mass does not remove this cost.

For a homogeneous interval Moran construction, let each parent of length $$\ell_{i-1}$$ have $$M_i$$ arithmetic children, of length $$\ell_i$$ and spacing

$$
h_i=\ell_{i-1}/M_i.
$$

After stage $$j$$ the total occupied length is

$$
L_j=\left(\prod_{i\le j}M_i\right)\ell_j
=\ell_0\prod_{i\le j}\frac{\ell_i}{h_i}.
\tag{5}
$$

If the product tends to zero, subsequent fine-grid estimates of the form (3), normalized for the full vertical probability, necessarily have constants tending to infinity at least as fast as a fixed multiple of $$L_j^{-1}$$. Taking the next microscopic resolution extremely small makes the discretization error harmless, but cannot make this inherited factor bounded.

There is a direct relation to the finite collision proof. Its nonzero slat-shift estimate counts pin indices in an interval arising from a linear phase. For a genuinely uniform full arithmetic grid, the fraction of indices in such an interval is controlled by its length plus the grid error, with an absolute constant. A nested vertical support supplies this estimate only after the inherited distribution is included; a uniform bound for arbitrary phase windows is subject to (4).

Conditioning in a single coarse cell merely changes the normalization and spatial scale. On an interval of length $$\ell$$, the normalized count has the form

$$
C\left(\frac{|I|}{\ell}+\frac{h}{\ell}\right).
$$

The factor from the parent length cannot be discarded. This is consistent with the elementary fact that a probability density supported on a radial interval of length comparable to $$\ell$$ has squared second norm at least a fixed multiple of $$\ell^{-1}$$.

## 4. What remains possible

The argument above does not show that the actual collision phase windows always realize the worst interval in (4). Their centers depend jointly on source offsets, source slat indices, and pin positions. Nor does it show that the growth survives after conditional source and pin weights are summed. A successful transfer may exploit exactly those correlations or replace the uniform counting step with a weighted multiscale estimate.

It does show that the following proposed proof is invalid: condition on coarse cells, insert the sharp finite estimate with the same absolute constant at every fresh stage, and claim that sufficiently rapid scale separation absorbs every error. The inherited occupied length is a real normalization factor, not a microscopic error.

No fixed singular Moran construction with a uniformly bounded retained full collision integral has been obtained here. The missing task is to control the weighted sum of inherited geometric costs, together with a persistent positive-mass selection, rather than to repeat the finite arithmetic averaging in isolation.
