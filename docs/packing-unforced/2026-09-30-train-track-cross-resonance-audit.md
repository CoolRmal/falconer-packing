# Independent audit of sharp finite train-track deletion

Date: 2026-09-30. Audited source: 2026-09-30-sharp-finite-train-track-deletion.md, together with the necessary lower bound in Section 1 of 2026-09-30-persistent-selection-and-half-potential.md and the original finite family in 2026-09-30-positive-train-track-selection.md.

**Result:** no substantive defect found. The deterministic cross-track estimate, radius summation, and matching deletion exponent pass the checks below. This audit concerns the finite family only.

## 1. No hidden independence of pin coordinates

The draft defines offsets using the pin track center, not the exact horizontal pin coordinate:

$$
r_i=|c_i-c_j|.
$$

Every microscopic pin in its slat lies within a horizontal error of order w and a vertical error of order delta from the stated center. Retained offsets are at least rho, with rho at least a fixed multiple of a and a much larger than w. Replacing the actual horizontal coordinate by the track center changes a squared-radius difference by at most a constant times Rw. This is already included in the collision tolerance.

The slat envelope is pointwise over all microscopic pin positions. Consequently averaging equal pin-slat masses is valid even if the conditional horizontal and vertical coordinates inside those microscopic cells are dependent. No conditional-uniformity or random-shift assumption is being made.

## 2. Independent derivation of the lattice count

For two near tracks with offsets

$$
\rho\le r\le R\le r_0,\qquad \Delta=R^2-r^2,
$$

the product of the two slat envelopes has amplitude

$$
\frac{Cm^2h^2}{rRw^2}.
$$

Its interval intersection has length at most a constant times rw. Integration in distance therefore leaves the prefactor

$$
\frac{Cm^2h^2}{Rw}.
$$

With source slat shift q and source–pin vertical separation V, the remaining condition is

$$
|\Delta-qh(2V-qh)|\le CRw.
\tag{1}
$$

Both V and V-qh remain in a fixed positive compact interval. For fixed source slat k and q not zero, changing the pin slat by one changes the expression in (1) by exactly

$$
2|q|h^2.
$$

Thus its number of admissible pin slats is at most

$$
C\left(1+\frac{Rw}{|q|h^2}\right).
$$

Dividing by the pin slat count and summing the source slat gives, before any simplification, the bound per nonzero q

$$
Cm^2\left(\frac{h^2}{Rw}+\frac1{|q|}\right).
\tag{2}
$$

The discrete error in (2) is genuinely controlled. Necessity of (1) gives

$$
|q|h\le C(\Delta+Rw)\le C(R^2+Rw),
$$

and hence

$$
\frac{|q|h^2}{Rw}\le C(Rr_0+h).
$$

Since R is at most r_0 and r_0 tends to zero, the right side is uniformly bounded. Therefore the first term in (2) is absorbed into its second term, as asserted in the draft.

If Delta is larger than a fixed multiple of Rw, then q is positive and lies in a fixed-ratio interval

$$
c\Delta/h\le q\le C\Delta/h.
$$

Its harmonic sum is uniformly bounded, even if the interval meets the first positive integer. If Delta is at most a fixed multiple of Rw, then

$$
|q|\le CRw/h\le C,
$$

so again the nonzero reciprocal sum is bounded. There is no unestimated logarithm or equidistribution assertion.

For q equal to zero, all corresponding source and pin slats may resonate. Keeping all of them gives exactly the additional upper bound

$$
Cm^2\frac{r_0}{R}\,\mathbf1_{\{\Delta\le CRw\}}.
$$

This includes the most adverse exact arithmetic resonance rather than discarding it.

## 3. Equal-radius resonances do not accumulate a new multiplicity

The exceptional condition implies

$$
|r_i-r_{i'}|\le Cw.
$$

For any fixed pin track and fixed source track, possible partner centers lie in two intervals of length comparable to w: one near the source center itself and one near its reflection through the pin center. The center separation is comparable to a, and w divided by a tends to zero. Hence there are only a bounded number of partner tracks, even when the center set contains many exact three-term arithmetic progressions.

This is the decisive distinction between many global reflection symmetries and multiplicity for one fixed source–pin pair. Exact reflected pairs and the diagonal pair remain allowed, but their degree is bounded.

The exceptional contribution after summing is therefore at most

$$
Cm^2r_0\sum_{r_i\ge\rho}\frac1{r_i}
\le Cmr_0\rho^{\alpha-1}.
$$

The last inequality follows from the center counting estimate and a convergent geometric series because alpha is less than one. Its constants may depend on the fixed alpha, as in the original model. Far tracks have a pointwise bounded combined density, so both their self term and their cross term with all near tracks are bounded.

## 4. Cutoff algebra and the lower bound

For alpha less than one third,

$$
\rho=(mr_0)^{1/(1-\alpha)}
\asymp\delta^{2\beta/(1-\alpha)}
$$

satisfies both rho divided by a tending to infinity and rho divided by r_0 tending to zero. The extra collision term becomes one, and the deleted mass is at most

$$
C\rho^\alpha
\asymp C\delta^{2\alpha\beta/(1-\alpha)}.
$$

I also checked the referenced necessary estimate independently. In a radius-rho neighborhood of a pin track, lower Ahlfors regularity gives source mass at least a constant times rho to the alpha, distributed among at most a constant times rho to the alpha divided by m tracks. If the retained masses in these tracks are q_i, their radial support lengths imply

$$
\|f_y\|_2^2
\ge c r_0\sum_i\frac{q_i^2}{r_i}
\ge c mr_0\rho^{-1-\alpha}
       (c\rho^\alpha-r_y)_+^2.
$$

Averaging and Jensen show that a uniformly bounded joint second norm requires deleted mass at least a constant, depending on that norm bound, times rho to the alpha when rho is a sufficiently small fixed multiple of the displayed optimal scale. This matches the upper deletion order.

## 5. Scope

The claim is an optimal deletion order for the specified deterministic finite geometry and the averaged squared second norm. It does not prove a uniform pinwise second norm, a persistent selection for a fixed infinite construction, or a new Hausdorff–packing dimension inequality. The draft states these limitations correctly.
