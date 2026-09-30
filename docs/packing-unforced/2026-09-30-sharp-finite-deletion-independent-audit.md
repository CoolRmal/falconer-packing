# Independent audit of the sharp finite train-track deletion estimate

30 September 2026. The proof in [the sharp finite-deletion note](2026-09-30-sharp-finite-train-track-deletion.md) passes an independent check. This audit concerns the finite family and averaged squared second norm only; it supplies no persistent selection for an arbitrary fixed fractal measure.

The slat envelope is valid for arbitrary microscopic cell probabilities. Horizontal monotonicity, with derivative comparable to the retained track offset, permits only a constant times its reciprocal many cells to contribute at a given radial location. Both pin and source horizontal errors change the radial center by at most the offset times the slat width; their quadratic error and the vertical microscopic errors are absorbed because the offset is much larger than the slat width.

For two track offsets $$r\le R$$, integrating the product of their envelopes contributes the smaller interval width. This cancels the smaller offset in the amplitudes, leaving the coefficient

$$
\frac{m^2h^2}{Rw}
$$

in the collision count. Writing the vertical slat difference as $$q$$ gives exactly the phase

$$
\Delta-qh(2V-qh),\qquad \Delta=R^2-r^2.
$$

When the pin-slat index increases by one, this phase changes by $$2|q|h^2$$. The discrete counting error is absorbable because every contributing shift satisfies

$$
|q|h\lesssim\Delta+Rw,
\qquad
\frac{|q|h^2}{Rw}\lesssim Rr_0+h\lesssim1.
$$

Thus each nonzero shift contributes at most a constant times $$m^2/|q|$$ after averaging the actual discrete pin slats. If the squared-offset difference is larger than the collision tolerance, the shifts lie in a multiplicative window of fixed ratio. Otherwise there are only boundedly many shifts. Their harmonic sum is therefore bounded in both cases. No equidistribution or random shift is assumed.

The zero shift is coherent and must be retained. Its condition forces

$$
\bigl||c_i-c_j|-|c_{i'}-c_j|\bigr|\lesssim w.
$$

Because the center spacing is much larger than the slat width, each track has only boundedly many such partners, including itself and possible reflected partners across the pin track. Summing their contribution with the center-mass estimate gives exactly

$$
m r_0\rho^{\alpha-1}.
$$

The cutoff

$$
\rho=(m r_0)^{1/(1-\alpha)}
$$

makes this quantity one. Its removed mass has order at most

$$
(m r_0)^{\alpha/(1-\alpha)}
\asymp\delta^{2\alpha\beta/(1-\alpha)}.
$$

For the stated range below one third, the cutoff lies strictly between the center spacing and the transverse potential scale. The previously proved lower bound for arbitrary positive selections has the same order, with constants allowed to depend on the asserted norm bound. The new argument therefore closes the earlier sufficient/necessary deletion gap for this finite model. The gain comes from pin-slat averaging; a uniform pinwise norm bound is not proved.
