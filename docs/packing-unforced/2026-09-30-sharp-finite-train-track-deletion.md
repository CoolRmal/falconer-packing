# Sharp deletion order for the finite train-track family

30 September 2026. Natural-language proof for independent audit. This is an exact estimate for the deterministic finite geometry in `2026-09-30-positive-train-track-selection.md`. It makes no claim for arbitrary sets of the same Hausdorff and packing dimensions.

## 1. Statement

Use the finite family from that note, with

$$
\alpha=u-1<\frac13,\qquad \beta=\frac{s-1}{2},\qquad
m=N_T^{-1}\asymp\delta^\beta,
$$

$$
a=\delta^{\beta/\alpha},\qquad w=\delta^{1/2},\qquad
h=\delta^{s/2},\qquad r_0=h/w=\delta^\beta.
$$

The original parameter assumptions imply a much larger than w. Track centers c_i are 3a-separated and their equal-mass counting measure obeys

$$
\sum_{c_i\in J}m\le C(|J|^\alpha+a^\alpha). \tag{1}
$$

All source tracks have the same vertical slat centers kh, in a fixed bounded interval, and the pins are the vertical translate of the whole source by three. There are N_S comparable to h^{-1} slats. Slat horizontal width is comparable to w; its microscopic cells have diameter O(delta), spacing comparable to delta, and equal masses. Internal cell probabilities may be arbitrary: only their support and mass are used below. Source–pin vertical differences stay in a fixed compact subinterval of (0,infinity).

Let epsilon/delta lie between two fixed positive constants, and let phi_epsilon be the fixed smooth nonnegative probability mollifier from the previous note.

**Theorem.** For every cutoff rho satisfying

$$
Ca\le\rho\le r_0,
$$

delete, at each pin in pin track j, every source track i with

$$|c_i-c_j|<\rho.$$

This is a measurable positive source–pin restriction. Write eta_y for the retained source and f_y=phi_epsilon*(d_y)_*eta_y. Its deleted mass is at most C rho^alpha, and

$$
\boxed{\quad
\int\|f_y\|_2^2\,d\nu_\delta(y)
\le C\bigl(1+m r_0\rho^{\alpha-1}\bigr).
\quad} \tag{2}
$$

The constant is independent of delta and rho. Consequently choose

$$
\rho_{\mathrm{opt}}=(m r_0)^{1/(1-\alpha)}
\asymp r_0^{2/(1-\alpha)}.
\tag{3}
$$

For alpha<1/3 this satisfies a much smaller than rho_opt much smaller than r_0, for sufficiently small delta. The retained joint squared second norm is uniformly bounded, while the deleted mass is at most

$$
C(mr_0)^{\alpha/(1-\alpha)}
\asymp C\delta^{2\alpha\beta/(1-\alpha)}.
\tag{4}
$$

This matches, up to constants depending on the norm bound, the necessary deletion order for arbitrary positive selections proved in Section 1 of `2026-09-30-persistent-selection-and-half-potential.md`. The improvement over the half-potential estimate comes from averaging the deterministic vertical pin slats, not from independent or random vertical shifts.

## 2. Uniform slat envelopes

Fix a pin track j and put

$$r_i=|c_i-c_j|.$$

Every pin in its vertical slat ell has coordinates within O(w) horizontally and O(delta) vertically of (c_j,3+ell h). For a retained track, r_i at least rho is much larger than w. Its source slat k has radial center

$$
t_{i,k,\ell}=\sqrt{r_i^2+(3+(\ell-k)h)^2}. \tag{5}
$$

The same estimate holds if the harmless fixed vertical translation is written as a different positive constant.

Let f_{i,y} denote the density from source track i. The cell count in the previous note gives the pointwise majorant

$$
f_{i,y}(t)\le
C\frac{m h}{r_i w}
\sum_k
\mathbf 1_{\{|t-t_{i,k,\ell}|\le C r_iw\}}.
\tag{6}
$$

This bound holds for every pin y in pin track j, slat ell, regardless of its microscopic horizontal and vertical position. Indeed, variation in either source or pin horizontal coordinate changes the central distance by O(r_i w+w^2)=O(r_i w). Microscopic vertical errors and mollification add O(delta), also absorbed because r_i much larger than w and delta=w^2. At any prescribed distance, the horizontal derivative has magnitude comparable to r_i. Only O(1/r_i) source cells in a slat can contribute; each has mass comparable to m h delta/w, and the mollifier is bounded by C/delta. This gives the amplitude in (6).

For offsets at least r_0, the previously proved slat count implies

$$f_{i,y}(t)\le C m(1+r_0/r_i)\le C'm.$$

Thus the sum of all such far-track densities is uniformly bounded pointwise and has mass at most one. It contributes only O(1) to the full squared norm, including its cross term with all remaining tracks. It remains to estimate the tracks with

$$\rho\le r_i\le r_0.$$

## 3. The deterministic cross-track estimate

Fix two near tracks i and i', reorder them so that

$$r=r_i\le R=r_{i'}\le r_0,\qquad \Delta=R^2-r^2.$$

Average over the vertical slats of the pin track j, retaining arbitrary microscopic pin positions within each slat. We claim

$$
\frac1m\int_{y\text{ in pin track }j}
\int f_{i,y}(t)f_{i',y}(t)\,dt\,d\nu_\delta(y)
\le C m^2\left[
1+\frac{r_0}{R}\mathbf1_{\{\Delta\le C Rw\}}
\right].
\tag{7}
$$

Here and below C in an indicator may be enlarged independently of multiplicative constants.

Multiplying (6) for the two tracks and integrating t shows that the left side of (7) is bounded by

$$
C\frac{m^2h^2}{R w}\,
\frac1{N_S}\sum_\ell\sum_{k,k'}
\mathbf1_{\{|t_{i,k,\ell}-t_{i',k',\ell}|\le C Rw\}}.
\tag{8}
$$

The factor r w from the intersection length of the two radial intervals has canceled the smaller radius r in the amplitudes. Pin slats have equal masses m/N_S, so taking a pointwise supremum within each slat justifies (8) for arbitrary microscopic pin probabilities.

Put q=k'-k and V=3+(ell-k)h. Since both V and V-qh lie in a fixed positive compact interval, the distance-collision condition in (8) implies

$$
|\Delta-qh(2V-qh)|\le C Rw. \tag{9}
$$

### The zero shift

When q=0, (9) can hold only if Delta at most C Rw. There are at most N_S pairs k=k' for each pin slat. Their contribution to (8) is at most

$$
C\frac{m^2h^2}{Rw}\,N_S\,
\mathbf1_{\{\Delta\le C Rw\}}
\le C m^2\frac{r_0}{R}\,
\mathbf1_{\{\Delta\le C Rw\}}.
\tag{10}
$$

These are the coherent equal-radius resonances, and are not treated as random.

### Nonzero shifts

Fix q not zero and k. As ell changes by one, the left expression inside the absolute value in (9) changes by exactly 2|q|h^2. Consequently the number of pin slats satisfying (9) is at most

$$C\left(1+\frac{Rw}{|q|h^2}\right).$$

An admissible q necessarily satisfies

$$|q|h\le C(\Delta+Rw)\le C(R^2+Rw). \tag{11}$$

Because R at most r_0=h/w and r_0 tends to zero,

$$
\frac{|q|h^2}{Rw}\le C(Rr_0+h)\le C.
$$

Thus the discrete counting error one is absorbed, and the fraction of pin slats satisfying (9), for each fixed k,q, is at most

$$C\frac{Rw}{|q|h}. \tag{12}$$

Summing over k and using N_S comparable to h^{-1}, the contribution of this shift q to (8) is at most C m^2/|q|.

The possible nonzero shifts have a uniformly bounded harmonic sum. To see this, fix a sufficiently large constant C_1. If Delta>C_1 Rw, the positivity and boundedness of V and V-qh in (9) force q>0 and

$$c\Delta\le qh\le C\Delta.$$

Hence the relevant positive integers lie in a multiplicative window of fixed ratio, and their reciprocals sum to O(1). This includes a window meeting q=1. If Delta at most C_1 Rw, (11) and Rw at most r_0w=h show that |q| is bounded by a fixed constant. Again the reciprocal sum is O(1). This proves that all nonzero shifts together contribute at most C m^2. With (10), the claim (7) follows.

Notice why averaging the actual discrete pin slats is enough: (12) explicitly absorbs the lattice error. No equidistribution of qh or quadratic phases is assumed.

## 4. Summing coherent resonances and proving the theorem

Since Delta=(R-r)(R+r), its exceptional condition in (7) implies

$$|r_i-r_{i'}|\le Cw.$$

For fixed pin track j and fixed source track i, there are only O(1) source tracks i' with this property. On the same side of c_j, such centers lie in an interval of length O(w) around c_i; on the opposite side they lie in an interval of length O(w) around 2c_j-c_i. The centers are 3a-separated and w/a tends to zero. This proves the claimed O(1) bound, including i'=i and exact reflected pairs. On these exceptional pairs R is comparable to r_i, because r_i at least rho is much larger than w.

Sum (7) over near tracks. The baseline C m^2 sums to at most C, since N_T m=1. The exceptional terms sum to at most

$$C m^2 r_0\sum_{r_i\ge\rho}\frac1{r_i}.$$

The center count (1), dyadic annuli and alpha<1 give

$$
\sum_{r_i\ge\rho}\frac m{r_i}
\le C_\alpha\rho^{\alpha-1},\qquad \rho\ge Ca.
\tag{13}
$$

Thus the conditional averaged squared norm in pin track j is bounded by C(1+mr_0 rho^{alpha-1}), uniformly in j. Average over j with pin masses m and add the already bounded far-track contribution. This proves (2).

The removed mass is bounded by (1) applied to an interval of radius rho centered at c_j. It is at most C(rho^alpha+a^alpha), hence at most C rho^alpha. For the choice (3), the extra term in (2) is exactly one. Moreover m comparable to a^alpha comparable to r_0 gives

$$
\frac{\rho_{\rm opt}}a
\asymp a^{(3\alpha-1)/(1-\alpha)}\longrightarrow\infty,
\qquad
\frac{\rho_{\rm opt}}{r_0}
\asymp r_0^{(1+\alpha)/(1-\alpha)}\longrightarrow0.
$$

The asserted cutoff range and deletion estimate (4) follow.

## 5. Matching lower bound and scope

For clarity, the necessary bound being matched applies to an arbitrary positive kernel eta_y at most mu_delta. If its averaged squared second norm is bounded by a fixed constant C_0, and e_delta is its averaged deleted source mass, the earlier support-length and weighted Cauchy--Schwarz argument gives

$$
e_\delta\ge c_{C_0}(mr_0)^{\alpha/(1-\alpha)}.
$$

The upper estimate here supplies a whole-track selection with a uniform norm bound and loss at most a constant times that expression. Therefore the power 2 alpha beta/(1-alpha) is the optimal deletion order for bounded averaged squared second norm in this finite model (with constants allowed to depend on the norm bound and the fixed geometry).

This is stronger than the previous pinwise half-potential upper bound, whose sufficient loss was delta^{alpha beta/(1-2alpha)}. The improvement relies on the common arithmetic vertical slats and averaging all pin slats. It does not supply a uniform pinwise second-norm bound. Nor does it build a persistent selection across scales for a fixed general fractal measure. In particular it does not imply a weaker dimension-only condition for positive-length distances.
