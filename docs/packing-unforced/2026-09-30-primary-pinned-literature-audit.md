# Primary-source audit of possible improvements to the packing cutoff

Date: 2026-09-30. Scope: ordinary Euclidean pinned distances in the plane. This is a literature comparison, not a proof of optimality of the manuscript's sufficient condition.

Write

$$
d=\dim_H E,\qquad D=\dim_P E.
$$

The comparison curve is the manuscript's current condition

$$
D<B_{\rm H}(d),\qquad 1<d\le\frac54,
$$

whose upper branch is

$$
B_{\rm H}(d)=\frac1{3-2d},\qquad
\frac{2+\sqrt6}{4}<d\le\frac54.
$$

**Result of this audit:** none of the primary results checked below gives a strictly larger dimension-only sufficient region for positive pinned distance length. No checked theorem supplies the boundary case where packing dimension equals this curve, or the unrestricted endpoint with Hausdorff dimension five quarters and packing dimension two. This is a conclusion about these results, not a claim that the literature has been exhaustively searched or that either endpoint is false.

## 1. Liu's regular-pin theorem and the measure actually estimated

[Bochen Liu, arXiv:2603.15328v3, Theorem 1.1](https://arxiv.org/html/2603.15328v3) states that Borel planar sets satisfy

$$
\dim_H E>1,\qquad
\dim_H E+\dim_H F>2,\qquad
\dim_H F=\dim_P F
\quad\Longrightarrow\quad
\exists y\in F:\ |\Delta_y(E)|>0.
$$

The pin dimension can be at most one. Propositions 3.2 and 4.1 use separated probabilities with

$$
I_s(\mu)<\infty,\quad s>1,\qquad
\nu(B(x,r))\lesssim r^t,\quad t>2-s,\qquad
\overline{\dim}_B\operatorname{supp}\nu<t+\delta^2,
$$

for sufficiently small positive delta. They estimate a pin-dependent microlocal modification:

$$
\int\|d^y_*\mu_{\mathrm{good},y}-d^y_*\mu\|_{L^1}\,d\nu(y)<\frac1{100},
\qquad
\int\|d^y_*\mu_{\mathrm{good},y}\|_{L^2}^2\,d\nu(y)<\infty.
$$

The good object is built from signed Fourier-localized packets; it is not asserted to be a positive source restriction. These statements do not say that the original pinned law belongs to joint quadratic integrability, or that a single positive source restriction has that property. Consequently, source-only raw-density obstructions do not contradict this theorem. The strict dimension inequalities and arbitrarily small power losses supply no endpoint conclusion by themselves.

## 2. A genuine additional sufficient hypothesis, with no new dimension-only bound

As an immediate consequence of the preceding theorem, a Borel planar set has a positive-length self-pinned distance set if

$$
\dim_H E=d>1,
\qquad
\exists\text{ Borel }F\subset E:
\dim_H F=\dim_P F=t>2-d.
\tag{1}
$$

The proof is simply to apply the theorem with source set equal to the whole set and pin set equal to this subset. Condition (1) does not bound the packing dimension of the whole set. It can therefore establish positivity for particular sets outside the manuscript's curve, including sets with packing dimension two.

For clarity, this does **not** show that all sets with a prescribed pair of Hausdorff and packing dimensions have such a subset. No such extraction theorem is established here. In fact, an unrestricted extraction of this strength for every Borel set of Hausdorff dimension greater than one would, together with Liu's theorem, settle the whole planar pinned conjecture. It cannot be silently supplied by Frostman's lemma.

An especially simple application is any set of Hausdorff dimension greater than one containing a line segment: the segment itself is a regular pin set of dimension one. This illustrates why a theorem about additional geometric subsets need not appear as a larger cutoff depending only on the two dimensions.

## 3. Csörnyei–Stull: radial dimension, and an explicit discrete selection hypothesis

[Csörnyei–Stull, arXiv:2508.18228, Theorem 1.3](https://arxiv.org/html/2508.18228) concerns the angular map

$$
\pi_x(y)=\frac{y-x}{|y-x|}.
$$

For Borel sets with positive-dimensional pin set not contained in a line, its conclusion is

$$
\sup_{x\in X}\dim_H\pi_x(Y\setminus\{x\})
\ge\min\left\{\frac{\dim_H X+\dim_H Y}{2},\dim_H Y,1\right\}.
$$

For a pin set contained in a line, replace the source dimensions by those of its complement in that line. The output is a supremum of angular Hausdorff dimensions, not positive distance length.

Remark 5.2 explicitly identifies a train-track obstruction to an unconditional discrete analogue of a needed intermediate theorem. Theorem 5.3 instead assumes a positive-mass pair set whose selected source marginal obeys

$$
\nu\{y\in R:(x,y)\in\mathcal E\}\le\delta^{-\eta}r^\sigma
$$

for every width-r rectangle containing the pin and every scale at least delta. For uniform discrete measures on dimension-s and dimension-t sets, it gives one pin with a discretely regular angular subset of exponent at most

$$
\min\{t,(s+t)/2,1\}-O(\varepsilon).
$$

It does not construct a common persistent selection across scales or prove bounded distance densities. Such a transfer would require an additional argument.

## 4. The tempting larger packing curve only gives full dimension

[Fiedler–Stull, arXiv:2309.11701, Theorem 1](https://arxiv.org/html/2309.11701) assumes an analytic planar set and a parameter strictly below its Hausdorff dimension:

$$
1<s<\dim_H E,\qquad D=\dim_P E.
$$

It produces a full-dimensional set of pins whose complement has Hausdorff dimension at most s. Its full-dimension conclusion applies when

$$
D<1+\frac{3+\sqrt5}{2}(s-1).
$$

Consequently, the same strict inequality with the set dimension in place of s permits choosing a suitable smaller s. However, the conclusion remains

$$
\dim_H\Delta_x(E)=1,
$$

not positive Lebesgue measure. Near Hausdorff dimension one, the slope of this tempting packing curve exceeds two; this is not a stronger positive-length theorem. A one-dimensional set can have zero length.

## 5. Other recent positive-length inputs checked

[Borges–Ou–Pasquariello, arXiv:2607.10574, Theorem 1.1](https://arxiv.org/html/2607.10574) gives a positive-measure pinned k-star threshold in ambient dimension n of

$$
\frac{n^2+nk+k}{2n+1}.
$$

The ordinary planar distance specialization is seven fifths, exceeding five quarters. This theorem does not enlarge the current planar region.

[Borges–Foster–Ou–Palsson, arXiv:2503.15709v2, Theorem 6](https://arxiv.org/html/2503.15709v2) proves a stronger nonempty-interior conclusion for planar pinned tree sets above seven quarters. Again this does not lower the positive-length threshold relevant here.

[On Fourier decay and the distance set problem, arXiv:2604.19486, Theorems 2.1 and 2.4](https://arxiv.org/html/2604.19486) imposes Fourier-dimension or Fourier-spectrum hypotheses on compactly supported measures. Such hypotheses are additional analytic information; the checked statements do not deduce a new packing cutoff from the two set dimensions alone. Their almost-every-pin conclusions must not be imported after discarding their measure hypotheses.

## 6. What the comparison permits us to say

There are three distinct levels of conclusion here: full Hausdorff dimension of a distance set; existence of a positive-length pinned set after microlocal modification; and quadratic integrability of an original prescribed joint pinned law. None can be replaced by the next without a proof.

The valid positive input most directly extending the manuscript's scope is (1), involving a regular subset of pins. The radial-projection result offers useful incidence information conditional on a selected pair estimate, but does not itself provide the missing distance-collision estimate. No checked primary theorem proves a larger universal packing threshold or closes the manuscript's boundary cases.
