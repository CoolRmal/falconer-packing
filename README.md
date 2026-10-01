# A Hausdorff–packing criterion for self-pinned distance sets

A complete Lean 4 formalization of Theorem 1.1 in the
[theorem and proof PDF](docs/falconer-human/falconer-packing-theorem.pdf).
The [independent comparator and clean build passed](https://github.com/CoolRmal/falconer-packing/actions/runs/36824796497),
using only `propext`, `Classical.choice`, and `Quot.sound`.

## The theorem

Let E be a Borel subset of the Euclidean plane, and write

$$
d=\dim_H E,\qquad \Delta_y(E)=\lbrace\lVert x-y\rVert:x\in E\rbrace.
$$

If

$$
1\lt d\le\frac54,\qquad \dim_P E\lt B_{\mathrm H}(d),
$$

then some point y in E has a pinned distance set of positive Lebesgue measure:

$$
\exists y\in E:\quad |\Delta_y(E)|>0.
$$

The packing inequality is strict. No compactness or additional regularity is assumed.
The cutoff is

$$
B_{\mathrm H}(d)=\begin{cases}
2d-1, & 1\lt d\le d_\alpha, \\
1+r_2(d-1), & d_\alpha\lt d\le d_c, \\
\dfrac{1}{3-2d}, & d_c\lt d\le\dfrac54.
\end{cases}
$$

$$
d_\alpha=\frac{7-\sqrt7}{4}\approx1.088562172,
\qquad d_c=\frac{2+\sqrt6}{4}\approx1.112372436,
$$

$$
r_2(a)=\frac{6a}{8a^2-a+2+\sqrt{64a^4+32a^3-63a^2-28a+4}}.
$$

For example, the theorem applies when the Hausdorff dimension is 1.15 and the
packing dimension is 1.40: the cutoff is 10/7. The weakest possible dimensional
condition remains unknown.

![The Hausdorff–packing cutoff compared with earlier bounds.](docs/figures/packing-unforced.svg)

## Formal proof and verification

- [Main theorem](FalconerPacking/HausdorffPackingTheorem.lean):
  `FalconerPacking.exists_pin_volume_pinnedDistances_pos`.
- [Statement definitions](FalconerPacking/Statement.lean) and
  [solution entry point](Solution.lean).
- [Independent specification](Challenge.lean) and [comparator configuration](comparator.json).

The comparator verified [proof commit 34c7c95](https://github.com/CoolRmal/falconer-packing/commit/34c7c95d82dc85bb2c166f64c2a36700b1bb0ca4)
on a fresh Linux runner. It compared the theorem and its recursive definition dependencies,
checked the permitted axioms, and replayed the exported proof in Lean's kernel.
The solution has no proof placeholders or additional analytic hypotheses.
The specification's theorem hole is not imported by the solution.

Hausdorff dimension is Mathlib's `dimH`. Packing dimension uses the standard
bounded countable-cover characterization in terms of upper box dimension.

## Build

Pinned to Lean 4.32.0 and Mathlib revision `81a5d257`.

```bash
lake exe cache get
lake build FalconerPacking Challenge Solution
```

## Further reading

The [short guide](docs/falconer-human/README.md) accompanies the focused proof PDF.
The [research archive](docs/packing-unforced/README.md) and
[earlier refinements](docs/packing-refinement/README.md) preserve the broader investigations;
not every result in those notes is formalized.
