# A Hausdorff–packing criterion for self-pinned distance sets

A complete Lean 4 formalization of Theorem 1.1 in the
[theorem and proof PDF](docs/falconer-human/falconer-packing-theorem.pdf).
The proof previously [passed the independent comparator and a clean build](https://github.com/CoolRmal/falconer-packing/actions/runs/36824796497)
on Lean 4.32.0, using only `propext`, `Classical.choice`, and `Quot.sound`.

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

![The current Hausdorff–packing bound.](docs/figures/packing-unforced.svg)

## Formal proof and verification

- [Main theorem](FalconerPacking/HausdorffPackingTheorem.lean):
  `FalconerPacking.exists_pin_volume_pinnedDistances_pos`.
- [Statement definitions](FalconerPacking/Statement.lean) and
  [solution entry point](Solution.lean).
- [Independent specification](Challenge.lean) and [comparator configuration](comparator.json).

The comparator verified [proof commit 34c7c95](https://github.com/CoolRmal/falconer-packing/commit/34c7c95d82dc85bb2c166f64c2a36700b1bb0ca4)
on a fresh Linux runner. It compared the theorem and its recursive definition dependencies,
checked the permitted axioms, and replayed the exported proof in Lean's kernel.
The compared theorem and its imported proof have no proof placeholders or additional analytic hypotheses.
The specification's theorem hole is not imported by the solution.

The migrated Lean `4.35.0-rc2` development passes a complete local build and
local Comparator comparison, with the exported proof accepted by Lean's
kernel, NanoDa, and con-ron. This macOS comparison ran without the Linux
sandbox. The required full hosted Palomar report remains a separate check
of the exact submission commit.

Hausdorff dimension is Mathlib's `dimH`. Packing dimension uses the standard
bounded countable-cover characterization in terms of upper box dimension:
`upperBoxDim` is the infimum of nonnegative exponents admitting a uniform
polynomial covering bound at dyadic radii, and `packingDim` is the infimum,
over bounded countable covers, of the supremum of these upper box dimensions.
The ambient metric is the Euclidean metric, `MeasurableSet E` means Borel
measurability here, and `volume` on the real line is Lebesgue measure.
The countable-cover characterization is the chosen definition of packing
dimension in this formalization. The repository does not formally identify it
with a separately defined packing-measure dimension; that interpretation is
part of the statement review.

The submitted claim is the single theorem named above, with the strict
`hausdorffPackingBound` cutoff. The older `bound`, `Target`, and
`exists_pin_of_branches` declarations describe a different, historical
conditional result and are outside this submission.

## Palomar submission

[Registration metadata](formalization.yaml) records the source, statement,
authors, review status, and comparator configuration. The [Palomar submission
workflow](.github/workflows/build.yml) runs source hygiene and Lean builds on
pushes and pull requests. Run it manually with the appropriate author or
maintainer declaration to invoke the full pinned Palomar checker, including
definition comparison, Lean's kernel, NanoDa, and con-ron. A passing ordinary
build is not a passing Palomar mechanical report.
Registration requires successful mechanical verification, editorial review
without a blocking issue, and the submitter's decision to register.

The five literature entries in the metadata are background references for the
proof's analytic and scale-selection arguments. Their needed results are proved
within the imported Lean development; they are not additional analytic axioms.

The source headers and Git history attribute the work to **Yongxi Lin**.
This submission preparation used Codex assistance. A complete historical
record of AI models and their roles, and an independent human review of the
formal statement and custom definitions, are not documented in the existing
repository. Automated compilation and comparison establish different checks
from human review; submitters should confirm the metadata against the actual
contribution and review history before making registration attestations.

## Build

The submission is pinned to Lean `4.35.0-rc2` and Mathlib revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The historical Linux verification
linked above predates this toolchain migration; the current local checks do
not replace Palomar's full hosted workflow.

```bash
lake exe cache get
lake build FalconerPacking Challenge Solution
```

Before submitting, use the **Run workflow** action on the exact submission
branch and check that the full Palomar report says `status: pass`. Record that
commit's full 40-character SHA. The repository uses the conventional root
layout: select `comparator.json` and leave the project and metadata paths at
their defaults. Follow [Palomar's submission instructions](https://palomar-registry.org/how-to-submit)
for intake and the separate decision to publish the review and register.

## Further reading

The [short guide](docs/falconer-human/README.md) accompanies the focused proof PDF.
The [research archive](docs/packing-unforced/README.md) and
[earlier refinements](docs/packing-refinement/README.md) preserve the broader investigations;
not every result in those notes is formalized.
