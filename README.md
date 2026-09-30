# A Hausdorff–packing criterion for self-pinned distance sets

A Lean 4 formalization project for Theorem 1.1 of the manuscript *Self-pinned distance sets: a
Hausdorff–packing dimension criterion* (19 September 2026).

**Research update, 30 September 2026.** The [latest proof manuscript](docs/packing-unforced/packing-unforced-proof.pdf)
gives the explicit stronger cutoff

$$
B_{\mathrm H}(d)=
\begin{cases}
2d-1,&1<d\le d_\alpha,\\[6pt]
1+r_2(d-1),&d_\alpha<d\le d_c,\\[6pt]
\dfrac1{3-2d},&d_c<d\le\dfrac54,
\end{cases}
$$

$$
d_\alpha=\frac{7-\sqrt7}{4}\approx1.088562172,
\qquad d_c=\frac{2+\sqrt6}{4}\approx1.112372436.
$$

The middle branch is the explicit radical

$$
r_2(a)=\frac{2-a+8a^2-\sqrt{4-28a-63a^2+32a^3+64a^4}}
{4(1+4a-2a^2)}.
$$

For a Borel planar set, packing dimension strictly below this curve implies a
positive-length pinned distance set for some pin in the set. The
[full statement and proof](docs/packing-unforced/README.md) include the exact joins
and all strict endpoint conditions.

New examples include Hausdorff dimension 1.09 with packing dimension 1.181, and
Hausdorff dimension 1.15 with packing dimension 1.40. At Hausdorff dimension 1.10,
the exact cutoff is 28/23; at dimension 1.15 it is 10/7.

![The explicit gap bound, the preceding adaptive bound, and the originally quoted curve.](docs/figures/packing-unforced.svg)

Matching profiles prove this curve is optimal for the specified combination of
the coherent test and the limiting universal chain-cost test. They are not planar
distance-set counterexamples: the weakest possible dimensional condition for the
distance theorem remains unknown. Internal audits are not external refereeing or
complete Lean verification. The original Lean target and curve below are preserved.

The [new algebra module](FalconerPacking/HardGapAlgebra.lean) now verifies both
weighted certificates and five supporting algebraic statements with only the
three standard axioms. The manuscript also proves that matching profiles recur
in a single Frostman measure and that optimizing the finite starting depth does
not improve this profile criterion. These are limitations of specific methods,
not distance-set counterexamples.

The [earlier forced-midpoint refinements](docs/packing-refinement/README.md) remain
available with their proofs and audits.

The latest natural-language proof also strengthens the conclusion under the same
curve: selected separated source and pin probabilities have a **raw joint
distance density whose pth power is integrable for some exponent greater than
one**. The proof treats
both analytic branches and explicitly handles the pin mass discarded in finite
regularization. This improves integrability without changing the dimension
cutoff. Further formalization is currently set aside at the user's request.

For a Borel set $E \subseteq \mathbb{R}^2$ write $\Delta_y(E) = \{|x-y| : x \in E\}$, put

$$d_0 = \frac{9+\sqrt{33}}{12}, \qquad d_1 = \frac{5+\sqrt{97}}{12},$$

and define, for $1 < d \le 5/4$,

$$
B(d) =
\begin{cases}
2d-1,
  & 1 < d \le d_0, \\[4pt]
3d^2 - \dfrac52 d,
  & d_0 < d \le d_1, \\[8pt]
\dfrac{(2d-1)^2 + \sqrt{(2d-1)^4+8d}}{4},
  & d_1 < d \le \dfrac54.
\end{cases}
$$

![Graph of the piecewise packing-dimension threshold B(d), with its two transition points and
the admissible band between d and B(d).](docs/bound-curve.svg)

**Theorem 1.1.** If $E \subseteq \mathbb{R}^2$ is Borel, $d = \dim_H E \in (1, 5/4]$ and
$\dim_P E < B(d)$, then $|\Delta_y(E)| > 0$ for some $y \in E$.

The pin lies in $E$ itself, no compactness or regularity is assumed, and the packing inequality
is strict, including at the two transition points.

## Status

The **checked theorem is the conditional form of Theorem 1.1** (Section 4 of the manuscript):
the two analytic criteria enter as explicit hypotheses, and the theorem is the branch
combination that derives the curve `B(d)` from them. That combination is fully proved, so the
comparator's axiom report is `[propext, Classical.choice, Quot.sound]`.

Unconditional Theorem 1.1 is recorded in `Challenge.lean` as `Target` and is **not proved**: it
needs the original branch (Proposition 2.5) and the finite-profile branch (Theorem 3.1), whose
formalization requires Orponen's radial-projection theorem, GIOW packet localization, tube
deletion, the inflation step, the pinned identity, the shell bounds and the joint limit —
modules 7 to 14 of the manuscript's ledger, none of which exists in Mathlib. A green comparator
here certifies the conditional theorem, nothing more.

| stage | state |
|---|---|
| challenge statement | type-checks; elaborated type identical to `Solution.lean` |
| branch combination (Section 4) — **the checked theorem** | **proved**, no holes |
| curve algebra (transition points, monotone branches) | **proved**, no holes |
| new hard-gap weighted certificates, threshold algebra, and exact margins | **proved**, seven theorems, standard axioms only |
| dimensions: `dimH ≤ packingDim`, monotonicity, countable stability | **proved**, no holes |
| profile: Lemma 3.2 (chain to the origin), Lemma 3.3 (endpoint estimate) | **proved**, no holes |
| dyadic cubes: partition, nesting, ancestors, diameter, four-cube bound | **proved**, no holes |
| energy: Frostman measures have no atoms and finite `a`-energy for `a < s` | **proved**, no holes |
| restrictions, selection, separation, Hausdorff content | **proved**, no holes |
| **finite Frostman lemma**: allowances hold and total mass dominates the content | **proved**, no holes |
| compact occupied-cube covers and normalized atomic Frostman measures | **proved**, no holes |
| weak compactness, supported subsequence extraction, and dyadic Frostman bounds in the limit | **proved**, no holes |
| compact Frostman lemma: positive content or larger Hausdorff dimension gives an all-radius Frostman probability | **proved**, no holes |
| pinned pushforward: absolute continuity or a displayed density implies positive-length pinned distances | **proved**, no holes |
| localized conditional-energy bounds and full-measure finite conditioning families | **proved**, no holes |
| $$u<2s-1$$ gives powered conditional-energy summability and convergence from a first-norm comparison | **proved**, no holes |
| positive `L¹` density limits, weak identification, affine-map limits, and absolute continuity | **proved**, no holes |
| coherent joint approximation: summable `L¹` densities and affine-map convergence give joint absolute continuity and a positive-length pin | **proved**, no holes |
| affine distance geometry: measurability and the quadratic error bound under positive source–pin separation | **proved**, no holes |
| compact dyadic source centers: measurable selectors with a uniform cube-diameter error | **proved**, no holes |
| unconditional Theorem 1.1 (`Target`) | **open** — the two analytic branches |

## Layout

| path | contents |
|---|---|
| `Challenge.lean` | the statement, self-contained, with the theorem hole |
| `Solution.lean` | the target theorem, in the same form, proved from the library |
| `FalconerPacking/Statement.lean` | the same definitions, for the modular development |
| `FalconerPacking/Algebra.lean` | the curve algebra of Section 4 |
| `FalconerPacking/HardGapAlgebra.lean` | weighted certificates and threshold algebra for the improved curve |
| `FalconerPacking/Dimensions.lean` | module 1: the covering definitions against Mathlib's `dimH` |
| `FalconerPacking/Profile.lean` | module 3: finite profiles, edge costs, Lemmas 3.2 and 3.3 |
| `FalconerPacking/Dyadic.lean` | module 4: the dyadic cube hierarchy of the plane |
| `FalconerPacking/Energy.lean` | module 6: Frostman measures, Riesz kernels and finite energy |
| `FalconerPacking/Restriction.lean` | module 4: normalized restrictions and their Frostman bounds |
| `FalconerPacking/Extraction.lean` | module 15: the selection and separation steps of the reduction |
| `FalconerPacking/Content.lean` | Hausdorff content, towards Frostman's lemma |
| `FalconerPacking/FrostmanWeights.lean` | the finite Frostman normalization on the cube tree |
| `FalconerPacking/WeightMeasure.lean` | normalized atomic measures and their cube and ball bounds |
| `FalconerPacking/OccupiedCubes.lean` | finite occupied covers and support-point selection for compact sets |
| `FalconerPacking/WeakLimit.lean` | compactness, subsequences, and preservation of dyadic ball bounds in the weak limit |
| `FalconerPacking/FrostmanLimit.lean` | conversion from dyadic estimates to a genuine Frostman measure on a compact set |
| `FalconerPacking/PinnedMeasure.lean` | pinned distance pushforwards and the absolute-continuity-to-positive-length implication |
| `FalconerPacking/LocalEnergy.lean` | scale-sensitive bounds and geometric summability for normalized dyadic restrictions |
| `FalconerPacking/PositiveLimit.lean` | `L¹` density convergence, weak limits, and absolute continuity |
| `FalconerPacking/PinnedKernel.lean` | joint pin-distance laws, coherent affine limits, disintegration, and the positive-length fiber conclusion |
| `FalconerPacking/AffineDistance.lean` | measurable affine distance maps and their uniform quadratic approximation error |
| `FalconerPacking/DyadicCenters.lean` | measurable representative maps for occupied compact-source cubes |
| `FalconerPacking/Main.lean` | the branch combination |
| `comparator.json` | permits only `propext`, `Quot.sound`, `Classical.choice` |

`comparator.json` has no `definition_names` escape hatch: the definitions reachable from the
statement — `packingDim`, `upperBoxDim`, `HasUpperBoxBound`, `pinnedDistances`, `bound`, `d0`,
`d1` — are compared recursively, so they cannot be restated or weakened in the solution.

## Definitions used by the statement

`dimH` is Mathlib's Hausdorff dimension. Packing dimension is not in Mathlib at the pinned
revision, so `packingDim` is defined here by the standard bounded countable-cover
characterization, over the covering-based `upperBoxDim`. A comparator that fixes a different
reference definition of packing dimension requires a proved equivalence; substituting
`upperBoxDim E` for `packingDim E` is not admissible, as the two disagree even for compact sets.

## Building

```bash
lake exe cache get
lake build FalconerPacking Challenge Solution
```

Pinned to Lean and Mathlib `v4.32.0` (Mathlib revision `81a5d257`). The `comparator` job of the
[Lean build workflow](.github/workflows/build.yml) builds the challenge and the solution inside
the `landrun` sandbox on a fresh runner and checks the statements and the axiom list.

## References

- T. Orponen, *On the dimension and smoothness of radial projections*, Anal. PDE **12** (2019),
  1273–1294.
- T. Keleti and P. Shmerkin, *New bounds on the dimensions of planar distance sets*, GAFA **29**
  (2019), 1886–1948.
- L. Guth, A. Iosevich, Y. Ou and H. Wang, *On Falconer's distance set problem in the plane*,
  Invent. Math. **219** (2020), 779–830.
- B. Liu, *An L²-identity and pinned distance problem*, GAFA **29** (2019), 283–294.
