# A Hausdorff–packing criterion for self-pinned distance sets

A Lean 4 formalization project for Theorem 1.1 of the manuscript *Self-pinned distance sets: a
Hausdorff–packing dimension criterion* (19 September 2026).

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

`RadialProjection.lean` begins module 7 with the part that is elementary: the separation
estimate `|det (y - x, z - x)| ≤ ‖y - x‖ ‖z - x‖ · |Θ_x y - Θ_x z|`, and its consequence that
pins with close radial projections lie in a thin tube. That reduction also shows why the
remaining step is genuinely hard: the reciprocal-determinant integral needs
`μ(tube of width w) ≲ w^(1+ε)`, one power beyond what a planar Frostman exponent `s ≤ 2` gives,
and closing that gap is Orponen's theorem, whose proof runs through Bourgain's discretized
projection theorem. It is therefore recorded as `OrponenRadialProjection`, unproved.

`Tubes.lean` proves the soft half of the heavy-tube count that both branches need. Tube
directions are parametrized by slope rather than by a point of the circle, so no arclength
measure and no inverse trigonometry appear; the two slope charts `(1, a)` and `(a, 1)`
degenerate on different directions and together cover the circle. The outcome is
`Σ_k μ(slab)² ≲ δ · I₁(μ)` on average over the direction, hence finite for every Frostman
exponent above one. This is a *second-moment* bound, so it counts slabs of mass `≥ lam` only to
precision `lam⁻²`; Orponen's theorem needs heavy slabs to be rarer than any second-moment
argument can show, which is the step that requires the discretized projection machinery.

| stage | state |
|---|---|
| challenge statement | type-checks; elaborated type identical to `Solution.lean` |
| branch combination (Section 4) — **the checked theorem** | **proved**, no holes |
| curve algebra (transition points, monotone branches) | **proved**, no holes |
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
| radial projections (module 7): cross-product geometry, the separation estimate, and tube containment | **proved**, no holes |
| tubes (module 7): slab partitions, the two-chart directional estimate, and the averaged tube-square bound against the Riesz `1`-energy | **proved**, no holes |
| caps (module 7): radial caps pull back into tubes, and tubes are covered by an explicit interval of slabs | **proved**, no holes |
| Orponen's radial-projection theorem (module 7) | **open** — stated as `OrponenRadialProjection`, not proved |
| projection energy (module 8): the `s`-Riesz kernel of a slope chart is integrable, with the expected bound | **proved**, no holes |
| projection-energy comparison (module 8): Marstrand's projection theorem in energy form, `∫ I_s(π_a μ) da ≲ I_s(μ)` for `0 < s < 1` | **proved**, no holes |
| Marstrand's projection theorem in energy form (module 8): a.e. projection of a finite-`s`-energy measure has finite `s`-energy | **proved**, no holes |
| unconditional Theorem 1.1 (`Target`) | **open** — the two analytic branches |

## Layout

| path | contents |
|---|---|
| `Challenge.lean` | the statement, self-contained, with the theorem hole |
| `Solution.lean` | the target theorem, in the same form, proved from the library |
| `FalconerPacking/Statement.lean` | the same definitions, for the modular development |
| `FalconerPacking/Algebra.lean` | the curve algebra of Section 4 |
| `FalconerPacking/Dimensions.lean` | module 1: the covering definitions against Mathlib's `dimH` |
| `FalconerPacking/Profile.lean` | module 3: finite profiles, edge costs, Lemmas 3.2 and 3.3 |
| `FalconerPacking/Dyadic.lean` | module 4: the dyadic cube hierarchy of the plane |
| `FalconerPacking/Energy.lean` | module 6: Frostman measures, Riesz kernels and finite energy |
| `FalconerPacking/RadialProjection.lean` | module 7: the scalar cross product, the radial separation estimate, tubes, and the statement of Orponen's theorem |
| `FalconerPacking/Tubes.lean` | module 7: slab partitions, the two slope charts, the directional estimate, and the averaged tube-square bound |
| `FalconerPacking/Caps.lean` | module 7: radial caps pull back into pin tubes, and pin tubes are covered by an explicit interval of slabs |
| `FalconerPacking/Projection.lean` | module 8: the projection-energy estimate on a slope chart |
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
