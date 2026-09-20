# A Hausdorff–packing criterion for self-pinned distance sets

A Lean 4 formalization project for Theorem 1.1 of the manuscript *Self-pinned distance sets: a
Hausdorff–packing dimension criterion* (19 September 2026).

For a Borel set $E \subseteq \mathbb{R}^2$ write $\Delta_y(E) = \{|x-y| : x \in E\}$, put

$$d_0 = \frac{9+\sqrt{33}}{12}, \qquad d_1 = \frac{5+\sqrt{97}}{12},$$

and define, for $1 < d \le 5/4$,

$$B(d) = \begin{cases} 2d-1, & 1 < d \le d_0,\\ 3d^2 - \tfrac52 d, & d_0 < d \le d_1,\\
\dfrac{(2d-1)^2 + \sqrt{(2d-1)^4+8d}}{4}, & d_1 < d \le 5/4.\end{cases}$$

**Theorem 1.1.** If $E \subseteq \mathbb{R}^2$ is Borel, $d = \dim_H E \in (1, 5/4]$ and
$\dim_P E < B(d)$, then $|\Delta_y(E)| > 0$ for some $y \in E$.

The pin lies in $E$ itself, no compactness or regularity is assumed, and the packing inequality
is strict, including at the two transition points.

## Status

| stage | state |
|---|---|
| statement (`Challenge.lean`) | type-checks; fully elaborated type identical to `Solution.lean` |
| branch combination (Section 4) | **proved**, no holes |
| curve algebra (transition points, monotone branches) | **proved**, no holes |
| dimensions: `dimH ≤ packingDim`, monotonicity, bounded case | **proved**, no holes |
| profile: edge costs, potential, telescoped edge bound | **proved**, no holes |
| profile: greedy descent, insertion, perturbation, zero-cost edges | **proved**, no holes |
| profile: Lemma 3.2 (chain to the origin), Lemma 3.3 (endpoint estimate) | **proved**, no holes |
| dyadic cubes: partition, nesting, diameter, measurability | **proved**, no holes |
| energy: Frostman measures have no atoms and finite `a`-energy for `a < s` | **proved**, no holes |
| restrictions: normalized restrictions stay Frostman, with constant `C / σ Q` | **proved**, no holes |
| selection: bounded piece of positive mass, compact subset, separated compact pair | **proved**, no holes |
| truncated kernel and energy at scales `a ≤ b`, bounded by `b / a` | **proved**, no holes |
| `branch_original` (Proposition 2.5) | **not proved** — analytic input, `sorry` |
| `branch_finiteProfile` (Theorem 3.1) | **not proved** — analytic input, `sorry` |
| comparator | statement stage passes locally; axiom stage reports `sorryAx` |

The axiom report of the target theorem is currently

```text
'FalconerPacking.exists_pin_volume_pinnedDistances_pos' depends on axioms:
  [propext, sorryAx, Classical.choice, Quot.sound]
```

The comparator job runs the real `leanprover/comparator` in its `landrun` sandbox. It builds and
exports the challenge, builds the solution, and then stops at

```text
uncaught exception: Illegal axiom detected: 'sorryAx'
```

so the pipeline itself is in working order and the only obstruction is the unproved branches.

`sorryAx` disappears exactly when the two analytic branches are proved. Section 7 of the
manuscript lists the sixteen modules that needs: profile optimization, dyadic conditional
measures, truncated energies, tube deletion, packet localization, the inflation step, the pinned
identity, shell bounds, the joint limit, and the Borel reduction — together with Orponen's
radial-projection theorem, which is not in Mathlib. This repository is **not** ready for
registration; a registry submission asserts a complete machine-checked proof.

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
| `FalconerPacking/Restriction.lean` | module 4: normalized restrictions and their Frostman bounds |
| `FalconerPacking/Extraction.lean` | module 15: the selection and separation steps of the reduction |
| `FalconerPacking/Branches.lean` | the two analytic branches, as unproved interfaces |
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
