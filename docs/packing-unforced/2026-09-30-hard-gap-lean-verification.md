# Lean verification of the hard-gap algebra

30 September 2026.

The source module `FalconerPacking/HardGapAlgebra.lean` compiled without errors or warnings. The command `lake build FalconerPacking.HardGapAlgebra` completed successfully. The root library imports this module, so the ordinary library build includes it.

Separate axiom checks for each of the following seven declarations returned exactly `[propext, Classical.choice, Quot.sound]`; the source scans reported no suspicious patterns:

- `FalconerPacking.twoGapCost_bound`
- `FalconerPacking.singleGapCost_bound`
- `FalconerPacking.singleGapCost_lt_iff`
- `FalconerPacking.twoGapCost_sub_singleGapCost`
- `FalconerPacking.twoGapCost_lt_iff`
- `FalconerPacking.twoGapCost_example_margin`
- `FalconerPacking.singleGapCost_example_margin`

The first two theorems derive the claimed cost bounds from the explicitly displayed endpoint, gap, and tail inequalities. They include proofs of the nonnegative weights. The other five check the exact cost and threshold algebra used in the manuscript.

The [statement-fidelity audit](2026-09-30-hard-gap-lean-fidelity-audit.md) independently compares these formal statements with the manuscript. This verification does not certify the geometric derivation of the gap constraints, the hard-component identity, the analytic transfer, or the unconditional distance theorem. The existing comparator target is unchanged, and its conditional status remains documented in the repository README.
