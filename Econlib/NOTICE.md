# Vendored Econlib fixed-point proof

The six Lean modules under `Econlib/Math/{Combinatorics,Topology}` are adapted from
[Daniel Lyng's Econlib](https://github.com/danlyng/Econlib), licensed under Apache-2.0; see
[`LICENSE`](LICENSE). The upstream file copyright and author headers are retained.

These copies are adapted to this repository's Lean/Mathlib v4.34.1 from Econlib's v4.29.0
source. Compatibility edits are confined to API changes in `FreudenthalTriangulation.lean`,
`CubicalSperner.lean`, and `FanGlicksberg.lean`. The mathematical statements and proof structure
remain those of the upstream modules. The originals are available at
https://github.com/danlyng/Econlib/tree/main/Econlib/Math.
