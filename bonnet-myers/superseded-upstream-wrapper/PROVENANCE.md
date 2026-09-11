# Provenance

The proof-bearing geometric comparison implementation is used as a pinned
upstream dependency:

- Source: https://github.com/qinz1yang/differential-geometry
- Commit: `1b535dd102b94cc42b107cca27059687888f08b3`
- Release line: v0.1.2
- License: Apache-2.0, as declared by the upstream repository
- Relevant modules:
  - `DifferentialGeometry/Geometry/Comparison/BonnetMyers/RicciBound.lean`
  - `DifferentialGeometry/Geometry/Comparison/BonnetMyers/LengthBound.lean`
  - `DifferentialGeometry/Geometry/Comparison/BonnetMyers/Headlines.lean`
  - `DifferentialGeometry/Geometry/Comparison/HopfRinow.lean`
  - `DifferentialGeometry/Geometry/Metric/Completeness.lean`

Those modules contain the actual Ricci tensor, geodesic, variation, and
compactness arguments.  The local files do not copy or alter those sources;
they define aliases and wrapper theorems under the `BonnetMyers` namespace.
The wrapper theorem is therefore an integration surface, not a claim of a
new proof or a new mathematical result.  The dependency is pinned by the
immutable full commit in `lakefile.toml` and `lake-manifest.json`.
