# PoincareCurvature

`PoincareCurvature` is the main Lean package supporting the repository's
Poincaré/Ricci-flow program. It contains the proved foundational geometry for
roadmap milestones 1–3 and substantial proof-bearing infrastructure toward the
open Ricci-flow local-existence milestone.

It does **not** currently prove general compact-manifold Ricci-flow local
existence and uniqueness or the Poincaré conjecture.

## Documentation

- [Repository status](../docs/status.md)
- [Curvature package map](docs/curvature-package.md)
- [Point-4 plan](../docs/point4/README.md)
- [Full roadmap](../docs/roadmap.md)

## Public package boundary

The root module [`PoincareCurvature.lean`](PoincareCurvature.lean) exports the
supported curvature, time-dependent geometry, smoothing, selected analytic,
and research-theorem modules. The much larger optional aggregate
[`PoincareCurvature/RicciFlowLocalExistence.lean`](PoincareCurvature/RicciFlowLocalExistence.lean)
collects the developing Point-4 surface; its existence is not evidence that the
general theorem has been proved.

## Build

The project pins Lean 4.33.0 and its Mathlib revision in `lean-toolchain` and
`lakefile.toml`.

```bash
lake build
```

To build the optional Point-4 aggregate:

```bash
lake build PoincareCurvature.RicciFlowLocalExistence
```

To run the authoritative completion audit:

```bash
./scripts/point4_audit.sh
```

A faster source/type check is available during development:

```bash
./scripts/point4_audit.sh --no-build
```

The fast form intentionally skips the build gate and cannot produce a closed
verdict by itself.

## Proof standard

The package does not treat interfaces, `sorry`, added axioms, restricted special
cases, or assumed Banach-chart/closure data as a proof of the general Point-4
theorem. The audit checks the canonical target name, its elaborated type, its
axioms, the forbidden-term scan, and the full build.
