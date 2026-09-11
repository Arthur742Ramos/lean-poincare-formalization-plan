# Point 4: Ricci-flow local existence and uniqueness

Point 4 aims to prove short-time existence and uniqueness of Ricci flow for
general initial data on a compact smooth manifold. It is the first open
dependency in the [Poincaré roadmap](../roadmap.md).

This file records the current boundary and next work. The long chronological
development record has moved to
[`../history/point4-development-log.md`](../history/point4-development-log.md).

## Definition of done

The executable authority is
[`curvature/scripts/point4_audit.sh`](../../curvature/scripts/point4_audit.sh).
Point 4 is closed only when a full invocation, without `--no-build`, prints
`VERDICT: POINT 4 CLOSED` and exits successfully.

The audit requires:

1. a library free of `sorry`, `admit`, `sorryAx`, `axiom`, `opaque`,
   `native_decide`, and `decide!` after comments and strings are removed;
2. a successful `lake build`;
3. an unconditional theorem constructing
   `IntrinsicLocalExistenceUniquenessFamily` on a general compact manifold;
4. an axiom set contained in `propext`, `Classical.choice`, and `Quot.sound`;
5. an elaborated theorem type with no empty, subsingleton, rank, preconstructed
   chart, or preconstructed closure-data restriction.

The canonical declaration is named by
[`curvature/scripts/point4_target.txt`](../../curvature/scripts/point4_target.txt),
currently `intrinsicLocalExistenceUniquenessFamily_pointFour`.

## Current verdict

The fast audit run on 2026-09-11 passed the forbidden-term scan but did not find
the canonical target. The build gate was intentionally skipped in that fast
run. Gates 3–5 therefore failed and the verdict remained `POINT 4 OPEN`.

See [Current formalization status](../status.md) for the repository-wide dashboard.

## Proved architecture

The implementation already provides a real conditional route:

```text
Ricci–DeTurck Banach chart and parabolic solution
  + smooth geometric realization
  + reverse encoding of competing candidates
  + sufficiently regular DeTurck gauge flow
  + pullback-metric derivative identity
  ⇒ intrinsic Ricci-flow local existence and uniqueness
```

It also proves restricted theorem families and substantial reusable
infrastructure. These are meaningful intermediate results, but the audit
correctly prevents them from being mistaken for the unrestricted theorem.

## Remaining integration workstreams

The historical plan grouped the missing construction into three workstreams.
Many supporting lemmas inside each workstream have landed; the labels below
refer to the remaining end-to-end obligations, not to an absence of code.

### A. Gauge-pulled metric time derivative

Complete the general nonidentity time-dependent formula

```text
d/dt (Φ_t^* g_t) = Φ_t^* (∂_t g_t + Lie_{X_t} g_t)
```

in the repository's bundled tensor vocabulary. Scalar-to-tensor reductions,
bilinear chain rules, endpoint variants, and several model-coordinate pieces
already exist. What matters for closure is a theorem that supplies the required
derivative package for the actual gauge family used by the general
Ricci–DeTurck solution.

### B. Compact-manifold `C³` gauge flow

For the time-dependent DeTurck vector field, construct a short-time family of
self-diffeomorphisms satisfying

```text
∂_t Φ_t(x) = X_t(Φ_t(x)),    Φ_{t₀} = id,
```

with the spatial and temporal regularity required by gauge transport. The
repository contains extensive model-flow, chart-transfer, compact-cover,
inverse-flow, and special-construction machinery. Closure requires an
unconditional construction specialized to the actual general DeTurck field.

### C. Quasilinear Ricci–DeTurck PDE closure

Construct, for every relevant initial metric:

- the genuine time-dependent geometric Ricci–DeTurck Banach chart;
- local well-posedness for its strictly parabolic quasilinear evolution;
- preservation of the positive-definite metric locus;
- smooth realization of the Banach solution as geometric data;
- reverse encoding of every competing smooth candidate needed for uniqueness;
- identification of the analytic representative with the intrinsic geometric
  Ricci–DeTurck right-hand side.

This is the main Hamilton–DeTurck theorem and the longest remaining analytic
workstream. Existing Hölder, section-space, coordinate, mild-solution, and frozen
operator results reduce the distance to it but do not replace the quasilinear
parabolic theorem.

## Recommended execution order

1. Close the general compact-manifold gauge-flow specialization.
2. Close the pullback-metric derivative formula for that same gauge family.
3. Complete the quasilinear parabolic chart and closure data.
4. Assemble the existing conditional bridge into the canonical theorem.
5. Run the full Point-4 audit and retain its output as completion evidence.

Workstreams A–C can proceed independently where their APIs are already stable.
The order above minimizes uncertainty at final assembly; it is not a claim that
the PDE work must wait entirely for the gauge work.

## Reporting rule

Use theorem-specific language for partial progress. Examples:

- "proved the frozen affine evolution";
- "constructed a gauge flow under hypothesis H";
- "proved the chart-to-intrinsic conditional bridge".

Do not report "Ricci-flow local existence is proved" until the canonical
unconditional theorem exists and the complete audit closes.

## Historical detail

The former working plan and the separate July progress journal are preserved as
historical records:

- [Full Point-4 development log](../history/point4-development-log.md)
- [July 2026 Point-4 progress log](../history/point4-progress-log-2026-07.md)

Those files contain useful theorem names, failed approaches, performance notes,
and intermediate milestones. Their locally dated "next" statements are not
current-status claims.
