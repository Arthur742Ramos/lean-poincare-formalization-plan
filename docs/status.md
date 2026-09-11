# Current formalization status

This is the current-status authority for the Poincaré roadmap. The mathematical
route belongs in [the roadmap](roadmap.md); detailed historical implementation
notes belong in [the history directory](history/README.md).

Status claims must be checked against Lean source and, where available,
executable audits. A successful build proves that the checked source compiles;
it does not by itself prove that a roadmap target has been constructed.

## Status vocabulary

| Label | Meaning |
| --- | --- |
| **Proved** | The milestone's target statements have Lean proofs under the intended hypotheses. |
| **Conditional** | A proved theorem derives the target from additional data that still has to be constructed. |
| **Supporting** | Reusable definitions, estimates, special cases, or infrastructure are proved, but the general milestone is not. |
| **Open** | The required general theorem is absent or fails its completion gate. |
| **Future** | Work is downstream of an open dependency and is not claimed complete here. |

Submission states such as prepared, verified, submitted, accepted, or publicly
registered are deliberately excluded from this vocabulary. They are recorded
in [the Palomar portfolio](palomar-submission-plan.md).

## Roadmap dashboard

| # | Milestone | Status | Evidence boundary |
| ---: | --- | --- | --- |
| 1 | Riemannian curvature | **Proved** | Public `PoincareCurvature` imports expose covariant derivative, curvature, Ricci/scalar curvature, metric compatibility, and Levi–Civita uniqueness. |
| 2 | Curvature identities and existence | **Proved** | The package exposes Levi–Civita existence, sectional curvature, and Bianchi identities. |
| 3 | Time-dependent geometry | **Proved** | Time-indexed sections, metrics, connections, curvature quantities, and slice-wise Levi–Civita constructions are implemented. |
| 4 | Ricci-flow local existence and uniqueness | **Open** | Special cases and conditional bridges are proved, but `intrinsicLocalExistenceUniquenessFamily_pointFour` is absent and the audit does not close. |
| 5 | Evolution equations and maximum principles | **Future** | Depends on a genuine Ricci-flow solution theory. |
| 6 | Distance distortion and compactness | **Future** | Depends on milestones 4–5. |
| 7 | Perelman reduced geometry | **Future** | Depends on the evolving-metric analytic toolkit. |
| 8 | Non-collapsing | **Future** | Depends on reduced geometry and Ricci-flow estimates. |
| 9 | Three-dimensional ancient solutions | **Future** | Depends on compactness and non-collapsing. |
| 10 | Canonical neighborhoods and neck detection | **Future** | Depends on ancient-solution theory. |
| 11 | Ricci flow with surgery | **Future** | Depends on canonical-neighborhood control. |
| 12 | Topological control of surgery | **Future** | Depends on a formal surgery construction. |
| 13 | Finite-time extinction | **Future** | Depends on surgery plus its analytic and topological controls. |
| 14 | Topological Poincaré corollary | **Future** | Depends on extinction and three-manifold topology. |
| 15 | Smooth Poincaré corollary | **Future** | Depends on the topological corollary and the three-dimensional smoothing bridge. |

## Point-4 evidence

The completion gate is
[`curvature/scripts/point4_audit.sh`](../curvature/scripts/point4_audit.sh).
It requires all of the following in one full run:

1. no forbidden proof placeholders or locally declared axioms in the library;
2. a successful `lake build`;
3. an unconditional general compact-manifold construction of
   `IntrinsicLocalExistenceUniquenessFamily`;
4. only the accepted foundational axioms in the target's proof dependencies;
5. an elaborated target type without hidden restrictive hypotheses.

The canonical target name is maintained in
[`curvature/scripts/point4_target.txt`](../curvature/scripts/point4_target.txt).
As of the documentation audit on 2026-09-11, the fast audit found:

| Gate | Result |
| --- | --- |
| G1: forbidden-term scan | Pass |
| G2: build | Not rerun by the fast audit |
| G3: unconditional construction | Fail: canonical target missing |
| G4: axiom audit | Fail because target is missing |
| G5: faithful target type | Fail because target is missing |

Therefore milestone 4 is **open**. A previous successful build, a conditional
theorem, or a proved special family cannot override that verdict.

## Proved work inside the open frontier

The open status does not mean that the Point-4 files are empty scaffolding. The
repository contains proof-bearing work including:

- Ricci-flow and Ricci–DeTurck solution and initial-value-problem structures;
- intrinsic metric-only theorem-package interfaces;
- stationary results for empty, subsingleton, Ricci-flat, and rank-one settings;
- a nonstationary Einstein homothetic existence result, without the general
  uniqueness theorem;
- gauge transport for metrics, vector fields, and affine connections;
- conditional reductions from sufficiently strong Ricci–DeTurck chart,
  realization, encoding, and gauge data to intrinsic Ricci flow;
- continuous-section Banach models, smoothing results, metric-cone tools,
  parabolic Hölder primitives, coordinate estimates, model evolution, and
  frozen affine/operator-exponential results.

These results should be cited by their actual theorem statements. They must not
be summarized as general compact-manifold Ricci-flow local existence.

## Updating this page

When implementation changes:

1. run the relevant package build and audit;
2. identify the exact theorem closing or advancing a milestone;
3. update this dashboard and the focused plan, not the historical logs;
4. keep publication status in the submission portfolio;
5. preserve partial or failed approaches in `docs/history/` only when they are
   useful research records.
