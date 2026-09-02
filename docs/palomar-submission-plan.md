# Palomar submission portfolio

This document records a proposed family of focused Lean formalizations to be
carved out of the Poincare/Ricci-flow research repository. The repository is a
source monorepo and research record; each Palomar submission must eventually be
an independently reproducible artifact with its own exact commit, statement
surface, dependency closure, and scope description.

The portfolio is deliberately broader than the final Poincare theorem. A
formalized geometric-analysis library can produce several meaningful results
before the Ricci-flow-with-surgery endpoint is reached.

## Submission acceptance bar

Every candidate must have:

- a mathematically meaningful theorem cluster, not merely a renamed module or
  documentation snapshot;
- a minimal `Challenge.lean` statement surface and a proved `Solution.lean`;
- a pinned Lean toolchain and Lake manifest;
- a clean, reproducible build and an independent axiom/proof-hole audit;
- complete attribution and an honest account of what is and is not proved.

Local readiness, hosted mechanical verification, editorial review, registration,
and public indexing are separate states. No candidate is considered submitted
until the exact public repository, full commit SHA, Comparator configuration,
and authorization relationship have been explicitly confirmed.

## Proposed portfolio

| ID | Candidate | Main mathematical boundary | Current status |
| --- | --- | --- | --- |
| 01 | Raw Bianchi curvature identities | Pointwise first and raw differential second Bianchi identities for torsion-free affine connections | Accepted by Palomar (user-confirmed); immutable artifact at `04b00ba308fc5196a07a5cf7a9c6f985505ea041` |
| 02 | Raw curvature tensoriality and metric compatibility | Pointwise scalar tensoriality in all three slots and metric skew-adjointness of the raw curvature commutator | Preparing |
| 03 | Static Riemannian identities | Levi-Civita existence, sectional curvature, and Ricci/scalar curvature identities | Source code exists; isolate after 02 |
| 04 | Time-dependent geometric structures | One-parameter sections, connections, metrics, and slicewise curvature | Source code exists; isolate after 03 |
| 05 | Continuous sections and smoothing | Coordinate models, finite-cover gluing, smooth approximation, and convex fiber constraints | Source code exists; audit as a separate library contribution |
| 06 | The open metric cone | Symmetric positive-definite bilinear-form sections and openness in the section-space model | Source code exists; audit separately |
| 07 | Parabolic Holder primitives | Parabolic neighborhoods, Holder controls, covers, patching, and closure estimates | Source code exists; select a coherent theorem cluster |
| 08 | Matrix and local-frame estimates | Determinant/inverse/Christoffel estimates and coordinate Ricci-DeTurck bounds | Source code exists; select a coherent theorem cluster |
| 09 | Gauge transport | Pullback/pushforward of metrics, vector fields, connections, torsion, curvature, and Ricci data | Source code exists; isolate from point-4 scaffolding |
| 10 | Ricci-DeTurck gauge reduction | Background-dependent DeTurck equations and reduction back to intrinsic Ricci flow | Partially developed; do not present as local existence |
| 11 | Frozen chart evolution | The proved affine/linear evolution and stability theory for the frozen geometric operator | Partially developed; audit theorem scope before packaging |
| 12 | General local existence and uniqueness | Compact-manifold Ricci-flow local existence in arbitrary dimension | Future; remains open until the canonical theorem and audit gates pass |
| 13 | Evolution and maximum principles | Curvature evolution equations and parabolic maximum-principle consequences | Future |
| 14 | Distance distortion and compactness | Length/distance control, blow-up, rescaling, and compactness of flows | Future |
| 15 | Perelman reduced geometry | Reduced length, reduced distance, and reduced volume | Future |
| 16 | Non-collapsing and ancient solutions | No-local-collapsing and the dimension-three singularity-model theory | Future |
| 17 | Canonical neighborhoods and surgery | Neck/cap recognition and Ricci flow with surgery | Future; high-value differentiated target |
| 18 | Topology, extinction, and Poincare corollaries | Topological surgery bookkeeping, finite-time extinction, and topological/smooth corollaries | Future; final endpoint family |

The table is a portfolio, not a promise that every row should be submitted as
written. A row may be merged with a neighboring row when the dependency closure
and theorem statement form one coherent contribution, or split when a distinct
library result has an independently defensible boundary.

## Order of work

1. Preserve the accepted 01 artifact and package/validate 02 as the next
   non-overlapping raw-curvature result family.
2. Audit the dependency closure and research value of 03–06, then prepare the
   strongest non-overlapping candidates.
3. Package the analytic candidates 07–11 only around proved theorem clusters;
   keep point-4 interfaces and special cases clearly labeled as scaffolding.
4. Re-run a public novelty and interoperability audit before claiming a broad
   Ricci-flow result, especially for short-time existence, compactness, and
   non-collapsing.
5. Treat 12–18 as later milestone submissions whose status changes only when
   their actual mathematical content is proved.

## Submission 01: raw Bianchi curvature identities

The first candidate is the `curvature/` Lean package. Its Palomar surface is
prepared in that directory.

Selected statements:

- `PoincareCurvature.Palomar.first_bianchi_raw_of_torsion_free`
- `PoincareCurvature.Palomar.second_bianchi_raw_of_torsion_free`

The implementation imports the checked Bianchi module. It does not import the
root aggregate or the internal Ricci-flow scaffold as part of the selected proof
surface. The candidate formalizes the standard first and raw differential second
Bianchi identities, with the regularity hypotheses used by the commutator proofs;
it does not claim new mathematical priority. The former commutator-skew and
Levi-Civita-uniqueness wrappers remain supporting library results, not selected
research-interest results.

The complete role and oversight record is in
`curvature/AGENT-CONTRIBUTION.md`.

Current state: Palomar accepted the revised artifact according to the
maintainer's status report. Its exact public commit is
`04b00ba308fc5196a07a5cf7a9c6f985505ea041`; hosted verification and editorial
acceptance are not conflated with registration or public indexing.

## Submission 02: raw curvature tensoriality and metric compatibility

The next candidate retains the same checked `curvature/` implementation but
uses a distinct Comparator surface. It selects:

- `PoincareCurvature.Palomar.raw_curvature_left_tensoriality`;
- `PoincareCurvature.Palomar.raw_curvature_middle_tensoriality`;
- `PoincareCurvature.Palomar.raw_curvature_right_tensoriality`; and
- `PoincareCurvature.Palomar.raw_curvature_metric_skew_adjointness`.

These statements formalize the nontrivial pointwise tensoriality and metric
skew-adjointness behavior of the raw curvature commutator. They deliberately
do not reselect the accepted Bianchi surface, the immediate commutator sign
change, or textbook Levi-Civita uniqueness. The candidate-specific role and
oversight record is `curvature/AGENT-CONTRIBUTION-02.md`.

Current state: Challenge/Solution and metadata are being prepared locally;
the final public commit, local Lean/Comparator checks, and any Palomar intake
remain to be completed separately.
