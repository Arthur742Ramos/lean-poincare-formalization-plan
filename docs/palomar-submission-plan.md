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
| 02 | Raw curvature tensoriality and metric compatibility | Pointwise scalar tensoriality in all three slots and metric skew-adjointness of the raw curvature commutator | Passed by Palomar (user-confirmed); immutable artifact at `db821d6c926bc3fd9622893cc48e23637d406651` |
| 03 | Levi-Civita connections and metric-determined curvature invariants | Levi-Civita existence, curvature-tensor independence, Ricci symmetry, and Ricci/scalar-curvature invariance | Accepted by Palomar (user-confirmed); immutable artifact at `80b71f3a239ac2b294c91c66d020476f667a1306` |
| 04 | Diffeomorphism transport of connections and curvature | Tangent transport, pullback covariant derivative, raw curvature/torsion transport, and Levi–Civita preservation | Superseded; retained as historical review context |
| 05 | Geometric connection transport | Fixed `C^2` diffeomorphism covariance of the tangent-bundle connection, curvature, torsion, metric compatibility, and Levi–Civita property | Current candidate being submitted |
| 05 | Continuous sections and smoothing | Coordinate models, finite-cover gluing, smooth approximation, and convex fiber constraints | Source code exists; audit as a separate library contribution |
| 06 | The open metric cone | Symmetric positive-definite bilinear-form sections and openness in the section-space model | Source code exists; audit separately |
| 07 | Parabolic Holder primitives | Parabolic neighborhoods, Holder controls, covers, patching, and closure estimates | Supporting library material; not selected in corrected Submission 04 |
| 08 | Matrix and local-frame estimates | Determinant/inverse/Christoffel estimates and coordinate Ricci-DeTurck bounds | Supporting library material; reserve higher local-frame forms for later |
| 09 | Gauge transport | Pullback/pushforward of metrics, vector fields, connections, torsion, curvature, and Ricci data | Source code exists; isolate from point-4 scaffolding |
| 10 | Ricci-DeTurck gauge reduction | Background-dependent DeTurck equations and reduction back to intrinsic Ricci flow | Partially developed; do not present as local existence |
| 11 | Frozen chart evolution | The proved affine/linear evolution and stability theory for the frozen geometric operator | Supporting library material; not selected for the corrected Submission 04 surface |
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

1. Preserve the accepted 01 and 03 artifacts and the passed 02 artifact while
   packaging/validating 05 as the next non-overlapping manifold-level geometry
   result family.
2. Audit the dependency closure and research value of 06–07, then prepare the
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

Current state: Palomar passed this artifact according to the maintainer's
status report. Its accepted public artifact is recorded at immutable commit
`db821d6c926bc3fd9622893cc48e23637d406651`; the hosted receipt is maintained
with the submission record rather than treated as a substitute for the commit.

## Submission 03: Levi–Civita connections and metric-determined curvature invariants

The third candidate moves from raw curvature identities to the static
Riemannian package built on the bundled curvature and contraction
infrastructure. It selects:

- `PoincareCurvature.Palomar.exists_contMDiffLeviCivitaConnection`;
- `PoincareCurvature.Palomar.curvatureTensor_eq_of_isLeviCivita`;
- `PoincareCurvature.Palomar.ricciCurvature_symm_of_isLeviCivita`;
- `PoincareCurvature.Palomar.ricciCurvature_eq_of_isLeviCivita`; and
- `PoincareCurvature.Palomar.scalarCurvature_eq_of_isLeviCivita`.

This is a materially larger theorem family than the earlier elementary
commutator-skew and Levi–Civita-uniqueness wrappers: it connects existence of
the canonical connection to the metric-determined curvature tensor and both
principal trace contractions. The underlying mathematics is classical and is
presented as a formalization/adaptation, not as an original theorem or
priority claim.

The Challenge/Solution boundary uses three explicit Comparator definition
holes for the canonical curvature tensor, Ricci curvature, and scalar
curvature. The Challenge exposes their exact source types; the Solution
imports the actual package constructions and proves the five selected
statements. The candidate-specific role and oversight record is
`curvature/AGENT-CONTRIBUTION-03.md`.

Current state: Palomar accepted this artifact according to the maintainer's
status report. Its exact public commit is
`80b71f3a239ac2b294c91c66d020476f667a1306`; hosted acceptance is not conflated
with registration or public indexing.

## Submission 05: geometric connection transport

The current candidate selects the fixed-diffeomorphism transport family from
`curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/GaugeTransport.lean`:

- `PoincareCurvature.Palomar.curvatureAux_pullbackCovariantDerivative`;
- `PoincareCurvature.Palomar.curvatureAux_pullbackCovariantDerivative_apply`;
- `PoincareCurvature.Palomar.torsion_pullbackCovariantDerivative`;
- `PoincareCurvature.Palomar.isTorsionFree_pullbackCovariantDerivative`;
- `PoincareCurvature.Palomar.isMetricCompatibleTangent_pullbackCovariantDerivative`; and
- `PoincareCurvature.Palomar.isLeviCivita_pullbackCovariantDerivative`.

The compared definitions are the actual tangent pushforward/pullback, the
pullback covariant derivative, the raw curvature commutator, torsion-free
structure, metric compatibility, and the Levi–Civita predicate. The metric
compatibility theorems include the explicit equation identifying the target
inner product with the source metric pulled back by the tangent map. The
source-backed Solution proofs are genuine manifold theorems; the classical
provenance is recorded as standard affine-connection/Riemannian naturality,
not as an originality claim.

The candidate-specific role and oversight record is
`curvature/AGENT-CONTRIBUTION-05.md`; the final metadata pins it to an
immutable commit. The earlier coordinate, metric-cone, and frozen-affine
submissions remain historical or supporting material and are not selected by
this Comparator surface.

Current state: validate the Challenge/Solution surface and repository verifier
under Lean 4.33, push the final commit, and start a fresh Palomar intake with
the prior Palomar identity left blank.
