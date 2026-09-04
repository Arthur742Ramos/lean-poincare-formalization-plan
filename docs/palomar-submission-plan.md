# Palomar submission portfolio

This document records a proposed family of focused Lean formalizations to be
carved out of the Poincare/Ricci-flow research repository. The repository is a
source monorepo and research record; each Palomar submission must eventually be
an independently reproducible artifact with its own exact commit, statement
surface, dependency closure, and scope description.

The portfolio is deliberately broader than the final Poincare theorem. A
formalized geometric-analysis library can produce several meaningful results
before the Ricci-flow-with-surgery endpoint is reached.

## Registration lineage clarification

The first three artifacts were not three Palomar registry IDs. They reused
the same repository/project/Comparator identity, so Palomar correctly kept
them as versions 1--3 of `PALOMAR-2026-09-02-000007`:

- [version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-09-02-000007&version=1)
  is the raw Bianchi surface at
  `04b00ba308fc5196a07a5cf7a9c6f985505ea041`;
- [version 2](https://palomar-registry.org/entry?id=PALOMAR-2026-09-02-000007&version=2)
  is the raw curvature tensoriality surface at
  `db821d6c926bc3fd9622893cc48e23637d406651`; and
- [version 3](https://palomar-registry.org/entry?id=PALOMAR-2026-09-02-000007&version=3)
  is the Levi–Civita/invariant surface at
  `80b71f3a239ac2b294c91c66d020476f667a1306`.

Those versions remain separately citable and immutable, but Palomar does not
retroactively split them into independent records. A genuinely new result
must change the project/Comparator identity and use a blank external
`existing_id`. The contracted-Bianchi candidate below does that by living in
the separate `contracted-bianchi/` project directory.

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
| 05 | Geometric connection transport | Fixed `C^2` diffeomorphism covariance of the tangent-bundle connection, curvature, torsion, metric compatibility, and Levi–Civita property | Withdrawn after review; not submission-ready because the selected family is routine naturality |
| 06 | Continuous sections and smoothing | Coordinate models, finite-cover gluing, smooth approximation, and convex fiber constraints | Source code exists; audit as a separate library contribution |
| 07 | The open metric cone | Symmetric positive-definite bilinear-form sections and openness in the section-space model | Source code exists; audit separately |
| 08 | Parabolic Holder primitives | Parabolic neighborhoods, Holder controls, covers, patching, and closure estimates | Supporting library material; not selected in corrected Submission 04 |
| 09 | Matrix and local-frame estimates | Determinant/inverse/Christoffel estimates and coordinate Ricci-DeTurck bounds | Supporting library material; reserve higher local-frame forms for later |
| 10 | Gauge transport | Pullback/pushforward of metrics, vector fields, connections, torsion, curvature, and Ricci data | Source code exists; isolate from point-4 scaffolding |
| 11 | Ricci-DeTurck gauge reduction | Background-dependent DeTurck equations and reduction back to intrinsic Ricci flow | Partially developed; do not present as local existence |
| 12 | Frozen chart evolution | The proved affine/linear evolution and stability theory for the frozen geometric operator | Supporting library material; not selected for the corrected Submission 04 surface |
| 13 | General local existence and uniqueness | Compact-manifold Ricci-flow local existence in arbitrary dimension | Future; remains open until the canonical theorem and audit gates pass |
| 14 | Evolution and maximum principles | Curvature evolution equations and parabolic maximum-principle consequences | Future |
| 15 | Distance distortion and compactness | Length/distance control, blow-up, rescaling, and compactness of flows | Future |
| 16 | Perelman reduced geometry | Reduced length, reduced distance, and reduced volume | Future |
| 17 | Non-collapsing and ancient solutions | No-local-collapsing and the dimension-three singularity-model theory | Future |
| 18 | Canonical neighborhoods and surgery | Neck/cap recognition and Ricci flow with surgery | Future; high-value differentiated target |
| 19 | Topology, extinction, and Poincare corollaries | Topological surgery bookkeeping, finite-time extinction, and topological/smooth corollaries | Future; final endpoint family |
| CB-01 | Contracted second Bianchi identity | Explicit Ricci/scalar trace contraction of the cyclic second Bianchi identity and divergence-free Einstein tensor | In preparation as a fresh `contracted-bianchi/` project; no Palomar ID or `existing_id` assigned |

The table is a portfolio, not a promise that every row should be submitted as
written. A row may be merged with a neighboring row when the dependency closure
and theorem statement form one coherent contribution, or split when a distinct
library result has an independently defensible boundary.

## Order of work

1. Preserve the accepted 01 and 03 artifacts and the passed 02 artifact. They
   are versions 1--3 of the existing Palomar identity
   `PALOMAR-2026-09-02-000007`.
2. Do not resubmit 05. Its 784… intake was an attempted version 4 of that
   identity and was withdrawn; any future intake at the same identity must set
   the external `existing_id` field to the full Palomar ID.
3. Audit 06–12 for a theorem-level consequence that is stronger than routine
   transport, projection, scaling, or ODE assembly. No unreviewed row is
   currently cleared for submission.
4. Package a future candidate only after its definitions are auditable, its
   hypotheses do real mathematical work, its provenance is source-based, and
   its theorem family has a defensible serious-note case for an identified
   research audience.
5. Treat 13–19 as later milestone submissions whose status changes only when
   their actual mathematical content is proved and the same notability gate
   has been met.
6. Keep `contracted-bianchi/` on a fresh-submission track. Its Comparator
   selects the contracted identity and divergence-free Einstein tensor under a
   new project path; do not populate an `existing_id` with the registered
   curvature record.

## What passed, and why the later candidate failed

The first three public versions passed the research-interest review for
different, concrete reasons:

- 01 selected the first and differential second Bianchi identities as one
  coherent curvature-identity family. The public review described it as
  plausibly note-worthy for formalized differential geometry.
- 02 selected all three scalar tensoriality laws together with metric
  skew-adjointness. The public review treated this as a coherent foundational
  bundle with a credible specialist audience.
- 03 connected Levi–Civita existence to metric-determined curvature, Ricci,
  and scalar-curvature invariants. The public review treated this connected
  classical Riemannian family as substantial enough for a serious
  formalization note.

Candidate 05 was different in kind. Even though its formulas are genuinely
manifold-level and its hosted mechanical verification succeeded, it selected
fixed-diffeomorphism naturality identities followed by immediate torsion,
metric-compatibility, and Levi–Civita preservation corollaries. That is useful
infrastructure, but it does not supply a new construction, analytic estimate,
or geometric consequence that could plausibly carry a research paper or
serious note. More prose, authorship changes, or formalization effort cannot
repair that selection-level deficiency.

## No-go gate for future Palomar submissions

Do not submit a routine identity, transport, projection, or packaging theorem,
even when it is fully formalized. Before a future submission is considered, it
must have:

- a theorem-level consequence beyond definitions and immediate naturality;
- definitions and hypotheses that rule out vacuous interpretations and do
  genuine mathematical work;
- an accurate source/provenance account and exact registration lineage; and
- a credible case that the result could anchor a serious formalization note or
  research note for an identified audience.

At present, none of the unreviewed rows 06–18 has been cleared by this gate.

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

## Candidate 05: geometric connection transport (withdrawn)

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

Current state: withdrawn and closed without registration. The candidate is not
submission-ready, and no new intake should be made for this surface. Keep the
existing Palomar identity and status record intact; a materially stronger
theorem family is required before revisiting the portfolio.

## Fresh candidate CB-01: contracted second Bianchi identity

The next candidate is deliberately placed in the separate `contracted-bianchi/`
Lean project. Its Comparator selects:

- `ContractedBianchi.contractedSecondBianchi`; and
- `ContractedBianchi.einsteinTensorDivergence`.

The Challenge surface exposes genuine multilinear curvature and covariant
derivative tensors, explicit pair symmetries, the cyclic second-Bianchi
hypothesis, and the finite orthonormal-basis trace formulas for Ricci and
scalar curvature. The Solution performs the contraction and derives the
divergence-free Einstein tensor; neither conclusion is smuggled in as a
hypothesis. The current scope is intentionally tensor-level. It records the
raw manifold second-Bianchi theorem in the parent package as a formal
dependency, but does not claim a fully discharged manifold-to-tensor bridge
for every derivative symmetry.

This is a new mathematical result family for Palomar intake, not a correction
or version of `PALOMAR-2026-09-02-000007`: the project directory and Comparator
identity differ, and the external `existing_id` must remain blank. It will not
be called submission-ready until the pinned contribution record, clean build,
proof-hole audit, and any remaining geometric-scope concerns have been checked.
