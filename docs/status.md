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
| 5 | Evolution equations and maximum principles | **In Progress** | Hamilton–Ivey pinching is proved for the ordered curvature ODE, and a conditional intrinsic geometric evolution/pinching theorem is now proved from `IsRicciFlowOn` plus explicit mixed and spatial regularity. Those regularity and contact assumptions are not derived from the current slice-wise flow predicate; the general solution theory and maximum-principle layer remain open. |
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
3. an unconditional general compact-boundaryless-manifold construction of
   `IntrinsicLocalExistenceUniquenessFamily`;
4. only the accepted foundational axioms in the target's proof dependencies;
5. a kernel-checked assignment to the complete expected closed-manifold type,
   with no added analytic, solver, package or restrictive type hypotheses.

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

The maintainer-approved 2026-10-04 scope correction adds only the theorem-level
`BoundarylessManifold I M` premise. It does not change the reusable geometric,
IVP, candidate or family interfaces. The complete expected type and rationale
are recorded in [the closed-manifold contract milestone](point4/closed-contract.md).
This is an interface/audit milestone, not a construction of the canonical target.

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

Separately, `hamilton-ivey-reaction/` proves Hamilton--Ivey defect preservation
for ordered solutions of the three-dimensional curvature ODE, including the
scalar lower barrier, exact logarithmic-defect reaction identity, and strict
`(-nu)/9` coercivity estimate. It closes the ODE stage of milestone 5, but it
does not yet connect that calculation to an intrinsic Ricci flow or prove a
geometric parabolic maximum principle.

The latest `curvature/` follow-up now proves
`HamiltonIveyCurvatureEvolutionCertificate.of_intrinsicRicciFlow_and_jointRegularity`
and the conditional pinching endpoint
`hamiltonIveyPinching_of_intrinsicRicciFlow_and_jointGeometricEvolution_contactData_on_negative_spectrum`.
The constructor obtains the actual curvature-tensor velocity from
`IsRicciFlowOn` and explicit joint spacetime regularity of metric pairings and
nested covariant-derivative sections, deriving the connection variation from
Koszul rather than accepting a connection-variation or curvature-evolution
identity as input. It then derives the Ricci-trace and curvature-operator
evolution using the geometric contractions. The pinching theorem additionally
requires explicit slice/operator regularity, the initial least-eigenvalue
bound, scalar and eigenvalue continuity, and support-contact regularity.
These hypotheses are not consequences currently proved from the slice-wise
`IsRicciFlowOn` predicate. Thus the geometric PDE is no longer an independent
caller-supplied input, and a conditional geometric Hamilton--Ivey theorem is
proved; an unconditional theorem from `IsRicciFlowOn` alone, analytic
regularity/existence theory, and the general tensor maximum-principle layer
remain open. The earlier local second-derivative commutator,
induced-hom regularity, actual curvature-operator regularity, shifted-tensor
regularity, and `R - nu * g` connection-Laplacian bridge remain part of the
supporting development.

The next supporting source candidate adds fixed-chart actual chosen-LC
curvature coefficients and intrinsic Ricci readouts, keeping the ordinary
trace's transpose explicit before using intrinsic Ricci symmetry. It derives
local C¹ coefficient regularity and derivative transport from the actual
chosen connection and local frame. Exact Lean-4.33 verification is pending;
see [the precise candidate boundary](point4/chosen-lc-curvature.md). It does
not supply the conventional Lie/DeTurck, heat-generator or PDE bridges and
does not change the Point-4 **Open** status.

The next supporting source candidate supplies the actual conventional
StandardDeTurck background/W coordinate producers, genuine derivative
transport, actual torsion/metric-compatible Lie correction and intrinsic RHS
identification. It then specializes the corrected jet, principal and frozen
remainder identities to that same actual geometric RHS. Exact Lean-4.33
verification is pending; no local compiler was run for this unit. See
[actual standard coordinate-operator scope](point4/standard-coordinate-operator.md).
The heat-generator, analytic, PDE and canonical Point-4 **OPEN** boundaries
remain unchanged.

A further supporting source candidate identifies the actual preferred-frame
frozen metric inverse with the existing geometric tensor-heat principal
coefficient and evaluates its bounded finite-cylinder Cauchy operator using
genuine coordinate derivatives from the proved compatible derivative graph.
It preserves tensor output `(j,i)`, uses actual time differentiation only on
the open time interval, and requires no added candidate regularity or
principal-identification premise. Exact Lean-4.33 verification is pending;
see [the precise candidate boundary](point4/frozen-metric-principal.md).
This is differential-operator identification only. Point 4 remains **Open**.

## Latest supporting integration boundary

The [combined linear-heat geometry milestone](point4/linear-heat-geometry.md)
combines the independently qualified exact PR122 frozen actual-metric/holonomic
action, PR123 weak actual Laplacian and PR125 manifold-boundaryless chart/frame
proofs with current-master actual conventional W/Lie/Ricci RHS and the approved
closed-manifold contract. Their preparation-time candidate wording above and
in focused pages is historical. Exact combined-head Lean 4.33 full compilation,
all inherited/current/focused axiom and type checks, canonical contract
regressions and full-stack review remain pending. Mathematical proof blobs,
requirements and individual verification gates are preserved. The integration
adds no PDE solver or canonical theorem and leaves milestone 4 **Open**.

## Updating this page

When implementation changes:

1. run the relevant package build and audit;
2. identify the exact theorem closing or advancing a milestone;
3. update this dashboard and the focused plan, not the historical logs;
4. keep publication status in the submission portfolio;
5. preserve partial or failed approaches in `docs/history/` only when they are
   useful research records.

## Weak-regularity Laplacian proof unit

The [base-C¹, local-C² actual tensor-Laplacian adapter](point4/weak-laplacian.md)
has been authored and awaits independent source review and exact Lean 4.33.0
hosted verification. It constructs coordinate certificates internally and
preserves the actual operator and reversed tensor-output convention. It does
not provide Hölder coefficient bounds or close the canonical Point-4 target.
