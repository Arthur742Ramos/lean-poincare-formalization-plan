# Point-4 closed-manifold contract correction

**Supporting interface/audit milestone. Point 4 remains OPEN.**

The maintainer approved the narrow geometric correction on 2026-10-04.
The clean implementation base is
`db5bf257fa4c452b6f120ef49d916da31fe44da4`.
No Ricci-flow existence or uniqueness theorem is constructed by this milestone.

## Exact before and after

Before, the canonical completion goal admitted arbitrary compact smooth
manifolds modeled by `I : ModelWithCorners ℝ E H`, including boundary, with
no prescribed boundary data. Its result was the existing
`RicciFlow.IntrinsicLocalExistenceUniquenessFamily` for every spatially C²
initial metric.

After, the expected theorem has the additional theorem-level instance
`[BoundarylessManifold I M]`. Combined with `[CompactSpace M]`, this is the
closed-manifold setting of the Poincaré route. The model `I` remains arbitrary;
we do not require the stronger global `[I.Boundaryless]` or fix a Euclidean
model, dimension or rank.

The expected fully quantified type is
[`RicciFlow.PointFourClosedManifoldContract`](../../curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/PointFourContract.lean).
The existing normed real model, arbitrary topology/charted manifold, Hausdorff,
finite-dimensional and complete model, smooth manifold and C² tangent-bundle
premises remain, followed by compactness, the existing sigma-compactness
instance and precisely the approved boundaryless-manifold instance.
Its result uses the original `IntrinsicLocalExistenceUniquenessFamily` literally.
No new family, IVP, candidate, equation or time interval is substituted.

The general reusable interfaces are unchanged. In particular this correction
preserves all spatially C² initial data, the current slice-wise C² and ordinary
component-derivative candidate class, literal initial equality, and closed
`Set.Icc` initial and common uniqueness intervals. It neither substitutes smooth
initial data nor strengthens uniqueness-class regularity or changes endpoint
derivatives.

## Mathematical rationale and its evidence boundary

The original boundary scope permits a classical nonuniqueness route: start
from a flat compact ball, vary the boundary mean curvature by a positive-time
perturbation flat to all orders at zero while keeping the boundary conformal
class fixed, and compare with stationary flat flow. Boundary existence and
higher-regularity results, all-order compatibility and identity-initialized
DeTurck gauge provide the route. Constant flat past extension and a terminal
time inside the existence window address the ordinary derivative/endpoints.

This is an independently reviewed inference from
[Gianniotis, *The Ricci flow on manifolds with boundary*](https://arxiv.org/pdf/1210.0813),
Theorems 1.1 and 4.2, compatibility equations (4.12)–(4.14), and Remark 5.3.
No Lean counterexample or formal refutation was built. The inference motivates
an explicit approved narrowing of the written goal; it is not a completed
analytic bridge for the remaining goal.

At the pinned Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`,
[`InteriorBoundary.lean`, lines 164–217](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Geometry/Manifold/IsManifold/InteriorBoundary.lean#L164-L217)
defines `BoundarylessManifold I M` as every point being interior and proves its
equivalence with empty manifold boundary. Global model boundarylessness implies
it but is stronger; it is not the approved completion premise.

## Stronger completion checking

G1 still scans library source for admissions and local axioms after removing
comments and strings. G2 still performs the full `lake build`. G4 still permits
only `propext`, `Classical.choice`, and `Quot.sound`.

G5 now imports the actual target and checks a bare `@target` against the entire
expected dependent function type at three independent universes. Compiler exit
status is mandatory. G5 also requires the eight original requirement-interface
fingerprints and the complete expected binder/result expression to match the
immutable base. This guards against weakening a definition while retaining its
name. A future semantics-preserving refactor needs explicit reviewed fingerprint
renewal; the check is not permission to change the requirements. A name grep is no longer accepted as a signature proof.
G3 cannot certify unconditional construction when that assignment fails.
The previous forbidden restriction checks remain additional defenses. The
canonical identity is fixed as
`RicciFlow.intrinsicLocalExistenceUniquenessFamily_pointFour`.
An alias of its expected type is not that target or a proof of its inhabitation.

Only all five actual gates in one full run may produce `POINT 4 CLOSED`.
A `--no-build` run has G2 skipped, yields OPEN and exits unsuccessfully, even
if every other gate were to pass.

## Verification surfaces

- `scripts/point4_closed_contract_source_test.py` fingerprints eight original
  interface declarations against the immutable base, checks the entire expected
  binder/result expression, and preserves the canonical base-name
- `scripts/point4_closed_contract_probe.lean` prints the expected type and
  existing IVP/candidate/uniqueness/derivative fields
- `scripts/point4_closed_contract_regression.lean` checks identity plumbing for
  the accepted signature and rejects added package, solver, analytic, empty,
  subsingleton, tangent-subsingleton, rank, global-model-boundary and
  universe-specialized inputs; local fixture inputs do not construct the target
- The regression also proves the actual empty-boundary equivalence directions
  from the pinned Mathlib API, without assuming global model boundarylessness
- `.github/workflows/point4-closed-contract.yml` is a pinned read-only hosted
  compile-first workflow: exact checkout, expected-contract compilation,
  type printing, kernel regression tests, then the complete full build/audit
  with failure artifacts retained

Local source checks and shell syntax are distinct from Lean verification.
Exact Lean 4.33 hosted compilation and full gates must be established for the
frozen commit before review/publication claims. No toolchain, package, pin,
structured attribution or contributor notice is changed here. No registry
submission or broader smooth-data/candidate-class correction is authorized.

## Remaining open obligations

Existence for all C² initial data, uniqueness against every current weak
candidate, general ordinary initial-time extension, intrinsic geometric
identification and upstream version/model-space transport remain open.
The contract correction removes one scope obstruction; it does not solve any
of those obligations or unlock downstream roadmap milestones.
