# Combined supporting linear-heat geometry milestone

**Supporting integration milestone. Point 4 remains OPEN.**

This branch combines three independently qualified supporting proof units with
current master using real merge commits. It adds no mathematical proof body,
changes no canonical requirement and prepares no registry intake. Parent-head
verification does not certify this combined head; exact combined compilation,
all current checks and independent full-stack review remain required.

## Immutable sources and retained history

| Source | Exact immutable head | Reused boundary |
| --- | --- | --- |
| Current master | `60b6f8ef9d37d1fc5fac1f6113584e1b16370016` | Actual conventional background/W/Lie/Ricci RHS, all earlier spatial operators and approved closed-manifold contract |
| PR122 | `4e27b905a5645b27e0e101124fd011c4dbd00586` | Actual frozen inverse-metric principal and holonomic Cauchy action |
| PR123 | `f1ee137abbd46111f5d9722d41d4f62960e8f171` | Base-C¹/local-tensor-C² actual connection-Laplacian identity |
| PR125 | `ecb86c90b902b17cf6889c4f89a31e80702e39c9` | Manifold-boundaryless chart transport and actual preferred-frame replacement |

The exact three parent heads are retained in merge ancestry. No original
branch is rewritten. All inherited proof files and probes are byte-identical to
their corresponding source; `PreferredCoordinateFrame.lean` is the already
qualified PR125 proof-bearing replacement, not a new integration edit.
The root imports are the complete union of the four sources, including the
current `PointFourContract` and actual `StandardRicciDeTurckCoordinateOperator`.

The original focused results and limitations are documented in
[frozen metric principal](frozen-metric-principal.md),
[weak Laplacian](weak-laplacian.md),
[boundaryless chart/frame transport](boundaryless-chart-frames.md) and
[actual standard coordinate operator](standard-coordinate-operator.md).
Those pages retain their preparation-time verification snapshots. This page
records the later integration boundary without rewriting historical evidence.

## Mathematical combination and its limits

The frozen result identifies the actual preferred-frame inverse Gram matrix
with the chosen-LC coordinate inverse, then identifies the existing bounded
finite-cylinder Cauchy action using genuine compatible derivatives. Tensor
output remains `(j,i)`. Its ordinary time-derivative identity is on `Ioo t₀ T`;
the terminal-time `Ioc` identity retains the stored time slot.

The weak local adapter identifies the genuine intrinsic connection Laplacian
with `Aheat D²u + Bheat Du + Cheat u` from a C¹ base connection and a tensor
that is C² on the open frame patch. Tensor output remains `(q,p)` for intrinsic
arguments `frame p, frame q`. It supplies neither a C² connection premise nor
an assumed induced-three regularity or coordinate differential identity.

The chart/frame unit obtains openness of the actual fixed extended-chart
target and its interior-model-range neighborhood from `BoundarylessManifold
I M`. It proves genuine inverse-chart derivative and pullback transport and
preserves the actual preferred-frame, scalar derivative and commuting-frame
proofs. It does not derive global model boundarylessness.

These units coexist with the actual conventional standard geometric RHS.
They are not yet a theorem assembling a nonlinear manifold PDE solver.
The frame API now has theorem-level manifold-boundaryless scope, while the
chosen-LC, frozen, weak and gauge consumer declarations keep their original
stronger `[I.Boundaryless]` hypotheses. Their generalization, quantitative
norm/heat-generator transport, manifold encoding, localization/overlap gluing,
Schauder and quasilinear estimates, positivity, initial trace/realization,
recovery gauge construction and uniqueness remain open.

The approved canonical contract still requires every spatially C² initial
metric, the original weak candidate class, ordinary component derivatives,
and the original common closed intervals. Its existing eight fingerprints,
full expected dependent type, canonical name, audit and kernel regression
fixtures are preserved exactly from current master. The canonical target
`RicciFlow.intrinsicLocalExistenceUniquenessFamily_pointFour` remains absent.

## Individual-head evidence, preserved separately

The individually qualified primary workflow runs are:

- [PR122 exact `4e27b905` frozen qualification](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/37219961149): eight focused foundational-axiom surfaces and full source/build gates
- [PR123 exact `f1ee137a` weak qualification](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/37221373585): four focused foundational-axiom surfaces and full source/build gates
- [PR125 exact `ecb86c90` boundaryless qualification](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/37222588697): ten focused foundational-axiom surfaces, seven actual manifold-boundaryless type surfaces and full source/build gates

For each head, all 13 checks passed and the inherited 84 axiom occurrences and
seven full builds/audits were independently inspected. The full audits reported
G1/G2 PASS with the canonical target absent and Point 4 OPEN. These are historical
individual-head results; none is substituted for combined-head evidence.

The approved closed contract also has independent exact-head evidence at
[contract run 37228410080](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/37228410080).
The fresh current-master `60b6f8ef` prerequisites are
[standard operator run 37236572309](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/37236572309)
and [automatic package run 37236481540](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/37236481540).
They must be qualified before merging this integration; their pending state at
preparation is not reported as a pass here.

## Combined-head gates

The original focused workflows are unchanged and execute against this combined
head. The additional pinned read-only
[combined workflow](../../.github/workflows/point4-linear-heat-geometry.yml)
checks exact checkout/real ancestry, all inherited proof blobs and workflows,
current pins/attribution/audit, and complete import union before compilation.
It builds the entire public library, reruns all eleven original proof probes,
checks all 127 axiom occurrences across 121 distinct declarations (including
the six preferred-frame declarations repeated across probes),
rechecks the seven manifold-boundaryless type surfaces, prints the current
canonical contract and runs its original positive/negative kernel signature
fixtures. It then runs the unchanged full five-gate completion audit and
retains all exact-head logs, including failures.

The immutable-parent
[source/provenance guard](../../curvature/scripts/point4_linear_heat_geometry_source_test.py)
protects every inherited Lean proof throughout the repository, all existing
workflows, canonical completion machinery, dependency pins and contributor
records. It rejects unexpected added/deleted Lean sources, missing parent
imports, new root declarations, missing/duplicate provenance and changes to
selected artifact metadata. Structured `builds-on` entries record each exact
source plus all prior attribution. Duplicate same-source entries are joined
without dropping any original provenance note. The full official v0.4 schema
is separately validated against cached official bytes; the historical `agent`
method normalization preserves its model and contribution history.

The [negative source/evidence fixtures](../../curvature/scripts/point4_linear_heat_geometry_mock_test.py)
reject proof/workflow mutation, omitted contract/RHS imports, changed author,
license/model history, missing parent provenance, missing/extra/duplicate axiom
evidence, nonfoundational axioms, skipped full builds and false completion
claims. These tests do not simulate a successful Lean build.

Local preparation is source-only: parent blob comparison, schema validation,
negative Python fixtures, original contract source invariants, forbidden-token
scan, documentation links, shell syntax and diff hygiene. No local toolchain,
cache download or full compilation is claimed. Fresh exact combined-head Lean
4.33 hosted verification, all current checks and full-stack independent review
are still required before merge. A successful supporting integration will still
leave Point 4 OPEN; no intake, registry submission or PDE completion is claimed.
