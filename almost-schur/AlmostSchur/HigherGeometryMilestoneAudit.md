# Higher geometry intermediate milestone — 2026-09-06

## Outcome and audit pause

Eight new Lean modules build together: **3628 jobs, exit 0**. There are 28 public
API declarations and eight named local helper instances. All 36 were checked
individually with `#print axioms`; every report contains only `propext`,
`Classical.choice`, and `Quot.sound`. No proof placeholders or new axioms were
introduced. This is a sound intermediate milestone, **not yet a proof of
2 div Ric = d Scal**.

Only new files in AlmostSchur were created. No root, CheckAxioms, README,
existing modules, CurvatureVendor source, provenance manifest, or curvature/
files were edited by this work. Concurrent unrelated changes remain untouched.

## Proved mathematical scope

1. The actual constructed `leviCivitaConnection` has
   `ContMDiffCovariantDerivative 2`, proved through C² dual-frame reconstruction
   and C² Koszul pairings under a C³ metric. More generally the same result holds
   for every metric-compatible torsion-free connection.
2. Curvature evaluated on locally C³ fields is locally C¹. The genuine
   endomorphism whose trace is Ricci has C¹ hom-bundle regularity, and the actual
   Ricci scalar pairing has C¹ regularity.
3. Differentiation of that actual Ricci trace equals its moving-frame
   contraction. After the two Ricci-slot corrections, it contracts the
   corrected actual curvature derivative.
4. Metric-raised Ricci is constructed through Riesz duality. Its trace is
   proved equal to the existing bundled scalarCurvature. It is C¹, so actual
   scalar curvature is C¹ and its manifold differential is the corrected
   moving-frame trace derivative of that operator.
5. The corrected actual curvature derivative equals the attributed core's
   secondBianchiAux on locally C³ fields. Consequently actual corrected Ricci
   differentiation contracts secondBianchiAux.
6. The attributed curvature double-contraction theorem is instantiated for the
   constructed LC, discharging compatibility, torsion, and both connection
   regularity requirements. Its two sums are still not identified with the
   final Ricci divergence and scalar differential.

## Hypotheses and conventions

The common geometric context is a finite-dimensional complete real normed model
space E, a smooth (`IsManifold I ∞ M`) boundaryless manifold, its actual tangent
Riemannian bundle, and the existing C¹ tangent-bundle structure. The higher
connection and Ricci/scalar modules explicitly retain
`IsContMDiffRiemannianBundle I 1 E TM`,
`IsContMDiffRiemannianBundle I 2 E TM`, and
`IsContMDiffRiemannianBundle I 3 E TM`. Lower-order instances are the existing
context; mathematically C³ metric regularity entails them.

- MetricDualFrameTwo requires only C¹ and C² metric instances; no Hausdorff
  assumption is added there.
- LeviCivitaRegularityTwo requires C¹/C²/C³ metric instances but not T2Space M.
- EndomorphismFrameRegularity is metric-independent: it works at any order n
  with `ContMDiffVectorBundle n E TM I` and regularity of every frame evaluation.
- The bundled-curvature, Ricci/scalar, and Bianchi modules also require
  `T2Space M`, as does the already attributed bundled-curvature construction.
- Generic Ricci/scalar bridge theorems use a native connection with a C¹
  connection instance, `tangentMetricCompatible cov`, and `cov.torsion = 0`.
  Their needed stronger local regularity is proved from those hypotheses.
  The constructed-LC endpoint supplies these properties itself.
- Curvature regularity and the corrected raw/tensor comparison use locally C³
  fields. Ricci trace differentiation needs Y and Z locally C³; X is only
  evaluated at the point. The raw secondBianchiAux contraction comparison also
  requires X locally C³.
- Trace formulas permit any compatible local frame and finite model basis,
  evaluated at a point in its base set. No orthonormality or parallel-frame
  hypothesis is hidden in them.
- The double-contraction LC endpoint permits any finite family in a tangent
  fibre; interpreting its sums as metric traces requires further identification.
- Several declarations retain unused section instances (reported by Lean
  linters). Their literal signatures, not a stronger minimality claim, are
  authoritative.

The sign convention is unchanged:
R(X,Y)Z = ∇X∇Y Z − ∇Y∇X Z − ∇[X,Y]Z.
Ric(Y,Z) is trace(v ↦ R(v,Y)Z). The corrected curvature derivative subtracts
all three input-slot connection terms; corrected Ricci differentiation subtracts
both Ricci input-slot terms. Scalar curvature is trace of metric-raised Ricci.

## Remaining boundary

The final step is still missing: align the moving-frame Ricci/scalar
contractions with the canonical-extension sums in the double-contraction core,
including the metric-raising contraction and the necessary representative
comparisons. No theorem here asserts the actual final contracted Bianchi
identity, Einstein divergence, or an independently bundled covariant derivative
of Ricci. There is no new equality of connection objects on nondifferentiable
junk inputs, and no all-finite-orders LC regularity theorem.

## All named declarations

All names are in namespace AlmostSchur.

### MetricDualFrameTwo.lean

- `AlmostSchur.contMDiffAt_chartScalarCoordinate_three` — theorem.
- `AlmostSchur.contMDiffAt_metricDualFrame_two` — theorem.
- `AlmostSchur.contMDiffAt_section_of_inner_localFrame_two` — theorem.

### LeviCivitaRegularityTwo.lean

- `AlmostSchur.contMDiffAt_koszul_pairing_two` — theorem.
- `AlmostSchur.contMDiffAt_covariantAlong_of_metric_torsion_two` — theorem.
- `AlmostSchur.contMDiffAt_covariantDerivative_of_metric_torsion_two` — theorem.
- `AlmostSchur.contMDiffCovariantDerivative_of_metric_torsion_two` — theorem.
- `AlmostSchur.leviCivitaConnection_contMDiffCovariantDerivative_two` — instance.

### EndomorphismFrameRegularity.lean

- `AlmostSchur.contMDiffAt_endomorphism_of_localFrame` — theorem.

### CurvatureRicciRegularity.lean

- `AlmostSchur.curvatureRicciFiniteDimensional` — local helper instance.
- `AlmostSchur.contMDiffAt_curvatureAux_one` — theorem.
- `AlmostSchur.contMDiffAt_curvatureTensor_apply_one` — theorem.
- `AlmostSchur.ricciTraceEndomorphism` — def.
- `AlmostSchur.contMDiffAt_ricciTraceEndomorphism_one` — theorem.
- `AlmostSchur.contMDiffAt_ricciCurvature_apply_one` — theorem.

### RicciTraceDerivative.lean

- `AlmostSchur.ricciDerivativeFiniteDimensional` — local helper instance.
- `AlmostSchur.curvatureDirectionalDerivative` — def.
- `AlmostSchur.ricciDirectionalDerivative` — def.
- `AlmostSchur.mvfderiv_ricciCurvature_eq_contraction` — theorem.
- `AlmostSchur.ricciDirectionalDerivative_eq_contraction` — theorem.

### ScalarCurvatureTraceDerivative.lean

- `AlmostSchur.scalarDerivativeFiniteDimensional` — local helper instance.
- `AlmostSchur.ricciRaisedEndomorphism` — def.
- `AlmostSchur.inner_ricciRaisedEndomorphism` — theorem.
- `AlmostSchur.scalarCurvature_eq_trace_ricciRaisedEndomorphism` — theorem.
- `AlmostSchur.contMDiffAt_ricciRaisedEndomorphism_one` — theorem.
- `AlmostSchur.contMDiffAt_scalarCurvature_one` — theorem.
- `AlmostSchur.mvfderiv_scalarCurvature_eq_contraction` — theorem.

### LeviCivitaBianchiCore.lean

- `AlmostSchur.tangentMetricCompatible_to_curvatureVendor` — theorem.
- `AlmostSchur.manifoldMinTwo` — local helper instance.
- `AlmostSchur.manifoldMinThree` — local helper instance.
- `AlmostSchur.manifoldMinFour` — local helper instance.
- `AlmostSchur.manifoldTwoAddOne` — local helper instance.
- `AlmostSchur.manifoldThreeAddOne` — local helper instance.
- `AlmostSchur.leviCivita_curvatureDerivative_doubleContraction` — theorem.

### CurvatureDerivativeComparison.lean

- `AlmostSchur.curvatureDirectionalDerivative_eq_secondBianchiAux` — theorem.
- `AlmostSchur.ricciDirectionalDerivative_eq_secondBianchiAux_contraction` — theorem.

## Reproduction

```sh
lake build AlmostSchur.MetricDualFrameTwo AlmostSchur.LeviCivitaRegularityTwo AlmostSchur.EndomorphismFrameRegularity AlmostSchur.CurvatureRicciRegularity AlmostSchur.RicciTraceDerivative AlmostSchur.ScalarCurvatureTraceDerivative AlmostSchur.LeviCivitaBianchiCore AlmostSchur.CurvatureDerivativeComparison
python3 scripts/check-curvature-provenance.py
```
The provenance checker still passes all eight unchanged vendor files at
commit `12cebb809524d0cd185c6cd7bcb5b73d3562bce1`.
The new work imports that already attributed core; no sibling imports or new
vendor copying occurred.

Axiom audit input (feed to `lake env lean --stdin`):

```lean
import AlmostSchur.ScalarCurvatureTraceDerivative
import AlmostSchur.CurvatureDerivativeComparison
#print axioms AlmostSchur.contMDiffAt_chartScalarCoordinate_three
#print axioms AlmostSchur.contMDiffAt_metricDualFrame_two
#print axioms AlmostSchur.contMDiffAt_section_of_inner_localFrame_two
#print axioms AlmostSchur.contMDiffAt_koszul_pairing_two
#print axioms AlmostSchur.contMDiffAt_covariantAlong_of_metric_torsion_two
#print axioms AlmostSchur.contMDiffAt_covariantDerivative_of_metric_torsion_two
#print axioms AlmostSchur.contMDiffCovariantDerivative_of_metric_torsion_two
#print axioms AlmostSchur.leviCivitaConnection_contMDiffCovariantDerivative_two
#print axioms AlmostSchur.contMDiffAt_endomorphism_of_localFrame
#print axioms AlmostSchur.curvatureRicciFiniteDimensional
#print axioms AlmostSchur.contMDiffAt_curvatureAux_one
#print axioms AlmostSchur.contMDiffAt_curvatureTensor_apply_one
#print axioms AlmostSchur.ricciTraceEndomorphism
#print axioms AlmostSchur.contMDiffAt_ricciTraceEndomorphism_one
#print axioms AlmostSchur.contMDiffAt_ricciCurvature_apply_one
#print axioms AlmostSchur.ricciDerivativeFiniteDimensional
#print axioms AlmostSchur.curvatureDirectionalDerivative
#print axioms AlmostSchur.ricciDirectionalDerivative
#print axioms AlmostSchur.mvfderiv_ricciCurvature_eq_contraction
#print axioms AlmostSchur.ricciDirectionalDerivative_eq_contraction
#print axioms AlmostSchur.scalarDerivativeFiniteDimensional
#print axioms AlmostSchur.ricciRaisedEndomorphism
#print axioms AlmostSchur.inner_ricciRaisedEndomorphism
#print axioms AlmostSchur.scalarCurvature_eq_trace_ricciRaisedEndomorphism
#print axioms AlmostSchur.contMDiffAt_ricciRaisedEndomorphism_one
#print axioms AlmostSchur.contMDiffAt_scalarCurvature_one
#print axioms AlmostSchur.mvfderiv_scalarCurvature_eq_contraction
#print axioms AlmostSchur.tangentMetricCompatible_to_curvatureVendor
#print axioms AlmostSchur.manifoldMinTwo
#print axioms AlmostSchur.manifoldMinThree
#print axioms AlmostSchur.manifoldMinFour
#print axioms AlmostSchur.manifoldTwoAddOne
#print axioms AlmostSchur.manifoldThreeAddOne
#print axioms AlmostSchur.leviCivita_curvatureDerivative_doubleContraction
#print axioms AlmostSchur.curvatureDirectionalDerivative_eq_secondBianchiAux
#print axioms AlmostSchur.ricciDirectionalDerivative_eq_secondBianchiAux_contraction
```
