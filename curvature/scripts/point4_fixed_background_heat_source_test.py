#!/usr/bin/env python3
"""Source/provenance regression only; this is not a Lean proof check."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(Path(__file__).resolve().parent))
from point4_scan import strip_comments

module = ROOT / "curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatFixedBackgroundProducer.lean"
source = module.read_text()
code = "\n".join(strip_comments(source))
assert not code.lstrip().startswith("module"), "Legacy direct import requires a legacy producer"
assert "g₀.toRiemannianMetric" in code
assert "(g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)" in code
assert "[RiemannianBundle" not in code, "No ambient metric input permitted"
assert "[ContMDiffCovariantDerivative" not in code, "No supplied regularity witnesses"
assert "[ContMDiffVectorBundle" not in code, "Tangent regularity must be derived"
assert "ContMDiffVectorBundle.of_le (n := ∞)" in code
assert "exists_contMDiffAffineConnection_two" in code
assert "contMDiffCovariantDerivative_covariantTwoTensor_two" in code
assert "contMDiffCovariantDerivative_covariantThreeTensor_one" in code
assert "contDiffOn_actualTensorHeatCoefficients" in code
assert "CovariantDerivative.contDiffOn_actualTensorHeatCoefficients" not in code
assert "local instance fixedBackgroundThreeFiber" not in code
assert code.index("letI : RiemannianBundle TM") < code.index("letI : ∀ x : M, NormedAddCommGroup (T₃ x)")
assert "tensorCoordinatePrincipalNormedAddCommGroup" in code
assert "tensorCoordinateFirstCoefficientNormedAddCommGroup" in code
assert "tensorCoordinateZeroNormedAddCommGroup" in code
assert "exists_radius_actualLocalTensorHeatUnitBall_zeroTrace" in code
assert "localTensorHeatPrincipalCoefficient (I := I) p e b" in code
assert "localTensorHeatPrincipalCoefficient (I := I) cov" not in code
assert "localTensorHeatFirstCoefficient (I := I) cov p e b" in code
assert "localTensorHeatZeroCoefficient (I := I) cov p e b" in code
assert "FieldsAgreeOnUnitBall" in code and "initialTraceL" in code
assert "ParabolicC0AlphaBanach" in code and "FiniteParabolicC2AlphaBanach" in code
assert "[I.Boundaryless]" in code, "Do not hide the model-boundaryless restriction"
assert "intrinsicLocalExistenceUniquenessFamily_pointFour" not in code
metadata = (ROOT / "curvature/formalization.yaml").read_text()
assert "tree/99aa49484f8decc5a6344591d5e319011ebea73b/curvature" in metadata
assert "TensorHeatFixedBackgroundProducer.lean" in metadata
print("Source scope/provenance checks passed; Lean elaboration and axiom checking are separate gates")
