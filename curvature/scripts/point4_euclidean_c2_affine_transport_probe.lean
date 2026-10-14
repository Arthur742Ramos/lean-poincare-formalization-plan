import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanC2AffineTransport

-- Source-only whole-type/empty-domain/actual-axiom probe, native qualification pending.
open scoped Topology
open RicciFlow.AnalyticPDE

abbrev ExpectedC2ValueFrechetDerivative :=
  ∀ {n : ℕ} (D : EuclideanBoundedC2Data n) (x : Fin n → ℝ),
    HasFDerivAt D.value (D.affineValueGradient x) x

def c2ValueFrechetDerivativeFullSignatureAssignment : ExpectedC2ValueFrechetDerivative :=
  @EuclideanBoundedC2Data.hasFDerivAt_affineValueGradient

abbrev ExpectedC2FirstFrechetDerivative :=
  ∀ {n : ℕ} (D : EuclideanBoundedC2Data n) (l : Fin n) (x : Fin n → ℝ),
    HasFDerivAt (D.first l) (D.affineFirstGradient l x) x

def c2FirstFrechetDerivativeFullSignatureAssignment : ExpectedC2FirstFrechetDerivative :=
  @EuclideanBoundedC2Data.hasFDerivAt_affineFirstGradient

-- No positive dimension or selected index is needed for the actual value derivative.
example (D : EuclideanBoundedC2Data 0) (x : Fin 0 → ℝ) :
    HasFDerivAt D.value (D.affineValueGradient x) x :=
  D.hasFDerivAt_affineValueGradient x

set_option pp.universes false
set_option format.width 200
#check @EuclideanBoundedC2Data.hasFDerivAt_affineValueGradient
#check @EuclideanBoundedC2Data.hasFDerivAt_affineFirstGradient

-- Exactly the two derived scalar Frechet theorem declarations.
#print axioms RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.hasFDerivAt_affineValueGradient
#print axioms RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.hasFDerivAt_affineFirstGradient
