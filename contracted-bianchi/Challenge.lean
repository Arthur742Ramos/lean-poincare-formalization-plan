import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Contracted second Bianchi identity

This Challenge presents the Riemannian tensor interface used by the contracted second Bianchi
identity.  `curvature` and `derivative` are nested `LinearMap`s, so the curvature and its
covariant derivative are genuine multilinear tensors rather than arbitrary scalar-valued
families.  The displayed definitions are the usual trace contractions in an orthonormal basis.

The field `second_bianchi` is the cyclic identity for the covariant derivative of curvature;
`derivative_last_pair_skew` and `derivative_pair_interchange` are the metric-compatibility and
curvature-pair symmetries inherited by that derivative.  The selected conclusions are the
contracted identity `div Ric = 1/2 d scal` and the resulting divergence-free Einstein tensor.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace ContractedBianchi

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev Tensor4 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ

abbrev Tensor5 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ

structure CurvatureDerivativeData (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] where
  curvature : Tensor4 E
  derivative : Tensor5 E
  curvature_first_pair_skew : ∀ a b c d,
    curvature a b c d = -curvature b a c d
  curvature_last_pair_skew : ∀ a b c d,
    curvature a b c d = -curvature a b d c
  curvature_pair_interchange : ∀ a b c d,
    curvature a b c d = curvature c d a b
  derivative_first_pair_skew : ∀ p a b c d,
    derivative p a b c d = -derivative p b a c d
  derivative_last_pair_skew : ∀ p a b c d,
    derivative p a b c d = -derivative p a b d c
  derivative_pair_interchange : ∀ p a b c d,
    derivative p a b c d = derivative p c d a b
  second_bianchi : ∀ p a b c d,
    derivative p a b c d + derivative a b p c d + derivative b p a c d = 0

noncomputable def ricci (C : CurvatureDerivativeData E)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (u w : E) : ℝ :=
  ∑ k, C.curvature (b k) u w (b k)

noncomputable def scalarCurvature (C : CurvatureDerivativeData E)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) : ℝ :=
  ∑ i, ricci C b (b i) (b i)

noncomputable def ricciDerivative (C : CurvatureDerivativeData E)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (p u w : E) : ℝ :=
  ∑ k, C.derivative p (b k) u w (b k)

noncomputable def scalarCurvatureDerivative (C : CurvatureDerivativeData E)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (p : E) : ℝ :=
  ∑ i, ricciDerivative C b p (b i) (b i)

noncomputable def ricciDivergence (C : CurvatureDerivativeData E)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (w : E) : ℝ :=
  ∑ i, ricciDerivative C b (b i) (b i) w

noncomputable def einsteinTensor (C : CurvatureDerivativeData E)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (u w : E) : ℝ :=
  ricci C b u w - (1 / 2 : ℝ) * scalarCurvature C b * inner ℝ u w

noncomputable def einsteinDivergence (C : CurvatureDerivativeData E)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (w : E) : ℝ :=
  ricciDivergence C b w - (1 / 2 : ℝ) * scalarCurvatureDerivative C b w

theorem contractedSecondBianchi
    (C : CurvatureDerivativeData E)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (w : E) :
    scalarCurvatureDerivative C b w = 2 * ricciDivergence C b w := by
  sorry

theorem einsteinTensorDivergence
    (C : CurvatureDerivativeData E)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (w : E) :
    einsteinDivergence C b w = 0 := by
  sorry

end ContractedBianchi
