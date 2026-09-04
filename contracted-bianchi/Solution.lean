import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ContractedBianchi

/-!
# Solution: contracted second Bianchi identity

The proof is the finite-dimensional contraction of the cyclic second Bianchi identity.  It uses
the displayed metric skew-symmetry and pair-interchange equations of the covariant derivative of
curvature; no divergence or Einstein-tensor conclusion is assumed.
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
  unfold scalarCurvatureDerivative ricciDivergence ricciDerivative
  have hsum :
      (∑ x, ∑ x_1, C.derivative w (b x_1) (b x) (b x) (b x_1)) +
          ∑ x, ∑ x_1, C.derivative (b x_1) (b x) w (b x) (b x_1) +
            ∑ x, ∑ x_1, C.derivative (b x) w (b x_1) (b x) (b x_1) = 0 := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i hi => ?_
    refine Finset.sum_eq_zero fun k hk => ?_
    simpa using C.second_bianchi w (b k) (b i) (b i) (b k)
  have hsecond :
      (∑ x, ∑ x_1, C.derivative (b x_1) (b x) w (b x) (b x_1)) =
        -∑ x, ∑ x_1, C.derivative (b x) (b x_1) (b x) w (b x_1) := by
    have hB :
        (∑ x, ∑ x_1, C.derivative (b x_1) (b x) w (b x) (b x_1)) =
          ∑ x, ∑ x_1, -C.derivative (b x) (b x_1) (b x) w (b x_1) := by
      calc
        (∑ x, ∑ x_1, C.derivative (b x_1) (b x) w (b x) (b x_1)) =
            ∑ x, ∑ x_1, C.derivative (b x) (b x_1) w (b x_1) (b x) := by
              rw [Finset.sum_comm]
        _ = ∑ x, ∑ x_1, -C.derivative (b x) w (b x_1) (b x_1) (b x) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro k hk
              rw [C.derivative_first_pair_skew]
        _ = ∑ x, ∑ x_1, -C.derivative (b x) (b x_1) (b x) w (b x_1) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro k hk
              exact congrArg Neg.neg
                (C.derivative_pair_interchange (b i) w (b k) (b k) (b i))
    simpa only [Finset.sum_neg_distrib] using hB
  have hthird :
      (∑ x, ∑ x_1, C.derivative (b x) w (b x_1) (b x) (b x_1)) =
        -∑ x, ∑ x_1, C.derivative (b x) (b x_1) (b x) w (b x_1) := by
    have hpoint : ∀ i k,
        C.derivative (b i) (b k) (b i) w (b k) =
          -C.derivative (b i) w (b k) (b i) (b k) := by
      intro i k
      rw [C.derivative_pair_interchange, C.derivative_last_pair_skew]
    have hC :
        (∑ x, ∑ x_1, C.derivative (b x) w (b x_1) (b x) (b x_1)) =
          ∑ x, ∑ x_1, -C.derivative (b x) (b x_1) (b x) w (b x_1) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      refine Finset.sum_congr rfl ?_
      intro k hk
      have h := congrArg (fun z : ℝ => -z) (hpoint i k)
      have h' : -C.derivative (b i) (b k) (b i) w (b k) =
          C.derivative (b i) w (b k) (b i) (b k) := by
        simpa using h
      exact h'.symm
    simpa only [Finset.sum_neg_distrib] using hC
  linarith [hsum, hsecond, hthird]

theorem einsteinTensorDivergence
    (C : CurvatureDerivativeData E)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (w : E) :
    einsteinDivergence C b w = 0 := by
  unfold einsteinDivergence
  rw [contractedSecondBianchi C b w]
  ring

end ContractedBianchi
