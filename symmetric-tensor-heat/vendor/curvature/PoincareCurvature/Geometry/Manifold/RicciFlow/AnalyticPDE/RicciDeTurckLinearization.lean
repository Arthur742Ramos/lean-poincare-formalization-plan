/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.GenuineRicciDeTurckNemytskii

/-!
# Linearization of the Ricci–DeTurck operator: principal part

This file computes the principal part of the Fréchet derivative of the
genuine Ricci–DeTurck fiber map `Φ_RD : Jet2 d d → (Fin d → Fin d → ℝ)`.

## Mathematical content

The Ricci–DeTurck operator is `Φ_RD(g) = −2 Ric(g) + L_W g`, where `W` is the
DeTurck vector field. Its linearization at a metric `g` in the direction `h`
is, by the DeTurck trick,

  `DΦ_RD[g](h)_{ij} = g^{pq} ∂²_{pq} h_{ij} + (first-order in h) + (zeroth-order in h)`,

i.e. the principal part is the Lichnerowicz Laplacian's second-order piece:
contraction of the Hessian of `h` with the inverse metric. The "bad"
second-order terms of the linearized Ricci tensor
(`−g^{pq}(∂²_{pi}h_{qj} + ∂²_{pj}h_{qi} − ∂²_{ij}h_{pq})`) are exactly cancelled
by the second-order terms of the linearized DeTurck correction. This is what
makes Ricci–DeTurck flow strictly parabolic.

## Results

* `phiRDPrincipalCLM`: the explicit principal-part continuous linear map
  `δj ↦ fun i j_ => ∑ p q, g^{pq} * (δj.deriv2 p q) i j_`.
* `phiRDMatrixDeriv_eq_phiRDPrincipalCLM`: for a pure second-jet direction
  `δj` (vanishing 0-jet and 1-jet, symmetric 2-jet), the Fréchet derivative
  `DΦ_RD[j]` agrees with the principal part.  The proof goes through the
  affine curve `c(t) = j + t • δj`: along it every building block of `Φ_RD`
  is affine in `t` (0-jet and 1-jet coefficients are frozen), so the curve
  derivative is the explicit second-jet-linear part; the DeTurck cancellation
  is then pure finite-sum algebra (`deturckPrincipalPart_identity`).
* `phiRDPrincipal_stronglyParabolic`: the principal part sends a rank-one
  Hessian `ξ ⊗ ξ ⊗ w` to `q • w` with `q = g^{pq}ξ_pξ_q > 0` — the exact
  strong-ellipticity interface of
  `frozenLocalTensorHeatPrincipalCoefficient_stronglyElliptic`.

## Relation to the tensor-heat parametrix (Phase-2c2)

`exists_localizedTensorHeatSolutionL` needs a `TensorHeatLocalizedCoefficientData`
whose principal coefficient matches `frozenLocalTensorHeatPrincipalCoefficient`
at the chart center.  This file proves the *analytic* half: the linearized
Ricci–DeTurck operator's principal part is contraction with `g⁻¹`, which is
the same form as `movingFramePrincipalCoefficient`.  The remaining Phase-2c2
work is:
  (a) building the full `TensorHeatLocalizedCoefficientData` (first- and
      zeroth-order coefficients from the lower-order part of the linearization,
      with Lipschitz bounds from `C^{2,α}` metric regularity);
  (b) the chart bridge identifying `localFrameInverseGramMatrixInChart` with
      `invMetricOfJet` in coordinates;
  (c) promoting the frozen (constant-coefficient) match to `x`-dependent
      coefficients.

No `sorry`, no `admit`, no axioms.
-/

open Matrix Finset
open scoped Topology

namespace RicciFlow.AnalyticPDE
namespace GenuinePhiRD

variable {d : ℕ}
variable (Γbg : Fin d → Fin d → Fin d → ℝ)

/-! ## 1. The explicit principal-part linear map -/

/-- The second-jet component as a continuous linear map. -/
noncomputable def deriv2CompCLM (p q i j_ : Fin d) : (Jet2 d d) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun δj => ((δj.deriv2 p q) i j_)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1
    (by
      intro δj
      rw [one_mul]
      have h1 : ‖((δj.deriv2 p q) i j_)‖ ≤ ‖δj.deriv2 p q‖ := by
        calc ‖((δj.deriv2 p q) i j_)‖ ≤ ∑ j' : Fin d, ‖((δj.deriv2 p q) i j')‖ := by
              apply Finset.single_le_sum _ (Finset.mem_univ j_)
              intro _ _; exact norm_nonneg _
          _ ≤ ∑ i' : Fin d, ∑ j' : Fin d, ‖((δj.deriv2 p q) i' j')‖ := by
              apply Finset.single_le_sum _ (Finset.mem_univ i)
              intro _ _; exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
          _ = ‖δj.deriv2 p q‖ := rfl
      have h2 : ‖δj.deriv2 p q‖ ≤ ‖δj‖ := by
        have h_eq := Jet2.jet2_norm_eq (d := d) (j := δj)
        rw [h_eq]
        have h_le1 : ‖δj.deriv2 p q‖ ≤ ∑ k' : Fin d, ∑ l' : Fin d, ‖δj.deriv2 k' l'‖ := by
          calc ‖δj.deriv2 p q‖ ≤ ∑ l' : Fin d, ‖δj.deriv2 p l'‖ := by
                apply Finset.single_le_sum _ (Finset.mem_univ q)
                intro _ _; exact norm_nonneg _
            _ ≤ ∑ k' : Fin d, ∑ l' : Fin d, ‖δj.deriv2 k' l'‖ := by
                apply Finset.single_le_sum _ (Finset.mem_univ p)
                intro _ _; exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
        have h_nonneg : 0 ≤ ‖δj.val‖ + ∑ i : Fin d, ‖δj.deriv1 i‖ :=
          add_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
        linarith
      exact le_trans h1 h2)

@[simp] theorem deriv2CompCLM_apply (p q i j_ : Fin d) (δj : Jet2 d d) :
    deriv2CompCLM (d := d) p q i j_ δj = ((δj.deriv2 p q) i j_) := rfl

/-- The principal part of the linearized Ricci–DeTurck operator: contraction
of the second-jet direction with the inverse metric. -/
noncomputable def phiRDPrincipalCLM (j : Jet2 d d) :
    (Jet2 d d) →L[ℝ] (Fin d → Fin d → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j_ =>
    ∑ p : Fin d, ∑ q : Fin d,
      (invMetricOfJet (d := d) j p q) • (deriv2CompCLM (d := d) p q i j_)

@[simp] theorem phiRDPrincipalCLM_apply (j δj : Jet2 d d) (i j_ : Fin d) :
    (phiRDPrincipalCLM (d := d) j δj) i j_ =
      ∑ p : Fin d, ∑ q : Fin d,
        (invMetricOfJet (d := d) j p q) * ((δj.deriv2 p q) i j_) := by
  simp [phiRDPrincipalCLM, ContinuousLinearMap.pi_apply, smul_eq_mul]

/-- A pure second-jet direction from a rank-one Hessian `ξ ⊗ ξ ⊗ w`. -/
noncomputable def rankOneJet2 (ξ : Fin d → ℝ) (w : Fin d → Fin d → ℝ) :
    Jet2 d d :=
  ⟨0, 0, fun a b => (ξ a * ξ b) • w⟩

theorem rankOneJet2_deriv2 (ξ : Fin d → ℝ) (w : Fin d → Fin d → ℝ)
    (a b : Fin d) :
    (rankOneJet2 (d := d) ξ w).deriv2 a b = (ξ a * ξ b) • w := rfl

/-- The principal part on a rank-one Hessian direction is scalar
multiplication by the inverse-metric quadratic form — the principal symbol. -/
theorem phiRDPrincipalCLM_rankOne (j : Jet2 d d)
    (ξ : Fin d → ℝ) (w : Fin d → Fin d → ℝ) :
    phiRDPrincipalCLM (d := d) j (rankOneJet2 (d := d) ξ w) =
      (∑ p : Fin d, ∑ q : Fin d,
        (invMetricOfJet (d := d) j p q) * (ξ p * ξ q)) • w := by
  funext i j_
  rw [phiRDPrincipalCLM_apply]
  simp only [rankOneJet2_deriv2, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have h : ∀ x x_1 : Fin d,
      (invMetricOfJet (d := d) j x x_1) * (ξ x * (ξ x_1 * w i j_))
      = ((invMetricOfJet (d := d) j x x_1) * (ξ x * ξ x_1)) * w i j_ := by
    intro x x_1; ring
  simp only [h]
  have inner : ∀ x : Fin d,
      (∑ x_1 : Fin d, ((invMetricOfJet (d := d) j x x_1) * (ξ x * ξ x_1)) * w i j_)
      = (∑ x_1 : Fin d, (invMetricOfJet (d := d) j x x_1) * (ξ x * ξ x_1)) * w i j_ := by
    intro x
    rw [Finset.sum_mul]
  simp only [inner]
  rw [Finset.sum_mul]

/-! ## 2. Metric/inverse-metric contraction identities -/

/-- The inverse metric is symmetric for a symmetric metric, via `M⁻¹`. -/
theorem invMetricOfJet_symm (j : Jet2 d d)
    (hj : j.val.det ≠ 0) (hgsymm : ∀ a b : Fin d, j.val a b = j.val b a)
    (p q : Fin d) :
    invMetricOfJet (d := d) j p q = invMetricOfJet (d := d) j q p := by
  have hMinv : ∀ a b : Fin d, (j.val)⁻¹ a b = invMetricOfJet (d := d) j a b := by
    intro a b
    unfold invMetricOfJet
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  have hsymm : (j.val)ᵀ = j.val := by
    ext a b
    rw [Matrix.transpose_apply]
    exact hgsymm b a
  have hinv_symm : (j.val)⁻¹ᵀ = (j.val)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hsymm]
  calc invMetricOfJet (d := d) j p q
      = (j.val)⁻¹ p q := (hMinv p q).symm
    _ = (j.val)⁻¹ᵀ q p := by rw [Matrix.transpose_apply]
    _ = (j.val)⁻¹ q p := by rw [hinv_symm]
    _ = invMetricOfJet (d := d) j q p := hMinv q p

/-- Contraction of the metric against the inverse metric is the identity.
This is Cramer's rule via the adjugate. -/
theorem invMetricOfJet_contract (j : Jet2 d d)
    (hj : j.val.det ≠ 0) (hgsymm : ∀ a b : Fin d, j.val a b = j.val b a)
    (a b : Fin d) :
    ∑ k : Fin d, (j.val k a) * (invMetricOfJet (d := d) j k b)
      = if a = b then 1 else 0 := by
  have hdet : (j.val.det)⁻¹ * j.val.det = 1 := inv_mul_cancel₀ hj
  have hmul : j.val * j.val.adjugate = j.val.det • (1 : Matrix (Fin d) (Fin d) ℝ) :=
    Matrix.mul_adjugate j.val
  have hentry : ∀ x y : Fin d,
      ∑ k : Fin d, (j.val x k) * (j.val.adjugate k y)
        = j.val.det * (if x = y then 1 else 0) := by
    intro x y
    have h := congrFun (congrFun hmul x) y
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul] at h
    exact h
  calc ∑ k : Fin d, (j.val k a) * (invMetricOfJet (d := d) j k b)
      = ∑ k : Fin d, (j.val a k) * ((j.val.det)⁻¹ * j.val.adjugate k b) := by
        apply Finset.sum_congr rfl; intro k _
        rw [hgsymm k a]; unfold invMetricOfJet; ring
    _ = (j.val.det)⁻¹ * ∑ k : Fin d, (j.val a k) * (j.val.adjugate k b) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    _ = (j.val.det)⁻¹ * (j.val.det * (if a = b then 1 else 0)) := by
        rw [hentry a b]
    _ = if a = b then 1 else 0 := by
        by_cases hab : a = b <;> simp [hab, hdet, mul_assoc]

/-- Abstract contraction: `∑ k, g_{k,c} (∑ l, g^{kl} X_l) = X_c`. -/
theorem sum_metric_invMetric_contract
    (g gInv : Fin d → Fin d → ℝ)
    (hinv : ∀ a b : Fin d, ∑ k : Fin d, g k a * gInv k b = if a = b then 1 else 0)
    (X : Fin d → ℝ) (c : Fin d) :
    ∑ k : Fin d, g k c * (∑ l : Fin d, gInv k l * X l) = X c := by
  calc ∑ k : Fin d, g k c * (∑ l : Fin d, gInv k l * X l)
      = ∑ k : Fin d, ∑ l : Fin d, (g k c * gInv k l) * X l := by
        apply Finset.sum_congr rfl; intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro l _; ring
    _ = ∑ l : Fin d, ∑ k : Fin d, (g k c * gInv k l) * X l := Finset.sum_comm
    _ = ∑ l : Fin d, (if c = l then X l else 0) := by
        apply Finset.sum_congr rfl; intro l _
        rw [← Finset.sum_mul, hinv c l]
        by_cases hcl : c = l <;> simp [hcl]
    _ = X c := by rw [Finset.sum_ite_eq]; simp

/-- Triple-sum contraction through the metric inverse. -/
theorem sum_contract_triple
    (g gInv : Fin d → Fin d → ℝ)
    (hinv : ∀ a b : Fin d, ∑ k : Fin d, g k a * gInv k b = if a = b then 1 else 0)
    (X : Fin d → Fin d → Fin d → ℝ) (c : Fin d) :
    (∑ k : Fin d, g k c * (∑ a : Fin d, ∑ b : Fin d, ∑ l : Fin d,
      gInv a b * (gInv k l * X a b l)))
    = ∑ a : Fin d, ∑ b : Fin d, gInv a b * X a b c := by
  have step1 : ∀ k : Fin d,
      g k c * (∑ a : Fin d, ∑ b : Fin d, ∑ l : Fin d, gInv a b * (gInv k l * X a b l))
      = ∑ a : Fin d, ∑ b : Fin d,
        g k c * (∑ l : Fin d, gInv a b * (gInv k l * X a b l)) := by
    intro k
    simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun k _ => step1 k), Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  have step2 : ∀ k : Fin d,
      g k c * (∑ l : Fin d, gInv a b * (gInv k l * X a b l))
      = gInv a b * (g k c * (∑ l : Fin d, gInv k l * X a b l)) := by
    intro k
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro l _
    ring
  rw [Finset.sum_congr rfl (fun k _ => step2 k), ← Finset.mul_sum]
  congr 1
  exact sum_metric_invMetric_contract (d := d) g gInv hinv (fun l => X a b l) c

/-- The DeTurck-correction triple sum contracts through the metric inverse. -/
theorem contract_deturck_correction
    (gInv g : Fin d → Fin d → ℝ)
    (hinv : ∀ a b : Fin d, ∑ k : Fin d, g k a * gInv k b = if a = b then 1 else 0)
    (X : Fin d → Fin d → Fin d → ℝ) (c : Fin d) :
    (∑ k : Fin d, g k c * (∑ a : Fin d, ∑ b : Fin d, gInv a b *
      ((1/2) * ∑ l : Fin d, gInv k l * X a b l)))
    = (1/2) * ∑ a : Fin d, ∑ b : Fin d, gInv a b * X a b c := by
  have hmassage : ∀ k : Fin d,
      g k c * (∑ a : Fin d, ∑ b : Fin d, gInv a b *
        ((1/2) * ∑ l : Fin d, gInv k l * X a b l))
      = (1/2) * (g k c * (∑ a : Fin d, ∑ b : Fin d, ∑ l : Fin d,
        gInv a b * (gInv k l * X a b l))) := by
    intro k
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro l _
    ring
  rw [Finset.sum_congr rfl (fun k _ => hmassage k)]
  rw [← Finset.mul_sum, sum_contract_triple (d := d) g gInv hinv X c]

/-! ## 3. The DeTurck cancellation: pure finite-sum algebra -/

/-- Reindexing a double sum by swapping the indices. -/
theorem sum_swap (F : Fin d → Fin d → ℝ) :
    ∑ k : Fin d, ∑ l : Fin d, F k l = ∑ k : Fin d, ∑ l : Fin d, F l k :=
  Finset.sum_comm

/-- **The DeTurck cancellation identity.** -/
theorem deturckPrincipalPart_identity
    (gInv g : Fin d → Fin d → ℝ) (S : Fin d → Fin d → Fin d → Fin d → ℝ)
    (hgInv : ∀ p q : Fin d, gInv p q = gInv q p)
    (hinv : ∀ a b : Fin d, ∑ k : Fin d, g k a * gInv k b = if a = b then 1 else 0)
    (hS12 : ∀ a b c e : Fin d, S a b c e = S b a c e)
    (hS34 : ∀ a b c e : Fin d, S a b c e = S a b e c)
    (i j_ : Fin d) :
    -2 * (∑ k : Fin d, ((1/2) * ∑ l : Fin d, gInv k l *
        ((S k i j_ l + S k j_ i l - S k l i j_)
          - (S j_ k i l + S j_ i k l - S j_ l i k))))
      + ((1/2) * ∑ a : Fin d, ∑ b : Fin d, gInv a b *
          ((S i a b j_ + S i b a j_ - S i j_ a b)
            + (S j_ a b i + S j_ b a i - S j_ i a b)))
      = ∑ p : Fin d, ∑ q : Fin d, gInv p q * S p q i j_ := by
  have hR : -2 * (∑ k : Fin d, ((1/2) * ∑ l : Fin d, gInv k l *
      ((S k i j_ l + S k j_ i l - S k l i j_)
        - (S j_ k i l + S j_ i k l - S j_ l i k))))
      = -(∑ k : Fin d, ∑ l : Fin d, gInv k l * (S k i j_ l + S k j_ i l - S k l i j_))
        + (∑ k : Fin d, ∑ l : Fin d, gInv k l * (S j_ k i l + S j_ i k l - S j_ l i k)) := by
    have hRHS : (-(∑ k : Fin d, ∑ l : Fin d, gInv k l * (S k i j_ l + S k j_ i l - S k l i j_))
        + (∑ k : Fin d, ∑ l : Fin d, gInv k l * (S j_ k i l + S j_ i k l - S j_ l i k)))
        = ∑ k : Fin d, (-(∑ l : Fin d, gInv k l * (S k i j_ l + S k j_ i l - S k l i j_))
          + (∑ l : Fin d, gInv k l * (S j_ k i l + S j_ i k l - S j_ l i k))) := by
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    rw [hRHS, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.mul_sum, Finset.mul_sum]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro l _
    ring
  have G1 : (∑ k : Fin d, ∑ l : Fin d, gInv k l * (S k i j_ l))
      = (∑ a : Fin d, ∑ b : Fin d, gInv a b * (S i a b j_)) := by
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    rw [hS12 k i j_ l, hS34 i k j_ l]
  have H1 : (∑ a : Fin d, ∑ b : Fin d, gInv a b * (S i b a j_))
      = (∑ a : Fin d, ∑ b : Fin d, gInv a b * (S i a b j_)) := by
    rw [sum_swap (d := d) (fun a b => gInv a b * (S i b a j_))]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [hgInv b a]
  have G2 : (∑ k : Fin d, ∑ l : Fin d, gInv k l * (S k j_ i l))
      = (∑ a : Fin d, ∑ b : Fin d, gInv a b * (S j_ a b i)) := by
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    rw [hS12 k j_ i l, hS34 j_ k i l]
  have H2 : (∑ a : Fin d, ∑ b : Fin d, gInv a b * (S j_ b a i))
      = (∑ a : Fin d, ∑ b : Fin d, gInv a b * (S j_ a b i)) := by
    rw [sum_swap (d := d) (fun a b => gInv a b * (S j_ b a i))]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [hgInv b a]
  have G3 : (∑ k : Fin d, ∑ l : Fin d, gInv k l * (S j_ i k l))
      = (∑ a : Fin d, ∑ b : Fin d, gInv a b * (S i j_ a b)) := by
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    rw [hS12 j_ i k l]
  have G3' : (∑ a : Fin d, ∑ b : Fin d, gInv a b * (S j_ i a b))
      = (∑ a : Fin d, ∑ b : Fin d, gInv a b * (S i j_ a b)) := by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [hS12 j_ i a b]
  have G4 : (∑ k : Fin d, ∑ l : Fin d, gInv k l * (S j_ k i l))
      = (∑ k : Fin d, ∑ l : Fin d, gInv k l * (S j_ l i k)) := by
    rw [sum_swap (d := d) (fun k l => gInv k l * (S j_ l i k))]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    rw [hgInv l k]
  -- Split the combined sums into atoms.
  have splitA : (∑ k : Fin d, ∑ l : Fin d, gInv k l * (S k i j_ l + S k j_ i l - S k l i j_))
      = (∑ k : Fin d, ∑ l : Fin d, gInv k l * S k i j_ l)
        + (∑ k : Fin d, ∑ l : Fin d, gInv k l * S k j_ i l)
        - (∑ k : Fin d, ∑ l : Fin d, gInv k l * S k l i j_) := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have splitB : (∑ k : Fin d, ∑ l : Fin d, gInv k l * (S j_ k i l + S j_ i k l - S j_ l i k))
      = (∑ k : Fin d, ∑ l : Fin d, gInv k l * S j_ k i l)
        + (∑ k : Fin d, ∑ l : Fin d, gInv k l * S j_ i k l)
        - (∑ k : Fin d, ∑ l : Fin d, gInv k l * S j_ l i k) := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have splitC : (∑ a : Fin d, ∑ b : Fin d, gInv a b *
        ((S i a b j_ + S i b a j_ - S i j_ a b) + (S j_ a b i + S j_ b a i - S j_ i a b)))
      = ((∑ a : Fin d, ∑ b : Fin d, gInv a b * S i a b j_)
          + (∑ a : Fin d, ∑ b : Fin d, gInv a b * S i b a j_)
          - (∑ a : Fin d, ∑ b : Fin d, gInv a b * S i j_ a b))
        + ((∑ a : Fin d, ∑ b : Fin d, gInv a b * S j_ a b i)
          + (∑ a : Fin d, ∑ b : Fin d, gInv a b * S j_ b a i)
          - (∑ a : Fin d, ∑ b : Fin d, gInv a b * S j_ i a b)) := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hT3 : (∑ k : Fin d, ∑ l : Fin d, gInv k l * (S k l i j_))
      = (∑ p : Fin d, ∑ q : Fin d, gInv p q * S p q i j_) := rfl
  rw [hR, splitA, splitB, splitC]
  linear_combination -G1 + (1/2 : ℝ) * H1 - G2 + (1/2 : ℝ) * H2 + G4 + G3
    - (1/2 : ℝ) * G3' + hT3

/-! ## 4. Second-jet-linear parts of the building blocks -/

/-- The second-jet-linear part of `∂_m Γ^k_ij` in the direction `δj`. -/
noncomputable def dChristoffel2 (j δj : Jet2 d d) (m k i j_ : Fin d) : ℝ :=
  (1/2) * ∑ l : Fin d, (invMetricOfJet (d := d) j k l) *
    (deriv2Comp (d := d) δj m i j_ l + deriv2Comp (d := d) δj m j_ i l
      - deriv2Comp (d := d) δj m l i j_)

/-- The second-jet-linear part of `R_{ij}` in the direction `δj`. -/
noncomputable def dRicci2 (j δj : Jet2 d d) (i j_ : Fin d) : ℝ :=
  ∑ k : Fin d, (dChristoffel2 (d := d) j δj k k i j_
    - dChristoffel2 (d := d) j δj j_ k i k)

/-- The second-jet-linear part of `∂_m W^k` in the direction `δj`. -/
noncomputable def dDeTurckW2 (j δj : Jet2 d d) (m k : Fin d) : ℝ :=
  ∑ a : Fin d, ∑ b : Fin d,
    (invMetricOfJet (d := d) j a b) * (dChristoffel2 (d := d) j δj m k a b)

/-- The second-jet-linear part of `(L_W g)_{ij}` in the direction `δj`. -/
noncomputable def dCorrection2 (j δj : Jet2 d d) (i j_ : Fin d) : ℝ :=
  ∑ k : Fin d, ((valComp (d := d) j k j_) * (dDeTurckW2 (d := d) j δj i k)
    + (valComp (d := d) j i k) * (dDeTurckW2 (d := d) j δj j_ k))

/-! ## 5. Freezing the 0- and 1-jet along the affine curve -/

theorem jet2_add_smul_val (j δj : Jet2 d d) (t : ℝ) :
    (j + t • δj).val = j.val + t • δj.val := rfl

theorem jet2_add_smul_deriv1 (j δj : Jet2 d d) (t : ℝ) :
    (j + t • δj).deriv1 = j.deriv1 + t • δj.deriv1 := rfl

theorem invMetricOfJet_pureSecondJet (j δj : Jet2 d d)
    (hval : δj.val = 0) (t : ℝ) (p q : Fin d) :
    invMetricOfJet (d := d) (j + t • δj) p q = invMetricOfJet (d := d) j p q := by
  have hJ : (j + t • δj).val = j.val := by
    rw [jet2_add_smul_val, hval, smul_zero, add_zero]
  unfold invMetricOfJet
  rw [hJ]

theorem deriv1Comp_pureSecondJet (j δj : Jet2 d d)
    (hval : δj.val = 0) (h1 : δj.deriv1 = 0) (t : ℝ) (k i j_ : Fin d) :
    deriv1Comp (d := d) (j + t • δj) k i j_ = deriv1Comp (d := d) j k i j_ := by
  have hD1 : (j + t • δj).deriv1 = j.deriv1 := by
    rw [jet2_add_smul_deriv1, h1, smul_zero, add_zero]
  unfold deriv1Comp
  rw [hD1]

theorem valComp_pureSecondJet (j δj : Jet2 d d)
    (hval : δj.val = 0) (t : ℝ) (i j_ : Fin d) :
    valComp (d := d) (j + t • δj) i j_ = valComp (d := d) j i j_ := by
  have hJ : (j + t • δj).val = j.val := by
    rw [jet2_add_smul_val, hval, smul_zero, add_zero]
  unfold valComp
  rw [hJ]

theorem derivInvMetricOfJet_pureSecondJet (j δj : Jet2 d d)
    (hval : δj.val = 0) (h1 : δj.deriv1 = 0) (t : ℝ) (m k l : Fin d) :
    derivInvMetricOfJet (d := d) (j + t • δj) m k l
      = derivInvMetricOfJet (d := d) j m k l := by
  unfold derivInvMetricOfJet
  rw [neg_inj]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  rw [invMetricOfJet_pureSecondJet _ _ hval t k a,
    deriv1Comp_pureSecondJet _ _ hval h1 t m a b,
    invMetricOfJet_pureSecondJet _ _ hval t b l]

theorem christoffelOfJet_pureSecondJet (j δj : Jet2 d d)
    (hval : δj.val = 0) (h1 : δj.deriv1 = 0) (t : ℝ) (k i j_ : Fin d) :
    christoffelOfJet (d := d) (j + t • δj) k i j_
      = christoffelOfJet (d := d) j k i j_ := by
  unfold christoffelOfJet
  congr 1
  apply Finset.sum_congr rfl; intro l _
  rw [invMetricOfJet_pureSecondJet _ _ hval t k l,
    deriv1Comp_pureSecondJet _ _ hval h1 t i j_ l,
    deriv1Comp_pureSecondJet _ _ hval h1 t j_ i l,
    deriv1Comp_pureSecondJet _ _ hval h1 t l i j_]

theorem deTurckVectorOfJet_pureSecondJet (j δj : Jet2 d d)
    (hval : δj.val = 0) (h1 : δj.deriv1 = 0) (t : ℝ) (k : Fin d) :
    deTurckVectorOfJet (d := d) Γbg (j + t • δj) k
      = deTurckVectorOfJet (d := d) Γbg j k := by
  unfold deTurckVectorOfJet
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j_ _
  rw [invMetricOfJet_pureSecondJet _ _ hval t i j_,
    christoffelOfJet_pureSecondJet _ _ hval h1 t k i j_]

theorem deriv2Comp_pureSecondJet (j δj : Jet2 d d)
    (t : ℝ) (a b c e : Fin d) :
    deriv2Comp (d := d) (j + t • δj) a b c e
      = deriv2Comp (d := d) j a b c e
        + t * deriv2Comp (d := d) δj a b c e := by
  have hD2 : ((j + t • δj).deriv2 a b) = j.deriv2 a b + t • (δj.deriv2 a b) := rfl
  unfold deriv2Comp
  rw [hD2, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

/-! ## 6. Affineness of the building blocks along the curve -/

/-- A finite sum of affine functions is affine. -/
theorem sum_affine {ι : Type*} [Fintype ι] (X Y : ι → ℝ) (t : ℝ) :
    ∑ k : ι, (X k + t * Y k) = ∑ k : ι, X k + t * ∑ k : ι, Y k := by
  rw [Finset.sum_add_distrib, Finset.mul_sum]

theorem derivChristoffelOfJet_pureSecondJet (j δj : Jet2 d d)
    (hval : δj.val = 0) (h1 : δj.deriv1 = 0)
    (t : ℝ) (m k i j_ : Fin d) :
    derivChristoffelOfJet (d := d) (j + t • δj) m k i j_
      = derivChristoffelOfJet (d := d) j m k i j_
        + t * dChristoffel2 (d := d) j δj m k i j_ := by
  have hsum : ∀ l : Fin d,
      ((derivInvMetricOfJet (d := d) (j + t • δj) m k l) *
        (deriv1Comp (d := d) (j + t • δj) i j_ l
          + deriv1Comp (d := d) (j + t • δj) j_ i l
          - deriv1Comp (d := d) (j + t • δj) l i j_)
      + (invMetricOfJet (d := d) (j + t • δj) k l) *
        (deriv2Comp (d := d) (j + t • δj) m i j_ l
          + deriv2Comp (d := d) (j + t • δj) m j_ i l
          - deriv2Comp (d := d) (j + t • δj) m l i j_))
      = ((derivInvMetricOfJet (d := d) j m k l) *
        (deriv1Comp (d := d) j i j_ l + deriv1Comp (d := d) j j_ i l
          - deriv1Comp (d := d) j l i j_)
      + (invMetricOfJet (d := d) j k l) *
        (deriv2Comp (d := d) j m i j_ l + deriv2Comp (d := d) j m j_ i l
          - deriv2Comp (d := d) j m l i j_))
      + t * ((invMetricOfJet (d := d) j k l) *
        (deriv2Comp (d := d) δj m i j_ l + deriv2Comp (d := d) δj m j_ i l
          - deriv2Comp (d := d) δj m l i j_)) := by
    intro l
    rw [derivInvMetricOfJet_pureSecondJet _ _ hval h1 t m k l,
      deriv1Comp_pureSecondJet _ _ hval h1 t i j_ l,
      deriv1Comp_pureSecondJet _ _ hval h1 t j_ i l,
      deriv1Comp_pureSecondJet _ _ hval h1 t l i j_,
      invMetricOfJet_pureSecondJet _ _ hval t k l,
      deriv2Comp_pureSecondJet _ _ t m i j_ l,
      deriv2Comp_pureSecondJet _ _ t m j_ i l,
      deriv2Comp_pureSecondJet _ _ t m l i j_]
    ring
  simp only [derivChristoffelOfJet, dChristoffel2, hsum, sum_affine]
  ring

theorem ricciOfJet_pureSecondJet (j δj : Jet2 d d)
    (hval : δj.val = 0) (h1 : δj.deriv1 = 0)
    (t : ℝ) (i j_ : Fin d) :
    ricciOfJet (d := d) (j + t • δj) i j_
      = ricciOfJet (d := d) j i j_ + t * dRicci2 (d := d) j δj i j_ := by
  have h1sum : ∀ k : Fin d,
      (derivChristoffelOfJet (d := d) (j + t • δj) k k i j_
        - derivChristoffelOfJet (d := d) (j + t • δj) j_ k i k)
      = (derivChristoffelOfJet (d := d) j k k i j_
          - derivChristoffelOfJet (d := d) j j_ k i k)
        + t * (dChristoffel2 (d := d) j δj k k i j_
          - dChristoffel2 (d := d) j δj j_ k i k) := by
    intro k
    rw [derivChristoffelOfJet_pureSecondJet _ _ hval h1 t k k i j_,
      derivChristoffelOfJet_pureSecondJet _ _ hval h1 t j_ k i k]
    ring
  have h2sum : ∀ k l : Fin d,
      (christoffelOfJet (d := d) (j + t • δj) k k l
          * christoffelOfJet (d := d) (j + t • δj) l i j_
        - christoffelOfJet (d := d) (j + t • δj) k j_ l
          * christoffelOfJet (d := d) (j + t • δj) l i k)
      = (christoffelOfJet (d := d) j k k l * christoffelOfJet (d := d) j l i j_
        - christoffelOfJet (d := d) j k j_ l * christoffelOfJet (d := d) j l i k) := by
    intro k l
    rw [christoffelOfJet_pureSecondJet _ _ hval h1 t k k l,
      christoffelOfJet_pureSecondJet _ _ hval h1 t l i j_,
      christoffelOfJet_pureSecondJet _ _ hval h1 t k j_ l,
      christoffelOfJet_pureSecondJet _ _ hval h1 t l i k]
  have h2sum' : (∑ k : Fin d, ∑ l : Fin d,
      (christoffelOfJet (d := d) (j + t • δj) k k l
          * christoffelOfJet (d := d) (j + t • δj) l i j_
        - christoffelOfJet (d := d) (j + t • δj) k j_ l
          * christoffelOfJet (d := d) (j + t • δj) l i k))
      = ∑ k : Fin d, ∑ l : Fin d,
        (christoffelOfJet (d := d) j k k l * christoffelOfJet (d := d) j l i j_
          - christoffelOfJet (d := d) j k j_ l * christoffelOfJet (d := d) j l i k) :=
    Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => h2sum k l))
  simp only [ricciOfJet, dRicci2, h1sum, h2sum', sum_affine]
  ring

theorem derivDeTurckVectorOfJet_pureSecondJet (j δj : Jet2 d d)
    (hval : δj.val = 0) (h1 : δj.deriv1 = 0)
    (t : ℝ) (m k : Fin d) :
    derivDeTurckVectorOfJet (d := d) Γbg (j + t • δj) m k
      = derivDeTurckVectorOfJet (d := d) Γbg j m k
        + t * dDeTurckW2 (d := d) j δj m k := by
  have hsum : ∀ a b : Fin d,
      ((derivInvMetricOfJet (d := d) (j + t • δj) m a b) *
          (christoffelOfJet (d := d) (j + t • δj) k a b - Γbg k a b)
        + (invMetricOfJet (d := d) (j + t • δj) a b) *
          (derivChristoffelOfJet (d := d) (j + t • δj) m k a b))
      = ((derivInvMetricOfJet (d := d) j m a b) *
          (christoffelOfJet (d := d) j k a b - Γbg k a b)
        + (invMetricOfJet (d := d) j a b) *
          (derivChristoffelOfJet (d := d) j m k a b))
        + t * ((invMetricOfJet (d := d) j a b) *
          (dChristoffel2 (d := d) j δj m k a b)) := by
    intro a b
    rw [derivInvMetricOfJet_pureSecondJet _ _ hval h1 t m a b,
      christoffelOfJet_pureSecondJet _ _ hval h1 t k a b,
      invMetricOfJet_pureSecondJet _ _ hval t a b,
      derivChristoffelOfJet_pureSecondJet _ _ hval h1 t m k a b]
    ring
  simp only [derivDeTurckVectorOfJet, dDeTurckW2, hsum, sum_affine]

theorem deTurckCorrectionOfJet_pureSecondJet (j δj : Jet2 d d)
    (hval : δj.val = 0) (h1 : δj.deriv1 = 0)
    (t : ℝ) (i j_ : Fin d) :
    deTurckCorrectionOfJet (d := d) Γbg (j + t • δj) i j_
      = deTurckCorrectionOfJet (d := d) Γbg j i j_
        + t * dCorrection2 (d := d) j δj i j_ := by
  have hsum : ∀ k : Fin d,
      ((valComp (d := d) (j + t • δj) k j_)
          * (derivDeTurckVectorOfJet (d := d) Γbg (j + t • δj) i k)
        + (valComp (d := d) (j + t • δj) i k)
          * (derivDeTurckVectorOfJet (d := d) Γbg (j + t • δj) j_ k)
        + (deTurckVectorOfJet (d := d) Γbg (j + t • δj) k)
          * (deriv1Comp (d := d) (j + t • δj) k i j_))
      = ((valComp (d := d) j k j_) * (derivDeTurckVectorOfJet (d := d) Γbg j i k)
        + (valComp (d := d) j i k) * (derivDeTurckVectorOfJet (d := d) Γbg j j_ k)
        + (deTurckVectorOfJet (d := d) Γbg j k) * (deriv1Comp (d := d) j k i j_)
        + t * ((valComp (d := d) j k j_) * (dDeTurckW2 (d := d) j δj i k)
          + (valComp (d := d) j i k) * (dDeTurckW2 (d := d) j δj j_ k))) := by
    intro k
    rw [valComp_pureSecondJet _ _ hval t k j_,
      valComp_pureSecondJet _ _ hval t i k,
      derivDeTurckVectorOfJet_pureSecondJet Γbg _ _ hval h1 t i k,
      derivDeTurckVectorOfJet_pureSecondJet Γbg _ _ hval h1 t j_ k,
      deTurckVectorOfJet_pureSecondJet Γbg _ _ hval h1 t k,
      deriv1Comp_pureSecondJet _ _ hval h1 t k i j_]
    ring
  simp only [deTurckCorrectionOfJet, dCorrection2, hsum, sum_affine]

/-- The fiber map is affine along pure second-jet curves. -/
theorem phiRDMatrix_pureSecondJet_affine (j δj : Jet2 d d)
    (hval : δj.val = 0) (h1 : δj.deriv1 = 0) (t : ℝ) :
    phiRDMatrix (d := d) Γbg (j + t • δj)
      = phiRDMatrix (d := d) Γbg j
        + t • (fun i j_ => -2 * dRicci2 (d := d) j δj i j_
          + dCorrection2 (d := d) j δj i j_) := by
  funext i j_
  show phiRDOfJet (d := d) Γbg (j + t • δj) i j_ = _
  unfold phiRDMatrix phiRDOfJet
  rw [ricciOfJet_pureSecondJet _ _ hval h1 t i j_,
    deTurckCorrectionOfJet_pureSecondJet Γbg _ _ hval h1 t i j_]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## 7. Bridge lemmas: second-jet-linear parts in cancellation normal form -/

/-- The Ricci second-jet-linear part, in the normal form of
`deturckPrincipalPart_identity`. -/
theorem dRicci2_bridge (j δj : Jet2 d d) (i j_ : Fin d) :
    dRicci2 (d := d) j δj i j_
      = ∑ k : Fin d, ((1/2) * ∑ l : Fin d, (invMetricOfJet (d := d) j k l) *
        (((deriv2Comp (d := d) δj k i j_ l) + (deriv2Comp (d := d) δj k j_ i l)
            - (deriv2Comp (d := d) δj k l i j_))
          - ((deriv2Comp (d := d) δj j_ k i l) + (deriv2Comp (d := d) δj j_ i k l)
            - (deriv2Comp (d := d) δj j_ l i k)))) := by
  unfold dRicci2 dChristoffel2
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  ring

/-- The DeTurck-correction second-jet-linear part, in the normal form of
`deturckPrincipalPart_identity` (via the metric contraction). -/
theorem dCorrection2_bridge (j δj : Jet2 d d)
    (hinv : ∀ a b : Fin d, ∑ k : Fin d, (j.val k a) * (invMetricOfJet (d := d) j k b)
      = if a = b then 1 else 0)
    (hgsymm : ∀ a b : Fin d, j.val a b = j.val b a)
    (i j_ : Fin d) :
    dCorrection2 (d := d) j δj i j_
      = (1/2) * ∑ a : Fin d, ∑ b : Fin d, (invMetricOfJet (d := d) j a b) *
        ((((deriv2Comp (d := d) δj i a b j_) + (deriv2Comp (d := d) δj i b a j_)
            - (deriv2Comp (d := d) δj i j_ a b)))
          + (((deriv2Comp (d := d) δj j_ a b i) + (deriv2Comp (d := d) δj j_ b a i)
            - (deriv2Comp (d := d) δj j_ i a b)))) := by
  have key1 : (∑ k : Fin d, (j.val k j_) * (∑ a : Fin d, ∑ b : Fin d,
      (invMetricOfJet (d := d) j a b) *
      ((1/2) * ∑ l : Fin d, (invMetricOfJet (d := d) j k l) *
        ((deriv2Comp (d := d) δj i a b l) + (deriv2Comp (d := d) δj i b a l)
          - (deriv2Comp (d := d) δj i l a b)))))
      = (1/2) * ∑ a : Fin d, ∑ b : Fin d, (invMetricOfJet (d := d) j a b) *
        (((deriv2Comp (d := d) δj i a b j_) + (deriv2Comp (d := d) δj i b a j_)
          - (deriv2Comp (d := d) δj i j_ a b))) :=
    contract_deturck_correction (fun p q => invMetricOfJet (d := d) j p q)
      (fun a b => j.val a b) hinv
      (fun a b l => (deriv2Comp (d := d) δj i a b l)
        + (deriv2Comp (d := d) δj i b a l) - (deriv2Comp (d := d) δj i l a b)) j_
  have key2 : (∑ k : Fin d, (j.val k i) * (∑ a : Fin d, ∑ b : Fin d,
      (invMetricOfJet (d := d) j a b) *
      ((1/2) * ∑ l : Fin d, (invMetricOfJet (d := d) j k l) *
        ((deriv2Comp (d := d) δj j_ a b l) + (deriv2Comp (d := d) δj j_ b a l)
          - (deriv2Comp (d := d) δj j_ l a b)))))
      = (1/2) * ∑ a : Fin d, ∑ b : Fin d, (invMetricOfJet (d := d) j a b) *
        (((deriv2Comp (d := d) δj j_ a b i) + (deriv2Comp (d := d) δj j_ b a i)
          - (deriv2Comp (d := d) δj j_ i a b))) :=
    contract_deturck_correction (fun p q => invMetricOfJet (d := d) j p q)
      (fun a b => j.val a b) hinv
      (fun a b l => (deriv2Comp (d := d) δj j_ a b l)
        + (deriv2Comp (d := d) δj j_ b a l) - (deriv2Comp (d := d) δj j_ l a b)) i
  have hsymm_rw : ∀ k : Fin d, (j.val i k) = (j.val k i) := fun k => hgsymm i k
  unfold dCorrection2 dDeTurckW2 dChristoffel2
  simp only [valComp, hsymm_rw]
  rw [Finset.sum_add_distrib, key1, key2]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

/-! ## 8. The principal-part identity for the Fréchet derivative -/

/-- **Linearization principal part.** On a pure second-jet direction with
symmetric 2-jet, the Fréchet derivative of the Ricci–DeTurck fiber map is
exactly contraction of the Hessian with the inverse metric. -/
theorem phiRDMatrixDeriv_eq_phiRDPrincipalCLM (j δj : Jet2 d d)
    (hj : j ∈ jetInvertibleLocus (d := d))
    (hgsymm : ∀ a b : Fin d, j.val a b = j.val b a)
    (hval : δj.val = 0) (h1 : δj.deriv1 = 0)
    (hS12 : ∀ a b c e : Fin d, (δj.deriv2 a b) c e = (δj.deriv2 b a) c e)
    (hS34 : ∀ a b c e : Fin d, (δj.deriv2 a b) c e = (δj.deriv2 a b) e c) :
    phiRDMatrixDeriv (d := d) Γbg j δj
      = phiRDPrincipalCLM (d := d) j δj := by
  set Lfun : Fin d → Fin d → ℝ :=
    fun i j_ => -2 * dRicci2 (d := d) j δj i j_
      + dCorrection2 (d := d) j δj i j_ with hLfun
  have hdiff : DifferentiableAt ℝ (phiRDMatrix (d := d) Γbg) j :=
    ((contDiffOn_phiRDMatrix (d := d) Γbg).differentiableOn (by simp)).differentiableAt
      ((isOpen_jetInvertibleLocus (d := d)).mem_nhds hj)
  have hcurve : HasDerivAt (fun t : ℝ => j + t • δj) δj 0 := by
    have h := ((hasDerivAt_id (0:ℝ)).smul_const δj).const_add j
    simpa using h
  have hy_eq : j = (fun t : ℝ => j + t • δj) 0 := by simp
  have hcomp : HasDerivAt
      ((phiRDMatrix (d := d) Γbg) ∘ (fun t : ℝ => j + t • δj))
      ((fderiv ℝ (phiRDMatrix (d := d) Γbg) j) δj) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq
      (hl := hdiff.hasFDerivAt) (hf := hcurve) (hy := hy_eq)
  have hdirect : HasDerivAt
      ((phiRDMatrix (d := d) Γbg) ∘ (fun t : ℝ => j + t • δj)) Lfun 0 := by
    have haff : ∀ t : ℝ,
        ((phiRDMatrix (d := d) Γbg) ∘ (fun s : ℝ => j + s • δj)) t
          = (phiRDMatrix (d := d) Γbg) j + t • Lfun :=
      fun t => phiRDMatrix_pureSecondJet_affine (d := d) Γbg _ _ hval h1 t
    have hB : HasDerivAt (fun t : ℝ => (phiRDMatrix (d := d) Γbg) j + t • Lfun)
        Lfun 0 := by
      have h1' := ((hasDerivAt_id (0:ℝ)).smul_const Lfun).const_add
        ((phiRDMatrix (d := d) Γbg) j)
      simpa using h1'
    have heq : (fun t : ℝ => (phiRDMatrix (d := d) Γbg) j + t • Lfun)
        =ᶠ[nhds 0] ((phiRDMatrix (d := d) Γbg) ∘ (fun t : ℝ => j + t • δj)) := by
      apply Filter.Eventually.of_forall
      intro t
      show (phiRDMatrix (d := d) Γbg) j + t • Lfun = _
      exact Eq.symm (haff t)
    exact hB.congr_of_eventuallyEq heq.symm
  have heq : (fderiv ℝ (phiRDMatrix (d := d) Γbg) j) δj = Lfun :=
    hcomp.unique hdirect
  have hfw : fderivWithin ℝ (phiRDMatrix (d := d) Γbg)
      (jetInvertibleLocus (d := d)) j
      = fderiv ℝ (phiRDMatrix (d := d) Γbg) j :=
    fderivWithin_of_mem_nhds ((isOpen_jetInvertibleLocus (d := d)).mem_nhds hj)
  have hdet : j.val.det ≠ 0 := hj
  have hginv_symm : ∀ p q : Fin d,
      invMetricOfJet (d := d) j p q = invMetricOfJet (d := d) j q p :=
    fun p q => invMetricOfJet_symm (d := d) j hdet hgsymm p q
  have hinv : ∀ a b : Fin d,
      ∑ k : Fin d, (j.val k a) * (invMetricOfJet (d := d) j k b)
        = if a = b then 1 else 0 :=
    fun a b => invMetricOfJet_contract (d := d) j hdet hgsymm a b
  have hcancel : Lfun = fun i j_ => ∑ p : Fin d, ∑ q : Fin d,
      (invMetricOfJet (d := d) j p q) * ((δj.deriv2 p q) i j_) := by
    funext i j_
    rw [hLfun]
    show -2 * dRicci2 (d := d) j δj i j_
        + dCorrection2 (d := d) j δj i j_ = _
    rw [dRicci2_bridge (d := d) j δj i j_,
      dCorrection2_bridge (d := d) j δj hinv hgsymm i j_]
    exact deturckPrincipalPart_identity (d := d)
      (fun p q => invMetricOfJet (d := d) j p q)
      (fun a b => j.val a b)
      (fun a b c e => ((δj.deriv2 a b) c e))
      (fun p q => hginv_symm p q)
      (fun a b => by simpa using hinv a b)
      (fun a b c e => hS12 a b c e)
      (fun a b c e => hS34 a b c e)
      i j_
  unfold phiRDMatrixDeriv
  rw [hfw, heq, hcancel]
  funext i j_
  rw [phiRDPrincipalCLM_apply]

/-! ## 9. Strong parabolicity: the principal symbol is positive -/

/-- **Strong parabolicity.** On a rank-one Hessian direction, the principal
part is a positive scalar multiple of the direction. -/
theorem phiRDPrincipal_stronglyParabolic (j : Jet2 d d)
    (hj : j.val.det ≠ 0)
    (hpos : ∀ ξ : Fin d → ℝ, ξ ≠ 0 →
      0 < ∑ p : Fin d, ∑ q : Fin d,
        (invMetricOfJet (d := d) j p q) * (ξ p * ξ q))
    (ξ : Fin d → ℝ) (hξ : ξ ≠ 0) (w : Fin d → Fin d → ℝ) :
    ∃ q : ℝ, 0 < q ∧
      phiRDPrincipalCLM (d := d) j (rankOneJet2 (d := d) ξ w) = q • w := by
  refine ⟨∑ p : Fin d, ∑ q : Fin d,
    (invMetricOfJet (d := d) j p q) * (ξ p * ξ q), hpos ξ hξ, ?_⟩
  exact phiRDPrincipalCLM_rankOne (d := d) j ξ w

end GenuinePhiRD
end AnalyticPDE
end RicciFlow
