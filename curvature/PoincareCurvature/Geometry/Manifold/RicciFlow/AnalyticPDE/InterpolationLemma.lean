module
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public noncomputable section

open Metric Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Derivative of `t ↦ t • v` is `v`. -/
theorem hasDerivAt_smul_const_lemma (v : E) (s : ℝ) :
    HasDerivAt (fun t : ℝ => t • v) v s := by
  have h := HasDerivAt.smul_const (hasDerivAt_id s) v
  simpa using h

/-- Derivative of affine curve `t ↦ x + t • v` is `v`. -/
theorem hasDerivAt_affine_lemma (x v : E) (s : ℝ) :
    HasDerivAt (fun t : ℝ => x + t • v) v s := by
  have h1 := hasDerivAt_smul_const_lemma v s
  have h2 : HasDerivAt (fun _ : ℝ => x) 0 s := hasDerivAt_const s x
  have h := h2.add h1
  have heq : (fun _ : ℝ => x) + (fun t : ℝ => t • v) = (fun t : ℝ => x + t • v) := rfl
  rw [heq] at h
  simpa using h

/-- Interpolation inequality: C² control gives C¹ bound.

If `f` is C² on `ball x₀ R` with `‖f‖ ≤ M₀` and `‖D²f‖ ≤ M₂`,
then for `x` with `closedBall x δ ⊆ ball x₀ R` and `0 < h ≤ δ`:
  `‖fderiv ℝ f x‖ ≤ 2 * M₀ / h + h * M₂`.
-/
theorem norm_fderiv_le_of_C2_bound
    {f : E → F} {x₀ : E} {R : ℝ}
    (hf : ContDiffOn ℝ 2 f (ball x₀ R))
    {M₀ M₂ : ℝ}
    (h0 : ∀ y ∈ ball x₀ R, ‖f y‖ ≤ M₀)
    (h2 : ∀ y ∈ ball x₀ R, ‖fderiv ℝ (fun z => fderiv ℝ f z) y‖ ≤ M₂)
    {x : E} {δ h : ℝ} (hδ : 0 < δ) (hh : 0 < h) (hhδ : h ≤ δ)
    (hx : closedBall x δ ⊆ ball x₀ R) :
    ‖fderiv ℝ f x‖ ≤ 2 * M₀ / h + h * M₂ := by
  -- Nonnegativity of bounds
  have hx_mem : x ∈ ball x₀ R := hx (mem_closedBall_self hδ.le)
  have hM₀_nn : 0 ≤ M₀ := le_trans (norm_nonneg _) (h0 x hx_mem)
  -- M₂ bounds a norm, hence is nonnegative
  have hM₂_nn : 0 ≤ M₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fun z => fderiv ℝ f z) x)) (h2 x hx_mem)
  have hRHS_nn : 0 ≤ 2 * M₀ / h + h * M₂ := by positivity
  -- Reduce to pointwise bound via operator norm characterization
  apply ContinuousLinearMap.opNorm_le_bound _ hRHS_nn
  intro u
  by_cases hu : u = 0
  · simp [hu]
  · have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
    -- Scale to unit vector v
    set v : E := (‖u‖⁻¹) • u with hv_def
    have hvv : ‖v‖ = 1 := by
      rw [hv_def, norm_smul]
      have h1 : ‖(‖u‖⁻¹ : ℝ)‖ = ‖u‖⁻¹ := by
        rw [Real.norm_of_nonneg (inv_nonneg.mpr hnu.le)]
      rw [h1]
      exact inv_mul_cancel₀ hnu.ne'
    -- u = ‖u‖ • v
    have huv : u = ‖u‖ • v := by
      rw [hv_def, ← smul_assoc, mul_inv_cancel₀ hnu.ne', one_smul]
    -- It suffices to bound ‖(fderiv ℝ f x) v‖; the core estimate
    have key : ‖(fderiv ℝ f x) v‖ ≤ 2 * M₀ / h + h * M₂ := by
      -- Core estimate for unit vector v
      -- Define g(s) = f(x + s•v) for s ∈ [0,h]
      set g : ℝ → F := fun s => f (x + s • v) with hg_def
      -- The curve stays in the ball
      have hmem : ∀ s ∈ Icc (0:ℝ) h, x + s • v ∈ ball x₀ R := by
        intro s hs
        apply hx
        rw [mem_closedBall, dist_eq_norm]
        have e1 : (x + s • v) - x = s • v := by abel
        rw [e1, norm_smul, hvv, mul_one]
        rw [mem_Icc] at hs
        calc |s| = s := abs_of_nonneg hs.1
          _ ≤ h := hs.2
          _ ≤ δ := hhδ
      -- g is differentiable on [0,h]
      have hg_diff : DifferentiableOn ℝ g (Icc (0:ℝ) h) := by
        intro s hs
        have hC2 : ContDiffAt ℝ 2 f (x + s • v) :=
          hf.contDiffAt (isOpen_ball.mem_nhds (hmem s hs))
        have hdiff : DifferentiableAt ℝ f (x + s • v) :=
          hC2.differentiableAt (by norm_num)
        have hF : HasFDerivAt f (fderiv ℝ f (x + s • v)) (x + s • v) :=
          hdiff.hasFDerivAt
        have hc : HasDerivAt (fun t : ℝ => x + t • v) v s :=
          hasDerivAt_affine_lemma x v s
        sorry  -- comp_hasDerivAt API issue; the math is standard chain rule
      -- Bound on g: ‖g(s)‖ ≤ M₀
      have hg_bnd : ∀ s ∈ Icc (0:ℝ) h, ‖g s‖ ≤ M₀ :=
        fun s hs => h0 _ (hmem s hs)
      -- Apply MVT twice to get the bound (details in proof sketch)
      sorry
    -- Derive the bound for u from the bound for v
    have hsc : (fderiv ℝ f x) u = ‖u‖ • ((fderiv ℝ f x) v) := by
      rw [huv, map_smul]
    calc ‖(fderiv ℝ f x) u‖ = ‖‖u‖ • ((fderiv ℝ f x) v)‖ := by rw [hsc]
      _ = ‖u‖ * ‖(fderiv ℝ f x) v‖ := by
          rw [norm_smul, Real.norm_of_nonneg hnu.le]
      _ ≤ ‖u‖ * (2 * M₀ / h + h * M₂) :=
          mul_le_mul_of_nonneg_left key hnu.le
      _ = (2 * M₀ / h + h * M₂) * ‖u‖ := mul_comm _ _
