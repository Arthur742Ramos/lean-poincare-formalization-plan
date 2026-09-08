module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # The variational equation derived from a smooth flow equation -/

@[expose] public noncomputable section
open Filter
open scoped Topology ContDiff

namespace LichnerowiczObata

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Differentiating the actual flow equation and commuting second
derivatives yields the linearized equation for spatial variations. -/
theorem fderiv_variation_equation {φ : E → F} {v : F → F} {x : E}
    (hφ : ContDiffAt ℝ 2 φ x) (hv : DifferentiableAt ℝ v (φ x)) (a b : E)
    (hode : (fun y => fderiv ℝ φ y b) =ᶠ[𝓝 x] (v ∘ φ)) :
    fderiv ℝ (fun y => fderiv ℝ φ y a) x b =
      fderiv ℝ v (φ x) (fderiv ℝ φ x a) := by
  have hD : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have he (c d : E) : fderiv ℝ (fun y => fderiv ℝ φ y c) x d =
      fderiv ℝ (fderiv ℝ φ) x d c := by
    rw [fderiv_clm_apply hD (differentiableAt_const c)]
    simp
  rw [he a b, hφ.isSymmSndFDerivAt (by norm_num) b a, ← he b a]
  rw [hode.fderiv_eq, fderiv_comp x hv (hφ.differentiableAt (by norm_num))]
  rfl

/-- A smooth family of actual ODE solutions satisfies the variational ODE
in each initial-point direction. The linearized equation is a conclusion. -/
theorem hasDerivAt_flow_variation {φ : E × ℝ → F} {v : F → F}
    {U : Set (E × ℝ)} (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U)
    (hode : ∀ y ∈ U, HasDerivAt (fun t => φ (y.1, t)) (v (φ y)) y.2)
    {x : E} {t : ℝ} (hx : (x, t) ∈ U) (hv : DifferentiableAt ℝ v (φ (x, t))) (u : E) :
    HasDerivAt (fun s => fderiv ℝ φ (x, s) (u, 0))
      (fderiv ℝ v (φ (x, t)) (fderiv ℝ φ (x, t) (u, 0))) t := by
  have hs : ContDiffAt ℝ 2 φ (x, t) := (hφ _ hx).contDiffAt (hU.mem_nhds hx)
  have he : (fun y => fderiv ℝ φ y (0, 1)) =ᶠ[𝓝 (x, t)] (v ∘ φ) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hd := ((hφ y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
    have hp := hd.hasFDerivAt.comp_hasDerivAt y.2
      ((hasDerivAt_const y.2 y.1).prodMk (hasDerivAt_id y.2))
    exact hp.unique (hode y hy)
  have hD : DifferentiableAt ℝ (fderiv ℝ φ) (x, t) :=
    (hs.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hd := (hD.clm_apply (differentiableAt_const (u, (0 : ℝ)))).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  have hlin := fderiv_variation_equation hs hv (u, (0 : ℝ)) (0, (1 : ℝ)) he
  simpa only [Function.comp_def, hlin] using hd

/-- The initial-value identity determines every spatial derivative at time zero. -/
theorem fderiv_flow_initial_apply {φ : E × ℝ → E} {x : E}
    (hφ : DifferentiableAt ℝ φ (x, 0))
    (hinit : (fun y => φ (y, 0)) =ᶠ[𝓝 x] id) (u : E) :
    fderiv ℝ φ (x, 0) (u, 0) = u := by
  have hi : HasFDerivAt (fun y : E => (y, (0 : ℝ)))
      ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const (0 : ℝ) x)
  have hd := hφ.hasFDerivAt.comp x hi
  have he := hinit.fderiv_eq (𝕜 := ℝ)
  have hd' : HasFDerivAt (fun y => φ (y, 0))
      ((fderiv ℝ φ (x, 0)).comp ((ContinuousLinearMap.id ℝ E).prod 0)) x := hd
  rw [hd'.fderiv] at he
  simpa using congrArg (fun L : E →L[ℝ] E => L u) he

end LichnerowiczObata
