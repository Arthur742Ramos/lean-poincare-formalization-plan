import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Existence
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open scoped Topology

namespace PoincareCurvature

set_option maxHeartbeats 100000 in
theorem hasDerivAt_fderiv_space_of_joint_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E → ℝ) (Fdot : E → ℝ)
    (hF : ContDiff ℝ 2 (fun p : ℝ × E => F p.1 p.2))
    (hFdot : ∀ y : E, HasDerivAt (fun τ : ℝ => F τ y) (Fdot y) t)
    (v : E) :
    HasDerivAt
      (fun τ : ℝ => fderiv ℝ (fun y : E => F τ y) 0 v)
      (fderiv ℝ Fdot 0 v) t := by
  let full : (ℝ × E) → ℝ := fun p => F p.1 p.2
  have hfull : ContDiff ℝ 2 full := by
    simpa [full] using hF
  have hDf : ContDiffAt ℝ 1 (fderiv ℝ full) (t, 0) :=
    hfull.contDiffAt (x := (t, 0)) |>.fderiv_right (m := 1) (by norm_num)
  have hDff : HasFDerivAt (fderiv ℝ full)
      (fderiv ℝ (fderiv ℝ full) (t, 0)) (t, 0) :=
    (hDf.differentiableAt one_ne_zero).hasFDerivAt
  let inlMap : ℝ →L[ℝ] (ℝ × E) := ContinuousLinearMap.inl ℝ ℝ E
  let inrMap : E →L[ℝ] (ℝ × E) := ContinuousLinearMap.inr ℝ ℝ E
  let inl : ℝ × E := (1, (0 : E))
  have hS0 :=
    hDff.clm_apply
      (hasFDerivAt_const (inl : ℝ × E) (t, 0) :
        HasFDerivAt (fun _ : ℝ × E => inl)
          (0 : (ℝ × E) →L[ℝ] (ℝ × E)) (t, 0))
  have hS : HasFDerivAt
      (fun p : ℝ × E => (fderiv ℝ full p) inl)
      ((fderiv ℝ full (t, 0)).comp (0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
        (fderiv ℝ (fderiv ℝ full) (t, 0)).flip inl)
      (t, 0) := by
    simpa only using hS0
  have hPderiv : HasFDerivAt
      (fun y : E => (fderiv ℝ full (t, y)) inl)
      (((fderiv ℝ full (t, 0)).comp (0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
        (fderiv ℝ (fderiv ℝ full) (t, 0)).flip inl).comp inrMap)
      0 := by
    simpa [inl, Function.comp_def] using
      HasFDerivAt.comp (0 : E) hS
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) t (0 : E))
  have hP_eq_full : ∀ y : E,
      fderiv ℝ (fun τ : ℝ => F τ y) t 1 =
        (fderiv ℝ full (t, y)) inl := by
    intro y
    have htime := (hfull.contDiffAt (x := (t, y))).differentiableAt
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    have hcomp := HasFDerivAt.comp (t : ℝ) htime.hasFDerivAt
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) t y)
    have hfd := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hcomp.fderiv
    simpa [full, inl, inlMap, Function.comp_def] using hfd
  let P : E → ℝ := fun y => fderiv ℝ (fun τ : ℝ => F τ y) t 1
  have hP_eq : P = Fdot := by
    funext y
    have hy := (hFdot y).hasFDerivAt.fderiv
    have hy' := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hy
    simpa [P] using hy'
  have hPderiv' := hPderiv.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun y => by
      simpa [P] using hP_eq_full y))
  have hFdotDeriv := hPderiv'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun y => by
      simpa [P] using congrFun hP_eq.symm y))
  have hQ : HasFDerivAt
      (fun p : ℝ × E => (fderiv ℝ full p) (0, v))
      ((fderiv ℝ full (t, 0)).comp (0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
        (fderiv ℝ (fderiv ℝ full) (t, 0)).flip (0, v))
      (t, 0) :=
    hDff.clm_apply
      (hasFDerivAt_const (0, v) (t, 0) :
        HasFDerivAt (fun _ : ℝ × E => (0, v))
          (0 : (ℝ × E) →L[ℝ] (ℝ × E)) (t, 0))
  have hQtime0 := HasFDerivAt.comp (t : ℝ) hQ
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) t (0 : E))
  have hQtime := hQtime0.hasDerivAt
  have hsymm := (hfull.contDiffAt (x := (t, 0))).isSymmSndFDerivAt (by norm_num)
  have hswap :
      (fderiv ℝ (fderiv ℝ full) (t, 0)) inl (0, v) =
        (fderiv ℝ (fderiv ℝ full) (t, 0)) (0, v) inl := by
    exact hsymm.eq inl (0, v)
  have hQtime'₀ : HasDerivAt
      (fun τ : ℝ => (fderiv ℝ full (τ, 0)) (0, v)) _ t :=
    hQtime.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun τ => by
        simp only [Function.comp_apply]))
  have hQtime' : HasDerivAt
      (fun τ : ℝ => (fderiv ℝ full (τ, 0)) (0, v))
      (fderiv ℝ (fderiv ℝ full) (t, 0) inl (0, v))
      t := by
    exact hQtime'₀.congr_deriv (by
      simpa [inl] using hswap)
  have hslice : ∀ τ : ℝ,
      fderiv ℝ (fun y : E => F τ y) 0 v =
        (fderiv ℝ full (τ, 0)) (0, v) := by
    intro τ
    have htime := (hfull.contDiffAt (x := (τ, 0))).differentiableAt
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    have hcomp := HasFDerivAt.comp (0 : E) htime.hasFDerivAt
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) τ (0 : E))
    have hfd := congrArg (fun L : E →L[ℝ] ℝ => L v) hcomp.fderiv
    simpa [full, Function.comp_def] using hfd
  have htarget := hQtime'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun τ => hslice τ))
  have hderiv_eq :
      fderiv ℝ (fderiv ℝ full) (t, 0) (0, v) inl =
          fderiv ℝ Fdot 0 v := by
    calc
      fderiv ℝ (fderiv ℝ full) (t, 0) (0, v) inl =
          (((fderiv ℝ full (t, 0)).comp (0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
                (fderiv ℝ (fderiv ℝ full) (t, 0)).flip inl).comp inrMap) v := by
              simp [inl, inrMap, ContinuousLinearMap.add_apply,
                ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
                zero_add, ContinuousLinearMap.flip_apply]
      _ = fderiv ℝ Fdot 0 v := by
        rw [← congrArg (fun L : E →L[ℝ] ℝ => L v) hFdotDeriv.fderiv]
  exact htarget.congr_deriv (hswap.trans hderiv_eq)

/- The mixed time--space derivative theorem at an arbitrary spatial base point.

The derivative is obtained from the genuine joint C² field on
ℝ × E; the time derivative of the spatial differential is therefore the
spatial differential of the time derivative.  Keeping the base point
explicit is important for manifold applications, where the point at which
a connection or curvature component is read out is not a distinguished
origin of the model space. -/
set_option maxHeartbeats 100000 in
theorem hasDerivAt_fderiv_space_of_joint_contDiff_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E → ℝ) (Fdot : E → ℝ)
    (hF : ContDiff ℝ 2 (fun p : ℝ × E => F p.1 p.2))
    (hFdot : ∀ y : E, HasDerivAt (fun τ : ℝ => F τ y) (Fdot y) t)
    (x v : E) :
    HasDerivAt
      (fun τ => fderiv ℝ (fun y => F τ y) x v)
      (fderiv ℝ Fdot x v) t := by
  let full : (ℝ × E) → ℝ := fun p => F p.1 p.2
  have hfull : ContDiff ℝ 2 full := by
    simpa [full] using hF
  have hDf : ContDiffAt ℝ 1 (fderiv ℝ full) (t, x) :=
    hfull.contDiffAt (x := (t, x)) |>.fderiv_right (m := 1) (by norm_num)
  have hDff : HasFDerivAt (fderiv ℝ full)
      (fderiv ℝ (fderiv ℝ full) (t, x)) (t, x) :=
    (hDf.differentiableAt one_ne_zero).hasFDerivAt
  let inrMap : E →L[ℝ] (ℝ × E) := ContinuousLinearMap.inr ℝ ℝ E
  let inl : ℝ × E := (1, (0 : E))
  have hS0 :=
    hDff.clm_apply
      (hasFDerivAt_const (inl : ℝ × E) (t, x) :
        HasFDerivAt (fun _ : ℝ × E => inl)
          (0 : (ℝ × E) →L[ℝ] (ℝ × E)) (t, x))
  have hS : HasFDerivAt
      (fun p : ℝ × E => (fderiv ℝ full p) inl)
      ((fderiv ℝ full (t, x)).comp (0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
        (fderiv ℝ (fderiv ℝ full) (t, x)).flip inl)
      (t, x) := by
    simpa only using hS0
  have hPderiv : HasFDerivAt
      (fun y : E => (fderiv ℝ full (t, y)) inl)
      (((fderiv ℝ full (t, x)).comp (0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
        (fderiv ℝ (fderiv ℝ full) (t, x)).flip inl).comp inrMap)
      x := by
    simpa [inl, Function.comp_def] using
      HasFDerivAt.comp x hS
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
  have hP_eq_full : ∀ y : E,
      fderiv ℝ (fun τ : ℝ => F τ y) t 1 =
        (fderiv ℝ full (t, y)) inl := by
    intro y
    have htime := (hfull.contDiffAt (x := (t, y))).differentiableAt
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    have hcomp := HasFDerivAt.comp (t : ℝ) htime.hasFDerivAt
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) t y)
    have hfd := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hcomp.fderiv
    simpa [full, inl, Function.comp_def] using hfd
  let P : E → ℝ := fun y => fderiv ℝ (fun τ : ℝ => F τ y) t 1
  have hP_eq : P = Fdot := by
    funext y
    have hy := (hFdot y).hasFDerivAt.fderiv
    have hy' := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hy
    simpa [P] using hy'
  have hPderiv' := hPderiv.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun y => by
      simpa [P] using hP_eq_full y))
  have hFdotDeriv := hPderiv'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun y => by
      simpa [P] using congrFun hP_eq.symm y))
  have hQ : HasFDerivAt
      (fun p : ℝ × E => (fderiv ℝ full p) (0, v))
      ((fderiv ℝ full (t, x)).comp (0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
        (fderiv ℝ (fderiv ℝ full) (t, x)).flip (0, v))
      (t, x) :=
    hDff.clm_apply
      (hasFDerivAt_const (0, v) (t, x) :
        HasFDerivAt (fun _ : ℝ × E => (0, v))
          (0 : (ℝ × E) →L[ℝ] (ℝ × E)) (t, x))
  have hQtime0 := HasFDerivAt.comp (t : ℝ) hQ
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x)
  have hQtime := hQtime0.hasDerivAt
  have hsymm := (hfull.contDiffAt (x := (t, x))).isSymmSndFDerivAt (by norm_num)
  have hswap :
      (fderiv ℝ (fderiv ℝ full) (t, x)) inl (0, v) =
        (fderiv ℝ (fderiv ℝ full) (t, x)) (0, v) inl := by
    exact hsymm.eq inl (0, v)
  have hQtime'₀ : HasDerivAt
      (fun τ : ℝ => (fderiv ℝ full (τ, x)) (0, v)) _ t :=
    hQtime.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun τ => by
        simp only [Function.comp_apply]))
  have hQtime' : HasDerivAt
      (fun τ : ℝ => (fderiv ℝ full (τ, x)) (0, v))
      (fderiv ℝ (fderiv ℝ full) (t, x) inl (0, v))
      t := by
    exact hQtime'₀.congr_deriv (by
      simpa [inl] using hswap)
  have hslice : ∀ τ : ℝ,
      fderiv ℝ (fun y : E => F τ y) x v =
        (fderiv ℝ full (τ, x)) (0, v) := by
    intro τ
    have htime := (hfull.contDiffAt (x := (τ, x))).differentiableAt
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    have hcomp := HasFDerivAt.comp x htime.hasFDerivAt
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) τ x)
    have hfd := congrArg (fun L : E →L[ℝ] ℝ => L v) hcomp.fderiv
    simpa [full, Function.comp_def] using hfd
  have htarget := hQtime'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun τ => hslice τ))
  have hderiv_eq :
      fderiv ℝ (fderiv ℝ full) (t, x) (0, v) inl =
          fderiv ℝ Fdot x v := by
    calc
      fderiv ℝ (fderiv ℝ full) (t, x) (0, v) inl =
          (((fderiv ℝ full (t, x)).comp (0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
                (fderiv ℝ (fderiv ℝ full) (t, x)).flip inl).comp inrMap) v := by
              simp [inl, inrMap, ContinuousLinearMap.add_apply,
                ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
                zero_add, ContinuousLinearMap.flip_apply]
      _ = fderiv ℝ Fdot x v := by
        rw [← congrArg (fun L : E →L[ℝ] ℝ => L v) hFdotDeriv.fderiv]
  exact htarget.congr_deriv (hswap.trans hderiv_eq)

end PoincareCurvature
