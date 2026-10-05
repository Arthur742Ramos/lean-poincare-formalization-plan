/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Genuine bounded derivatives of compactly supported C² functions

Every derivative below is the ordinary Fréchet derivative of the input function,
evaluated on the actual standard coordinate vectors. Compact support, rather
than any third derivative or Hölder hypothesis, supplies boundedness and uniform
continuity of the second derivatives. The dimension-zero case needs no split.
-/

noncomputable section

open Set
open scoped Topology

namespace PoincareCurvature.CompactlySupportedC2Jet

variable {n : ℕ} {f : (Fin n → ℝ) → ℝ}

/-- The genuine first derivative along one coordinate direction. -/
def first (f : (Fin n → ℝ) → ℝ) (k : Fin n) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single k 1)

/-- Differentiate the actual first derivative in a second coordinate direction. -/
def second (f : (Fin n → ℝ) → ℝ) (j k : Fin n) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ (first f k) x (Pi.single j 1)

theorem contDiff_first (hf : ContDiff ℝ 2 f) (k : Fin n) :
    ContDiff ℝ 1 (first f k) := by
  exact (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
    contDiff_const

theorem continuous_second (hf : ContDiff ℝ 2 f) (j k : Fin n) :
    Continuous (second f j k) := by
  exact ((contDiff_first hf k).continuous_fderiv (by norm_num)).clm_apply
    continuous_const

theorem hasCompactSupport_first (hfc : HasCompactSupport f) (k : Fin n) :
    HasCompactSupport (first f k) :=
  hfc.fderiv_apply ℝ (Pi.single k 1)

theorem hasCompactSupport_second (hfc : HasCompactSupport f) (j k : Fin n) :
    HasCompactSupport (second f j k) :=
  (hasCompactSupport_first hfc k).fderiv_apply ℝ (Pi.single j 1)

theorem tsupport_second_subset (j k : Fin n) :
    tsupport (second f j k) ⊆ tsupport f :=
  (tsupport_fderiv_apply_subset ℝ (Pi.single j 1)).trans
    (tsupport_fderiv_apply_subset ℝ (Pi.single k 1))

/-- Identify the twice differentiated coordinate value with the actual Hessian. -/
theorem second_eq_fderiv_fderiv (hf : ContDiff ℝ 2 f) (j k : Fin n)
    (x : Fin n → ℝ) :
    second f j k x =
      fderiv ℝ (fderiv ℝ f) x (Pi.single j 1) (Pi.single k 1) := by
  have hd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable
      (by norm_num) x).hasFDerivAt
  have he := hd.clm_apply (hasFDerivAt_const (Pi.single k 1) x)
  change fderiv ℝ (fun y => fderiv ℝ f y (Pi.single k 1)) x (Pi.single j 1) = _
  rw [he.fderiv]
  simp

theorem hasDerivAt_value (hf : ContDiff ℝ 2 f) (k : Fin n) (x : Fin n → ℝ) :
    HasDerivAt (fun a => f (Function.update x k a)) (first f k x) (x k) := by
  have hd := (hf.differentiable (by norm_num) x).hasFDerivAt
  have hd' : HasFDerivAt f (fderiv ℝ f x) (Function.update x k (x k)) := by
    simpa only [Function.update_eq_self] using hd
  simpa only [first, Function.comp_def] using
    hd'.comp_hasDerivAt (x k) (hasDerivAt_update x k (x k))

theorem hasDerivAt_first (hf : ContDiff ℝ 2 f) (j k : Fin n) (x : Fin n → ℝ) :
    HasDerivAt (fun a => first f k (Function.update x j a))
      (second f j k x) (x j) := by
  have hd := ((contDiff_first hf k).differentiable (by norm_num) x).hasFDerivAt
  have hd' : HasFDerivAt (first f k) (fderiv ℝ (first f k) x)
      (Function.update x j (x j)) := by
    simpa only [Function.update_eq_self] using hd
  simpa only [second, Function.comp_def] using
    hd'.comp_hasDerivAt (x j) (hasDerivAt_update x j (x j))

/-- Compact support gives the bounded value without a supplied bound. -/
def boundedValue (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  _root_.ofCompactSupport f hf.continuous hfc

/-- Compact support is inherited by the actual first derivatives. -/
def boundedFirst (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (k : Fin n) :
    BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  _root_.ofCompactSupport (first f k)
    (contDiff_first hf k).continuous (hasCompactSupport_first hfc k)

/-- The actual second derivatives are continuous and compactly supported. -/
def boundedSecond (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (j k : Fin n) :
    BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  _root_.ofCompactSupport (second f j k)
    (continuous_second hf j k) (hasCompactSupport_second hfc j k)

/-- No positive Hölder exponent or C³ assumption is used for this conclusion. -/
theorem uniformContinuous_second (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (j k : Fin n) : UniformContinuous (second f j k) :=
  (continuous_second hf j k).uniformContinuous_of_tendsto_cocompact
    (HasCompactSupport.is_zero_at_infty (hasCompactSupport_second hfc j k))

end PoincareCurvature.CompactlySupportedC2Jet
