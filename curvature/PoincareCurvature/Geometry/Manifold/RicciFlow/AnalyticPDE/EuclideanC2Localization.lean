/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Analysis.CompactlySupportedC2Jet
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatInitialTrace
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ModelManifoldGaugeFlow

/-!
# C² localization into genuine bounded heat data

The cutoff and ordinary derivative witnesses are constructed. A compactly
supported perturbation of a constant field has a globally uniformly continuous
Hessian, even when the local field has no positive initial Hölder exponent.
This is supporting Euclidean localization; the metric-coordinate and global
Ricci-flow constructions remain separate obligations.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace RicciFlow.AnalyticPDE

namespace EuclideanBoundedC2Data

open PoincareCurvature.CompactlySupportedC2Jet

/-- Actual bounded C² heat input from a compactly supported C² scalar function. -/
def ofCompactSupport {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) : EuclideanBoundedC2Data n where
  value := boundedValue hf hfc
  first := boundedFirst hf hfc
  second := boundedSecond hf hfc
  hasDeriv_value := hasDerivAt_value hf
  hasDeriv_first := hasDerivAt_first hf

/-- A frozen exterior adds no derivative assumptions or additional regularity. -/
def addConst {n : ℕ} (D : EuclideanBoundedC2Data n) (c : ℝ) :
    EuclideanBoundedC2Data n where
  value := BoundedContinuousFunction.const _ c + D.value
  first := D.first
  second := D.second
  hasDeriv_value := by
    intro k x
    simpa using (hasDerivAt_const (x k) c).add (D.hasDeriv_value k x)
  hasDeriv_first := D.hasDeriv_first

theorem uniformContinuous_second_ofCompactSupport
    {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (j k : Fin n) :
    UniformContinuous ((ofCompactSupport hf hfc).second j k : (Fin n → ℝ) → ℝ) :=
  PoincareCurvature.CompactlySupportedC2Jet.uniformContinuous_second hf hfc j k

/-- The actual zero-time C² heat trace is globally continuous for the constructed
frozen-exterior data. Uniform continuity is proved, rather than assumed. -/
theorem continuousAt_heatC2Trace_zero_addConst_ofCompactSupport
    {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (c : ℝ) :
    ContinuousAt (fun t : ℝ =>
      (heatFlowPathBcf ((ofCompactSupport hf hfc).addConst c).value t,
        (fun k => heatFlowPathBcf (((ofCompactSupport hf hfc).addConst c).first k) t),
        (fun j k => heatFlowPathBcf
          (((ofCompactSupport hf hfc).addConst c).second j k) t))) 0 :=
  ((ofCompactSupport hf hfc).addConst c).continuousAt_heatC2Trace_zero
    (uniformContinuous_second_ofCompactSupport hf hfc)

end EuclideanBoundedC2Data

/-- A local C² finite matrix field is frozen outside a constructed compact
cutoff, remains equal to the original near the compact core, and produces genuine
bounded C² heat data with uniformly continuous second derivatives entrywise.
The constant exterior is the caller's selected matrix, not the zero matrix. -/
theorem exists_frozenC2MatrixHeatData
    {n d : ℕ} {G : (Fin n → ℝ) → (Fin d → Fin d → ℝ)}
    {K U : Set (Fin n → ℝ)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hG : ContDiffOn ℝ 2 G U) (G₀ : Fin d → Fin d → ℝ) :
    ∃ χ : (Fin n → ℝ) → ℝ,
      ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
      ∃ D : Fin d → Fin d → EuclideanBoundedC2Data n,
        (∀ i k x, (D i k).value x = G₀ i k + χ x * (G x i k - G₀ i k)) ∧
        (∀ᶠ x in 𝓝ˢ K, ∀ i k, (D i k).value x = G x i k) ∧
        (∀ x ∉ tsupport χ, ∀ i k, (D i k).value x = G₀ i k) ∧
        (∀ i k a b, UniformContinuous ((D i k).second a b : (Fin n → ℝ) → ℝ)) := by
  obtain ⟨χ, hχ, hχc, hχU, hχone, hχIcc⟩ :=
    SmoothDependenceCk.exists_contDiff_cutoff_one_nhdsSet_of_isCompact
      (n := (2 : ℕ∞)) hK hU hKU
  let P : (Fin n → ℝ) → (Fin d → Fin d → ℝ) := fun x => χ x • (G x - G₀)
  have hP : ContDiff ℝ 2 P ∧ HasCompactSupport P :=
    SmoothDependenceCk.contDiff_and_hasCompactSupport_cutoff_smul
      hU (hG.sub contDiffOn_const) hχ hχc hχU
  have hPe : ∀ i k, ContDiff ℝ 2 (fun x => P x i k) := fun i k =>
    contDiff_pi.mp (contDiff_pi.mp hP.1 i) k
  have hPec : ∀ i k, HasCompactSupport (fun x => P x i k) := by
    intro i k
    exact hP.2.comp_left (g := fun A : Fin d → Fin d → ℝ => A i k) rfl
  let D : Fin d → Fin d → EuclideanBoundedC2Data n := fun i k =>
    (EuclideanBoundedC2Data.ofCompactSupport (hPe i k) (hPec i k)).addConst (G₀ i k)
  refine ⟨χ, hχ, hχc, hχU, hχIcc, D, ?_, ?_, ?_, ?_⟩
  · intro i k x
    rfl
  · filter_upwards [hχone] with x hx i k
    change G₀ i k + χ x * (G x i k - G₀ i k) = G x i k
    rw [hx, one_mul]
    ring
  · intro x hx i k
    change G₀ i k + χ x * (G x i k - G₀ i k) = G₀ i k
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, add_zero]
  · intro i k a b
    exact EuclideanBoundedC2Data.uniformContinuous_second_ofCompactSupport
      (hPe i k) (hPec i k) a b

end RicciFlow.AnalyticPDE
