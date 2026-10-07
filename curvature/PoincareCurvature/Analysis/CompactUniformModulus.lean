/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Uniform ambient continuity near a compact set

Compactness makes ordinary continuity at the points of a compact set uniform
for comparisons with nearby points in the ambient space. The second point is
not required to belong to the compact set. This is stronger than continuity
uniformly restricted to the set and requires no global uniform continuity.
Boundedness is not needed for the modulus; the bounded-continuous wrapper is
provided for heat-kernel applications.
-/

open scoped Topology BoundedContinuousFunction

namespace PoincareCurvature.CompactUniformModulus

/-- Continuity at every point of a compact set gives a common positive metric
radius for comparison with arbitrary nearby ambient points. -/
theorem exists_pos_dist_modulus_of_continuousAt
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {K : Set X} (hK : IsCompact K) (f : X → Y)
    (hf : ∀ x ∈ K, ContinuousAt f x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y : X, dist x y < δ → dist (f y) (f x) < ε := by
  have h := hK.uniformContinuousAt_of_continuousAt f hf (Metric.dist_mem_uniformity hε)
  obtain ⟨δ, hδ, hmod⟩ := Metric.mem_uniformity_dist.mp h
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hxy
  have hdist : dist (f x) (f y) < ε := hmod hxy hx
  simpa only [dist_comm] using hdist

/-- A scalar continuous function has a uniform ambient modulus near a compact
set of a normed additive group. Only the first point lies in the compact set. -/
theorem exists_pos_norm_modulus_of_continuousAt
    {E : Type*} [NormedAddCommGroup E]
    {K : Set E} (hK : IsCompact K) (f : E → ℝ)
    (hf : ∀ x ∈ K, ContinuousAt f x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y : E, ‖x - y‖ < δ → |f y - f x| ≤ ε := by
  obtain ⟨δ, hδ, hmod⟩ := exists_pos_dist_modulus_of_continuousAt hK f hf hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hxy
  have hdist := hmod x hx y (by simpa only [dist_eq_norm] using hxy)
  exact le_of_lt (by simpa only [Real.dist_eq] using hdist)

/-- Ordinary global continuity suffices; global uniform continuity is not an
assumption. The comparison point can be outside the compact set. -/
theorem exists_pos_norm_modulus_of_continuous
    {E : Type*} [NormedAddCommGroup E]
    {K : Set E} (hK : IsCompact K) (f : E → ℝ)
    (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y : E, ‖x - y‖ < δ → |f y - f x| ≤ ε :=
  exists_pos_norm_modulus_of_continuousAt hK f (fun _ _ => hf.continuousAt) hε

/-- Bounded continuous scalar functions admit the compact-uniform ambient
modulus used in heat-trace estimates. -/
theorem exists_pos_norm_modulus_boundedContinuous
    {E : Type*} [NormedAddCommGroup E]
    {K : Set E} (hK : IsCompact K) (f : E →ᵇ ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y : E, ‖x - y‖ < δ → |f y - f x| ≤ ε :=
  exists_pos_norm_modulus_of_continuous hK f f.continuous hε

end PoincareCurvature.CompactUniformModulus
