module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Fiberwise composition of smooth hom-bundle sections

Mathlib's `Mathlib.Geometry.Manifold.VectorBundle.Hom` provides `ContMDiff.clm_bundle_apply`
(applying a smooth family of linear maps to a smooth section) and `clm_bundle_apply₂`, but no lemma
composing two smooth hom-bundle sections into a smooth hom-bundle section.

This module supplies exactly that: given `C^n` sections
`ϕ : ∀ x, E₂ x →L[𝕜] E₃ x` and `ψ : ∀ x, E₁ x →L[𝕜] E₂ x` of the hom bundles, the fiberwise
composition `x ↦ (ϕ x).comp (ψ x)` is a `C^n` section of `Hom(E₁, E₃)`.

The proof reduces `ContMDiff*_hom_bundle` to the `inCoordinates` representation and uses the fact
that, on the base set of the middle trivialization, the coordinate readout of a composition is the
composition of the coordinate readouts (the middle `symmL ∘ continuousLinearMapAt = id`
cancellation), reducing to the ordinary normed-space `ContMDiff*.clm_comp`.

* `inCoordinates_comp_eq` — the coordinate-readout factorization on the middle base set.
* `ContMDiffWithinAt.clm_bundle_comp` / `ContMDiffAt.clm_bundle_comp` / `ContMDiffOn.clm_bundle_comp`
  / `ContMDiff.clm_bundle_comp` — the composition of two smooth hom-bundle sections is smooth.
-/

@[expose] public noncomputable section

open Bundle Set ContinuousLinearMap

open scoped Manifold Bundle Topology

section

variable {𝕜 B F₁ F₂ F₃ : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {E₃ : B → Type*} [∀ x, AddCommGroup (E₃ x)]
  [∀ x, Module 𝕜 (E₃ x)] [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  [TopologicalSpace (TotalSpace F₃ E₃)] [∀ x, TopologicalSpace (E₃ x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]

/-- The coordinate readout of a fiberwise composition factors through the coordinate readouts, on
the base set of the middle trivialization: the intermediate `symmL ∘ continuousLinearMapAt` cancels
to the identity. -/
theorem inCoordinates_comp_eq {x₀ x : B}
    (hx : x ∈ (trivializationAt F₂ E₂ x₀).baseSet)
    (ϕ : E₂ x →L[𝕜] E₃ x) (ψ : E₁ x →L[𝕜] E₂ x) :
    ContinuousLinearMap.inCoordinates F₁ E₁ F₃ E₃ x₀ x x₀ x (ϕ.comp ψ) =
      (ContinuousLinearMap.inCoordinates F₂ E₂ F₃ E₃ x₀ x x₀ x ϕ).comp
        (ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x₀ x x₀ x ψ) := by
  simp only [ContinuousLinearMap.inCoordinates]
  ext y
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [Trivialization.symmL_continuousLinearMapAt (trivializationAt F₂ E₂ x₀) hx]

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [∀ x, IsTopologicalAddGroup (E₃ x)] [∀ x, ContinuousSMul 𝕜 (E₃ x)]

/-- The fiberwise composition of two `C^n` hom-bundle sections is a `C^n` hom-bundle section
(within-a-set-at-a-point version). -/
theorem ContMDiffWithinAt.clm_bundle_comp
    {ϕ : ∀ x, E₂ x →L[𝕜] E₃ x} {ψ : ∀ x, E₁ x →L[𝕜] E₂ x} {s : Set B} {x₀ : B}
    (hϕ : ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₃)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃) (E := fun x ↦ E₂ x →L[𝕜] E₃ x) x (ϕ x)) s x₀)
    (hψ : ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (ψ x)) s x₀) :
    ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₃)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₃) (E := fun x ↦ E₁ x →L[𝕜] E₃ x) x ((ϕ x).comp (ψ x)))
      s x₀ := by
  rw [contMDiffWithinAt_hom_bundle] at hϕ hψ ⊢
  refine ⟨hϕ.1, ?_⟩
  have hcomp := hϕ.2.clm_comp hψ.2
  have hmem : (trivializationAt F₂ E₂ x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt F₂ E₂ x₀).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' x₀)
  have hev :
      (fun x ↦ ContinuousLinearMap.inCoordinates F₁ E₁ F₃ E₃ x₀ x x₀ x ((ϕ x).comp (ψ x)))
        =ᶠ[𝓝[s] x₀]
      (fun x ↦ (ContinuousLinearMap.inCoordinates F₂ E₂ F₃ E₃ x₀ x x₀ x (ϕ x)).comp
        (ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x₀ x x₀ x (ψ x))) := by
    refine Filter.eventuallyEq_of_mem (nhdsWithin_le_nhds hmem) ?_
    intro x hx
    exact inCoordinates_comp_eq hx (ϕ x) (ψ x)
  exact hcomp.congr_of_eventuallyEq hev
    (inCoordinates_comp_eq (FiberBundle.mem_baseSet_trivializationAt' x₀) (ϕ x₀) (ψ x₀))

/-- The fiberwise composition of two `C^n` hom-bundle sections is a `C^n` hom-bundle section
(at-a-point version). -/
theorem ContMDiffAt.clm_bundle_comp
    {ϕ : ∀ x, E₂ x →L[𝕜] E₃ x} {ψ : ∀ x, E₁ x →L[𝕜] E₂ x} {x₀ : B}
    (hϕ : ContMDiffAt IB (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₃)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃) (E := fun x ↦ E₂ x →L[𝕜] E₃ x) x (ϕ x)) x₀)
    (hψ : ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (ψ x)) x₀) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₃)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₃) (E := fun x ↦ E₁ x →L[𝕜] E₃ x) x ((ϕ x).comp (ψ x)))
      x₀ := by
  rw [← contMDiffWithinAt_univ] at hϕ hψ ⊢
  exact hϕ.clm_bundle_comp hψ

/-- The fiberwise composition of two `C^n` hom-bundle sections is a `C^n` hom-bundle section
(on-a-set version). -/
theorem ContMDiffOn.clm_bundle_comp
    {ϕ : ∀ x, E₂ x →L[𝕜] E₃ x} {ψ : ∀ x, E₁ x →L[𝕜] E₂ x} {s : Set B}
    (hϕ : ContMDiffOn IB (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₃)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃) (E := fun x ↦ E₂ x →L[𝕜] E₃ x) x (ϕ x)) s)
    (hψ : ContMDiffOn IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (ψ x)) s) :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₃)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₃) (E := fun x ↦ E₁ x →L[𝕜] E₃ x) x ((ϕ x).comp (ψ x)))
      s :=
  fun x hx ↦ (hϕ x hx).clm_bundle_comp (hψ x hx)

/-- The fiberwise composition of two `C^n` hom-bundle sections is a `C^n` hom-bundle section. -/
theorem ContMDiff.clm_bundle_comp
    {ϕ : ∀ x, E₂ x →L[𝕜] E₃ x} {ψ : ∀ x, E₁ x →L[𝕜] E₂ x}
    (hϕ : ContMDiff IB (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₃)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃) (E := fun x ↦ E₂ x →L[𝕜] E₃ x) x (ϕ x)))
    (hψ : ContMDiff IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (ψ x))) :
    ContMDiff IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₃)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₃) (E := fun x ↦ E₁ x →L[𝕜] E₃ x) x ((ϕ x).comp (ψ x))) :=
  fun x ↦ (hϕ x).clm_bundle_comp (hψ x)

end
