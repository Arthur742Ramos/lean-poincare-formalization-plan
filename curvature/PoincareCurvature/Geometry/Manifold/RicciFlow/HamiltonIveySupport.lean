module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveySpectrum

/-!
# Spacetime support for the least curvature eigenvalue

At a spacetime contact point, choose the genuine unit least eigenvector and
extend it smoothly in space while keeping that extension fixed in time.  Its
Rayleigh quotient is a spacetime upper support for the least curvature
eigenvalue wherever the evolving metric keeps the extension nonzero.

Joint continuity of the evolving metric square is an explicit analytic
premise; the spectral support and the contact equality are proved here.
-/

@[expose] public noncomputable section

set_option linter.style.haveILetI false

open Bundle Filter Set Topology
open scoped Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The fixed-in-time smooth spatial extension of the least eigenvector
selected at `(t₀,x₀)`. -/
def curvatureNuContactVectorField
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) : ∀ y : M, TM y :=
  smoothExtend (I := I) (F := E) (V := TM) x₀
    (g.curvatureNuEigenvector cov hcov hLevi hdim t₀ x₀)

/-- The spacetime Rayleigh quotient obtained from the contact vector field. -/
def curvatureNuSpacetimeSupport
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) (p : ℝ × M) : ℝ :=
  g.curvatureRayleighQuotient cov hcov p.1 p.2
    (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ p.2)

/-- The spacetime support touches the least curvature eigenvalue at its
contact point. -/
theorem curvatureNuSpacetimeSupport_eq_at_contact
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) :
    g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ (t₀, x₀) =
      g.curvatureNu cov hcov hLevi hdim t₀ x₀ := by
  rw [curvatureNuSpacetimeSupport, curvatureNuContactVectorField,
    smoothExtend_apply]
  exact g.curvatureRayleighQuotient_curvatureNuEigenvector
    cov hcov hLevi hdim t₀ x₀

/-- Joint continuity of the contact field's metric square makes the
spacetime support valid on a full neighborhood of the contact point. -/
theorem curvatureNu_le_spacetimeSupport_eventually
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M)
    (hnormContinuous : ContinuousAt
      (fun p : ℝ × M => (g p.1).inner p.2
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ p.2)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ p.2))
      (t₀, x₀)) :
    ∀ᶠ p in nhds (t₀, x₀),
      g.curvatureNu cov hcov hLevi hdim p.1 p.2 ≤
        g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ p := by
  have hbase : (g t₀).inner x₀
      (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀)
      (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ x₀) = 1 := by
    rw [curvatureNuContactVectorField, smoothExtend_apply]
    exact g.inner_curvatureNuEigenvector_self cov hcov hLevi hdim t₀ x₀
  have hpositive : ∀ᶠ p in nhds (t₀, x₀),
      0 < (g p.1).inner p.2
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ p.2)
        (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ p.2) := by
    exact hnormContinuous.eventually
      (isOpen_Ioi.mem_nhds (by simpa [hbase]))
  filter_upwards [hpositive] with p hp
  exact g.curvatureNu_le_curvatureRayleighQuotient
    cov hcov hLevi hdim p.1 p.2 hp

end CovariantDerivative.TimeDependentRiemannianMetric
