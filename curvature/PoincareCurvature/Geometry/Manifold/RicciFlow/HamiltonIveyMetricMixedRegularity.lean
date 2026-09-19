import PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyMixedRegularity
import PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyKoszulVariation

/-!
# Mixed regularity of metric pairings

This module specializes the intrinsic chart bridge to the scalar pairings that occur in the
Koszul formula.  The joint spacetime regularity and spatial regularity of the velocity pairing
remain explicit hypotheses: they are genuine analytic regularity, not consequences of the
slicewise `TimeDependentRiemannianMetric` abbreviation.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [I.Boundaryless]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

set_option maxHeartbeats 1000000 in
theorem hasDerivAt_metricPairing_mvfderiv_of_jointContMDiff
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    {t : ℝ}
    (hmetric : ∀ (x : M) (u v : TM x),
      HasDerivAt (fun τ : ℝ => (g τ).inner x u v) (hdot x u v) t)
    {X Y Z : Π y : M, TM y} (x : M)
    (hjoint : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
      (fun p : ℝ × M => (g p.1).inner p.2 (Y p.2) (Z p.2)))
    (hdotSpace : MDiffAt (fun y : M => hdot y (Y y) (Z y)) x) :
    HasDerivAt
      (fun τ : ℝ => mvfderiv (I := I)
        (fun y : M => (g τ).inner y (Y y) (Z y)) x (X x))
      (mvfderiv (I := I) (fun y : M => hdot y (Y y) (Z y)) x (X x)) t := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  exact PoincareCurvature.hasDerivAt_mvfderiv_of_joint_contMDiff
    (F := fun τ y => (g τ).inner y (Y y) (Z y))
    (Fdot := fun y => hdot y (Y y) (Z y)) hjoint
    (fun y => hmetric y (Y y) (Z y)) x hdotSpace (X x)

/- The preceding scalar bridge discharges all three mixed-derivative families in the
finite-dimensional Koszul constructor. -/
set_option maxHeartbeats 1000000 in
theorem exists_hasDerivAt_along_const_of_jointMetricPairingRegularity
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    {t : ℝ}
    (hmetric : ∀ (x : M) (u v : TM x),
      HasDerivAt (fun τ : ℝ => (g τ).inner x u v) (hdot x u v) t)
    {X Y : Π y : M, TM y} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hjointXYZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (Y p.2) (Z p.2)))
    (hdotSpaceXYZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      MDiffAt (fun y ↦ hdot y (Y y) (Z y)) x)
    (hjointYXZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (X p.2) (Z p.2)))
    (hdotSpaceYXZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      MDiffAt (fun y ↦ hdot y (X y) (Z y)) x)
    (hjointZXY : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (X p.2) (Y p.2)))
    (hdotSpaceZXY : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      MDiffAt (fun y ↦ hdot y (X y) (Y y)) x) :
    ∃ Axy : TM x, HasDerivAt (fun τ : ℝ => (cov τ).along X Y x) Axy t := by
  apply exists_hasDerivAt_along_const_of_koszulExpression
    (I := I) (M := M) g cov hcov hLevi hdot (t := t) hmetric
    (X := X) (Y := Y) (x := x) hX hY
  · intro Z hZ
    exact hasDerivAt_metricPairing_mvfderiv_of_jointContMDiff
      (I := I) (M := M) g hdot (t := t) hmetric (X := X) (Y := Y) (Z := Z)
      x (hjointXYZ Z hZ) (hdotSpaceXYZ Z hZ)
  · intro Z hZ
    exact hasDerivAt_metricPairing_mvfderiv_of_jointContMDiff
      (I := I) (M := M) g hdot (t := t) hmetric (X := Y) (Y := X) (Z := Z)
      x (hjointYXZ Z hZ) (hdotSpaceYXZ Z hZ)
  · intro Z hZ
    exact hasDerivAt_metricPairing_mvfderiv_of_jointContMDiff
      (I := I) (M := M) g hdot (t := t) hmetric (X := Z) (Y := X) (Z := Y)
      x (hjointZXY Z hZ) (hdotSpaceZXY Z hZ)

/- The same replacement can be made at the cyclic level.  Thus the fixed-field
connection velocity used by the geometric evolution interface is obtained from
the actual spacetime metric pairings, rather than from three opaque mixed-
derivative assumptions. -/
set_option maxHeartbeats 1000000 in
theorem exists_hasDerivAt_along_const_with_cyclic_metricVariation_of_jointMetricPairingRegularity
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdot : ∀ x : M, TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ)
    {t : ℝ}
    (hmetric : ∀ (x : M) (u v : TM x),
      HasDerivAt (fun τ : ℝ => (g τ).inner x u v) (hdot x u v) t)
    {X Y : Π y : M, TM y} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hjointXYZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (Y p.2) (Z p.2)))
    (hdotSpaceXYZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      MDiffAt (fun y ↦ hdot y (Y y) (Z y)) x)
    (hjointYXZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (X p.2) (Z p.2)))
    (hdotSpaceYXZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      MDiffAt (fun y ↦ hdot y (X y) (Z y)) x)
    (hjointZXY : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (X p.2) (Y p.2)))
    (hdotSpaceZXY : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      MDiffAt (fun y ↦ hdot y (X y) (Y y)) x) :
    ∃ Axy : TM x,
      HasDerivAt (fun τ : ℝ => (cov τ).along X Y x) Axy t ∧
      ∀ (Z : Π y : M, TM y),
        ContMDiff I (I.prod 𝓘(ℝ, E)) 1
          (fun y ↦ TotalSpace.mk' E y (Z y)) →
        2 * (g t).inner x Axy (Z x) =
          metricVelocityCovariantDerivativeAlong
              (I := I) (M := M) cov hdot t X Y Z x +
            metricVelocityCovariantDerivativeAlong
              (I := I) (M := M) cov hdot t Y X Z x -
            metricVelocityCovariantDerivativeAlong
              (I := I) (M := M) cov hdot t Z X Y x := by
  apply exists_hasDerivAt_along_const_with_cyclic_metricVariation
    (I := I) (M := M) g cov hcov hLevi hdot (t := t) hmetric
    (X := X) (Y := Y) (x := x) hX hY
  · intro Z hZ
    exact hasDerivAt_metricPairing_mvfderiv_of_jointContMDiff
      (I := I) (M := M) g hdot (t := t) hmetric (X := X) (Y := Y) (Z := Z)
      x (hjointXYZ Z hZ) (hdotSpaceXYZ Z hZ)
  · intro Z hZ
    exact hasDerivAt_metricPairing_mvfderiv_of_jointContMDiff
      (I := I) (M := M) g hdot (t := t) hmetric (X := Y) (Y := X) (Z := Z)
      x (hjointYXZ Z hZ) (hdotSpaceYXZ Z hZ)
  · intro Z hZ
    exact hasDerivAt_metricPairing_mvfderiv_of_jointContMDiff
      (I := I) (M := M) g hdot (t := t) hmetric (X := Z) (Y := X) (Z := Y)
      x (hjointZXY Z hZ) (hdotSpaceZXY Z hZ)

end CovariantDerivative.TimeDependentRiemannianMetric
