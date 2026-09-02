import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Bianchi

public noncomputable section

open Bundle
open scoped Bundle Manifold ContDiff

namespace PoincareCurvature.Palomar

def rawSecondBianchi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z W : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  cov.along X (cov.curvatureAux Y Z W) -
    cov.curvatureAux (cov.along X Y) Z W -
    cov.curvatureAux Y (cov.along X Z) W -
    cov.curvatureAux Y Z (cov.along X W)

theorem first_bianchi_raw_of_torsion_free
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative 1]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (hT : cov.torsion = 0)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y (Z y))) :
    cov.curvatureAux X Y Z x + cov.curvatureAux Y Z X x + cov.curvatureAux Z X Y x = 0 := by
  exact CovariantDerivative.firstBianchiAux_apply_of_torsion_eq_zero cov hT hX hY hZ

theorem second_bianchi_raw_of_torsion_free
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
    [IsManifold I (minSmoothness ℝ 2) M]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I (minSmoothness ℝ 4) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [IsManifold I ((3 : ℕ∞) + 1) M]
    (hT : cov.torsion = 0)
    {X Y Z W : Π x : M, TangentSpace I x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y (Z y)))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3
      (fun y ↦ TotalSpace.mk' E y (W y))) :
    rawSecondBianchi cov X Y Z W x + rawSecondBianchi cov Y Z X W x +
      rawSecondBianchi cov Z X Y W x = 0 := by
  simpa [rawSecondBianchi, CovariantDerivative.secondBianchiAux] using
    (CovariantDerivative.secondBianchiAux_apply_of_torsion_eq_zero cov hT hX hY hZ hW)

end PoincareCurvature.Palomar
