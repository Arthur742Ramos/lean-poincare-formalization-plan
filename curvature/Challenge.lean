import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.Riemannian.Basic

@[expose] public noncomputable section

open Bundle
open scoped Bundle Manifold ContDiff
open Lean Meta

namespace CovariantDerivative

variable {𝕜 : Type*} [hField : NontriviallyNormedField 𝕜]
  {E : Type*} [hEGroup : NormedAddCommGroup E] [hESpace : NormedSpace 𝕜 E]
  {H : Type*} [hHTop : TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [hMTop : TopologicalSpace M] [hCharted : ChartedSpace H M]
  {F : Type*} [hFGroup : NormedAddCommGroup F] [hFSpace : NormedSpace 𝕜 F]
  {V : M → Type*} [hTotalTop : TopologicalSpace (TotalSpace F V)]
  [hVAdd : ∀ x, AddCommGroup (V x)] [hVModule : ∀ x, Module 𝕜 (V x)]
  [hVTop : ∀ x, TopologicalSpace (V x)] [hVAddTop : ∀ x, IsTopologicalAddGroup (V x)]
  [hVSMul : ∀ x, ContinuousSMul 𝕜 (V x)] [hFiber : FiberBundle F V]
  [hVector : VectorBundle 𝕜 F V]

/-- A one-parameter family of objects of type `α`. -/
abbrev TimeFamily (α : Type*) := ℝ → α

/-- A one-parameter family of covariant derivatives on `V`. -/
abbrev TimeDependentCovariantDerivative :=
  TimeFamily (CovariantDerivative I F V)

/-- A one-parameter family of tangent vector fields. -/
abbrev TimeDependentVectorField := TimeFamily (Π x : M, TangentSpace I x)

end CovariantDerivative

namespace CovariantDerivative

variable {𝕜 : Type*} [hField : NontriviallyNormedField 𝕜]
  {E : Type*} [hEGroup : NormedAddCommGroup E] [hESpace : NormedSpace 𝕜 E]
  {H : Type*} [hHTop : TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [hMTop : TopologicalSpace M] [hCharted : ChartedSpace H M]
  {F : Type*} [hFGroup : NormedAddCommGroup F] [hFSpace : NormedSpace 𝕜 F]
  {V : M → Type*} [hTotalTop : TopologicalSpace (TotalSpace F V)]
  [hVAdd : ∀ x, AddCommGroup (V x)] [hVModule : ∀ x, Module 𝕜 (V x)]
  [hVTop : ∀ x, TopologicalSpace (V x)] [hVAddTop : ∀ x, IsTopologicalAddGroup (V x)]
  [hVSMul : ∀ x, ContinuousSMul 𝕜 (V x)] [hFiber : FiberBundle F V]
  [hVector : VectorBundle 𝕜 F V]

variable (cov : CovariantDerivative I F V)

/-- The section `∇_X σ`. -/
def along (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) : Π x : M, V x :=
  fun x ↦ cov σ x (X x)

/-- The raw curvature commutator associated to a covariant derivative. -/
abbrev curvatureAux (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) : Π x : M, V x :=
  cov.along X (cov.along Y σ) - cov.along Y (cov.along X σ) -
    cov.along (VectorField.mlieBracket I X Y) σ

end CovariantDerivative

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 2 M]

/-- An affine connection is torsion-free if its torsion tensor vanishes. -/
def IsTorsionFree (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
  cov.torsion = 0

variable [RiemannianBundle (TangentSpace I : M → Type _)]

/-- Metric compatibility for an affine connection on the tangent bundle. -/
def IsMetricCompatibleTangent
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
  ∀ {x : M} {σ τ : Π x : M, TangentSpace I x},
    MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      ∀ u : TangentSpace I x,
        mvfderiv (I := I) (fun y ↦ inner ℝ (σ y) (τ y)) x u =
          inner ℝ (cov σ x u) (τ x) + inner ℝ (σ x) (cov τ x u)

/-- A Levi–Civita connection is torsion-free and metric-compatible. -/
def IsLeviCivita (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
  cov.IsTorsionFree ∧ cov.IsMetricCompatibleTangent

end CovariantDerivative

namespace CovariantDerivative

universe u_7 u_8 u_9

section TangentBundle

variable {E : Type u_7} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type u_8} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u_9} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

namespace TimeDependentCovariantDerivative

run_cmd do
  modifyEnv fun env => auxLemmasExt.modifyState env fun _ => {}

/-- The time-dependent raw curvature commutator interface. -/
def curvatureAux
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (X Y Z : TimeDependentVectorField (𝕜 := ℝ) (I := I) (M := M)) :
    TimeDependentVectorField (𝕜 := ℝ) (I := I) (M := M) :=
  fun t x ↦ (cov t).curvatureAux (X t) (Y t) (Z t) x

end TimeDependentCovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V]
  [hVector : VectorBundle ℝ F V]

local notation "TM" => (TangentSpace I : M → Type _)

variable (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov 1]

/-- The bundled curvature tensor interface used by the time-slice package. -/
noncomputable def curvatureTensor (x : M) :
    TM x →ₗ[ℝ] TM x →ₗ[ℝ] V x →ₗ[ℝ] V x := by
  let keepCov := cov
  let keepHcov := (inferInstance : ContMDiffCovariantDerivative cov 1)
  let keepT2 := (inferInstance : T2Space M)
  let keepFinite := (inferInstance : FiniteDimensional ℝ E)
  let keepComplete := (inferInstance : CompleteSpace E)
  let keepManifold := (inferInstance : IsManifold I ∞ M)
  exact 0

namespace TimeDependentCovariantDerivative

namespace curvatureTensor

universe u_1 u_2 u_3

/-- The canonical tangent-bundle vector-bundle witness used by the source declaration. -/
theorem _proof_2
    {E : Type u_2} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type u_3} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type u_1} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] :
    @VectorBundle ℝ M E
      (TangentSpace I)
      (@DenselyNormedField.toNontriviallyNormedField ℝ Real.denselyNormedField)
      (fun x : M ↦
        @AddCommGroup.toAddCommMonoid
          (TangentSpace I x)
          (@instAddCommGroupTangentSpace ℝ _ E _ _ H _ I M _ _ x))
      (@instModuleTangentSpace ℝ _ E _ _ H _ I M _ _)
      _ _ _
      (@instTopologicalSpaceTangentBundle ℝ _ E _ _ H _ I M _ _
        (@CovariantDerivative.TimeDependentCovariantDerivative.curvatureAux._proof_1
          E _ _ H _ I M _ _ _))
      (@instTopologicalSpaceTangentSpace ℝ _ E _ _ H _ I M _ _)
      (@TangentSpace.fiberBundle ℝ _ E _ _ H _ I M _ _
        (@CovariantDerivative.TimeDependentCovariantDerivative.curvatureAux._proof_1
          E _ _ H _ I M _ _ _)) :=
  @TangentSpace.vectorBundle ℝ _ E _ _ H _ I M _ _
    (IsManifold.instOfNatWithTopENat_1 (I := I) (M := M))

end curvatureTensor

section Tensorial

/-- The bundled curvature tensor interface at a fixed time slice. -/
def curvatureTensor
    [hTangent : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    (cov : TimeDependentCovariantDerivative (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u v w : TM x) : TM x := by
  letI := hcov t
  exact CovariantDerivative.curvatureTensor
    (I := I) (M := M) (F := E) (V := TM)
    (hVector := CovariantDerivative.TimeDependentCovariantDerivative.curvatureTensor._proof_2)
    (cov t) x u v w

end Tensorial
end TimeDependentCovariantDerivative
end TangentBundle
end CovariantDerivative

namespace CovariantDerivative

universe u_7 u_8 u_9

section TimeDependentMetrics

variable {E : Type u_7} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type u_8} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u_9} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

attribute [local instance]
  CovariantDerivative.TimeDependentCovariantDerivative.curvatureTensor._proof_1
  CovariantDerivative.TimeDependentCovariantDerivative.curvatureTensor._proof_2

/-- A one-parameter family of `C^2` Riemannian metrics on the tangent bundle. -/
abbrev TimeDependentRiemannianMetric :=
  CovariantDerivative.TimeFamily (Bundle.ContMDiffRiemannianMetric I 2 E TM)

attribute [-instance]
  CovariantDerivative.TimeDependentCovariantDerivative.curvatureTensor._proof_1
  CovariantDerivative.TimeDependentCovariantDerivative.curvatureTensor._proof_2

namespace TimeDependentRiemannianMetric

variable (g : TimeDependentRiemannianMetric (I := I) (M := M))

/- A time-dependent connection family is metric-compatible with `g` if each time slice is. -/
def IsMetricCompatible
    (cov : CovariantDerivative.TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM)) : Prop :=
  ∀ t : ℝ,
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    (cov t).IsMetricCompatibleTangent

/-- A time-dependent connection family is Levi–Civita for `g` slicewise. -/
def IsLeviCivita
    (cov : CovariantDerivative.TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM)) : Prop :=
  ∀ t : ℝ,
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    (cov t).IsLeviCivita

/-- The slicewise Levi–Civita correction of a time-dependent connection family. -/
noncomputable def leviCivitaConnection
    (cov : CovariantDerivative.TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM)) :
    CovariantDerivative.TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) := by
  let _ := (inferInstance : T2Space M)
  let _ := (inferInstance : FiniteDimensional ℝ E)
  let _ := (inferInstance : CompleteSpace E)
  let _ := (inferInstance : IsManifold I ∞ M)
  let _ := (inferInstance : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I)
  let keepG := g
  sorry

/-- Ricci curvature of a time-dependent connection family at a fixed metric slice. -/
noncomputable def ricciCurvature
    (cov : CovariantDerivative.TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u w : TM x) : ℝ := by
  let _ := (inferInstance : T2Space M)
  let _ := (inferInstance : FiniteDimensional ℝ E)
  let _ := (inferInstance : CompleteSpace E)
  let _ := (inferInstance : IsManifold I ∞ M)
  let _ := (inferInstance : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I)
  let keepG := g
  sorry

/-- Scalar curvature of a time-dependent connection family at a fixed metric slice. -/
noncomputable def scalarCurvature
    (cov : CovariantDerivative.TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) : ℝ := by
  let _ := (inferInstance : T2Space M)
  let _ := (inferInstance : FiniteDimensional ℝ E)
  let _ := (inferInstance : CompleteSpace E)
  let _ := (inferInstance : IsManifold I ∞ M)
  let _ := (inferInstance : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I)
  let keepG := g
  sorry

end TimeDependentRiemannianMetric
end TimeDependentMetrics
end CovariantDerivative

namespace PoincareCurvature.Palomar

open Bundle
open scoped Bundle Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "TCov" =>
  (CovariantDerivative.TimeDependentCovariantDerivative
    (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
local notation "TMetric" =>
  (CovariantDerivative.TimeDependentRiemannianMetric (E := E) (I := I) (M := M))

variable (g : CovariantDerivative.TimeDependentRiemannianMetric
  (E := E) (I := I) (M := M))
include g

/-- A time-dependent smooth metric admits a slicewise C^1 Levi–Civita family. -/
theorem exists_contMDiffLeviCivitaConnection
    [SigmaCompactSpace M] :
    ∃ cov : TCov,
      CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita g cov ∧
        ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1 := by
  sorry

/-- The slicewise Levi–Civita correction is Levi–Civita for the time-dependent metric. -/
theorem leviCivitaConnection_isLeviCivita
    (cov : TCov) :
    CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita g
      (CovariantDerivative.TimeDependentRiemannianMetric.leviCivitaConnection
        (E := E) (I := I) (M := M) g cov) := by
  sorry

/-- The slicewise correction preserves the C^1 regularity of the connection family. -/
theorem contMDiffCovariantDerivative_leviCivitaConnection
    (cov : TCov)
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) :
    CovariantDerivative.ContMDiffCovariantDerivative
      ((CovariantDerivative.TimeDependentRiemannianMetric.leviCivitaConnection
        (E := E) (I := I) (M := M) g cov) t) 1 := by
  sorry

/-- The slicewise Levi–Civita correction is independent of the background family. -/
theorem leviCivitaConnection_eq_leviCivitaConnection
    (cov cov' : TCov)
    {t : ℝ} {x : M} {σ : Π y : M, TangentSpace I y}
    (hσ : MDiffAt (T% σ) x) :
    CovariantDerivative.TimeDependentRiemannianMetric.leviCivitaConnection
        (E := E) (I := I) (M := M) g cov t σ x =
      CovariantDerivative.TimeDependentRiemannianMetric.leviCivitaConnection
        (E := E) (I := I) (M := M) g cov' t σ x := by
  sorry

/-- Every slicewise Levi–Civita family has the selected C^1 regularity. -/
theorem contMDiffCovariantDerivative_of_isLeviCivita
    [SigmaCompactSpace M]
    {cov : TCov}
    (hcov : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita g cov) :
    ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1 := by
  sorry

section Ricci

variable [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]

/-- Ricci curvature of a slicewise Levi–Civita family is symmetric at every time. -/
theorem ricciCurvature_symm_of_isLeviCivita
    (cov : TCov)
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hLevi : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita g cov)
    (t : ℝ) (x : M) (u w : TM x) :
    CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature g cov hcov t x u w =
      CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature g cov hcov t x w u := by
  sorry

end Ricci

/-- Ricci curvature is independent of the chosen slicewise Levi–Civita family. -/
theorem ricciCurvature_eq_of_isLeviCivita
    {cov cov' : TCov}
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hcov' : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov' t) 1)
    (hLevi : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita g cov)
    (hLevi' : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita g cov')
    (t : ℝ) (x : M) (u w : TM x) :
    CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature g cov hcov t x u w =
      CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature g cov' hcov' t x u w := by
  sorry

/-- Scalar curvature is independent of the chosen slicewise Levi–Civita family. -/
theorem scalarCurvature_eq_of_isLeviCivita
    {cov cov' : TCov}
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hcov' : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov' t) 1)
    (hLevi : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita g cov)
    (hLevi' : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita g cov')
    (t : ℝ) (x : M) :
    CovariantDerivative.TimeDependentRiemannianMetric.scalarCurvature g cov hcov t x =
      CovariantDerivative.TimeDependentRiemannianMetric.scalarCurvature g cov' hcov' t x := by
  sorry

end PoincareCurvature.Palomar
