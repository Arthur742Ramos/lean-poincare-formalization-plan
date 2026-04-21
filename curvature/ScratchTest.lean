-- Minimal test to check the four proof blocks at lines 453, 487, 518, 552

import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Existence
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

open Bundle FiberBundle
open scoped Bundle Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I 2 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

namespace CovariantDerivative

local notation "TM" => (TangentSpace I : M → Type _)
local notation "⟪" x ", " y "⟫" => inner ℝ x y

-- Simplified correctionFunctional to test the problematic proofs
noncomputable def testCorrectionFunctional (cov : CovariantDerivative I E TM) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦
        LinearMap.toContinuousLinearMap
          { toFun := fun u ↦
              LinearMap.toContinuousLinearMap
                { toFun := fun w ↦
                    (cov.metricDefect x v w u + cov.metricDefect x u w v -
                        cov.metricDefect x u v w -
                        ⟪cov.torsion x u v, w⟫ + ⟪cov.torsion x v w, u⟫ -
                        ⟪cov.torsion x w u, v⟫) / 2
                  map_add' := by
                    intro w₁ w₂
                    simp only [ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply,
                      inner_add_right, inner_add_left, add_div]
                    linarith
                  map_smul' := by
                    intro c w
                    simp only [ContinuousLinearMap.map_smulₛₗ, RingHom.id_apply,
                      ContinuousLinearMap.smul_apply, real_inner_smul_right,
                      real_inner_smul_left, smul_eq_mul, mul_div_assoc]
                    linarith }
             -- LINE 453 - FIRST PROOF BLOCK: map_add' for u
             map_add' := by
               intro u₁ u₂
               ext w
               have hD₁ :
                   cov.metricDefect x v w (u₁ + u₂) =
                     cov.metricDefect x v w u₁ + cov.metricDefect x v w u₂ := by
                 simpa using (cov.metricDefect x v w).map_add u₁ u₂
               have hD₂ :
                   cov.metricDefect x (u₁ + u₂) w v =
                     cov.metricDefect x u₁ w v + cov.metricDefect x u₂ w v := by
                 simpa [ContinuousLinearMap.add_apply] using
                   congrArg (fun f ↦ f w v) ((cov.metricDefect x).map_add u₁ u₂)
               have hD₃ :
                   cov.metricDefect x (u₁ + u₂) v w =
                     cov.metricDefect x u₁ v w + cov.metricDefect x u₂ v w := by
                 simpa [ContinuousLinearMap.add_apply] using
                   congrArg (fun f ↦ f v w) ((cov.metricDefect x).map_add u₁ u₂)
               have hT₁ :
                   ⟪cov.torsion x (u₁ + u₂) v, w⟫ =
                     ⟪cov.torsion x u₁ v, w⟫ + ⟪cov.torsion x u₂ v, w⟫ := by
                 simpa [ContinuousLinearMap.add_apply, inner_add_left] using
                   congrArg (fun f ↦ ⟪f v, w⟫) ((cov.torsion x).map_add u₁ u₂)
               have hT₂ :
                   ⟪cov.torsion x v w, u₁ + u₂⟫ =
                     ⟪cov.torsion x v w, u₁⟫ + ⟪cov.torsion x v w, u₂⟫ := by
                 rw [inner_add_right]
               have hT₃ :
                   ⟪cov.torsion x w (u₁ + u₂), v⟫ =
                     ⟪cov.torsion x w u₁, v⟫ + ⟪cov.torsion x w u₂, v⟫ := by
                 simpa [ContinuousLinearMap.add_apply, inner_add_left] using
                   congrArg (fun z ↦ ⟪z, v⟫) ((cov.torsion x w).map_add u₁ u₂)
               simp [hD₁, hD₂, hD₃, hT₁, hT₂, hT₃, add_div]
               field_simp
               ring
             -- LINE 487 - SECOND PROOF BLOCK: map_smul' for u
             map_smul' := by
               intro c u
               ext w
               have hD₁ :
                   cov.metricDefect x v w (c • u) = c * cov.metricDefect x v w u := by
                 simpa [smul_eq_mul, RingHom.id_apply] using
                   (cov.metricDefect x v w).map_smulₛₗ c u
               have hD₂ :
                   cov.metricDefect x (c • u) w v = c * cov.metricDefect x u w v := by
                 simpa [ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] using
                   congrArg (fun f ↦ f w v) ((cov.metricDefect x).map_smulₛₗ c u)
               have hD₃ :
                   cov.metricDefect x (c • u) v w = c * cov.metricDefect x u v w := by
                 simpa [ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] using
                   congrArg (fun f ↦ f v w) ((cov.metricDefect x).map_smulₛₗ c u)
               have hT₁ :
                   ⟪cov.torsion x (c • u) v, w⟫ = c * ⟪cov.torsion x u v, w⟫ := by
                 simpa [ContinuousLinearMap.smul_apply, real_inner_smul_left,
                   smul_eq_mul, RingHom.id_apply] using
                   congrArg (fun f ↦ ⟪f v, w⟫) ((cov.torsion x).map_smulₛₗ c u)
               have hT₂ :
                   ⟪cov.torsion x v w, c • u⟫ = c * ⟪cov.torsion x v w, u⟫ := by
                 simpa [smul_eq_mul] using real_inner_smul_right (cov.torsion x v w) u c
               have hT₃ :
                   ⟪cov.torsion x w (c • u), v⟫ = c * ⟪cov.torsion x w u, v⟫ := by
                 simpa [ContinuousLinearMap.smul_apply, real_inner_smul_left,
                   smul_eq_mul, RingHom.id_apply] using
                   congrArg (fun z ↦ ⟪z, v⟫) ((cov.torsion x w).map_smulₛₗ c u)
               simp [hD₁, hD₂, hD₃, hT₁, hT₂, hT₃, mul_div_assoc]
               field_simp
               ring }
      -- LINE 518 - THIRD PROOF BLOCK: map_add' for v
      map_add' := by
        intro v₁ v₂
        ext u w
        have hD₁ :
            cov.metricDefect x (v₁ + v₂) w u =
              cov.metricDefect x v₁ w u + cov.metricDefect x v₂ w u := by
          simpa [ContinuousLinearMap.add_apply] using
            congrArg (fun f ↦ f w u) ((cov.metricDefect x).map_add v₁ v₂)
        have hD₂ :
            cov.metricDefect x u w (v₁ + v₂) =
              cov.metricDefect x u w v₁ + cov.metricDefect x u w v₂ := by
          simpa using (cov.metricDefect x u w).map_add v₁ v₂
        have hD₃ :
            cov.metricDefect x u (v₁ + v₂) w =
              cov.metricDefect x u v₁ w + cov.metricDefect x u v₂ w := by
          simpa [ContinuousLinearMap.add_apply] using
            congrArg (fun f ↦ f w) ((cov.metricDefect x u).map_add v₁ v₂)
        have hT₁ :
            ⟪cov.torsion x u (v₁ + v₂), w⟫ =
              ⟪cov.torsion x u v₁, w⟫ + ⟪cov.torsion x u v₂, w⟫ := by
          simpa [inner_add_left] using
            congrArg (fun z ↦ ⟪z, w⟫) ((cov.torsion x u).map_add v₁ v₂)
        have hT₂ :
            ⟪cov.torsion x (v₁ + v₂) w, u⟫ =
              ⟪cov.torsion x v₁ w, u⟫ + ⟪cov.torsion x v₂ w, u⟫ := by
          simpa [ContinuousLinearMap.add_apply, inner_add_left] using
            congrArg (fun f ↦ ⟪f w, u⟫) ((cov.torsion x).map_add v₁ v₂)
        have hT₃ :
            ⟪cov.torsion x w u, v₁ + v₂⟫ =
              ⟪cov.torsion x w u, v₁⟫ + ⟪cov.torsion x w u, v₂⟫ := by
          rw [inner_add_right]
        simp [hD₁, hD₂, hD₃, hT₁, hT₂, hT₃, add_div]
        field_simp
        ring
      -- LINE 552 - FOURTH PROOF BLOCK: map_smul' for v
      map_smul' := by
        intro c v
        ext u w
        have hD₁ :
            cov.metricDefect x (c • v) w u = c * cov.metricDefect x v w u := by
          simpa [ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] using
            congrArg (fun f ↦ f w u) ((cov.metricDefect x).map_smulₛₗ c v)
        have hD₂ :
            cov.metricDefect x u w (c • v) = c * cov.metricDefect x u w v := by
          simpa [smul_eq_mul, RingHom.id_apply] using
            (cov.metricDefect x u w).map_smulₛₗ c v
        have hD₃ :
            cov.metricDefect x u (c • v) w = c * cov.metricDefect x u v w := by
          simpa [ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] using
            congrArg (fun f ↦ f w) ((cov.metricDefect x u).map_smulₛₗ c v)
        have hT₁ :
            ⟪cov.torsion x u (c • v), w⟫ = c * ⟪cov.torsion x u v, w⟫ := by
          simpa [real_inner_smul_left, smul_eq_mul, RingHom.id_apply] using
            congrArg (fun z ↦ ⟪z, w⟫) ((cov.torsion x u).map_smulₛₗ c v)
        have hT₂ :
            ⟪cov.torsion x (c • v) w, u⟫ = c * ⟪cov.torsion x v w, u⟫ := by
          simpa [ContinuousLinearMap.smul_apply, real_inner_smul_left,
            smul_eq_mul, RingHom.id_apply] using
            congrArg (fun f ↦ ⟪f w, u⟫) ((cov.torsion x).map_smulₛₗ c v)
        have hT₃ :
            ⟪cov.torsion x w u, c • v⟫ = c * ⟪cov.torsion x w u, v⟫ := by
          simpa [smul_eq_mul] using real_inner_smul_right (cov.torsion x w u) v c
        simp [hD₁, hD₂, hD₃, hT₁, hT₂, hT₃, mul_div_assoc]
        field_simp
        ring }

end CovariantDerivative
