import Mathlib.Analysis.InnerProductSpace.Dual

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

noncomputable def correctionFunctional'
    (D : X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ)
    (T : X →L[ℝ] X →L[ℝ] X) :
    X →L[ℝ] X →L[ℝ] (X →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦
        LinearMap.toContinuousLinearMap
          { toFun := fun u ↦
              LinearMap.toContinuousLinearMap
                { toFun := fun w ↦
                    (D v w u + D u w v - D u v w -
                        ⟪T u v, w⟫ + ⟪T v w, u⟫ - ⟪T w u, v⟫) / 2
                  map_add' := by
                    intro w₁ w₂
                    simp only [ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply,
                      inner_add_right, inner_add_left]
                    linarith
                  map_smul' := by
                    intro c w
                    simp only [ContinuousLinearMap.map_smulₛₗ, RingHom.id_apply,
                      ContinuousLinearMap.smul_apply, real_inner_smul_right,
                      real_inner_smul_left, smul_eq_mul]
                    linarith }
            map_add' := by
              intro u₁ u₂
              ext w
              have hD₁ : D v w (u₁ + u₂) = D v w u₁ + D v w u₂ := by
                simpa using (D v w).map_add u₁ u₂
              have hD₂ : D (u₁ + u₂) w v = D u₁ w v + D u₂ w v := by
                simpa [ContinuousLinearMap.add_apply] using
                  congrArg (fun f ↦ f w v) (D.map_add u₁ u₂)
              have hD₃ : D (u₁ + u₂) v w = D u₁ v w + D u₂ v w := by
                simpa [ContinuousLinearMap.add_apply] using
                  congrArg (fun f ↦ f v w) (D.map_add u₁ u₂)
              have hT₁ : ⟪T (u₁ + u₂) v, w⟫ = ⟪T u₁ v, w⟫ + ⟪T u₂ v, w⟫ := by
                simpa [ContinuousLinearMap.add_apply, inner_add_left] using
                  congrArg (fun f ↦ ⟪f v, w⟫) (T.map_add u₁ u₂)
              have hT₂ : ⟪T v w, u₁ + u₂⟫ = ⟪T v w, u₁⟫ + ⟪T v w, u₂⟫ := by
                rw [inner_add_right]
              have hT₃ : ⟪T w (u₁ + u₂), v⟫ = ⟪T w u₁, v⟫ + ⟪T w u₂, v⟫ := by
                simpa [ContinuousLinearMap.add_apply, inner_add_left] using
                  congrArg (fun z ↦ ⟪z, v⟫) ((T w).map_add u₁ u₂)
              rw [hD₁, hD₂, hD₃, hT₁, hT₂, hT₃]
              ring_nf
            map_smul' := by
              intro c u
              ext w
              have hD₁ : D v w (c • u) = c * D v w u := by
                simpa [smul_eq_mul, RingHom.id_apply] using (D v w).map_smulₛₗ c u
              have hD₂ : D (c • u) w v = c * D u w v := by
                simpa [ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] using
                  congrArg (fun f ↦ f w v) (D.map_smulₛₗ c u)
              have hD₃ : D (c • u) v w = c * D u v w := by
                simpa [ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] using
                  congrArg (fun f ↦ f v w) (D.map_smulₛₗ c u)
              have hT₁ : ⟪T (c • u) v, w⟫ = c * ⟪T u v, w⟫ := by
                simpa [ContinuousLinearMap.smul_apply, real_inner_smul_left,
                  smul_eq_mul, RingHom.id_apply] using
                  congrArg (fun f ↦ ⟪f v, w⟫) (T.map_smulₛₗ c u)
              have hT₂ : ⟪T v w, c • u⟫ = c * ⟪T v w, u⟫ := by
                simpa [smul_eq_mul] using real_inner_smul_right (T v w) u c
              have hT₃ : ⟪T w (c • u), v⟫ = c * ⟪T w u, v⟫ := by
                simpa [ContinuousLinearMap.smul_apply, real_inner_smul_left,
                  smul_eq_mul, RingHom.id_apply] using
                  congrArg (fun z ↦ ⟪z, v⟫) ((T w).map_smulₛₗ c u)
              rw [hD₁, hD₂, hD₃, hT₁, hT₂, hT₃]
              ring_nf }
      map_add' := by
        intro v₁ v₂
        ext u w
        have hD₁ : D (v₁ + v₂) w u = D v₁ w u + D v₂ w u := by
          simpa [ContinuousLinearMap.add_apply] using congrArg (fun f ↦ f w u) (D.map_add v₁ v₂)
        have hD₂ : D u w (v₁ + v₂) = D u w v₁ + D u w v₂ := by
          simpa using (D u w).map_add v₁ v₂
        have hD₃ : D u (v₁ + v₂) w = D u v₁ w + D u v₂ w := by
          simpa [ContinuousLinearMap.add_apply] using congrArg (fun f ↦ f w) ((D u).map_add v₁ v₂)
        have hT₁ : ⟪T u (v₁ + v₂), w⟫ = ⟪T u v₁, w⟫ + ⟪T u v₂, w⟫ := by
          simpa [inner_add_left] using congrArg (fun z ↦ ⟪z, w⟫) ((T u).map_add v₁ v₂)
        have hT₂ : ⟪T (v₁ + v₂) w, u⟫ = ⟪T v₁ w, u⟫ + ⟪T v₂ w, u⟫ := by
          simpa [ContinuousLinearMap.add_apply, inner_add_left] using
            congrArg (fun f ↦ ⟪f w, u⟫) (T.map_add v₁ v₂)
        have hT₃ : ⟪T w u, v₁ + v₂⟫ = ⟪T w u, v₁⟫ + ⟪T w u, v₂⟫ := by
          rw [inner_add_right]
        rw [hD₁, hD₂, hD₃, hT₁, hT₂, hT₃]
        ring_nf
      map_smul' := by
        intro c v
        ext u w
        have hD₁ : D (c • v) w u = c * D v w u := by
          simpa [ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] using
            congrArg (fun f ↦ f w u) (D.map_smulₛₗ c v)
        have hD₂ : D u w (c • v) = c * D u w v := by
          simpa [smul_eq_mul, RingHom.id_apply] using
            (D u w).map_smulₛₗ c v
        have hD₃ : D u (c • v) w = c * D u v w := by
          simpa [ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] using
            congrArg (fun f ↦ f w) ((D u).map_smulₛₗ c v)
        have hT₁ : ⟪T u (c • v), w⟫ = c * ⟪T u v, w⟫ := by
          simpa [real_inner_smul_left, smul_eq_mul, RingHom.id_apply] using
            congrArg (fun z ↦ ⟪z, w⟫) ((T u).map_smulₛₗ c v)
        have hT₂ : ⟪T (c • v) w, u⟫ = c * ⟪T v w, u⟫ := by
          simpa [ContinuousLinearMap.smul_apply, real_inner_smul_left,
            smul_eq_mul, RingHom.id_apply] using
            congrArg (fun f ↦ ⟪f w, u⟫) (T.map_smulₛₗ c v)
        have hT₃ : ⟪T w u, c • v⟫ = c * ⟪T w u, v⟫ := by
          simpa [smul_eq_mul] using real_inner_smul_right (T w u) v c
        rw [hD₁, hD₂, hD₃, hT₁, hT₂, hT₃]
        ring_nf }
