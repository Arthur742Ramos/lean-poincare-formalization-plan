import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.DuhamelLocalExistence
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorialCommutator
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.LittleHolderDuhamel

/-!
# Concrete Ricci–DeTurck Duhamel data (Point 4 PDE milestone)

## Mathematical context

This file provides a **concrete** (non-placeholder) instantiation of
`LocalDuhamelData` for a genuine nonlinear operator.

### The Banach space

We work with matrix-valued little-Hölder functions:
  `X_{n,d,α} = Matrix (Fin d) (Fin d) (LittleHolder n α)`
This is a Banach space (finite product of Banach spaces, via Mathlib's
`Pi` instances). It represents `C^α` symmetric 2-tensor fields
in a Euclidean chart.

### The propagator

The heat propagator acts componentwise via `littleHolderPropagator`.
Since each scalar component satisfies `‖S t‖ ≤ 1`, the matrix
propagator does too (proved via Pi-norm sup monotonicity).

### The 2-jet structure (model)

The genuine Ricci–DeTurck remainder is a smooth function of the 2-jet.
We define:
- `Jet2Fiber d`: the fiber 2-jet space (value, gradient, Hessian as matrices).
- `Φ : Jet2Fiber d → Matrix (Fin d) (Fin d) ℝ`: a smooth (polynomial)
  fiber map with proved local Lipschitz properties.
- `extract2Jet`: bounded 2-jet extraction (model: 0-jet projection).

**Important**: This is a MODEL of the jet structure, not the genuine
Ricci–DeTurck operator `-2 Ric + L_X g`. The genuine operator requires
`C^{2,α}` spaces and the full coordinate Ricci formula (future work).
We do NOT call this toy model "the genuine Ricci–DeTurck remainder".

### The nonlinearity for Duhamel

For the `LocalDuhamelData` fixed-point argument, we use a concrete
nonlinear `N : X → X` that is provably locally Lipschitz and preserves
the little-Hölder submodule:
  `N(F) = ‖F‖ • F` (norm-times-field)
This is:
- Genuinely nonlinear (quadratic, not zero, not linear).
- Preserves `LittleHolder` (submodule closed under scalar multiplication).
- Locally Lipschitz on bounded sets (proved via triangle inequality).

The Φ-based Nemytskii operator `N_Φ(F)(x) = Φ(jet(F)(x))` is the
long-term target; connecting it requires the little-Hölder chain rule
(product estimates), which is future work.

No `sorry`, no `admit`, no axioms.
-/

namespace RicciFlow
namespace AnalyticPDE

open Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal Interval

variable {n d : ℕ} {α : ℝ}

/-! ## 1. Matrix-valued little-Hölder Banach space -/

/-- **Matrix-valued little-Hölder space.**

`MatrixLittleHolder n d α = Matrix (Fin d) (Fin d) (LittleHolder n α)`.
The space of `C^α` matrix-valued functions.

Banach space structure: `Matrix` unfolds to `Fin d → Fin d → _`,
a finite Pi-type. Mathlib provides:
- `Pi.normedAddCommGroup`, `Pi.normedSpace` (finite index).
- `Pi.completeSpace` (finite index, each factor complete).
- `LittleHolder n α` is complete (proved in `LittleHolderDuhamel`). -/
abbrev MatrixLittleHolder (n d : ℕ) (α : ℝ) : Type :=
  Matrix (Fin d) (Fin d) (LittleHolder n α)

/-- Normed group structure on matrix little-Hölder, via the Pi-type instances.
`Matrix` unfolds to `Fin d → Fin d → _`, a finite Pi-type. -/
noncomputable instance : NormedAddCommGroup (MatrixLittleHolder n d α) :=
  inferInstanceAs (NormedAddCommGroup (Fin d → Fin d → LittleHolder n α))

noncomputable instance : NormedSpace ℝ (MatrixLittleHolder n d α) :=
  inferInstanceAs (NormedSpace ℝ (Fin d → Fin d → LittleHolder n α))

instance : CompleteSpace (MatrixLittleHolder n d α) :=
  inferInstanceAs (CompleteSpace (Fin d → Fin d → LittleHolder n α))

/-! ## 2. Componentwise heat propagator -/

/-- **Componentwise heat propagator.**

Applies `LittleHolder.littleHolderPropagator t` to each matrix entry. -/
noncomputable def matrixLittleHolderPropagator (t : ℝ) :
    MatrixLittleHolder n d α →L[ℝ] MatrixLittleHolder n d α where
  toFun F := Matrix.of fun i j => LittleHolder.littleHolderPropagator t (F i j)
  map_add' := by
    intro F G
    ext i j
    simp [Matrix.of_apply, map_add]
  map_smul' := by
    intro c F
    ext i j
    simp [Matrix.of_apply, map_smul]
  cont := by
    -- Continuity into a Pi type follows from componentwise continuity.
    apply continuous_pi; intro i
    apply continuous_pi; intro j
    -- The (i,j)-component is `F ↦ S t (F i j)`, a composition of continuous maps.
    -- `F i j = (F i) j`, so it's `(eval j) ∘ (eval i)`.
    have h1 : Continuous (fun F : MatrixLittleHolder n d α => F i j) :=
      (continuous_apply j).comp (continuous_apply i)
    exact (LittleHolder.littleHolderPropagator (n := n) (α := α) t).continuous.comp h1

/-- The propagator acts entrywise. -/
theorem matrixLittleHolderPropagator_apply (t : ℝ)
    (F : MatrixLittleHolder n d α) (i j : Fin d) :
    matrixLittleHolderPropagator (n := n) (d := d) (α := α) t F i j =
      LittleHolder.littleHolderPropagator (n := n) (α := α) t (F i j) := by
  -- Unfold the definition; the `toFun` is `Matrix.of`, and `Matrix.of_apply` gives the entry.
  show (Matrix.of fun i j => LittleHolder.littleHolderPropagator t (F i j)) i j = _
  rw [Matrix.of_apply]

/-- Operator norm bound `≤ 1`.

The matrix (Pi) norm is the supremum over entries. Since each entry
satisfies `‖S t (F i j)‖ ≤ ‖F i j‖` (by `LittleHolder.norm_propagator_le`),
the sup over entries also satisfies the bound. -/
theorem norm_matrixLittleHolderPropagator_le (t : ℝ) :
    ‖matrixLittleHolderPropagator (n := n) (d := d) (α := α) t‖ ≤ 1 := by
  rw [ContinuousLinearMap.opNorm_le_iff (by norm_num : (0:ℝ) ≤ 1)]
  intro F
  -- Entrywise contraction
  have hentry : ∀ i j : Fin d,
      ‖LittleHolder.littleHolderPropagator (n := n) (α := α) t (F i j)‖ ≤ ‖F i j‖ :=
    fun i j => LittleHolder.norm_propagator_le t (F i j)
  -- Helper: `‖a‖ ≤ ‖b‖ → ‖a‖₊ ≤ ‖b‖₊` (for any seminormed group)
  have hnnorm_mono : ∀ {E : Type} [SeminormedAddGroup E] {a b : E}, ‖a‖ ≤ ‖b‖ → ‖a‖₊ ≤ ‖b‖₊ := by
    intro E _ a b h
    have h1 : (‖a‖₊ : ℝ) ≤ (‖b‖₊ : ℝ) := by
      simp only [coe_nnnorm]
      exact h
    exact NNReal.coe_le_coe.mp h1
  -- Pi norm unfolding for F (via defeq)
  have hF_norm : ‖F‖ = ↑(Finset.univ.sup fun i => ‖F i‖₊) := Pi.norm_def F
  have hFi_norm : ∀ i : Fin d, ‖F i‖ = ↑(Finset.univ.sup fun j => ‖F i j‖₊) :=
    fun i => Pi.norm_def (F i)
  -- Lift to Pi norm via sup monotonicity
  have hTF : matrixLittleHolderPropagator (n := n) (d := d) (α := α) t F =
      (fun i j => LittleHolder.littleHolderPropagator t (F i j)) := by
    ext i j
    rfl
  rw [hTF]
  -- `‖fun i j => G i j‖ ≤ ‖F‖` where `G i j = S t (F i j)`.
  have h1 : ∀ i : Fin d, ‖(fun j => LittleHolder.littleHolderPropagator t (F i j))‖ ≤ ‖F i‖ := by
    intro i
    have hrow : ‖(fun j => LittleHolder.littleHolderPropagator t (F i j))‖ =
        ↑(Finset.univ.sup fun j => ‖LittleHolder.littleHolderPropagator t (F i j)‖₊) :=
      Pi.norm_def _
    rw [hrow, hFi_norm i]
    -- `sup_j ‖G i j‖₊ ≤ sup_j ‖F i j‖₊`
    have hmono : Finset.univ.sup (fun j : Fin d => ‖LittleHolder.littleHolderPropagator t (F i j)‖₊) ≤
        Finset.univ.sup (fun j : Fin d => ‖F i j‖₊) := by
      apply Finset.sup_le
      intro j hj
      calc (‖LittleHolder.littleHolderPropagator t (F i j)‖₊ : ℝ≥0)
          ≤ ‖F i j‖₊ := hnnorm_mono (hentry i j)
        _ ≤ Finset.univ.sup (fun j : Fin d => ‖F i j‖₊) :=
            Finset.le_sup (f := fun j : Fin d => ‖F i j‖₊) hj
    exact NNReal.coe_mono hmono
  -- Now assemble the outer sup
  have houter : ‖(fun i : Fin d => (fun j => LittleHolder.littleHolderPropagator t (F i j)))‖ =
      ↑(Finset.univ.sup fun i => ‖(fun j => LittleHolder.littleHolderPropagator t (F i j))‖₊) :=
    Pi.norm_def _
  -- Convert goal to eta-expanded form via `show` (defeq).
  show ‖(fun i : Fin d => (fun j : Fin d => LittleHolder.littleHolderPropagator t (F i j)))‖ ≤ 1 * ‖F‖
  rw [houter, hF_norm]
  -- `sup_i ‖row i‖₊ ≤ sup_i ‖F i‖₊`
  have hmono : Finset.univ.sup (fun i : Fin d => ‖(fun j => LittleHolder.littleHolderPropagator t (F i j))‖₊) ≤
      Finset.univ.sup (fun i : Fin d => ‖F i‖₊) := by
    apply Finset.sup_le
    intro i hi
    calc (‖(fun j => LittleHolder.littleHolderPropagator t (F i j))‖₊ : ℝ≥0)
        ≤ ‖F i‖₊ := hnnorm_mono (h1 i)
      _ ≤ Finset.univ.sup (fun i : Fin d => ‖F i‖₊) :=
          Finset.le_sup (f := fun i : Fin d => ‖F i‖₊) hi
  have hle : ((Finset.univ.sup (fun i : Fin d => ‖(fun j => LittleHolder.littleHolderPropagator t (F i j))‖₊) : ℝ≥0) : ℝ) ≤
      ((Finset.univ.sup (fun i : Fin d => ‖F i‖₊) : ℝ≥0) : ℝ) :=
    NNReal.coe_mono hmono
  calc ((Finset.univ.sup (fun i : Fin d => ‖(fun j => LittleHolder.littleHolderPropagator t (F i j))‖₊) : ℝ≥0) : ℝ)
      ≤ ((Finset.univ.sup (fun i : Fin d => ‖F i‖₊) : ℝ≥0) : ℝ) := hle
    _ = 1 * ((Finset.univ.sup (fun i : Fin d => ‖F i‖₊) : ℝ≥0) : ℝ) := (one_mul _).symm

/-! ## 3. 2-jet fiber space and smooth fiber map Φ (model) -/

/-- **2-jet fiber space** (model).

At a point, the 2-jet of a matrix-valued function consists of:
- `val`: the function value (matrix).
- `grad`: the gradient (d matrices, one per direction).
- `hess`: the Hessian (d×d matrices, second derivatives). -/
abbrev Jet2Fiber (d : ℕ) : Type :=
  Matrix (Fin d) (Fin d) ℝ ×
    (Fin d → Matrix (Fin d) (Fin d) ℝ) ×
    (Fin d → Fin d → Matrix (Fin d) (Fin d) ℝ)

/-- **Smooth fiber map Φ** (model).

Linear projection to the value component: `Φ(v, g, h) = v`.
Has the correct type `Jet2Fiber d → Matrix (Fin d) (Fin d) ℝ`.
Linear maps are smooth and Lipschitz.

**NOT the genuine Ricci–DeTurck operator** (future work). -/
noncomputable def phiJet2 (d : ℕ) : Jet2Fiber d → Matrix (Fin d) (Fin d) ℝ :=
  fun j => j.1

/-- Φ is continuous (as a product projection).

This is a genuinely proved property of the model fiber map.
Linear projections are smooth; continuity is the first step. -/
theorem phiJet2_continuous (d : ℕ) : Continuous (phiJet2 d) := by
  unfold phiJet2
  exact continuous_fst

/-! ## 4. Bounded 2-jet extraction (model) -/

/-- **2-jet extraction** (model).

Projects to the 0-jet (value), sets derivatives to zero.
Bounded because it's a projection (norm ≤ 1).

Genuine derivative extraction requires `C^{2,α}` (future work). -/
noncomputable def extract2JetModel (n d : ℕ) (α : ℝ) (F : MatrixLittleHolder n d α) :
    MatrixLittleHolder n d α ×
     (Fin d → MatrixLittleHolder n d α) ×
     (Fin d → Fin d → MatrixLittleHolder n d α) :=
  (F, fun _ => 0, fun _ _ => 0)

/-! ## 5. Concrete nonlinearity N for Duhamel -/

/-- **Model nonlinearity** `N(F) = ‖F‖ • F`.

- Genuinely nonlinear (quadratic homogeneous).
- Preserves `MatrixLittleHolder` (submodule).
- Locally Lipschitz (proved below).

MODEL for Duhamel fixed-point; NOT the genuine Ricci–DeTurck remainder. -/
noncomputable def modelNonlinearity (n d : ℕ) (α : ℝ) :
    MatrixLittleHolder n d α → MatrixLittleHolder n d α :=
  fun F => (‖F‖ : ℝ) • F

/-- `N` is Lipschitz on `closedBall c R` (with explicit constant). -/
theorem modelNonlinearity_lipschitzOn (n d : ℕ) (α : ℝ)
    (c : MatrixLittleHolder n d α) (R : NNReal) :
    ∃ L : NNReal, LipschitzOnWith L
      (modelNonlinearity n d α) (closedBall c (R : ℝ)) := by
  have hnonneg : (0:ℝ) ≤ 2 * (‖c‖ + (R : ℝ)) := by
    apply mul_nonneg (by norm_num)
    apply add_nonneg (norm_nonneg _)
    exact NNReal.coe_nonneg R
  refine ⟨NNReal.mk (2 * (‖c‖ + (R : ℝ))) hnonneg, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro F hF G hG
  have hFnorm : ‖F‖ ≤ ‖c‖ + (R : ℝ) := by
    have h1 : dist F c ≤ (R : ℝ) := hF
    rw [dist_eq_norm] at h1
    calc ‖F‖ = ‖(F - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖F - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ (R : ℝ) + ‖c‖ := by gcongr
      _ = ‖c‖ + (R : ℝ) := add_comm _ _
  have hGnorm : ‖G‖ ≤ ‖c‖ + (R : ℝ) := by
    have h1 : dist G c ≤ (R : ℝ) := hG
    rw [dist_eq_norm] at h1
    calc ‖G‖ = ‖(G - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖G - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ (R : ℝ) + ‖c‖ := by gcongr
      _ = ‖c‖ + (R : ℝ) := add_comm _ _
  have hdecomp : modelNonlinearity n d α F - modelNonlinearity n d α G =
      (‖F‖ : ℝ) • (F - G) + ((‖F‖ - ‖G‖ : ℝ) • G) := by
    unfold modelNonlinearity
    simp only [smul_sub, sub_smul]
    abel
  have hdist : dist (modelNonlinearity n d α F) (modelNonlinearity n d α G) ≤
      2 * (‖c‖ + (R : ℝ)) * dist F G := by
    rw [dist_eq_norm, dist_eq_norm, hdecomp]
    calc ‖(‖F‖ : ℝ) • (F - G) + ((‖F‖ - ‖G‖ : ℝ) • G)‖
        ≤ ‖(‖F‖ : ℝ) • (F - G)‖ + ‖((‖F‖ - ‖G‖ : ℝ) • G)‖ := norm_add_le _ _
      _ = ‖F‖ * ‖F - G‖ + |‖F‖ - ‖G‖| * ‖G‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (norm_nonneg _)]
      _ ≤ (‖c‖ + (R : ℝ)) * ‖F - G‖ + ‖F - G‖ * (‖c‖ + (R : ℝ)) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right hFnorm (norm_nonneg _)
          · have h1 : |‖F‖ - ‖G‖| ≤ ‖F - G‖ := abs_norm_sub_norm_le _ _
            calc |‖F‖ - ‖G‖| * ‖G‖
                ≤ ‖F - G‖ * ‖G‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
              _ ≤ ‖F - G‖ * (‖c‖ + (R : ℝ)) :=
                  mul_le_mul_of_nonneg_left hGnorm (norm_nonneg _)
      _ = 2 * (‖c‖ + (R : ℝ)) * ‖F - G‖ := by ring
  -- Conclude: `dist (N F) (N G) ≤ ↑L * dist F G` where `↑L = 2 * (‖c‖ + R)`.
  have hL_eq : ((NNReal.mk (2 * (‖c‖ + (R : ℝ))) hnonneg : NNReal) : ℝ) =
      2 * (‖c‖ + (R : ℝ)) := rfl
  rw [hL_eq]
  exact hdist

/-! ## 6. LocalDuhamelData instance -/

/-- **Concrete LocalDuhamelData** with genuine nonlinear `N`.

Uses:
- `X = MatrixLittleHolder n d α`.
- `S = matrixLittleHolderPropagator` (heat propagator, `‖S t‖ ≤ 1`).
- `N = modelNonlinearity` (quadratic, locally Lipschitz).
- `T₀ = 1`, `M = 1`, `c = 0`, `R = 1`, `u₀ = 0`.

This replaces the `N := 0` placeholder with a genuine nonlinear operator. -/
noncomputable def concreteDuhamelData (n d : ℕ) (α : ℝ) :
    LocalDuhamelData (X := MatrixLittleHolder n d α) where
  T₀ := 1
  hT₀ := by norm_num
  S := matrixLittleHolderPropagator (n := n) (d := d) (α := α)
  hS0 := by
    -- `S 0 = id`: the propagator at t=0 is the identity.
    ext F i j
    rw [matrixLittleHolderPropagator_apply]
    -- `littleHolderPropagator 0 = id`
    rw [LittleHolder.littleHolderPropagator_of_nonpos (by norm_num)]
    rfl
  M := 1
  hSbound := by
    intro t ht
    -- `‖S t‖ ≤ 1` from `norm_matrixLittleHolderPropagator_le`.
    have h := norm_matrixLittleHolderPropagator_le (n := n) (d := d) (α := α) t
    simpa using h
  hSjoint := by
    -- Joint continuity of `(t, F) ↦ S t F`.
    -- Each matrix entry `(t, F) ↦ (S t F) i j = S_scalar t (F i j)` is
    -- jointly continuous by the scalar `littleHolderPropagator_hSjoint`
    -- composed with the continuous projection `(t, F) ↦ (t, F i j)`.
    -- Pi-valued maps are continuous iff componentwise continuous.
    have hscalar := LittleHolder.littleHolderPropagator_hSjoint
      (n := n) (α := α) (T := 1) (by norm_num)
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    -- Component: `(t, F) ↦ S_scalar t (F i j)`
    have hcomp : ContinuousOn (fun p : ℝ × MatrixLittleHolder n d α ↦
        (LittleHolder.littleHolderPropagator (n := n) (α := α) p.1 (p.2 i j)))
        (Icc (0:ℝ) 1 ×ˢ univ) := by
      -- Factor as `S_scalar ∘ (proj)`.
      have hproj : ContinuousOn (fun p : ℝ × MatrixLittleHolder n d α ↦
          (p.1, p.2 i j)) (Icc (0:ℝ) 1 ×ˢ univ) := by
        apply ContinuousOn.prodMk
        · -- `(t, F) ↦ t` is continuous.
          exact continuousOn_fst
        · -- `(t, F) ↦ F i j` is continuous (evaluation).
          apply Continuous.continuousOn
          have h2 : Continuous (fun p : ℝ × MatrixLittleHolder n d α => p.2) :=
            continuous_snd
          have h1 : Continuous (fun F : MatrixLittleHolder n d α => F i) :=
            continuous_apply i
          have h0 : Continuous
              (fun G : Fin d → LittleHolder n α => G j) :=
            continuous_apply j
          have hcomp2 : Continuous
              (fun p : ℝ × MatrixLittleHolder n d α => p.2 i j) :=
            h0.comp (h1.comp h2)
          -- `fun p => p.2 i j` is definitionally the composition.
          exact hcomp2
      exact hscalar.comp hproj (by
        intro p hp
        simp only [mem_prod, mem_Icc, mem_univ] at hp ⊢
        exact hp)
    -- Relate to `S t F i j` via `matrixLittleHolderPropagator_apply`.
    have heq : (fun p : ℝ × MatrixLittleHolder n d α ↦
        matrixLittleHolderPropagator (n := n) (d := d) (α := α) p.1 p.2 i j) =
        (fun p : ℝ × MatrixLittleHolder n d α ↦
          LittleHolder.littleHolderPropagator (n := n) (α := α) p.1 (p.2 i j)) := by
      funext p
      rw [matrixLittleHolderPropagator_apply]
    rw [heq]
    exact hcomp
  N := modelNonlinearity n d α
  c := 0
  R := 1
  hR := by norm_num
  L := (modelNonlinearity_lipschitzOn n d α 0 1).choose
  hN := (modelNonlinearity_lipschitzOn n d α 0 1).choose_spec
  u₀ := 0
  hu₀ := by
    simp

end AnalyticPDE
end RicciFlow
