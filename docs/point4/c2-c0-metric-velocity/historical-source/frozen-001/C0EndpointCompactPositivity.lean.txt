import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.C0FiniteAtlasGaussian

/-!
# Compact positivity control for the constructed Gaussian tensor

SOURCE CANDIDATE, UNCOMPILED. The estimates are in the fixed preferred
model frames, so no unexplained uniform norm on varying tangent fibers is
used. Compactness supplies actual metric-cone radii on the partition pieces.
Finite Gaussian contraction bounds supply one positive amplitude reserve.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 2000000

open Bundle FiberBundle Set Filter
open scoped Manifold Topology ContDiff BigOperators

namespace RicciFlow.AnalyticPDE.C0Endpoint

open PoincareCurvature.Bundle.Trivialization
open PoincareCurvature.PreferredCoordinateFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [CompactSpace M] [SigmaCompactSpace M] [BoundarylessManifold I M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "BilE" => (E →L[ℝ] E →L[ℝ] ℝ)
local notation "Cover" => FiniteSmoothPreferredTrivializingCover I (F := E) (V := TM)

variable {d : ℕ}

def coefficientBound (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (i : C.Index) : ℝ :=
  ∑ j : Fin d, ∑ k : Fin d,
    (‖localizedVelocityBcf v C b i j k‖ + ‖localizedVelocityBcf v C b i k j‖)

lemma coefficientBound_nonneg
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (i : C.Index) :
    0 ≤ coefficientBound v C b i :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)

lemma norm_gaussianMatrix_le
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (i : C.Index) (h : ℝ) (z : Fin d → ℝ) :
    ‖gaussianMatrix v C b i h z‖ ≤ coefficientBound v C b i := by
  classical
  apply (pi_norm_le_iff_of_nonneg (coefficientBound_nonneg v C b i)).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg (coefficientBound_nonneg v C b i)).mpr
  intro k
  have hj := abs_gaussianPath_apply_le (localizedVelocityBcf v C b i j k) h z
  have hk := abs_gaussianPath_apply_le (localizedVelocityBcf v C b i k j) h z
  have hterm : ‖localizedVelocityBcf v C b i j k‖ + ‖localizedVelocityBcf v C b i k j‖ ≤
      coefficientBound v C b i := by
    exact (Finset.single_le_sum
      (fun k _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ k)).trans
      (Finset.single_le_sum
        (fun j _ => Finset.sum_nonneg fun k _ => add_nonneg (norm_nonneg _) (norm_nonneg _))
        (Finset.mem_univ j))
  have hsum := (abs_add (gaussianPath (localizedVelocityBcf v C b i j k) h z)
    (gaussianPath (localizedVelocityBcf v C b i k j) h z)).trans (add_le_add hj hk)
  rw [Real.norm_eq_abs, gaussianMatrix, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hdiv : |gaussianPath (localizedVelocityBcf v C b i j k) h z +
      gaussianPath (localizedVelocityBcf v C b i k j) h z| / 2 ≤
      ‖localizedVelocityBcf v C b i j k‖ + ‖localizedVelocityBcf v C b i k j‖ := by
    nlinarith [norm_nonneg (localizedVelocityBcf v C b i j k),
      norm_nonneg (localizedVelocityBcf v C b i k j)]
  exact hdiv.trans hterm

def matrixBound (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (i : C.Index) : ℝ :=
  ‖matrixBilinearSynthesis b‖ * coefficientBound v C b i

lemma matrixBound_nonneg
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (i : C.Index) :
    0 ≤ matrixBound v C b i := mul_nonneg (norm_nonneg _) (coefficientBound_nonneg v C b i)

lemma norm_matrixBilinear_gaussianMatrix_le
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (i : C.Index) (h : ℝ) (z : Fin d → ℝ) :
    ‖matrixBilinearCLM b (gaussianMatrix v C b i h z)‖ ≤ matrixBound v C b i :=
  ((matrixBilinearSynthesis b).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (norm_gaussianMatrix_le v C b i h z) (norm_nonneg _))

def metricVelocity (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM) :
    ContinuousSymmetricVelocity (I := I) (M := M) where
  tensor := g₀.inner
  continuous := g₀.contMDiff.continuous
  symmetric := g₀.symm

def metricModelForm (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (p : M) (b : Module.Basis (Fin d) ℝ E) (x : M) : BilE :=
  matrixBilinearCLM b (fun j k => velocityComponent (metricVelocity g₀) p b j k x)

lemma continuousOn_metricModelForm
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (p : M) (b : Module.Basis (Fin d) ℝ E) :
    ContinuousOn (metricModelForm g₀ p b) (trivialization (I := I) p).baseSet := by
  have hcoeff : ContinuousOn
      (fun x j k => velocityComponent (metricVelocity g₀) p b j k x)
      (trivialization (I := I) p).baseSet :=
    continuousOn_pi.2 fun j => continuousOn_pi.2 fun k =>
      continuousOn_velocityComponent (metricVelocity g₀) p b j k
  exact (matrixBilinearSynthesis b).continuous.comp_continuousOn hcoeff

lemma metricModelForm_eq_bilinearComp
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (p : M) (b : Module.Basis (Fin d) ℝ E) (x : M)
    (hx : x ∈ (trivialization (I := I) p).baseSet) :
    metricModelForm g₀ p b x = (g₀.inner x).bilinearComp
      ((trivialization (I := I) p).linearEquivAt ℝ x hx).symm.toContinuousLinearEquiv.toContinuousLinearMap
      ((trivialization (I := I) p).linearEquivAt ℝ x hx).symm.toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.toLinearMap₁₂_injective
  apply b.ext
  intro j
  apply b.ext
  intro k
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, metricModelForm,
    matrixBilinearCLM_apply_basis, ContinuousLinearMap.bilinearComp_apply,
    velocityComponent, metricVelocity, frame,
    (trivialization (I := I) p).localFrame_apply_of_mem_baseSet b hx,
    ContinuousLinearEquiv.coe_coe]

lemma metricModelForm_pos
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (p : M) (b : Module.Basis (Fin d) ℝ E) (x : M)
    (hx : x ∈ (trivialization (I := I) p).baseSet) (w : E) (hw : w ≠ 0) :
    0 < metricModelForm g₀ p b x w w := by
  rw [metricModelForm_eq_bilinearComp g₀ p b x hx]
  apply g₀.pos
  intro hzero
  apply hw
  simpa using congrArg ((trivialization (I := I) p).linearEquivAt ℝ x hx) hzero

/-- The model positivity-radius lemma also covers rank zero and empty
compact parameter spaces, without inserting a Nontrivial assumption. -/
lemma exists_uniform_pos_ball_any {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → BilE) (hg : Continuous g)
    (hpos : ∀ x (w : E), w ≠ 0 → 0 < g x w w) :
    ∃ ε > 0, ∀ q : X → BilE, (∀ x, ‖q x - g x‖ < ε) →
      ∀ x (w : E), w ≠ 0 → 0 < q x w w := by
  by_cases hsub : Subsingleton E
  · letI : Subsingleton E := hsub
    refine ⟨1, zero_lt_one, ?_⟩
    intro q hq x w hw
    exact (hw (Subsingleton.elim w 0)).elim
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hsub
    exact Bundle.ContinuousLinearMap.exists_uniform_pos_ball_of_continuous g hg hpos

lemma exists_piece_positivity_radius
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) (i : C.Index) :
    ∃ ε > 0, ∀ q : (C.pieces i : Set M) → BilE,
      (∀ x, ‖q x - metricModelForm g₀ (i : M) b x‖ < ε) →
      ∀ x (w : E), w ≠ 0 → 0 < q x w w := by
  letI : CompactSpace (C.pieces i : Set M) :=
    isCompact_iff_compactSpace.mp (C.pieces i).isCompact
  have hg : Continuous (fun x : (C.pieces i : Set M) => metricModelForm g₀ (i : M) b x) :=
    ((continuousOn_metricModelForm g₀ (i : M) b).mono (C.pieces_subset_baseSet i)).restrict
  exact exists_uniform_pos_ball_any _ hg
    (fun x w hw => metricModelForm_pos g₀ (i : M) b x (C.pieces_subset_baseSet i x.property) w hw)

/-- A finite family of positive metric radii and finite nonnegative bounds
has one positive amplitude reserve. The empty index case is included. -/
lemma exists_common_amplitude {ι : Type*} [Fintype ι]
    (ε B : ι → ℝ) (hε : ∀ i, 0 < ε i) (hB : ∀ i, 0 ≤ B i) :
    ∃ δ > 0, ∀ i, δ * B i < ε i := by
  classical
  let S : ℝ := ∑ i, B i / ε i
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => div_nonneg (hB i) (hε i).le
  let δ : ℝ := 1 / (2 * (1 + S))
  have hden : 0 < 2 * (1 + S) := by positivity
  have hδ : 0 < δ := one_div_pos.mpr hden
  have hδeq : δ * (2 * (1 + S)) = 1 := by
    dsimp [δ]
    exact one_div_mul_cancel hden.ne'
  have hδS : δ * S < 1 := by nlinarith
  refine ⟨δ, hδ, ?_⟩
  intro i
  have hterm : B i / ε i ≤ S :=
    Finset.single_le_sum (fun j _ => div_nonneg (hB j) (hε j).le) (Finset.mem_univ i)
  have hsmall : δ * (B i / ε i) < 1 :=
    (mul_le_mul_of_nonneg_left hterm hδ.le).trans_lt hδS
  have hdiv : (δ * B i) / ε i < 1 := by simpa only [mul_div_assoc] using hsmall
  simpa only [one_mul] using (div_lt_iff₀ (hε i)).mp hdiv

lemma metricModelForm_tangentCoord_apply
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (p : M) (b : Module.Basis (Fin d) ℝ E) (x : M)
    (hx : x ∈ (trivialization (I := I) p).baseSet) (u w : TM x) :
    metricModelForm g₀ p b x
      (tangentCoordCLM (trivialization (I := I) p) x hx u)
      (tangentCoordCLM (trivialization (I := I) p) x hx w) = g₀.inner x u w := by
  rw [metricModelForm_eq_bilinearComp g₀ p b x hx]
  simp only [ContinuousLinearMap.bilinearComp_apply, tangentCoordCLM,
    ContinuousLinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- One fixed positive amplitude reserve controls every real Gaussian
parameter. This is a conclusion from the literal metric and actual C0
velocity, not a supplied positivity/regularizer hypothesis. -/
lemma exists_gaussianTensor_positivity_reserve
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (v : ContinuousSymmetricVelocity (I := I) (M := M))
    (C : Cover) (b : Module.Basis (Fin d) ℝ E) :
    ∃ δ > 0, ∀ a : ℝ, |a| ≤ δ → ∀ h : ℝ, ∀ x : M, ∀ w : TM x, w ≠ 0 →
      0 < (g₀.inner x + a • gaussianTensor v C b h x) w w := by
  classical
  choose ε hε hcone using exists_piece_positivity_radius g₀ C b
  obtain ⟨δ, hδ, hsmall⟩ := exists_common_amplitude ε (matrixBound v C b) hε
    (matrixBound_nonneg v C b)
  have hlocal : ∀ (i : C.Index) (a h : ℝ), |a| ≤ δ →
      ∀ y : (C.pieces i : Set M), ∀ z : E, z ≠ 0 →
        0 < (metricModelForm g₀ (i : M) b y + a •
          matrixBilinearCLM b (gaussianMatrixOnManifold v C b i h y)) z z := by
    intro i a h ha
    apply hcone i
      (fun y => metricModelForm g₀ (i : M) b y + a •
        matrixBilinearCLM b (gaussianMatrixOnManifold v C b i h y))
    intro y
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    exact ((mul_le_mul_of_nonneg_left
      (norm_matrixBilinear_gaussianMatrix_le v C b i h
        (chartCoordinate (I := I) (i : M) b y)) (abs_nonneg a)).trans
      (mul_le_mul_of_nonneg_right ha (matrixBound_nonneg v C b i))).trans_lt (hsmall i)
  refine ⟨δ, hδ, ?_⟩
  intro a ha h x w hw
  let f : C.Index → ℝ := fun i => C.partition i x *
    (g₀.inner x w w + a * localTensorOfMatrix (C.trivialization i) b
      (gaussianMatrixOnManifold v C b i h) x w w)
  have hpiece : ∀ i : C.Index, 0 < C.partition i x →
      0 < g₀.inner x w w + a * localTensorOfMatrix (C.trivialization i) b
        (gaussianMatrixOnManifold v C b i h) x w w := by
    intro i hψ
    have hx : x ∈ (C.pieces i : Set M) :=
      subset_closure (Function.mem_support.2 (ne_of_gt hψ))
    have hxBase := C.pieces_subset_baseSet i hx
    have hz : tangentCoordCLM (C.trivialization i) x hxBase w ≠ 0 := by
      intro hz
      apply hw
      simpa only [tangentCoordCLM, ContinuousLinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, map_zero] using
        congrArg ((C.trivialization i).linearEquivAt ℝ x hxBase).symm hz
    have hp := hlocal i a h ha ⟨x, hx⟩
      (tangentCoordCLM (C.trivialization i) x hxBase w) hz
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      _root_.smul_apply, _root_.smul_apply, smul_eq_mul] at hp
    rw [metricModelForm_tangentCoord_apply g₀ (i : M) b x hxBase] at hp
    simpa only [localTensorOfMatrix_apply_of_mem (C.trivialization i) b
      (gaussianMatrixOnManifold v C b i h) hxBase] using hp
  have hnonneg : ∀ i ∈ (Finset.univ : Finset C.Index), 0 ≤ f i := by
    intro i hi
    by_cases hψ : C.partition i x = 0
    · simp [f, hψ]
    · exact (mul_pos (lt_of_le_of_ne (C.partition.nonneg i x) (Ne.symm hψ))
        (hpiece i (lt_of_le_of_ne (C.partition.nonneg i x) (Ne.symm hψ)))).le
  obtain ⟨i, hi⟩ := C.partition.exists_pos_of_mem (mem_univ x)
  have hsum : 0 < ∑ i : C.Index, f i :=
    Finset.sum_pos' hnonneg ⟨i, Finset.mem_univ i, mul_pos hi (hpiece i hi)⟩
  have hpartition : ∑ i : C.Index, C.partition i x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using C.partition.sum_eq_one (mem_univ x)
  have heq : (g₀.inner x + a • gaussianTensor v C b h x) w w = ∑ i : C.Index, f i := by
    simp only [gaussianTensor, cutoffLocalTensorOfMatrix, _root_.sum_apply,
      _root_.smul_apply, smul_eq_mul, ContinuousLinearMap.add_apply, f]
    have hpoly : ∀ i : C.Index,
        C.partition i x * (g₀.inner x w w + a * localTensorOfMatrix (C.trivialization i) b
          (gaussianMatrixOnManifold v C b i h) x w w) =
        C.partition i x * g₀.inner x w w + a * (C.partition i x *
          localTensorOfMatrix (C.trivialization i) b
            (gaussianMatrixOnManifold v C b i h) x w w) := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hpoly i), Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, hpartition, one_mul]
  rw [heq]
  exact hsum

end RicciFlow.AnalyticPDE.C0Endpoint
