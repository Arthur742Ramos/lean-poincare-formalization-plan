module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Topology.VectorBundle.FiniteDimensional
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Compact
public import PoincareCurvature.Geometry.Manifold.VectorBundle.ContinuousSection

/-!
# Riemannian metrics as bilinear-form sections

This file packages continuous and `C^n` Riemannian metrics as honest sections of
the hom bundle with fiber `F →L[ℝ] F →L[ℝ] ℝ`. This is the section-space side of
the metric data that later point-4 work needs: metrics can be fed directly into
continuous-section machinery instead of only being handled through ad hoc
structures.

It also adds extensionality lemmas for continuous and smooth Riemannian metrics,
so later arguments can reduce metric equality to pointwise equality of the
fiberwise bilinear forms.
-/

@[expose] public noncomputable section

open scoped Bundle Manifold ContDiff

namespace Bundle

/-- The bundle of real bilinear forms on the fibers of `V`. -/
abbrev BilinearFormBundle {B : Type*} {V : B → Type*}
    [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] :
    B → Type _ :=
  fun x : B ↦ V x →L[ℝ] V x →L[ℝ] ℝ

section Continuous

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

local notation "BilV" => BilinearFormBundle (V := V)

/-- Forget the positivity axioms and view a continuous Riemannian metric as a section of the
bilinear-form bundle. -/
def ContinuousRiemannianMetric.toSection (g : ContinuousRiemannianMetric F V) :
    Π x : B, BilV x :=
  g.inner

@[simp] theorem ContinuousRiemannianMetric.toSection_apply
    (g : ContinuousRiemannianMetric F V) (x : B) :
    g.toSection x = g.inner x :=
  rfl

/-- The section associated to a continuous Riemannian metric is continuous as a map to the total
space of the bilinear-form bundle. -/
lemma ContinuousRiemannianMetric.continuous_toSection (g : ContinuousRiemannianMetric F V) :
    Continuous
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (g.toSection x)) := by
  simpa [ContinuousRiemannianMetric.toSection] using g.continuous

/-- A continuous Riemannian metric determines a bundled continuous section of the bilinear-form
bundle. -/
def ContinuousRiemannianMetric.toContinuousSection (g : ContinuousRiemannianMetric F V) :
    {s : Π x : B, BilV x //
      Continuous (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (s x))} :=
  ⟨g.toSection, g.continuous_toSection⟩

@[simp] theorem ContinuousRiemannianMetric.coe_toContinuousSection
    (g : ContinuousRiemannianMetric F V) :
    ((g.toContinuousSection : {s : Π x : B, BilV x //
      Continuous (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (s x))}).1) = g.toSection :=
  rfl

@[ext] theorem ContinuousRiemannianMetric.ext
    {g g' : ContinuousRiemannianMetric F V}
    (hinner : ∀ x : B, ∀ u v : V x, g.inner x u v = g'.inner x u v) :
    g = g' := by
  have hinner' : g.inner = g'.inner := by
    funext x
    ext u v
    exact hinner x u v
  cases g
  cases g'
  simp at hinner' ⊢
  exact hinner'

end Continuous

section Smooth

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

local notation "BilV" => BilinearFormBundle (V := V)

/-- Forget the positivity axioms and view a `C^n` Riemannian metric as a section of the
bilinear-form bundle. -/
def ContMDiffRiemannianMetric.toSection (g : ContMDiffRiemannianMetric IB n F V) :
    Π x : B, BilV x :=
  g.inner

@[simp] theorem ContMDiffRiemannianMetric.toSection_apply
    (g : ContMDiffRiemannianMetric IB n F V) (x : B) :
    g.toSection x = g.inner x :=
  rfl

/-- The section associated to a `C^n` Riemannian metric is `C^n` as a map to the total space of
the bilinear-form bundle. -/
lemma ContMDiffRiemannianMetric.contMDiff_toSection (g : ContMDiffRiemannianMetric IB n F V) :
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (g.toSection x)) := by
  simpa [ContMDiffRiemannianMetric.toSection] using g.contMDiff

/-- The section associated to a `C^n` Riemannian metric is continuous as a map to the total space
of the bilinear-form bundle. -/
lemma ContMDiffRiemannianMetric.continuous_toSection (g : ContMDiffRiemannianMetric IB n F V) :
    Continuous
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (g.toSection x)) := by
  simpa [ContMDiffRiemannianMetric.toSection] using g.contMDiff.continuous

/-- A `C^n` Riemannian metric determines a bundled continuous section of the bilinear-form bundle. -/
def ContMDiffRiemannianMetric.toContinuousSection (g : ContMDiffRiemannianMetric IB n F V) :
    {s : Π x : B, BilV x //
      Continuous (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (s x))} :=
  ⟨g.toSection, g.continuous_toSection⟩

@[simp] theorem ContMDiffRiemannianMetric.coe_toContinuousSection
    (g : ContMDiffRiemannianMetric IB n F V) :
    ((g.toContinuousSection : {s : Π x : B, BilV x //
      Continuous (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (s x))}).1) = g.toSection :=
  rfl

@[ext] theorem ContMDiffRiemannianMetric.ext
    {g g' : ContMDiffRiemannianMetric IB n F V}
    (hinner : ∀ x : B, ∀ u v : V x, g.inner x u v = g'.inner x u v) :
    g = g' := by
  have hinner' : g.inner = g'.inner := by
    funext x
    ext u v
    exact hinner x u v
  cases g
  cases g'
  simp at hinner' ⊢
  exact hinner'

end Smooth

section FiberwisePositivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace ContinuousLinearMap

open Set

local notation "BilE" => (E →L[ℝ] E →L[ℝ] ℝ)

local instance bilENormedAddCommGroup : NormedAddCommGroup BilE :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))

local instance bilEPseudoMetricSpace : PseudoMetricSpace BilE :=
  (inferInstance : PseudoMetricSpace (E →L[ℝ] E →L[ℝ] ℝ))

/-- The continuous linear involution that flips the arguments of a bilinear form. -/
noncomputable def flipBilinear : BilE →L[ℝ] BilE :=
  (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] lemma flipBilinear_apply_apply
    (B : BilE) (v w : E) :
    flipBilinear (E := E) B v w = B w v := by
  simp [flipBilinear, ContinuousLinearMap.flipₗᵢ, ContinuousLinearMap.flip_apply]

/-- A bilinear form is fixed by slot-flip exactly when it is symmetric. -/
lemma flipBilinear_eq_self_iff
    (B : BilE) :
    flipBilinear (E := E) B = B ↔ ∀ v w : E, B v w = B w v := by
  constructor
  · intro h v w
    have h' := congrArg (fun C : BilE => C v w) h
    have h'' : B w v = B v w := by
      simpa using h'
    exact h''.symm
  · intro h
    ext v w
    simpa using (h w v)

/-- Slot-flip preserves the pointwise positive-definite inequality because it leaves diagonal
values unchanged. -/
lemma flipBilinear_forall_pos_iff
    (B : BilE) :
    (∀ v : E, v ≠ 0 → 0 < flipBilinear (E := E) B v v) ↔
      ∀ v : E, v ≠ 0 → 0 < B v v := by
  simp

/-- The antisymmetric defect of a bilinear form. It vanishes exactly on symmetric forms. -/
noncomputable def symmetryDefect : BilE →L[ℝ] BilE :=
  { toLinearMap := (ContinuousLinearMap.id ℝ BilE).toLinearMap - (flipBilinear (E := E)).toLinearMap
    cont := (ContinuousLinearMap.id ℝ BilE).continuous.sub (flipBilinear (E := E)).continuous }

@[simp] lemma symmetryDefect_apply_apply
    (B : BilE) (v w : E) :
    symmetryDefect (E := E) B v w = B v w - B w v := by
  simp [symmetryDefect, sub_eq_add_neg]

lemma symmetryDefect_eq_zero_iff
    (B : BilE) :
    symmetryDefect (E := E) B = 0 ↔ ∀ v w : E, B v w = B w v := by
  constructor
  · intro h v w
    have h' := congrArg (fun A : BilE => A v w) h
    exact sub_eq_zero.mp (by simpa [symmetryDefect] using h')
  · intro h
    ext v w
    simp [symmetryDefect, h v w]

/-- A positive-definite continuous bilinear form on a finite-dimensional real normed space
uniformly dominates a positive multiple of the ambient norm squared. -/
lemma exists_pos_mul_sq_le_of_pos [FiniteDimensional ℝ E] [Nontrivial E]
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) :
    ∃ c > 0, ∀ v : E, c * ‖v‖ ^ 2 ≤ B v v := by
  let f : E → ℝ := fun v ↦ B v v
  have hcont : Continuous f := by
    dsimp [f]
    fun_prop
  letI : ProperSpace E := FiniteDimensional.proper_real E
  have hcompact : IsCompact (Metric.sphere (0 : E) 1) := by
    simpa using (isCompact_sphere (0 : E) 1)
  have hsphere : (Metric.sphere (0 : E) 1).Nonempty := by
    exact NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨u, hu, hmin⟩ := hcompact.exists_isMinOn hsphere hcont.continuousOn
  have hu_ne : u ≠ 0 := Metric.ne_of_mem_sphere hu one_ne_zero
  refine ⟨B u u, hpos u hu_ne, ?_⟩
  intro v
  by_cases hv : v = 0
  · simp [hv]
  · let w : E := ‖v‖⁻¹ • v
    have hw_norm : ‖w‖ = 1 := by
      dsimp [w]
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
    have hw_mem : w ∈ Metric.sphere (0 : E) 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm, w] using hw_norm
    have hminw : B u u ≤ B w w := (isMinOn_iff.mp hmin) w hw_mem
    have hscaled : B u u * ‖v‖ ^ 2 ≤ B w w * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hminw (sq_nonneg ‖v‖)
    have hw_eval : B w w * ‖v‖ ^ 2 = B v v := by
      dsimp [w]
      have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      simp [pow_two, mul_assoc]
      field_simp [hvn]
    simpa [mul_comm] using hscaled.trans_eq hw_eval

/-- The unit sublevel set of a positive-definite continuous bilinear form is von Neumann bounded.
This supplies the boundedness field needed to reify positive-definite bilinear-form sections as
continuous Riemannian metrics. -/
lemma isVonNBounded_sublevel_one_of_pos [FiniteDimensional ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) :
    Bornology.IsVonNBounded ℝ {v : E | B v v < 1} := by
  by_cases hsub : Subsingleton E
  · letI : Subsingleton E := hsub
    exact Bornology.IsVonNBounded.of_subsingleton
  · haveI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hsub
    rcases exists_pos_mul_sq_le_of_pos (E := E) B hpos with ⟨c, hc, hc_le⟩
    refine NormedSpace.isVonNBounded_of_isBounded ℝ ((Metric.isBounded_iff_subset_ball 0).2 ?_)
    refine ⟨c⁻¹ + 1, ?_⟩
    intro v hv
    rw [Metric.mem_ball, dist_zero_right]
    have hc_inv_pos : 0 < c⁻¹ := inv_pos.mpr hc
    have hB_lt : c * ‖v‖ ^ 2 < 1 := lt_of_le_of_lt (hc_le v) hv
    by_cases hn : ‖v‖ ≤ 1
    · linarith
    · have hn_gt : 1 < ‖v‖ := lt_of_not_ge hn
      have hsq_ge : ‖v‖ ≤ ‖v‖ ^ 2 := by
        nlinarith [hn_gt]
      have hmul_le : c * ‖v‖ ≤ c * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsq_ge (le_of_lt hc)
      have hmul_lt : c * ‖v‖ < 1 := lt_of_le_of_lt hmul_le hB_lt
      have hn_lt_inv : ‖v‖ < c⁻¹ := by
        have hn_lt_div : ‖v‖ < 1 / c := by
          exact (lt_div_iff₀ hc).2 (by simpa [mul_comm] using hmul_lt)
        simpa [one_div] using hn_lt_div
      linarith

/-- Transfer the von Neumann boundedness of the unit sublevel set of a positive-definite bilinear
form across a continuous linear equivalence to a finite-dimensional model space. -/
lemma isVonNBounded_sublevel_one_of_pos_of_continuousLinearEquiv
    {E' : Type*} [TopologicalSpace E'] [AddCommGroup E'] [Module ℝ E']
    [FiniteDimensional ℝ E]
    (e : E' ≃L[ℝ] E)
    (B : E' →L[ℝ] E' →L[ℝ] ℝ)
    (hpos : ∀ v : E', v ≠ 0 → 0 < B v v) :
    Bornology.IsVonNBounded ℝ {v : E' | B v v < 1} := by
  let m : (E' →L[ℝ] E' →L[ℝ] ℝ) ≃L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
    e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))
  let B' : E →L[ℝ] E →L[ℝ] ℝ := m B
  have hpos' : ∀ v : E, v ≠ 0 → 0 < B' v v := by
    intro v hv
    have hv' : e.symm v ≠ 0 := by
      intro hzero
      apply hv
      simpa using congrArg e hzero
    simpa [B', m] using hpos (e.symm v) hv'
  have hbounded_model :
      Bornology.IsVonNBounded ℝ {v : E | B' v v < 1} :=
    isVonNBounded_sublevel_one_of_pos (E := E) B' hpos'
  have hbounded_image :
      Bornology.IsVonNBounded ℝ
        ((e.symm : E →L[ℝ] E') '' {v : E | B' v v < 1}) :=
    Bornology.IsVonNBounded.image hbounded_model (e.symm : E →L[ℝ] E')
  refine Bornology.IsVonNBounded.subset ?_ hbounded_image
  intro v hv
  refine ⟨e v, ?_, ?_⟩
  · simpa [B', m] using hv
  · simp

/-- If a bilinear form is bounded below by a positive multiple of `‖v‖^2`, then every sufficiently
small perturbation in operator norm remains positive-definite. -/
lemma pos_of_norm_sub_lt
    {B C : E →L[ℝ] E →L[ℝ] ℝ} {c : ℝ}
    (hB : ∀ v : E, c * ‖v‖ ^ 2 ≤ B v v)
    (hBC : ‖C - B‖ < c) :
    ∀ v : E, v ≠ 0 → 0 < C v v := by
  intro v hv
  have hv_sq_pos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hCv : ‖(C - B) v‖ ≤ ‖C - B‖ * ‖v‖ := ContinuousLinearMap.le_opNorm (C - B) v
  have hdiff_le : ‖(C - B) v v‖ ≤ ‖C - B‖ * ‖v‖ ^ 2 := by
    calc
      ‖(C - B) v v‖ ≤ ‖(C - B) v‖ * ‖v‖ := ContinuousLinearMap.le_opNorm ((C - B) v) v
      _ ≤ (‖C - B‖ * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right hCv (norm_nonneg v)
      _ = ‖C - B‖ * ‖v‖ ^ 2 := by ring
  have hdiff_lt : ‖(C - B) v v‖ < c * ‖v‖ ^ 2 := by
    exact lt_of_le_of_lt hdiff_le (by
      have := mul_lt_mul_of_pos_right hBC hv_sq_pos
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this)
  have hlower : -(c * ‖v‖ ^ 2) < (C - B) v v := by
    exact (abs_lt.mp (by simpa using hdiff_lt)).1
  have hBv : c * ‖v‖ ^ 2 ≤ B v v := hB v
  have hsum : 0 < B v v + (C - B) v v := by
    have hneg : -(B v v) ≤ -(c * ‖v‖ ^ 2) := neg_le_neg hBv
    have hlt : -(B v v) < (C - B) v v := lt_of_le_of_lt hneg hlower
    linarith
  have hrepr : B v v + (C - B) v v = C v v := by
    simpa [add_comm] using congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L v v) (sub_add_cancel C B)
  rw [hrepr] at hsum
  exact hsum

/-- Positive-definite continuous bilinear forms form an open subset of the operator-norm space of
all continuous bilinear forms on a finite-dimensional real normed space. -/
lemma exists_pos_ball_of_pos [FiniteDimensional ℝ E] [Nontrivial E]
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) :
    ∃ ε > 0, ∀ C : E →L[ℝ] E →L[ℝ] ℝ, ‖C - B‖ < ε → ∀ v : E, v ≠ 0 → 0 < C v v := by
  obtain ⟨c, hc, hcoer⟩ := exists_pos_mul_sq_le_of_pos B hpos
  refine ⟨c, hc, ?_⟩
  intro C hC v hv
  exact pos_of_norm_sub_lt hcoer hC v hv

/-- A continuous family of positive-definite continuous bilinear forms over a compact space admits a
uniform pointwise perturbation radius that preserves positive-definiteness. -/
lemma exists_uniform_pos_ball_of_continuous
    {α : Type*} [TopologicalSpace α] [CompactSpace α]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (g : α → BilE) (hg : Continuous g)
    (hpos : ∀ x : α, ∀ v : E, v ≠ 0 → 0 < g x v v) :
    ∃ ε > 0, ∀ h : α → BilE, (∀ x : α, ‖h x - g x‖ < ε) →
      ∀ x : α, ∀ v : E, v ≠ 0 → 0 < h x v v := by
  classical
  by_cases hα : Nonempty α
  · letI := hα
    choose ε hεpos hεball using
      fun x : α => exists_pos_ball_of_pos (g x) (hpos x)
    let U : α → Set α := fun x => {y | ‖g y - g x‖ < ε x / 2}
    have hUo : ∀ x, IsOpen (U x) := by
      intro x
      have hcont : Continuous fun y : α => g y - g x := by
        exact hg.sub (continuous_const : Continuous fun _ : α => g x)
      exact isOpen_lt hcont.norm continuous_const
    have hcover : univ ⊆ ⋃ x, U x := by
      intro y hy
      refine mem_iUnion.2 ⟨y, ?_⟩
      change ‖g y - g y‖ < ε y / 2
      simpa using half_pos (hεpos y)
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo hcover
    have htne : t.Nonempty := by
      obtain ⟨x0⟩ := hα
      have hx0 : x0 ∈ ⋃ x ∈ t, U x := ht (by simp)
      rcases mem_iUnion₂.1 hx0 with ⟨i, hit, _⟩
      exact ⟨i, hit⟩
    let δ : ℝ := t.inf' htne (fun x => ε x / 2)
    have hδpos : 0 < δ := by
      have hmem : δ ∈ Ioi (0 : ℝ) := by
        refine Finset.inf'_mem (s := Ioi (0 : ℝ)) ?_ t htne (fun x => ε x / 2) ?_
        · intro a ha b hb
          simpa [mem_Ioi] using lt_min ha hb
        · intro x hx
          simpa [mem_Ioi] using half_pos (hεpos x)
      exact hmem
    refine ⟨δ, hδpos, ?_⟩
    intro h hh x v hv
    have hx : x ∈ ⋃ y ∈ t, U y := ht (by simp)
    rcases mem_iUnion₂.1 hx with ⟨i, hit, hix⟩
    have hδle : δ ≤ ε i / 2 := Finset.inf'_le (fun y => ε y / 2) hit
    have hgix : ‖g x - g i‖ < ε i / 2 := by
      simpa [U] using hix
    have hhix : ‖h x - g i‖ < ε i := by
      have hlt : ‖h x - g i‖ < δ + ε i / 2 := by
        calc
          ‖h x - g i‖ = ‖(h x - g x) + (g x - g i)‖ := by
            congr 1
            abel
          _ ≤ ‖h x - g x‖ + ‖g x - g i‖ := norm_add_le _ _
          _ < δ + ε i / 2 := add_lt_add_of_lt_of_lt (hh x) hgix
      have hbound : δ + ε i / 2 ≤ ε i := by
        linarith
      exact lt_of_lt_of_le hlt hbound
    exact hεball i (h x) hhix v hv
  · refine ⟨1, zero_lt_one, ?_⟩
    intro h hh x
    exact (hα ⟨x⟩).elim

/-- Positive-definite bounded continuous bilinear-form families form an open subset of the
sup-metric space of bounded continuous families on a compact base. -/
lemma exists_pos_ball_of_continuousMap
    {α : Type*} [TopologicalSpace α] [CompactSpace α]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (g : C(α, BilE))
    (hpos : ∀ x : α, ∀ v : E, v ≠ 0 → 0 < g x v v) :
    ∃ ε > 0, ∀ h : C(α, BilE), dist h g < ε →
      ∀ x : α, ∀ v : E, v ≠ 0 → 0 < h x v v := by
  obtain ⟨ε, hεpos, hε⟩ := exists_uniform_pos_ball_of_continuous g g.continuous hpos
  refine ⟨ε, hεpos, ?_⟩
  intro h hh x v hv
  have hpointwise : ∀ y : α, dist (h y) (g y) ≤ dist h g :=
    (ContinuousMap.dist_le (f := h) (g := g) (C := dist h g) dist_nonneg).1 le_rfl
  exact hε h
    (fun y => by
      have hy : dist (h y) (g y) < ε := lt_of_le_of_lt (hpointwise y) hh
      simpa [dist_eq_norm] using hy)
    x v hv

lemma isOpen_setOf_continuousMap_forall_pos
    {α : Type*} [TopologicalSpace α] [CompactSpace α]
    [FiniteDimensional ℝ E] [Nontrivial E] :
    IsOpen {g : C(α, BilE) | ∀ x : α, ∀ v : E, v ≠ 0 → 0 < g x v v} := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  obtain ⟨ε, hεpos, hε⟩ := exists_pos_ball_of_continuousMap g hg
  refine Filter.mem_of_superset (Metric.ball_mem_nhds g hεpos) ?_
  intro h hh
  exact hε h (by simpa [Metric.mem_ball] using hh)

/-- Positive-definite bounded continuous bilinear-form families form an open subset of the
sup-metric space of bounded continuous families on a compact base. -/
lemma exists_pos_ball_of_boundedContinuousFunction
    {α : Type*} [TopologicalSpace α] [CompactSpace α]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (g : BoundedContinuousFunction α BilE)
    (hpos : ∀ x : α, ∀ v : E, v ≠ 0 → 0 < g x v v) :
    ∃ ε > 0, ∀ h : BoundedContinuousFunction α BilE, dist h g < ε →
      ∀ x : α, ∀ v : E, v ≠ 0 → 0 < h x v v := by
  obtain ⟨ε, hεpos, hε⟩ := exists_uniform_pos_ball_of_continuous g g.continuous hpos
  refine ⟨ε, hεpos, ?_⟩
  intro h hh x v hv
  exact hε h
    (fun y => by
      have hy : dist (h y) (g y) < ε := by
        exact lt_of_le_of_lt (BoundedContinuousFunction.dist_coe_le_dist y) hh
      simpa [dist_eq_norm] using hy)
    x v hv

lemma isOpen_setOf_boundedContinuousFunction_forall_pos
    {α : Type*} [TopologicalSpace α] [CompactSpace α]
    [FiniteDimensional ℝ E] [Nontrivial E] :
    IsOpen {g : BoundedContinuousFunction α BilE | ∀ x : α, ∀ v : E, v ≠ 0 → 0 < g x v v} := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  obtain ⟨ε, hεpos, hε⟩ := exists_pos_ball_of_boundedContinuousFunction g hg
  refine Filter.mem_of_superset (Metric.ball_mem_nhds g hεpos) ?_
  intro h hh
  exact hε h (by simpa [Metric.mem_ball] using hh)

end ContinuousLinearMap

end FiberwisePositivity

end Bundle

namespace Bundle

section LocalCoordinatePositivity

variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {W : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F W)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [FiberBundle F W] [VectorBundle ℝ F W]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)
local notation "BilW" => BilinearFormBundle (V := W)

/-- In preferred local coordinates, a bundled bilinear form evaluates by pulling the model vectors
back through the inverse fiber trivialization. -/
lemma trivializationAt_bilinearFormBundle_apply_eq
    (x0 x : M) (hx : x ∈ (trivializationAt F W x0).baseSet)
    (B : BilW x) (u v : F) :
    ((trivializationAt BilF BilW x0 ⟨x, B⟩).2) u v =
      B (((trivializationAt F W x0).continuousLinearEquivAt ℝ x hx).symm u)
        (((trivializationAt F W x0).continuousLinearEquivAt ℝ x hx).symm v) := by
  let e : W x ≃L[ℝ] F := (trivializationAt F W x0).continuousLinearEquivAt ℝ x hx
  let eDual : (W x →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] ℝ) :=
    ((trivializationAt (F →L[ℝ] ℝ) (fun y => W y →L[ℝ] ℝ) x0).continuousLinearEquivAt ℝ x
      (by simpa using hx) : (W x →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] ℝ))
  have hdual (φ : W x →L[ℝ] ℝ) :
      ((trivializationAt (F →L[ℝ] ℝ) (fun y => W y →L[ℝ] ℝ) x0 ⟨x, φ⟩).2) v =
        φ (e.symm v) := by
    have htrivDual := hom_trivializationAt_apply (σ := RingHom.id ℝ)
        (F₁ := F) (E₁ := W) (F₂ := ℝ) (E₂ := fun _ : M => ℝ) x0 ⟨x, φ⟩
    have hφ :
        (trivializationAt (F →L[ℝ] ℝ) (fun y => W y →L[ℝ] ℝ) x0 ⟨x, φ⟩).2 =
          φ.comp (e.symm : F →L[ℝ] W x) := by
      simpa [e, ContinuousLinearMap.inCoordinates_eq, hx] using congrArg Prod.snd htrivDual
    have hv := congrArg (fun ψ : F →L[ℝ] ℝ => ψ v) hφ
    simpa [e] using hv
  have htriv := hom_trivializationAt_apply (σ := RingHom.id ℝ)
      (F₁ := F) (E₁ := W) (F₂ := F →L[ℝ] ℝ) (E₂ := fun y => W y →L[ℝ] ℝ) x0 ⟨x, B⟩
  have hB :
      (trivializationAt BilF BilW x0 ⟨x, B⟩).2 =
        eDual.comp (B.comp (e.symm : F →L[ℝ] W x)) := by
    simpa [e, eDual, ContinuousLinearMap.inCoordinates_eq, hx] using congrArg Prod.snd htriv
  have hu := congrArg (fun ψ : F →L[ℝ] F →L[ℝ] ℝ => ψ u v) hB
  simpa [hdual, e, eDual] using hu

/-- In preferred local coordinates, a bundled bilinear form evaluates by pulling the model vector
back through the inverse fiber trivialization. -/
lemma trivializationAt_bilinearFormBundle_apply_apply_eq
    (x0 x : M) (hx : x ∈ (trivializationAt F W x0).baseSet)
    (B : BilW x) (u : F) :
    ((trivializationAt BilF BilW x0 ⟨x, B⟩).2) u u =
      B (((trivializationAt F W x0).continuousLinearEquivAt ℝ x hx).symm u)
        (((trivializationAt F W x0).continuousLinearEquivAt ℝ x hx).symm u) := by
  simpa using trivializationAt_bilinearFormBundle_apply_eq
    (F := F) (W := W) x0 x hx B u u

end LocalCoordinatePositivity

end Bundle

namespace PoincareCurvature

namespace Bundle.Trivialization

section CoordinatePositivity

variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)

local instance bilFNormedAddCommGroup : NormedAddCommGroup BilF :=
  (inferInstance : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ))

local instance bilFPseudoMetricSpace : PseudoMetricSpace BilF :=
  (inferInstance : PseudoMetricSpace (F →L[ℝ] F →L[ℝ] ℝ))

variable {W : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F W)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [FiberBundle F W] [VectorBundle ℝ F W]

local notation "BilW" => _root_.Bundle.BilinearFormBundle (V := W)

local instance bilWAddCommGroup (x : M) : AddCommGroup (BilW x) := inferInstance
local instance bilWModule (x : M) : Module ℝ (BilW x) := inferInstance
local instance bilWIsTopologicalAddGroup (x : M) : IsTopologicalAddGroup (BilW x) :=
  inferInstance
local instance bilWContinuousSMul (x : M) : ContinuousSMul ℝ (BilW x) :=
  inferInstance

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

/-- Coordinatewise slot-flip on compact continuous families of model bilinear forms. This is the
compact-coordinate operator that must later be shown to preserve the finite-cover compatibility
kernel in order to produce the global section-space slot-swap map. -/
noncomputable def flipBilinearCoordContinuousLinearMap
    (K : TopologicalSpace.Compacts M) :
    C(K, BilF) →L[ℝ] C(K, BilF) :=
  (_root_.Bundle.ContinuousLinearMap.flipBilinear (E := F)).compLeftContinuous ℝ K

@[simp] lemma flipBilinearCoordContinuousLinearMap_apply_apply
    (K : TopologicalSpace.Compacts M) (u : C(K, BilF)) (x : K) (v w : F) :
    flipBilinearCoordContinuousLinearMap (M := M) (F := F) K u x v w = u x w v := by
  simp [flipBilinearCoordContinuousLinearMap]

lemma flipBilinearCoordContinuousLinearMap_forall_pos_iff
    (K : TopologicalSpace.Compacts M) (u : C(K, BilF)) :
    (∀ x : K, ∀ v : F, v ≠ 0 →
      0 < flipBilinearCoordContinuousLinearMap (M := M) (F := F) K u x v v) ↔
      ∀ x : K, ∀ v : F, v ≠ 0 → 0 < u x v v := by
  simp

/-- Coordinatewise slot-flip on the ambient finite product of compact bilinear-form coordinate
families. The next global section-space step is proving that this map preserves the finite-cover
compatibility kernel for preferred bilinear-form trivializations. -/
noncomputable def flipBilinearCoordFamilyContinuousLinearMap
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M) :
    CoordFamily (M := M) (F := BilF) Kc →L[ℝ]
      CoordFamily (M := M) (F := BilF) Kc :=
  ContinuousLinearMap.piMap fun i ↦ flipBilinearCoordContinuousLinearMap (M := M) (F := F) (Kc i)

@[simp] lemma flipBilinearCoordFamilyContinuousLinearMap_apply_apply
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M)
    (u : CoordFamily (M := M) (F := BilF) Kc)
    (i : κ) (x : Kc i) (v w : F) :
    flipBilinearCoordFamilyContinuousLinearMap Kc u i x v w =
      u i x w v := by
  rfl

lemma flipBilinearCoordFamilyContinuousLinearMap_forall_pos_iff
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M)
    (u : CoordFamily (M := M) (F := BilF) Kc) :
    (∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 →
      0 < flipBilinearCoordFamilyContinuousLinearMap Kc u i x v v) ↔
      ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v := by
  simp

lemma flipBilinearCoordFamilyContinuousLinearMap_eq_self_iff
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M)
    (u : CoordFamily (M := M) (F := BilF) Kc) :
    flipBilinearCoordFamilyContinuousLinearMap Kc u = u ↔
      ∀ i : κ, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v := by
  constructor
  · intro h i x v w
    have h' := congrArg (fun U : CoordFamily (M := M) (F := BilF) Kc => U i x v w) h
    have h'' : u i x w v = u i x v w := by
      simpa using h'
    exact h''.symm
  · intro h
    funext i
    ext x v w
    simpa using h i x w v

/-- Coordinatewise antisymmetric defect on compact continuous families of model bilinear forms. -/
noncomputable def symmetryDefectCoordContinuousLinearMap
    (K : TopologicalSpace.Compacts M) :
    C(K, BilF) →L[ℝ] C(K, BilF) :=
  (_root_.Bundle.ContinuousLinearMap.symmetryDefect (E := F)).compLeftContinuous ℝ K

@[simp] lemma symmetryDefectCoordContinuousLinearMap_apply_apply
    (K : TopologicalSpace.Compacts M) (u : C(K, BilF)) (x : K) (v w : F) :
    symmetryDefectCoordContinuousLinearMap (M := M) (F := F) K u x v w =
      u x v w - u x w v := by
  simp [symmetryDefectCoordContinuousLinearMap]

/-- Coordinatewise antisymmetric defect on finite products of compact coordinate families. -/
noncomputable def symmetryDefectCoordFamilyContinuousLinearMap
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M) :
    CoordFamily (M := M) (F := BilF) Kc →L[ℝ]
      CoordFamily (M := M) (F := BilF) Kc :=
  ContinuousLinearMap.piMap fun i ↦ symmetryDefectCoordContinuousLinearMap (M := M) (F := F) (Kc i)

@[simp] lemma symmetryDefectCoordFamilyContinuousLinearMap_apply_apply
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M)
    (u : CoordFamily (M := M) (F := BilF) Kc)
    (i : κ) (x : Kc i) (v w : F) :
    symmetryDefectCoordFamilyContinuousLinearMap Kc u i x v w =
      u i x v w - u i x w v := by
  rfl

lemma symmetryDefectCoordFamilyContinuousLinearMap_eq_zero_iff
    {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M)
    (u : CoordFamily (M := M) (F := BilF) Kc) :
    symmetryDefectCoordFamilyContinuousLinearMap Kc u = 0 ↔
      ∀ i : κ, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v := by
  constructor
  · intro h i x v w
    have h' := congrArg
      (fun U : CoordFamily (M := M) (F := BilF) Kc => U i x v w) h
    exact sub_eq_zero.mp (by simpa using h')
  · intro h
    funext i
    ext x v w
    simp [h i x v w]

/-- If a bundled bilinear-form section is pointwise positive-definite, then its compact local
coordinate map in the preferred bilinear-form trivialization is pointwise positive-definite on the
model fiber. -/
lemma coordContinuousMap_forall_pos_of_forall_pos
    (x0 : M) (K : TopologicalSpace.Compacts M)
    (hK : (K : Set M) ⊆ (trivializationAt BilF BilW x0).baseSet)
    {s : Π x : M, BilW x}
    (hs : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (s x)))
    (hpos : ∀ x : M, ∀ v : W x, v ≠ 0 → 0 < s x v v) :
    ∀ y : K, ∀ u : F, u ≠ 0 →
      0 <
        coordContinuousMap (e := trivializationAt BilF BilW x0)
          K hK hs.continuousOn y u u := by
  intro y u hu
  have hyW : y.1 ∈ (trivializationAt F W x0).baseSet := by
    simpa using hK y.2
  let e := (trivializationAt F W x0).continuousLinearEquivAt ℝ y.1 hyW
  have huW :
      (e.symm u) ≠ 0 := by
    intro h
    apply hu
    have hu0 : u = e 0 := by
      simpa using congrArg e h
    exact hu0.trans (by simpa using map_zero e)
  rw [coordContinuousMap_apply]
  erw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_apply_eq
    (x0 := x0) (x := y.1) hyW (s y.1) u]
  exact hpos y.1 _ huW

/-- Around the compact preferred-coordinate image of a pointwise positive bilinear-form section,
there is a sup-norm ball of coordinate maps that stays pointwise positive-definite. -/
lemma exists_pos_ball_of_coordContinuousMap_of_forall_pos
    (x0 : M) (K : TopologicalSpace.Compacts M)
    (hK : (K : Set M) ⊆ (trivializationAt BilF BilW x0).baseSet)
    {s : Π x : M, BilW x}
    (hs : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (s x)))
    (hpos : ∀ x : M, ∀ v : W x, v ≠ 0 → 0 < s x v v)
    [FiniteDimensional ℝ F] [Nontrivial F] :
    ∃ ε > 0, ∀ h : C(K, BilF),
      dist h (coordContinuousMap (e := trivializationAt BilF BilW x0)
        K hK hs.continuousOn) < ε →
      ∀ y : K, ∀ u : F, u ≠ 0 → 0 < h y u u := by
  obtain ⟨ε, hεpos, hε⟩ :=
    _root_.Bundle.ContinuousLinearMap.exists_pos_ball_of_continuousMap
      (g := coordContinuousMap (e := trivializationAt BilF BilW x0)
        K hK hs.continuousOn)
      (hpos := coordContinuousMap_forall_pos_of_forall_pos
        (x0 := x0) (K := K) hK hs hpos)
  exact ⟨ε, hεpos, hε⟩

/-- Coordinate families of bilinear forms that are pointwise positive-definite on every compact
piece form an open subset of the ambient finite product of compact `ContinuousMap` spaces. -/
lemma isOpen_setOf_coordFamily_forall_pos
    {κ : Type*} [Finite κ] (Kc : κ → TopologicalSpace.Compacts M)
    [FiniteDimensional ℝ F] [Nontrivial F] :
    IsOpen ({u : CoordFamily (M := M) (F := BilF) Kc |
      ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
        Set (CoordFamily (M := M) (F := BilF) Kc)) := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  have hA : ∀ i : κ,
      IsOpen ({u : CoordFamily (M := M) (F := BilF) Kc |
        ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
          Set (CoordFamily (M := M) (F := BilF) Kc)) := by
    intro i
    let S : Set (C(Kc i, BilF)) := {g | ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < g x v v}
    have hopen : IsOpen S := by
      simpa [S] using
        (_root_.Bundle.ContinuousLinearMap.isOpen_setOf_continuousMap_forall_pos
          (α := Kc i) (E := F))
    have hπi : Continuous (fun u : CoordFamily (M := M) (F := BilF) Kc => u i) := by
      simpa using
        (continuous_apply i :
          Continuous fun u : CoordFamily (M := M) (F := BilF) Kc => u i)
    have hpre : IsOpen ((fun u : CoordFamily (M := M) (F := BilF) Kc => u i) ⁻¹' S) :=
      hopen.preimage hπi
    change IsOpen ((fun u : CoordFamily (M := M) (F := BilF) Kc => u i) ⁻¹' S)
    exact hpre
  have hfin : ∀ s : Finset κ,
      IsOpen ({u : CoordFamily (M := M) (F := BilF) Kc |
        ∀ i ∈ s, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
          Set (CoordFamily (M := M) (F := BilF) Kc)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · have hUniv :
        ({u : CoordFamily (M := M) (F := BilF) Kc |
            ∀ i ∈ (∅ : Finset κ), ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
            Set (CoordFamily (M := M) (F := BilF) Kc)) = Set.univ := by
          ext u
          simp
      rw [hUniv]
      exact isOpen_univ
    · intro a s _ hs
      have haOpen :
          IsOpen ({u : CoordFamily (M := M) (F := BilF) Kc |
            ∀ x : Kc a, ∀ v : F, v ≠ 0 → 0 < u a x v v} :
              Set (CoordFamily (M := M) (F := BilF) Kc)) := hA a
      have hsOpen :
          IsOpen ({u : CoordFamily (M := M) (F := BilF) Kc |
            ∀ i ∈ s, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
              Set (CoordFamily (M := M) (F := BilF) Kc)) := hs
      have hInsert :
          ({u : CoordFamily (M := M) (F := BilF) Kc |
              ∀ i ∈ insert a s, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
              Set (CoordFamily (M := M) (F := BilF) Kc)) =
            ({u : CoordFamily (M := M) (F := BilF) Kc |
                ∀ x : Kc a, ∀ v : F, v ≠ 0 → 0 < u a x v v} :
                Set (CoordFamily (M := M) (F := BilF) Kc)) ∩
            ({u : CoordFamily (M := M) (F := BilF) Kc |
                ∀ i ∈ s, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
                Set (CoordFamily (M := M) (F := BilF) Kc)) := by
          ext u
          simp
      rw [hInsert]
      exact haOpen.inter hsOpen
  have huniv : IsOpen ({u : CoordFamily (M := M) (F := BilF) Kc |
      ∀ i ∈ (Finset.univ : Finset κ), ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
        Set (CoordFamily (M := M) (F := BilF) Kc)) :=
    hfin (Finset.univ : Finset κ)
  have hAll :
      ({u : CoordFamily (M := M) (F := BilF) Kc |
          ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
          Set (CoordFamily (M := M) (F := BilF) Kc)) =
        ({u : CoordFamily (M := M) (F := BilF) Kc |
            ∀ i ∈ (Finset.univ : Finset κ), ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v} :
            Set (CoordFamily (M := M) (F := BilF) Kc)) := by
    ext u
    simp
  rw [hAll]
  exact huniv

/-- Coordinate families of bilinear forms that are pointwise symmetric on every compact piece form a
closed subset of the ambient finite product of compact `ContinuousMap` spaces. -/
lemma isClosed_setOf_coordFamily_forall_symmetric
    {κ : Type*} [Finite κ] (Kc : κ → TopologicalSpace.Compacts M) :
    IsClosed ({u : CoordFamily (M := M) (F := BilF) Kc |
      ∀ i : κ, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} :
        Set (CoordFamily (M := M) (F := BilF) Kc)) := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  have hA : ∀ i : κ,
      IsClosed ({u : CoordFamily (M := M) (F := BilF) Kc |
        ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} :
          Set (CoordFamily (M := M) (F := BilF) Kc)) := by
    intro i
    let L : C(Kc i, BilF) →L[ℝ] C(Kc i, BilF) :=
      _root_.ContinuousLinearMap.compLeftContinuous (R := ℝ) (α := Kc i)
        (_root_.Bundle.ContinuousLinearMap.symmetryDefect (E := F))
    let S : Set (C(Kc i, BilF)) := {g | ∀ x : Kc i, ∀ v w : F, g x v w = g x w v}
    have hEqS : S = (L.ker : Set (C(Kc i, BilF))) := by
      ext g
      constructor
      · intro hg
        change L g = 0
        ext x v w
        exact sub_eq_zero.mpr (by simpa [L] using hg x v w)
      · intro hg
        have hg0 : L g = 0 := hg
        intro x v w
        have hx : _root_.Bundle.ContinuousLinearMap.symmetryDefect (E := F) (g x) = 0 := by
          have h' := congrArg (fun h : C(Kc i, BilF) => h x) hg0
          simpa [L] using h'
        exact (_root_.Bundle.ContinuousLinearMap.symmetryDefect_eq_zero_iff (E := F) (g x)).1 hx v w
    have hclosedS : IsClosed S := by
      rw [hEqS]
      exact ContinuousLinearMap.isClosed_ker L
    have hπi : Continuous (fun u : CoordFamily (M := M) (F := BilF) Kc => u i) := by
      simpa using
        (continuous_apply i :
          Continuous fun u : CoordFamily (M := M) (F := BilF) Kc => u i)
    have hpre : IsClosed ((fun u : CoordFamily (M := M) (F := BilF) Kc => u i) ⁻¹' S) :=
      hclosedS.preimage hπi
    change IsClosed ((fun u : CoordFamily (M := M) (F := BilF) Kc => u i) ⁻¹' S)
    exact hpre
  have hfin : ∀ s : Finset κ,
      IsClosed ({u : CoordFamily (M := M) (F := BilF) Kc |
        ∀ i ∈ s, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} :
          Set (CoordFamily (M := M) (F := BilF) Kc)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · have hUniv :
          ({u : CoordFamily (M := M) (F := BilF) Kc |
              ∀ i ∈ (∅ : Finset κ), ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} :
              Set (CoordFamily (M := M) (F := BilF) Kc)) = Set.univ := by
        ext u
        simp
      rw [hUniv]
      exact isClosed_univ
    · intro a s _ hs
      have haClosed :
          IsClosed ({u : CoordFamily (M := M) (F := BilF) Kc |
            ∀ x : Kc a, ∀ v w : F, u a x v w = u a x w v} :
              Set (CoordFamily (M := M) (F := BilF) Kc)) := hA a
      have hsClosed :
          IsClosed ({u : CoordFamily (M := M) (F := BilF) Kc |
            ∀ i ∈ s, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} :
              Set (CoordFamily (M := M) (F := BilF) Kc)) := hs
      have hInsert :
          ({u : CoordFamily (M := M) (F := BilF) Kc |
              ∀ i ∈ insert a s, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} :
              Set (CoordFamily (M := M) (F := BilF) Kc)) =
            ({u : CoordFamily (M := M) (F := BilF) Kc |
                ∀ x : Kc a, ∀ v w : F, u a x v w = u a x w v} :
                Set (CoordFamily (M := M) (F := BilF) Kc)) ∩
            ({u : CoordFamily (M := M) (F := BilF) Kc |
                ∀ i ∈ s, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} :
                Set (CoordFamily (M := M) (F := BilF) Kc)) := by
        ext u
        simp
      rw [hInsert]
      exact haClosed.inter hsClosed
  have huniv : IsClosed ({u : CoordFamily (M := M) (F := BilF) Kc |
      ∀ i ∈ (Finset.univ : Finset κ), ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} :
        Set (CoordFamily (M := M) (F := BilF) Kc)) :=
    hfin (Finset.univ : Finset κ)
  have hAll :
      ({u : CoordFamily (M := M) (F := BilF) Kc |
          ∀ i : κ, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} :
          Set (CoordFamily (M := M) (F := BilF) Kc)) =
        ({u : CoordFamily (M := M) (F := BilF) Kc |
            ∀ i ∈ (Finset.univ : Finset κ), ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v} :
            Set (CoordFamily (M := M) (F := BilF) Kc)) := by
    ext u
    simp
  rw [hAll]
  exact huniv

variable {V : M → Type*}
  [TopologicalSpace (_root_.Bundle.TotalSpace (F →L[ℝ] F →L[ℝ] ℝ) V)] [∀ x, TopologicalSpace (V x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle (F →L[ℝ] F →L[ℝ] ℝ) V] [VectorBundle ℝ (F →L[ℝ] F →L[ℝ] ℝ) V]

/-- The pointwise positive-definite locus is open inside the closed compatibility kernel for compact
coordinate families of bilinear-form sections. -/
lemma isOpen_setOf_compatibleCoordFamilySubmodule_forall_pos
    {κ : Type*} [Finite κ]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    [FiniteDimensional ℝ F] [Nontrivial F] :
    IsOpen {u : compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo |
      ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u.1 i x v v} := by
  let S : Set (CoordFamily (M := M) (F := BilF) Kc) := {u |
    ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u i x v v}
  have hS : IsOpen S := isOpen_setOf_coordFamily_forall_pos (M := M) (F := F) Kc
  change IsOpen (Subtype.val ⁻¹' S)
  exact hS.preimage continuous_subtype_val

/-- The pointwise symmetric locus is closed inside the compatibility kernel for compact coordinate
families of bilinear-form sections. -/
lemma isClosed_setOf_compatibleCoordFamilySubmodule_forall_symmetric
    {κ : Type*} [Finite κ]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)) :
    IsClosed {u : compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo |
      ∀ i : κ, ∀ x : Kc i, ∀ v w : F, u.1 i x v w = u.1 i x w v} := by
  let S : Set (CoordFamily (M := M) (F := BilF) Kc) := {u |
    ∀ i : κ, ∀ x : Kc i, ∀ v w : F, u i x v w = u i x w v}
  have hS : IsClosed S := isClosed_setOf_coordFamily_forall_symmetric (M := M) (F := F) Kc
  change IsClosed (Subtype.val ⁻¹' S)
  exact hS.preimage continuous_subtype_val

namespace ContinuousSectionSpace

/-- After transporting the finite-cover compatibility kernel to the bundled continuous-section
wrapper, the coordinatewise pointwise positive-definite locus remains open. -/
lemma isOpen_setOf_coordwise_forall_pos
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F] :
    IsOpen {s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := V)
        et Kc hKc Ko hKo hKoEq hcover |
      ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 →
        0 <
          ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
            et Kc hKc Ko hKo hKoEq hcover s).1 i x v v)} := by
  letI : Fintype κ := Fintype.ofFinite κ
  let e := equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
    et Kc hKc Ko hKo hKoEq hcover
  let S :
      Set (compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo) := {u |
        ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 → 0 < u.1 i x v v}
  have hS : IsOpen S :=
    isOpen_setOf_compatibleCoordFamilySubmodule_forall_pos
      (M := M) (F := F) (V := V) et Kc hKc Ko hKo
  have hIso : Isometry e := by
    intro x y
    rfl
  change IsOpen (e ⁻¹' S)
  exact hS.preimage hIso.continuous

/-- After transporting the finite-cover compatibility kernel to the bundled continuous-section
wrapper, the coordinatewise pointwise symmetric locus remains closed. -/
lemma isClosed_setOf_coordwise_forall_symmetric
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    IsClosed {s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := V)
        et Kc hKc Ko hKo hKoEq hcover |
      ∀ i : κ, ∀ x : Kc i, ∀ v w : F,
        ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
            et Kc hKc Ko hKo hKoEq hcover s).1 i x v w) =
          ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
            et Kc hKc Ko hKo hKoEq hcover s).1 i x w v)} := by
  letI : Fintype κ := Fintype.ofFinite κ
  let e := equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
    et Kc hKc Ko hKo hKoEq hcover
  let S :
      Set (compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo) := {u |
        ∀ i : κ, ∀ x : Kc i, ∀ v w : F, u.1 i x v w = u.1 i x w v}
  have hS : IsClosed S :=
    isClosed_setOf_compatibleCoordFamilySubmodule_forall_symmetric
      (M := M) (F := F) (V := V) et Kc hKc Ko hKo
  have hIso : Isometry e := by
    intro x y
    rfl
  change IsClosed (e ⁻¹' S)
  exact hS.preimage hIso.continuous

/-- The transported continuous-linear coordinatewise antisymmetric-defect map on bundled
continuous sections. Its codomain is the ambient finite coordinate-family product, so it does not
require proving that the defect or slot-flip preserves the compatibility kernel. -/
noncomputable def coordwiseSymmetryDefectContinuousLinearMap
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := V)
        et Kc hKc Ko hKo hKoEq hcover →L[ℝ]
      CoordFamily (M := M) (F := BilF) Kc :=
  letI : Fintype κ := Fintype.ofFinite κ
  let e := equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
    et Kc hKc Ko hKo hKoEq hcover
  let D : compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo →L[ℝ]
      CoordFamily (M := M) (F := BilF) Kc :=
    (symmetryDefectCoordFamilyContinuousLinearMap (M := M) (F := F) Kc).comp
      (compatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) et Kc hKc Ko hKo).subtypeL
  { toFun := fun s ↦ D (e s)
    map_add' := by
      intro s t
      change D (e (s + t)) = D (e s) + D (e t)
      have he : e (s + t) = e s + e t := by
        apply e.symm.injective
        change e.symm (e (e.symm (e s + e t))) = e.symm (e s + e t)
        simp
      rw [he, map_add]
    map_smul' := by
      intro c s
      change D (e (c • s)) = c • D (e s)
      have he : e (c • s) = c • e s := by
        apply e.symm.injective
        change e.symm (e (e.symm (c • e s))) = e.symm (c • e s)
        simp
      rw [he, map_smul]
    cont := by
      have hIso : Isometry e := by
        intro s t
        rfl
      exact D.continuous.comp hIso.continuous }

section PreferredTrivializations

/-- On a finite compact cover by preferred bilinear-form trivializations, an actually
positive-definite bilinear-form section has positive-definite compact coordinate maps on every
covering piece. -/
lemma coordwise_forall_pos_of_forall_pos
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)
    (hpos : ∀ x : M, ∀ v : W x, v ≠ 0 → 0 < s x v v) :
    ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 →
      0 <
        coordContinuousMap
          (e := et i)
          (Kc i) (hKc i) s.continuous_toFun.continuousOn x v v := by
  intro i x v hv
  have hKpref :
      (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet := by
    simpa [het i] using hKc i
  simpa [het i] using
    coordContinuousMap_forall_pos_of_forall_pos
      (x0 := x0 i) (K := Kc i) (hK := hKpref)
      (s := fun y ↦ s y) s.continuous_toFun hpos x v hv

/-- Conversely, if all compact preferred-coordinate maps of a bilinear-form section are
positive-definite, then the section itself is pointwise positive-definite. -/
lemma forall_pos_of_coordwise_forall_pos
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)
    (hcoord : ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 →
      0 <
        coordContinuousMap
          (e := et i)
          (Kc i) (hKc i) s.continuous_toFun.continuousOn x v v) :
    ∀ x : M, ∀ v : W x, v ≠ 0 → 0 < s x v v := by
  intro x v hv
  have hxcover : x ∈ ⋃ i, (Kc i : Set M) := by
    simpa [hcover]
  rcases Set.mem_iUnion.mp hxcover with ⟨i, hxi⟩
  let xK : Kc i := ⟨x, hxi⟩
  have hKpref :
      (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet := by
    simpa [het i] using hKc i
  have hxbase : x ∈ (trivializationAt F W (x0 i)).baseSet := by
    simpa using hKpref hxi
  let e := (trivializationAt F W (x0 i)).continuousLinearEquivAt ℝ x hxbase
  have hu : e v ≠ 0 := by
    intro h
    apply hv
    apply e.injective
    simpa using h
  have hcoord' : 0 <
      coordContinuousMap
        (e := trivializationAt BilF BilW (x0 i))
        (Kc i) hKpref s.continuous_toFun.continuousOn xK (e v) (e v) := by
    simpa [het i] using hcoord i xK (e v) hu
  have hEq :
      coordContinuousMap
          (e := trivializationAt BilF BilW (x0 i))
          (Kc i) hKpref s.continuous_toFun.continuousOn xK (e v) (e v) = s x v v := by
    rw [coordContinuousMap_apply]
    erw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_apply_eq
      (x0 := x0 i) (x := x) hxbase (s x) (e v)]
    have hvEq :
        e.symm (e v) = v := by
      simpa using e.symm_apply_apply v
    rw [hvEq]
  exact hEq ▸ hcoord'

/-- On a finite compact cover by preferred bilinear-form trivializations, an actually symmetric
bilinear-form section has symmetric compact coordinate maps on every covering piece. -/
lemma coordwise_forall_symmetric_of_forall_symmetric
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)
    (hsymm : ∀ x : M, ∀ v w : W x, s x v w = s x w v) :
    ∀ i : κ, ∀ x : Kc i, ∀ v w : F,
      coordContinuousMap
          (e := et i)
          (Kc i) (hKc i) s.continuous_toFun.continuousOn x v w =
        coordContinuousMap
          (e := et i)
          (Kc i) (hKc i) s.continuous_toFun.continuousOn x w v := by
  intro i x v w
  have hKpref :
      (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet := by
    simpa [het i] using hKc i
  have hpref :
      coordContinuousMap
          (e := trivializationAt BilF BilW (x0 i))
          (Kc i) hKpref s.continuous_toFun.continuousOn x v w =
        coordContinuousMap
          (e := trivializationAt BilF BilW (x0 i))
          (Kc i) hKpref s.continuous_toFun.continuousOn x w v := by
    have hxbase : x.1 ∈ (trivializationAt F W (x0 i)).baseSet := by
      simpa using hKpref x.2
    erw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_eq
      (x0 := x0 i) (x := x.1) hxbase (s x.1) v w]
    erw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_eq
      (x0 := x0 i) (x := x.1) hxbase (s x.1) w v]
    exact hsymm x.1 _ _
  simpa [het i] using hpref

/-- Conversely, if all compact preferred-coordinate maps of a bilinear-form section are symmetric,
then the section itself is pointwise symmetric. -/
lemma forall_symmetric_of_coordwise_forall_symmetric
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)
    (hcoord : ∀ i : κ, ∀ x : Kc i, ∀ v w : F,
      coordContinuousMap
          (e := et i)
          (Kc i) (hKc i) s.continuous_toFun.continuousOn x v w =
        coordContinuousMap
          (e := et i)
          (Kc i) (hKc i) s.continuous_toFun.continuousOn x w v) :
    ∀ x : M, ∀ v w : W x, s x v w = s x w v := by
  intro x v w
  have hxcover : x ∈ ⋃ i, (Kc i : Set M) := by
    simpa [hcover]
  rcases Set.mem_iUnion.mp hxcover with ⟨i, hxi⟩
  let xK : Kc i := ⟨x, hxi⟩
  have hKpref :
      (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet := by
    simpa [het i] using hKc i
  have hxbase : x ∈ (trivializationAt F W (x0 i)).baseSet := by
    simpa using hKpref hxi
  let e := (trivializationAt F W (x0 i)).continuousLinearEquivAt ℝ x hxbase
  have hcoord' :
      coordContinuousMap
          (e := trivializationAt BilF BilW (x0 i))
          (Kc i) hKpref s.continuous_toFun.continuousOn xK (e v) (e w) =
        coordContinuousMap
          (e := trivializationAt BilF BilW (x0 i))
          (Kc i) hKpref s.continuous_toFun.continuousOn xK (e w) (e v) := by
    simpa [het i] using hcoord i xK (e v) (e w)
  have hEqLeft :
      coordContinuousMap
          (e := trivializationAt BilF BilW (x0 i))
          (Kc i) hKpref s.continuous_toFun.continuousOn xK (e v) (e w) =
        s x v w := by
    rw [coordContinuousMap_apply]
    erw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_eq
      (x0 := x0 i) (x := x) hxbase (s x) (e v) (e w)]
    change s x (e.symm (e v)) (e.symm (e w)) = s x v w
    simpa using congrArg₂ (fun a b => s x a b) (e.symm_apply_apply v) (e.symm_apply_apply w)
  have hEqRight :
      coordContinuousMap
          (e := trivializationAt BilF BilW (x0 i))
          (Kc i) hKpref s.continuous_toFun.continuousOn xK (e w) (e v) =
        s x w v := by
    rw [coordContinuousMap_apply]
    erw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_eq
      (x0 := x0 i) (x := x) hxbase (s x) (e w) (e v)]
    change s x (e.symm (e w)) (e.symm (e v)) = s x w v
    simpa using congrArg₂ (fun a b => s x a b) (e.symm_apply_apply w) (e.symm_apply_apply v)
  calc
    s x v w =
        coordContinuousMap
            (e := trivializationAt BilF BilW (x0 i))
            (Kc i) hKpref s.continuous_toFun.continuousOn xK (e v) (e w) := hEqLeft.symm
    _ =
        coordContinuousMap
            (e := trivializationAt BilF BilW (x0 i))
            (Kc i) hKpref s.continuous_toFun.continuousOn xK (e w) (e v) := hcoord'
    _ = s x w v := hEqRight

/-- The actual pointwise positive-definite locus inside a bundled continuous-section space of
bilinear forms. -/
def positiveDefiniteLocus
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) :=
  {s | ∀ x : M, ∀ v : W x, v ≠ 0 → 0 < s x v v}

/-- The pointwise symmetric locus inside a bundled continuous-section space of bilinear forms. -/
def symmetricLocus
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) :=
  {s | ∀ x : M, ∀ v w : W x, s x v w = s x w v}

/-- On preferred finite-cover coordinates, the transported coordinatewise antisymmetric-defect map
cuts out exactly the actual pointwise symmetric locus of bundled bilinear-form sections. -/
lemma coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) :
    coordwiseSymmetryDefectContinuousLinearMap (F := F) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover s = 0 ↔
      s ∈ symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover := by
  let e := equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
    et Kc hKc Ko hKo hKoEq hcover
  change
    symmetryDefectCoordFamilyContinuousLinearMap (M := M) (F := F) Kc (e s).1 = 0 ↔
      s ∈ symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover
  constructor
  · intro h
    have hcoord :=
      (symmetryDefectCoordFamilyContinuousLinearMap_eq_zero_iff (M := M) (F := F)
        Kc (e s).1).1 h
    exact forall_symmetric_of_coordwise_forall_symmetric
      (M := M) (F := F) (W := W)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover) s (by
        intro i x v w
        have h' := hcoord i x v w
        simpa [e, ContinuousSectionSpace.equivCompatibleCoordFamilySubmodule,
          ContinuousSectionSpace.toSubtype, continuousSectionEquivCompatibleCoordFamilySubmodule,
          continuousSectionEquivCompatibleCoordFamily, compatibleCoordFamilyEquivSubmodule,
          compatibleCoordFamilyOfSection, coordFamilyOfSection] using h')
  · intro hs
    have hcoord := coordwise_forall_symmetric_of_forall_symmetric
      (M := M) (F := F) (W := W)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover) s hs
    exact
      (symmetryDefectCoordFamilyContinuousLinearMap_eq_zero_iff (M := M) (F := F)
        Kc (e s).1).2 (by
          intro i x v w
          have h' := hcoord i x v w
          simpa [e, ContinuousSectionSpace.equivCompatibleCoordFamilySubmodule,
            ContinuousSectionSpace.toSubtype, continuousSectionEquivCompatibleCoordFamilySubmodule,
            continuousSectionEquivCompatibleCoordFamily, compatibleCoordFamilyEquivSubmodule,
            compatibleCoordFamilyOfSection, coordFamilyOfSection] using h')

/-- The symmetric positive-definite locus inside the bundled continuous-section space of bilinear
forms. This is the most faithful finite-cover section-space model of continuous metric data
currently available in the repo. -/
def symmetricPositiveDefiniteLocus
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) :=
  symmetricLocus (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover ∩
    positiveDefiniteLocus (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover

lemma mem_symmetricLocus_of_continuousRiemannianMetric
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : _root_.Bundle.ContinuousRiemannianMetric F W) :
    (⟨g.toSection, g.continuous_toSection⟩ :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover) ∈
      symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover := by
  intro x v w
  simpa [_root_.Bundle.ContinuousRiemannianMetric.toSection] using g.symm x v w

lemma mem_positiveDefiniteLocus_of_continuousRiemannianMetric
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : _root_.Bundle.ContinuousRiemannianMetric F W) :
    (⟨g.toSection, g.continuous_toSection⟩ :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover) ∈
      positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover := by
  intro x v hv
  simpa [_root_.Bundle.ContinuousRiemannianMetric.toSection] using g.pos x v hv

lemma mem_symmetricPositiveDefiniteLocus_of_continuousRiemannianMetric
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : _root_.Bundle.ContinuousRiemannianMetric F W) :
    (⟨g.toSection, g.continuous_toSection⟩ :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover) ∈
      symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover := by
  exact ⟨mem_symmetricLocus_of_continuousRiemannianMetric
      (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover g,
    mem_positiveDefiniteLocus_of_continuousRiemannianMetric
      (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover g⟩

/-- Reify a continuous bilinear-form section in the symmetric positive-definite finite-cover locus
as a bundled continuous Riemannian metric. -/
def _root_.Bundle.ContinuousRiemannianMetric.ofContinuousSectionSpace
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F]
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)
    (hs : s ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) :
    _root_.Bundle.ContinuousRiemannianMetric F W where
  inner := s
  symm := hs.1
  pos := hs.2
  isVonNBounded x := by
    let e : W x ≃L[ℝ] F :=
      _root_.Bundle.Trivialization.continuousLinearEquivAt ℝ
        (trivializationAt F W x) _ (FiberBundle.mem_baseSet_trivializationAt' x)
    exact
      _root_.Bundle.ContinuousLinearMap.isVonNBounded_sublevel_one_of_pos_of_continuousLinearEquiv
        (E := F) e (s x) (hs.2 x)
  continuous := s.continuous_toFun

@[simp] theorem _root_.Bundle.ContinuousRiemannianMetric.ofContinuousSectionSpace_inner
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F]
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)
    (hs : s ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    (x : M) :
    (_root_.Bundle.ContinuousRiemannianMetric.ofContinuousSectionSpace
      (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover s hs).inner x = s x := rfl

/-- Read one scalar component of a bilinear-form coordinate chart as a continuous linear map on the
bundled finite-cover continuous-section space. -/
noncomputable def coordBilinearFormReadoutContinuousLinearMap
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (i : κ) (x : Kc i) (u v : F) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →L[ℝ] ℝ :=
  ((ContinuousLinearMap.apply ℝ ℝ v).comp
    (ContinuousLinearMap.apply ℝ (F →L[ℝ] ℝ) u)).comp
      (coordReadoutContinuousLinearMap
        (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover i x)

@[simp]
lemma coordBilinearFormReadoutContinuousLinearMap_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (i : κ) (x : Kc i) (u v : F)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) :
    coordBilinearFormReadoutContinuousLinearMap
        (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover i x u v s =
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover s).1 i x u v := by
  simp [coordBilinearFormReadoutContinuousLinearMap]

/-- Read one actual fibrewise bilinear-form value from a preferred compact coordinate chart as a
continuous linear map on the finite-cover continuous-section space. -/
noncomputable def pointBilinearFormReadoutContinuousLinearMap
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (i : κ) (x : Kc i) (u v : W x.1) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover →L[ℝ] ℝ :=
  coordBilinearFormReadoutContinuousLinearMap
    (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover i x
      ((trivializationAt F W (x0 i)).continuousLinearMapAt ℝ x.1 u)
      ((trivializationAt F W (x0 i)).continuousLinearMapAt ℝ x.1 v)

@[simp]
lemma pointBilinearFormReadoutContinuousLinearMap_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (i : κ) (x : Kc i) (u v : W x.1)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) :
    pointBilinearFormReadoutContinuousLinearMap
        (M := M) (F := F) (W := W) x0 et Kc hKc Ko hKo hKoEq hcover i x u v s =
      s x.1 u v := by
  have hKpref :
      (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet := by
    simpa [het i] using hKc i
  have hxbase : x.1 ∈ (trivializationAt F W (x0 i)).baseSet := by
    simpa using hKpref x.2
  let e := (trivializationAt F W (x0 i)).continuousLinearEquivAt ℝ x.1 hxbase
  have hEq :
      coordBilinearFormReadoutContinuousLinearMap
          (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
          i x (e u) (e v) s =
        s x.1 u v := by
    rw [coordBilinearFormReadoutContinuousLinearMap_apply]
    change (et i ⟨x.1, s x.1⟩).2 (e u) (e v) = s x.1 u v
    rw [het i]
    erw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_eq
      (x0 := x0 i) (x := x.1) hxbase (s x.1) (e u) (e v)]
    rw [show e.symm (e u) = u from e.symm_apply_apply u,
      show e.symm (e v) = v from e.symm_apply_apply v]
  change
    coordBilinearFormReadoutContinuousLinearMap
        (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover i x
        ((trivializationAt F W (x0 i)).continuousLinearMapAt ℝ x.1 u)
        ((trivializationAt F W (x0 i)).continuousLinearMapAt ℝ x.1 v) s =
      s x.1 u v
  have huCoord :
      (trivializationAt F W (x0 i)).linearMapAt ℝ x.1 u = e u := by
    rw [Bundle.Trivialization.linearMapAt_apply, if_pos hxbase]
    rfl
  have hvCoord :
      (trivializationAt F W (x0 i)).linearMapAt ℝ x.1 v = e v := by
    rw [Bundle.Trivialization.linearMapAt_apply, if_pos hxbase]
    rfl
  have huCoord' :
      (trivializationAt F W (x0 i)).continuousLinearMapAt ℝ x.1 u = e u := by
    rw [Bundle.Trivialization.continuousLinearMapAt_apply]
    exact huCoord
  have hvCoord' :
      (trivializationAt F W (x0 i)).continuousLinearMapAt ℝ x.1 v = e v := by
    rw [Bundle.Trivialization.continuousLinearMapAt_apply]
    exact hvCoord
  rw [huCoord', hvCoord']
  exact hEq

/-- Two bilinear-form section states are equal when all scalar finite-cover bilinear coordinate
readouts agree. -/
theorem eq_of_coordBilinearFormReadout_eq
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {s t : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover}
    (hcoord : ∀ i (x : Kc i) (u v : F),
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover s).1 i x u v =
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := ℝ) (F := BilF) (V := BilW) et Kc hKc Ko hKo hKoEq hcover t).1 i x u v) :
    s = t := by
  apply eq_of_coordReadout_eq
  intro i x
  ext u v
  exact hcoord i x u v

/-- A continuous Riemannian metric determines a point of the closed symmetric section space. -/
def _root_.Bundle.ContinuousRiemannianMetric.toSymmetricSectionSpace
    {κ : Type*} [Finite κ] [T2Space M]
    (g : _root_.Bundle.ContinuousRiemannianMetric F W)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :=
  (⟨⟨g.toSection, g.continuous_toSection⟩,
      mem_symmetricLocus_of_continuousRiemannianMetric
        (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover g⟩ :
    {s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover //
      s ∈ symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover})

section

set_option maxHeartbeats 1000000

/-- For a finite compact cover by preferred bilinear-form trivializations, the actual
positive-definite locus of bundled bilinear-form sections is open in the transported
`ContinuousSectionSpace`. -/
lemma isOpen_setOf_forall_pos
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F] :
    IsOpen (positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) := by
  let S : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) := {s |
        ∀ i : κ, ∀ x : Kc i, ∀ v : F, v ≠ 0 →
          0 <
            ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
                et Kc hKc Ko hKo hKoEq hcover s).1 i x v v)}
  have hS : IsOpen S :=
    isOpen_setOf_coordwise_forall_pos
      (M := M) (F := F) (V := BilW)
      (et := et)
      Kc hKc Ko hKo hKoEq hcover
  have hEq :
      positiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover = S := by
    ext s
    constructor
    · intro hs
      intro i x v hv
      have hs' := coordwise_forall_pos_of_forall_pos
        (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
        (hKoEq := hKoEq) (hcover := hcover) s hs i x v hv
      change 0 <
        ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
            et Kc hKc Ko hKo hKoEq hcover s).1 i x v v)
      simpa [ContinuousSectionSpace.equivCompatibleCoordFamilySubmodule,
        ContinuousSectionSpace.toSubtype, continuousSectionEquivCompatibleCoordFamilySubmodule,
        continuousSectionEquivCompatibleCoordFamily, compatibleCoordFamilyEquivSubmodule,
        compatibleCoordFamilyOfSection, coordFamilyOfSection] using hs'
    · intro hs
      exact forall_pos_of_coordwise_forall_pos
        (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
        (hKoEq := hKoEq) (hcover := hcover) s (by
          intro i x v hv
          have hs' := hs i x v hv
          simpa [ContinuousSectionSpace.equivCompatibleCoordFamilySubmodule,
            ContinuousSectionSpace.toSubtype, continuousSectionEquivCompatibleCoordFamilySubmodule,
            continuousSectionEquivCompatibleCoordFamily, compatibleCoordFamilyEquivSubmodule,
            compatibleCoordFamilyOfSection, coordFamilyOfSection] using hs')
  rw [hEq]
  exact hS

/-- For a finite compact cover by preferred bilinear-form trivializations, the actual pointwise
symmetric locus of bundled bilinear-form sections is closed in the transported
`ContinuousSectionSpace`. -/
lemma isClosed_symmetricLocus
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    IsClosed (symmetricLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) := by
  let S : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) := {s |
        ∀ i : κ, ∀ x : Kc i, ∀ v w : F,
          ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
              et Kc hKc Ko hKo hKoEq hcover s).1 i x v w) =
            ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF)
              et Kc hKc Ko hKo hKoEq hcover s).1 i x w v)}
  have hS : IsClosed S :=
    isClosed_setOf_coordwise_forall_symmetric
      (M := M) (F := F) (V := BilW) et Kc hKc Ko hKo hKoEq hcover
  have hEq :
      symmetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover = S := by
    ext s
    constructor
    · intro hs
      intro i x v w
      have hs' := coordwise_forall_symmetric_of_forall_symmetric
        (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
        (hKoEq := hKoEq) (hcover := hcover) s hs i x v w
      simpa [ContinuousSectionSpace.equivCompatibleCoordFamilySubmodule,
        ContinuousSectionSpace.toSubtype, continuousSectionEquivCompatibleCoordFamilySubmodule,
        continuousSectionEquivCompatibleCoordFamily, compatibleCoordFamilyEquivSubmodule,
        compatibleCoordFamilyOfSection, coordFamilyOfSection] using hs'
    · intro hs
      exact forall_symmetric_of_coordwise_forall_symmetric
        (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
        (hKoEq := hKoEq) (hcover := hcover) s (by
          intro i x v w
          have hs' := hs i x v w
          simpa [ContinuousSectionSpace.equivCompatibleCoordFamilySubmodule,
            ContinuousSectionSpace.toSubtype, continuousSectionEquivCompatibleCoordFamilySubmodule,
            continuousSectionEquivCompatibleCoordFamily, compatibleCoordFamilyEquivSubmodule,
            compatibleCoordFamilyOfSection, coordFamilyOfSection] using hs')
  rw [hEq]
  exact hS

/-- The bundled section space restricted to pointwise symmetric bilinear-form sections. This is the
closed symmetric locus of the ambient bilinear-form section space, viewed as a subtype. -/
abbrev SymmetricSectionSpace
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) : Type _ :=
  {s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover //
    s ∈ symmetricLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover}

instance instCompleteSpaceSymmetricSectionSpace
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [CompleteSpace (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)] :
    CompleteSpace (SymmetricSectionSpace (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) := by
  letI : IsClosed
      (symmetricLocus (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover) :=
    isClosed_symmetricLocus (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover
  infer_instance

/-- The finite-cover metric locus inside the closed symmetric section space. Since symmetry is
already built into the ambient subtype, only positivity needs to be imposed here. -/
def riemannianMetricLocus
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    Set (SymmetricSectionSpace (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) :=
  {s | s.1 ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
    et Kc hKc Ko hKo hKoEq hcover}

/-- Inside the closed symmetric section space, the symmetric positive-definite locus is open. This
packages the usual heuristic that Riemannian metrics form an open subset of symmetric bilinear
forms in the transported finite-cover model. -/
lemma isOpen_symmetricPositiveDefiniteLocus_in_symmetricSectionSpace
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F] :
    IsOpen {s : SymmetricSectionSpace (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover |
      s.1 ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover} := by
  let T : Set (SymmetricSectionSpace (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) := {s |
        s.1 ∈ positiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover}
  have hT : IsOpen T := by
    change IsOpen (Subtype.val ⁻¹' positiveDefiniteLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover)
    exact (isOpen_setOf_forall_pos (M := M) (F := F) (W := W)
      x0 et het Kc hKc Ko hKo hKoEq hcover).preimage continuous_subtype_val
  have hEq :
      {s : SymmetricSectionSpace (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover |
        s.1 ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
          et Kc hKc Ko hKo hKoEq hcover} = T := by
    ext s
    constructor
    · intro hs
      exact hs.2
    · intro hs
      exact ⟨s.2, hs⟩
  rw [hEq]
  exact hT

/-- The metric locus is open inside the closed symmetric section space. -/
lemma isOpen_riemannianMetricLocus
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F] :
    IsOpen (riemannianMetricLocus (M := M) (F := F) (W := W)
      et Kc hKc Ko hKo hKoEq hcover) := by
  change IsOpen (Subtype.val ⁻¹' positiveDefiniteLocus (M := M) (F := F) (W := W)
    et Kc hKc Ko hKo hKoEq hcover)
  exact (isOpen_setOf_forall_pos (M := M) (F := F) (W := W)
    x0 et het Kc hKc Ko hKo hKoEq hcover).preimage continuous_subtype_val

/-- Genuine continuous Riemannian metrics land in the open metric locus of the closed symmetric
section space. -/
lemma _root_.Bundle.ContinuousRiemannianMetric.mem_riemannianMetricLocus
    {κ : Type*} [Finite κ] [T2Space M]
    (g : _root_.Bundle.ContinuousRiemannianMetric F W)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    g.toSymmetricSectionSpace et Kc hKc Ko hKo hKoEq hcover ∈
      riemannianMetricLocus (M := M) (F := F) (W := W)
        et Kc hKc Ko hKo hKoEq hcover := by
  show (g.toSymmetricSectionSpace et Kc hKc Ko hKo hKoEq hcover).1 ∈
      positiveDefiniteLocus (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover
  exact mem_positiveDefiniteLocus_of_continuousRiemannianMetric
    (M := M) (F := F) (W := W) et Kc hKc Ko hKo hKoEq hcover g

end

end PreferredTrivializations

end ContinuousSectionSpace

end CoordinatePositivity

end Bundle.Trivialization

end PoincareCurvature
