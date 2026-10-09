import ChartPort.LocalRawCurvatureBridge
import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor

noncomputable section
open Bundle FiberBundle Set
open scoped Manifold Topology ContDiff

namespace ChartPort

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

/-- Localize the proved spatial-infinity predicate using a genuine smooth bump.
This follows the project's finite-level class-to-set proof, at level infinity. -/
theorem timeFamilyChosen_contMDiffCovariantDerivativeOn_infinity
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ)
    {u : Set M} (hu : IsOpen u) :
    ContMDiffCovariantDerivativeOn E ∞ (timeFamilyChosen g t).toFun u := by
  let cov := timeFamilyChosen g t
  letI := timeFamilyChosen_contMDiffCovariantDerivative g t
  refine { contMDiff := ?_ }
  intro σ hσ
  have hσSmooth : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% σ) u := by
    simpa only [ENat.coe_top_add_one] using hσ
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  have hux : u ∈ nhds x := hu.mem_nhds hx
  obtain ⟨ψ, hψtsupp, hψsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) (c := x) hux).mem_iff.mp hux
  let τ : Π y : M, TangentSpace I y := fun y ↦ ψ y • σ y
  have hτ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% τ) := by
    simpa [τ] using
      (ContMDiffOn.smul_section_of_tsupport (I := I) (F := E)
        (V := (TangentSpace I : M → Type _)) (u := u)
        (n := (∞ : WithTop ℕ∞)) (ψ := ψ) ψ.contMDiff.contMDiffOn hu hψtsupp hσSmooth)
  have hτOn : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
      (T% τ) Set.univ := by
    simpa only [ENat.coe_top_add_one] using hτ.contMDiffOn
  have hcovτ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z) y (cov τ y)) :=
    contMDiffOn_univ.mp
      ((timeFamilyChosen_contMDiffCovariantDerivative g t).contMDiff.contMDiff hτOn)
  have hψeq1 : {y : M | ψ y = 1} ∈ nhds x := by
    filter_upwards [ψ.eventuallyEq_one] with y hy
    simpa using hy
  rcases mem_nhds_iff.mp hψeq1 with ⟨w, hwsub, hwopen, hxw⟩
  have hwu : w ⊆ u := by
    intro y hy
    have hy1 : ψ y = 1 := hwsub hy
    have hysupp : y ∈ Function.support ψ := by
      simpa [Function.support] using show ψ y ≠ 0 by rw [hy1]; norm_num
    exact hψsupp hysupp
  have hEq : ∀ y ∈ w, cov σ y = cov τ y := by
    intro y hy
    have hyu : y ∈ u := hwu hy
    have hσy : MDiffAt (T% σ) y :=
      ((hσSmooth y hyu).contMDiffAt (hu.mem_nhds hyu)).mdifferentiableAt (by simp)
    have hτy : MDiffAt (T% τ) y := hτ.contMDiffAt.mdifferentiableAt (by simp)
    exact (cov.isCovariantDerivativeOn (s := w)).congr_of_eqOn hσy hτy (hwopen.mem_nhds hy)
      (fun z hz ↦ by
        have hz1 : ψ z = 1 := hwsub hz
        simpa [τ, hz1] using (one_smul ℝ (σ z)).symm)
  have hcovσw : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z) y (cov σ y)) w := by
    refine ContMDiffOn.congr hcovτ.contMDiffOn ?_
    intro y hy
    exact congrArg (fun A ↦ TotalSpace.mk'
      (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z) (E →L[ℝ] E) y A) (hEq y hy)
  refine ⟨w, hwopen, hxw, ?_⟩
  simpa [Set.inter_eq_right.mpr hwu] using hcovσw

set_option backward.isDefEq.respectTransparency false in
/-- The actual chosen slice is C¹, derived from its proved spatial-infinity
predicate by smooth local frames and the genuine connection decomposition. -/
theorem timeFamilyChosen_contMDiffCovariantDerivative_one
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) :
    CovariantDerivative.ContMDiffCovariantDerivative (timeFamilyChosen g t) 1 where
  contMDiff := by
    classical
    haveI : ContMDiffVectorBundle (1 + 1) E (TangentSpace I : M → Type _) I := by
      convert (inferInstance : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I)
        using 1 <;> norm_num
    refine { contMDiff := ?_ }
    intro σ hσ
    apply contMDiffOn_of_locally_contMDiffOn
    intro x hx
    let e := trivializationAt E (TangentSpace I : M → Type _) x
    let b := Module.finBasis ℝ E
    have hxbase : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E _ x
    refine ⟨e.baseSet, e.open_baseSet, hxbase, ?_⟩
    have hopen : IsOpen (Set.univ ∩ e.baseSet) := isOpen_univ.inter e.open_baseSet
    have hsub : Set.univ ∩ e.baseSet ⊆ e.baseSet := Set.inter_subset_right
    have hσ2 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (T% σ)
        (Set.univ ∩ e.baseSet) := by
      convert hσ.mono Set.inter_subset_left using 1 <;> norm_num
    have hσ12 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (1 + 1) (T% σ)
        (Set.univ ∩ e.baseSet) := by
      convert hσ2 using 1 <;> norm_num
    have hframe1 := Bundle.Trivialization.contMDiffOn_frameCovariantDerivative_of_level
      (I := I) (V := (TangentSpace I : M → Type _)) (n := 1) e b hopen hsub hσ12
    have hcoeff : ∀ i, ContMDiffOn I 𝓘(ℝ) 2
        ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) (Set.univ ∩ e.baseSet) := fun i =>
      contMDiffOn_localFrameCoeff (I := I) (F := E)
        (V := (TangentSpace I : M → Type _)) (e := e) (b := b)
        (s := σ) (t := Set.univ ∩ e.baseSet) (k := (2 : WithTop ℕ∞)) hopen hsub hσ2 i
    have hframeSmooth : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
        (T% (e.localFrame b i)) e.baseSet := fun i => by
      simpa only [ENat.coe_top_add_one] using
        (e.contMDiffOn_localFrame_baseSet (I := I) (n := (∞ : WithTop ℕ∞)) b i)
    have hcovSmooth := timeFamilyChosen_contMDiffCovariantDerivativeOn_infinity g t e.open_baseSet
    have hcovframe := fun i => hcovSmooth.contMDiff (hframeSmooth i)
    have hdiff1 := ContMDiffOn.sum_section
      (F := E →L[ℝ] E)
      (V := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z)
      (s := (Finset.univ : Finset _))
      (fun i (_ : i ∈ Finset.univ) =>
        ContMDiffOn.smul_section (F := E →L[ℝ] E)
          (V := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z)
          (n := (1 : WithTop ℕ∞))
          ((hcoeff i).of_le (by norm_num))
          (((hcovframe i).mono hsub).of_le (by simp)))
    have htotal := ContMDiffOn.add_section (F := E →L[ℝ] E)
      (V := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z) hframe1 hdiff1
    refine htotal.congr fun y hy => ?_
    have hMDiff : MDiffAt (T% σ) y :=
      ((hσ2 y hy).contMDiffAt (hopen.mem_nhds hy)).mdifferentiableAt (by norm_num)
    congr 1
    refine ContinuousLinearMap.ext fun v => ?_
    have hdec := e.covariantDerivative_apply_eq_sum_localFrame_add_sum_covariantDerivative_localFrame
      (I := I) (F := E) (V := (TangentSpace I : M → Type _))
      b (timeFamilyChosen g t) hy.2 hMDiff v
    simpa [Bundle.Trivialization.frameCovariantDerivative, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smul_apply, Pi.add_apply, Finset.sum_apply] using hdec

end ChartPort
