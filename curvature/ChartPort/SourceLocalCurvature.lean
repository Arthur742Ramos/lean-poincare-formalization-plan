import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Along
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

/-!
Exact local proofs from Arthur742Ramos/lean-poincare-formalization-plan,
commit 5185c1abd500e997414401af3fe6a533dd3a3b47,
curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/DeTurckCorrectionRegularity.lean.
Original names are RicciFlow.curvatureAux_apply_eq_of_eventuallyEq_fields and
RicciFlow.curvatureAux_apply_eq_curvatureTensor_of_contMDiffOn_frame.
The separate namespace avoids collisions if the original module is imported later.
Exact originals, attribution, ambient context and source/proof receipts accompany this port.
-/

noncomputable section
open Bundle
open scoped Manifold ContDiff Topology
namespace ChartPort.SourceLocalCurvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]


theorem curvatureAux_apply_eq_of_eventuallyEq_fields
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {ea eb ec X Y σ : Π x : M, TangentSpace I x} {y : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun z ↦ TotalSpace.mk' E z (X z)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun z ↦ TotalSpace.mk' E z (Y z)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (σ z)))
    (hea : ea =ᶠ[nhds y] X) (heb : eb =ᶠ[nhds y] Y) (hec : ec =ᶠ[nhds y] σ) :
    cov.curvatureAux ea eb ec y = cov.curvatureAux X Y σ y := by
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  have hcov_congr : ∀ {s t : Π x : M, TangentSpace I x} {z : M},
      MDiffAt (T% s) z → MDiffAt (T% t) z → s =ᶠ[nhds z] t → cov s z = cov t z := by
    intro s t z hs ht hst
    exact IsCovariantDerivativeOn.congr_of_eventuallyEq
      (hcov := cov.isCovariantDerivativeOnUniv) hs ht Filter.univ_mem hst
  have hσ2' : ContMDiff I (I.prod 𝓘(ℝ, E)) (1 + 1)
      (fun z ↦ TotalSpace.mk' E z (σ z)) := hσ.of_le (by norm_num)
  have hAlongYσ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun z ↦ TotalSpace.mk' E z (cov.along Y σ z)) := cov.contMDiff_along hY hσ2'
  have hAlongXσ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun z ↦ TotalSpace.mk' E z (cov.along X σ z)) := cov.contMDiff_along hX hσ2'
  have hEbEc : ∀ᶠ z in nhds y, cov.along eb ec z = cov.along Y σ z := by
    have hec_ev : ∀ᶠ z in nhds y, ec =ᶠ[nhds z] σ := eventually_eventually_nhds.2 hec
    filter_upwards [heb, hec_ev] with z hzeb hzec_ev
    have hσz : MDiffAt (T% σ) z := (hσ z).mdifferentiableAt (by norm_num)
    have htec_ev : (fun w ↦ TotalSpace.mk' E w (ec w)) =ᶠ[nhds z]
        (fun w ↦ TotalSpace.mk' E w (σ w)) := by
      filter_upwards [hzec_ev] with w hw; simp [hw]
    have hecz : MDiffAt (T% ec) z := hσz.congr_of_eventuallyEq htec_ev
    have hcovz : cov ec z = cov σ z := hcov_congr hecz hσz hzec_ev
    simp only [CovariantDerivative.along_apply, hzeb, hcovz]
  have hEaEc : ∀ᶠ z in nhds y, cov.along ea ec z = cov.along X σ z := by
    have hec_ev : ∀ᶠ z in nhds y, ec =ᶠ[nhds z] σ := eventually_eventually_nhds.2 hec
    filter_upwards [hea, hec_ev] with z hzea hzec_ev
    have hσz : MDiffAt (T% σ) z := (hσ z).mdifferentiableAt (by norm_num)
    have htec_ev : (fun w ↦ TotalSpace.mk' E w (ec w)) =ᶠ[nhds z]
        (fun w ↦ TotalSpace.mk' E w (σ w)) := by
      filter_upwards [hzec_ev] with w hw; simp [hw]
    have hecz : MDiffAt (T% ec) z := hσz.congr_of_eventuallyEq htec_ev
    have hcovz : cov ec z = cov σ z := hcov_congr hecz hσz hzec_ev
    simp only [CovariantDerivative.along_apply, hzea, hcovz]
  have hAlongYσ_y : MDiffAt (T% (cov.along Y σ)) y :=
    (hAlongYσ y).mdifferentiableAt one_ne_zero
  have hAlongXσ_y : MDiffAt (T% (cov.along X σ)) y :=
    (hAlongXσ y).mdifferentiableAt one_ne_zero
  have htEbEc_ev : (fun z ↦ TotalSpace.mk' E z (cov.along eb ec z)) =ᶠ[nhds y]
      (fun z ↦ TotalSpace.mk' E z (cov.along Y σ z)) := by
    filter_upwards [hEbEc] with z hz; exact congrArg (TotalSpace.mk' E z) hz
  have htEaEc_ev : (fun z ↦ TotalSpace.mk' E z (cov.along ea ec z)) =ᶠ[nhds y]
      (fun z ↦ TotalSpace.mk' E z (cov.along X σ z)) := by
    filter_upwards [hEaEc] with z hz; exact congrArg (TotalSpace.mk' E z) hz
  have hAlongEbEc_y : MDiffAt (T% (cov.along eb ec)) y :=
    hAlongYσ_y.congr_of_eventuallyEq htEbEc_ev
  have hAlongEaEc_y : MDiffAt (T% (cov.along ea ec)) y :=
    hAlongXσ_y.congr_of_eventuallyEq htEaEc_ev
  have hTermA : cov.along ea (cov.along eb ec) y = cov.along X (cov.along Y σ) y := by
    have hcov1 : cov (cov.along eb ec) y = cov (cov.along Y σ) y :=
      hcov_congr hAlongEbEc_y hAlongYσ_y hEbEc
    have heay : ea y = X y := hea.eq_of_nhds
    simp only [CovariantDerivative.along_apply, heay, hcov1]
  have hTermB : cov.along eb (cov.along ea ec) y = cov.along Y (cov.along X σ) y := by
    have hcov1 : cov (cov.along ea ec) y = cov (cov.along X σ) y :=
      hcov_congr hAlongEaEc_y hAlongXσ_y hEaEc
    have heby : eb y = Y y := heb.eq_of_nhds
    simp only [CovariantDerivative.along_apply, heby, hcov1]
  have hbr : VectorField.mlieBracket I ea eb =ᶠ[nhds y] VectorField.mlieBracket I X Y :=
    hea.mlieBracket_vectorField heb
  have hTermC : cov.along (VectorField.mlieBracket I ea eb) ec y
      = cov.along (VectorField.mlieBracket I X Y) σ y := by
    have hσy : MDiffAt (T% σ) y := (hσ y).mdifferentiableAt (by norm_num)
    have htec_ev : (fun w ↦ TotalSpace.mk' E w (ec w)) =ᶠ[nhds y]
        (fun w ↦ TotalSpace.mk' E w (σ w)) := by
      filter_upwards [hec] with w hw; simp [hw]
    have hecy : MDiffAt (T% ec) y := hσy.congr_of_eventuallyEq htec_ev
    have hcov1 : cov ec y = cov σ y := hcov_congr hecy hσy hec
    have hbry : VectorField.mlieBracket I ea eb y = VectorField.mlieBracket I X Y y :=
      hbr.eq_of_nhds
    simp only [CovariantDerivative.along_apply, hbry, hcov1]
  rw [CovariantDerivative.curvatureAux_apply, CovariantDerivative.curvatureAux_apply,
    hTermA, hTermB, hTermC]

theorem curvatureAux_apply_eq_curvatureTensor_of_contMDiffOn_frame
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {ea eb ec : Π x : M, TangentSpace I x} {u : Set M} (hu : IsOpen u) {y : M} (hy : y ∈ u)
    (hea : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (ea z)) u)
    (heb : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (eb z)) u)
    (hec : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (ec z)) u) :
    cov.curvatureAux ea eb ec y =
      CovariantDerivative.curvatureTensor (cov := cov) y (ea y) (eb y) (ec y) := by
  classical
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  set e := trivializationAt E (TangentSpace I : M → Type _) y with he
  set u' : Set M := u ∩ e.baseSet with hu'def
  have hu'open : IsOpen u' := hu.inter e.open_baseSet
  have hyu' : y ∈ u' := ⟨hy, mem_baseSet_trivializationAt E _ y⟩
  have hu'subu : u' ⊆ u := Set.inter_subset_left
  have hu'sube : u' ⊆ e.baseSet := Set.inter_subset_right
  have hu'nhds : u' ∈ nhds y := hu'open.mem_nhds hyu'
  obtain ⟨ψ, hψtsupp, hψsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) (c := y) hu'nhds).mem_iff.mp hu'nhds
  have hψ : ContMDiff I 𝓘(ℝ) 2 (ψ : M → ℝ) :=
    ψ.contMDiff.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by decide)
  set X : Π z : M, TangentSpace I z := fun z ↦ ψ z • ea z with hXdef
  set Y : Π z : M, TangentSpace I z := fun z ↦ ψ z • eb z with hYdef
  set σ : Π z : M, TangentSpace I z := fun z ↦ ψ z • ec z with hσdef
  have hXglob : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (X z)) := by
    simpa [hXdef] using
      (ContMDiffOn.smul_section_of_tsupport (I := I) (F := E)
        (V := (TangentSpace I : M → Type _)) (u := u') (n := (2 : WithTop ℕ∞)) (ψ := ψ)
        hψ.contMDiffOn hu'open hψtsupp (hea.mono hu'subu))
  have hYglob : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (Y z)) := by
    simpa [hYdef] using
      (ContMDiffOn.smul_section_of_tsupport (I := I) (F := E)
        (V := (TangentSpace I : M → Type _)) (u := u') (n := (2 : WithTop ℕ∞)) (ψ := ψ)
        hψ.contMDiffOn hu'open hψtsupp (heb.mono hu'subu))
  have hσglob : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (σ z)) := by
    simpa [hσdef] using
      (ContMDiffOn.smul_section_of_tsupport (I := I) (F := E)
        (V := (TangentSpace I : M → Type _)) (u := u') (n := (2 : WithTop ℕ∞)) (ψ := ψ)
        hψ.contMDiffOn hu'open hψtsupp (hec.mono hu'subu))
  have hψ1 : {z : M | ψ z = 1} ∈ nhds y := by
    filter_upwards [ψ.eventuallyEq_one] with z hz; simpa using hz
  have hψy1 : (ψ : M → ℝ) y = 1 := by simpa using ψ.eventuallyEq_one.eq_of_nhds
  have hXea : X =ᶠ[nhds y] ea := by
    filter_upwards [hψ1] with z hz
    have : ψ z = 1 := hz
    simp [hXdef, this] <;> rfl
  have hYeb : Y =ᶠ[nhds y] eb := by
    filter_upwards [hψ1] with z hz
    have : ψ z = 1 := hz
    simp [hYdef, this] <;> rfl
  have hσec : σ =ᶠ[nhds y] ec := by
    filter_upwards [hψ1] with z hz
    have : ψ z = 1 := hz
    simp [hσdef, this] <;> rfl
  have hgerm : cov.curvatureAux ea eb ec y = cov.curvatureAux X Y σ y :=
    ChartPort.SourceLocalCurvature.curvatureAux_apply_eq_of_eventuallyEq_fields
      (hXglob.of_le (by norm_num)) (hYglob.of_le (by norm_num)) hσglob
      hXea.symm hYeb.symm hσec.symm
  let b := Module.finBasis ℝ E
  have hσcoeff : ∀ i, ContMDiff I 𝓘(ℝ) 2
      (fun z ↦ e.localFrameCoeff I b i z (σ z)) := by
    intro i
    have hbase : ContMDiffOn I 𝓘(ℝ) 2
        (fun z ↦ e.localFrameCoeff I b i z (σ z)) u' :=
      contMDiffOn_localFrameCoeff (I := I) (e := e) (b := b) (t := u')
        (k := (2 : WithTop ℕ∞)) hu'open hu'sube hσglob.contMDiffOn i
    have hcompl : ContMDiffOn I 𝓘(ℝ) 2
        (fun z ↦ e.localFrameCoeff I b i z (σ z)) (tsupport ψ)ᶜ := by
      have hzero : ContMDiffOn I 𝓘(ℝ) 2 (fun _ : M ↦ (0 : ℝ)) (tsupport ψ)ᶜ :=
        contMDiff_const.contMDiffOn
      refine hzero.congr ?_
      intro z hz
      have hψz : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [hσdef, hψz]
    have hcover : u' ∪ (tsupport ψ)ᶜ = Set.univ := by
      refine Set.eq_univ_iff_forall.mpr fun z ↦ ?_
      by_cases hz : z ∈ tsupport ψ
      · exact Or.inl (hψtsupp hz)
      · exact Or.inr hz
    exact contMDiff_of_contMDiffOn_union_of_isOpen hbase hcompl hcover hu'open
      (isOpen_compl_iff.mpr (isClosed_tsupport ψ))
  have hXy : X y = ea y := by simp [hXdef, hψy1]
  have hYy : Y y = eb y := by simp [hYdef, hψy1]
  have hσy : σ y = ec y := by simp [hσdef, hψy1]
  have hcoeff_eq : ∀ i,
      e.localFrameCoeff I b i y (σ y) = e.localFrameCoeff I b i y (ec y) := by
    intro i; rw [hσy]
  have htens : cov.curvatureAux X Y σ y =
      CovariantDerivative.curvatureTensor (cov := cov) y (ea y) (eb y) (ec y) :=
    cov.curvatureAux_eq_curvatureTensor_apply_of_eq_left_middle_localFrameCoeff_right
      (b := b) (X := X) (Y := Y) (σ := σ) (x := y)
      (hXglob.of_le (by norm_num)) (hYglob.of_le (by norm_num)) hσglob
      hXy hYy hσcoeff hcoeff_eq
  rw [hgerm, htens]

end ChartPort.SourceLocalCurvature
