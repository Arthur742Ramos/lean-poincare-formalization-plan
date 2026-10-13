import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.C2MetricVelocityExtension
import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.DowngradeNormFree
import PoincareCurvature.Geometry.Manifold.RicciFlow.IntrinsicRicciReindex

/-!
# Initial intrinsic Ricci jet from the direct continuous-curvature route

SOURCE CANDIDATE, UNCOMPILED. This file isolates the existing C0 curvature,
finite-frame trace and bilinear-section reconstruction proofs. It imports
neither a DeTurck operator nor a contracted-Bianchi bridge. The constructor
still produces positive spatial-C2 metric slices at every real time and the
actual intrinsic Ricci component derivative only at the initial time.
No interval equation, joint regularity, uniqueness or Point 4 closure follows.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 2000000

open Bundle FiberBundle Set Filter
open scoped Manifold ContDiff Topology

namespace RicciFlow.AnalyticPDE.C0Endpoint

section ThinRicciBackground

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

local instance thinRicciBilENormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thinRicciBilENormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

namespace ThinRicciContinuity

-- Exact existing C0 proof extracted from lines 345-408.
private theorem curvatureAux_contMDiffOn_zero
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {X Y Z : Π x : M, TangentSpace I x} {u : Set M} (hu : IsOpen u)
    (hX : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun x ↦ TotalSpace.mk' E x (X x)) u)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun x ↦ TotalSpace.mk' E x (Y x)) u)
    (hZ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun x ↦ TotalSpace.mk' E x (Z x)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) 0
      (fun x ↦ TotalSpace.mk' E x (cov.curvatureAux X Y Z x)) u := by
  haveI : ContMDiffVectorBundle 0 E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  haveI : IsManifold I ((2 : ℕ∞) + 1) M :=
    IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by exact_mod_cast le_top)
  have hcov1 : ContMDiffCovariantDerivativeOn E 1 cov.toFun u :=
    CovariantDerivative.TangentFrame.contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_one
      hu
  have hcov0 : ContMDiffCovariantDerivativeOn E 0 cov.toFun u :=
    CovariantDerivative.TangentFrame.contMDiffCovariantDerivativeOn_zero_of_contMDiffCovariantDerivative_one
      hu
  have hX1 := hX.of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)
  have hY1 := hY.of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)
  have hX0 := hX.of_le (show (0 : WithTop ℕ∞) ≤ 2 by norm_num)
  have hY0 := hY.of_le (show (0 : WithTop ℕ∞) ≤ 2 by norm_num)
  have hZ1 := hZ.of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)
  have hYZ1 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (fun x ↦ TotalSpace.mk' E x (cov.along Y Z x)) u := by
    simpa [CovariantDerivative.along] using (hcov1.contMDiff hZ).clm_bundle_apply hY1
  have hXZ1 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (fun x ↦ TotalSpace.mk' E x (cov.along X Z x)) u := by
    simpa [CovariantDerivative.along] using (hcov1.contMDiff hZ).clm_bundle_apply hX1
  have hT1 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 0
      (fun x ↦ TotalSpace.mk' E x (cov.along X (cov.along Y Z) x)) u := by
    simpa [CovariantDerivative.along] using (hcov0.contMDiff hYZ1).clm_bundle_apply hX0
  have hT2 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 0
      (fun x ↦ TotalSpace.mk' E x (cov.along Y (cov.along X Z) x)) u := by
    simpa [CovariantDerivative.along] using (hcov0.contMDiff hXZ1).clm_bundle_apply hY0
  have hBrWithin : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 0
      (fun x ↦ TotalSpace.mk' E x (VectorField.mlieBracketWithin I X Y u x)) u := by
    simpa using
      (hX.mlieBracketWithin_vectorField (I := I) (m := (0 : ℕ∞)) hY hu.uniqueMDiffOn
        (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num))
  have hBr : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 0
      (fun x ↦ TotalSpace.mk' E x (VectorField.mlieBracket I X Y x)) u := by
    refine ContMDiffOn.congr hBrWithin ?_
    intro x hx
    have hXx : MDiffAt (T% X) x :=
      (((hX x hx).contMDiffAt (hu.mem_nhds hx)).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).mdifferentiableAt one_ne_zero
    have hYx : MDiffAt (T% Y) x :=
      (((hY x hx).contMDiffAt (hu.mem_nhds hx)).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).mdifferentiableAt one_ne_zero
    congr 1
    simpa using
      (VectorField.mlieBracketWithin_eq_mlieBracket (I := I) (s := u) (x := x)
        (hu.uniqueMDiffWithinAt hx) hXx hYx).symm
  have hT3 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 0
      (fun x ↦ TotalSpace.mk' E x (cov.along (VectorField.mlieBracket I X Y) Z x)) u := by
    simpa [CovariantDerivative.along] using (hcov0.contMDiff hZ1).clm_bundle_apply hBr
  have hcomb := (hT1.sub_section hT2).sub_section hT3
  simpa only [CovariantDerivative.curvatureAux] using hcomb

-- Exact existing C0 proof extracted from lines 417-497.
private theorem curvatureAux_apply_eq_of_eventuallyEq_fields
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

-- Exact existing C0 proof extracted from lines 508-603.
private theorem curvatureAux_apply_eq_curvatureTensor_of_contMDiffOn_frame
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
    curvatureAux_apply_eq_of_eventuallyEq_fields
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

-- Exact existing C0 proof extracted from lines 611-625.
private theorem curvatureTensor_contMDiffOn_frame_zero
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {ea eb ec : Π x : M, TangentSpace I x} {u : Set M} (hu : IsOpen u)
    (hea : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (ea z)) u)
    (heb : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (eb z)) u)
    (hec : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (ec z)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) 0
      (fun z ↦ TotalSpace.mk' E z
        (CovariantDerivative.curvatureTensor (cov := cov) z (ea z) (eb z) (ec z))) u := by
  have hcurv := curvatureAux_contMDiffOn_zero (cov := cov) hu hea heb hec
  refine hcurv.congr ?_
  intro z hz
  exact congrArg (TotalSpace.mk' E z)
    (curvatureAux_apply_eq_curvatureTensor_of_contMDiffOn_frame hu hz hea heb hec).symm

-- Exact existing C0 proof extracted from lines 667-691.
private theorem continuousOn_clm_of_forall_apply_basis
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {t : Set M} {f : M → (E →L[ℝ] G)}
    (h : ∀ i, ContinuousOn (fun x ↦ f x (b i)) t) :
    ContinuousOn f t := by
  classical
  have hrec : ∀ x : M, f x = b.constrL (fun i ↦ f x (b i)) := by
    intro x
    apply ContinuousLinearMap.coe_injective
    refine b.ext (fun i ↦ ?_)
    simp only [ContinuousLinearMap.coe_coe, Module.Basis.constrL_basis]
  set recon : (ι → G) →ₗ[ℝ] (E →L[ℝ] G) :=
    (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] G) ≃ₗ[ℝ] (E →L[ℝ] G)).toLinearMap.comp
      (b.constr ℝ : (ι → G) ≃ₗ[ℝ] (E →ₗ[ℝ] G)).toLinearMap with hreconDef
  have hrecon_apply : ∀ g : ι → G, recon g = b.constrL g := by
    intro g; rfl
  have hcont : Continuous recon := recon.continuous_of_finiteDimensional
  have hg : ContinuousOn (fun x : M ↦ (fun i ↦ f x (b i) : ι → G)) t :=
    continuousOn_pi.mpr h
  have hcomp : ContinuousOn (fun x : M ↦ recon (fun i ↦ f x (b i))) t :=
    hcont.comp_continuousOn hg
  refine hcomp.congr (fun x _ ↦ ?_)
  change f x = recon (fun i ↦ f x (b i))
  rw [hrecon_apply, ← hrec x]

-- Exact existing C0 proof extracted from lines 702-734.
private theorem contMDiff_zero_bilinearFormBundleSection_of_forall_localFrame
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {s : Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x}
    (hcomp : ∀ (x0 : M) (i j : ι),
      ContinuousOn (fun x ↦ s x ((trivializationAt E TM x0).localFrame b i x)
        ((trivializationAt E TM x0).localFrame b j x)) (trivializationAt E TM x0).baseSet) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := _root_.Bundle.BilinearFormBundle (V := TM)) x (s x)) := by
  classical
  intro x0
  rw [Bundle.contMDiffAt_section (IB := I) (F := (E →L[ℝ] E →L[ℝ] ℝ))
    (E := _root_.Bundle.BilinearFormBundle (V := TM)) (s := s) x0]
  set e := trivializationAt E TM x0 with he
  have hx0 : x0 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E TM x0
  have hcontOn : ContinuousOn
      (fun x ↦ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (_root_.Bundle.BilinearFormBundle (V := TM)) x0 ⟨x, s x⟩).2) e.baseSet := by
    refine continuousOn_clm_of_forall_apply_basis (E := E) b (fun i ↦ ?_)
    refine continuousOn_clm_of_forall_apply_basis (E := E) b (fun j ↦ ?_)
    refine (hcomp x0 i j).congr (fun x hx ↦ ?_)
    have hxe : x ∈ e.baseSet := hx
    rw [trivializationAt_bilinearFormBundle_apply_eq (F := E) (W := TM) x0 x hxe (s x) (b i) (b j)]
    have hli : ∀ k, ((e.continuousLinearEquivAt ℝ x hxe).symm (b k)) = e.localFrame b k x := by
      intro k
      rw [e.localFrame_apply_of_mem_baseSet b hxe]
      rfl
    rw [hli i, hli j]
  have hCM : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) 0
      (fun x ↦ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (_root_.Bundle.BilinearFormBundle (V := TM)) x0 ⟨x, s x⟩).2) e.baseSet := by
    rw [contMDiffOn_zero_iff]; exact hcontOn
  exact hCM.contMDiffAt (e.open_baseSet.mem_nhds hx0)

-- Exact existing C0 proof extracted from lines 740-750.
private lemma repr_basisAt_eq_localFrameCoeff
    {ι : Type*} (b : Module.Basis ι ℝ E) (x0 : M)
    {x : M} (hx : x ∈ (trivializationAt E TM x0).baseSet) (V : TM x) (k : ι) :
    ((trivializationAt E TM x0).basisAt b hx).repr V k
      = (trivializationAt E TM x0).localFrameCoeff I b k x V := by
  classical
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  have h := (trivializationAt E TM x0).localFrameCoeff_apply_of_mem_baseSet (I := I) b hx
    (Function.update (0 : Π y : M, TM y) x V) k
  simpa using h.symm

-- Exact existing C0 proof extracted from lines 757-774.
private lemma ricciCurvature_eq_sum_localFrameCoeff
    [_root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [cov.ContMDiffCovariantDerivative 1]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) (x0 : M)
    {x : M} (hx : x ∈ (trivializationAt E TM x0).baseSet) (u w : TM x) :
    CovariantDerivative.ricciCurvature (cov := cov) x u w =
      ∑ k, (trivializationAt E TM x0).localFrameCoeff I b k x
        (CovariantDerivative.curvatureTensor (cov := cov) x
          ((trivializationAt E TM x0).localFrame b k x) u w) := by
  classical
  rw [CovariantDerivative.ricciCurvature_apply,
    LinearMap.trace_eq_matrix_trace ℝ ((trivializationAt E TM x0).basisAt b hx), Matrix.trace]
  refine Finset.sum_congr rfl (fun k _ ↦ ?_)
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply,
    CovariantDerivative.ricciEndomorphism_apply,
    (trivializationAt E TM x0).localFrame_apply_of_mem_baseSet b hx]
  exact repr_basisAt_eq_localFrameCoeff b x0 hx _ k

-- Exact existing C0 proof extracted from lines 779-786.
private noncomputable def ricciBilinearFormSection
    [_root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative 1] :
    Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x :=
  fun x ↦ LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := TangentSpace I x) (F' := ℝ)).toLinearMap.comp
      (CovariantDerivative.ricciCurvature (cov := cov) x))

-- Exact existing C0 proof extracted from lines 788-793.
@[simp] private lemma ricciBilinearFormSection_apply
    [_root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative 1] (x : M) (u v : TM x) :
    ricciBilinearFormSection (I := I) (M := M) cov x u v =
      CovariantDerivative.ricciCurvature (cov := cov) x u v := rfl

-- Exact existing C0 proof extracted from lines 805-843.
private theorem ricciBilinearFormSection_contMDiff_zero
    [_root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative 1]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := _root_.Bundle.BilinearFormBundle (V := TM)) x
        (ricciBilinearFormSection (I := I) (M := M) cov x)) := by
  classical
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  refine contMDiff_zero_bilinearFormBundleSection_of_forall_localFrame b (fun x0 i j ↦ ?_)
  have hbase : IsOpen (trivializationAt E TM x0).baseSet := (trivializationAt E TM x0).open_baseSet
  have hframe : ∀ m : ι, ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
      (fun x ↦ TotalSpace.mk' E x ((trivializationAt E TM x0).localFrame b m x))
      (trivializationAt E TM x0).baseSet :=
    fun m ↦ (trivializationAt E TM x0).contMDiffOn_localFrame_baseSet (I := I) (n := 2) b m
  have hsum : Set.EqOn
      (fun x ↦ ricciBilinearFormSection (I := I) (M := M) cov x
        ((trivializationAt E TM x0).localFrame b i x) ((trivializationAt E TM x0).localFrame b j x))
      (fun x ↦ ∑ k, (trivializationAt E TM x0).localFrameCoeff I b k x
        (CovariantDerivative.curvatureTensor (cov := cov) x
          ((trivializationAt E TM x0).localFrame b k x)
          ((trivializationAt E TM x0).localFrame b i x)
          ((trivializationAt E TM x0).localFrame b j x)))
      (trivializationAt E TM x0).baseSet := by
    intro x hx
    dsimp only
    rw [ricciBilinearFormSection_apply]
    exact ricciCurvature_eq_sum_localFrameCoeff b x0 hx
      ((trivializationAt E TM x0).localFrame b i x) ((trivializationAt E TM x0).localFrame b j x)
  refine ContinuousOn.congr ?_ hsum
  refine continuousOn_finset_sum Finset.univ (fun k _ ↦ ?_)
  have hcurv := curvatureTensor_contMDiffOn_frame_zero (cov := cov) hbase
    (hframe k) (hframe i) (hframe j)
  have hcoeff := contMDiffOn_localFrameCoeff (I := I) (e := trivializationAt E TM x0) (b := b)
    (k := (0 : WithTop ℕ∞)) hbase (subset_refl _) hcurv k
  exact hcoeff.continuousOn

-- Exact existing C0 proof extracted from lines 1258-1280.
private theorem exists_intrinsicRicciFlowRHSSection_contMDiff_zero
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) :
    ∃ rhs : Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x,
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := _root_.Bundle.BilinearFormBundle (V := TM)) x (rhs x)) ∧
      ∀ (x : M) (u v : TM x),
        rhs x u v = intrinsicRicciFlowRHS (I := I) (M := M) g t x u v := by
  letI : _root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g t).toRiemannianMetric⟩
  haveI hcov :=
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g t
  refine ⟨_, (ricciBilinearFormSection_contMDiff_zero (I := I) (M := M)
      (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
        (I := I) (M := M) g t) (Module.finBasis ℝ E)).const_smul_section (a := (-2 : ℝ)), ?_⟩
  intro x u v
  have hval : ricciBilinearFormSection (I := I) (M := M)
      (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
        (I := I) (M := M) g t) x u v = intrinsicRicciTensor (I := I) (M := M) g t x u v := by
    rw [ricciBilinearFormSection_apply]; rfl
  simp only [Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hval,
    intrinsicRicciFlowRHS_apply, ricciFlowRHS_apply, intrinsicRicciTensor_apply]

end ThinRicciContinuity

end ThinRicciBackground

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [SigmaCompactSpace M] [BoundarylessManifold I M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The original initial Ricci equation, using only the direct C0 curvature
trace route. No continuity, velocity or chosen connection is supplied. -/
theorem exists_c2_metricFamily_with_intrinsicRicci_endpoint_derivative_thin
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM) (t₀ : ℝ) :
    ∃ g : RicciFlow.MetricFamily (I := I) (M := M),
      g t₀ = g₀ ∧ ∀ x : M, ∀ u w : TM x,
        HasDerivAt (fun t => RicciFlow.metricTensor g t x u w)
          ((-2 : ℝ) * RicciFlow.intrinsicRicciTensor g t₀ x u w) t₀ := by
  letI : RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩
  haveI : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact IsManifold.of_le (n := (∞ : WithTop ℕ∞))
      (show (3 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)
  haveI : IsManifold I ((2 : ℕ∞) + 1) M :=
    IsManifold.of_le (n := (∞ : WithTop ℕ∞))
      (by exact_mod_cast (show (2 : ℕ∞) + 1 ≤ ⊤ from le_top))
  let gConst : RicciFlow.MetricFamily (I := I) (M := M) := fun _ => g₀
  obtain ⟨rhs, hrhsContinuous, hrhsEq⟩ :=
    ThinRicciContinuity.exists_intrinsicRicciFlowRHSSection_contMDiff_zero
      (I := I) (M := M) gConst t₀
  let velocity : ContinuousSymmetricVelocity (I := I) (M := M) := {
    tensor := rhs
    continuous := hrhsContinuous.continuous
    symmetric := by
      intro x u w
      rw [hrhsEq x u w, hrhsEq x w u]
      exact RicciFlow.intrinsicRicciFlowRHS_symm (I := I) (M := M) gConst t₀ x u w }
  obtain ⟨g, hInitial, hDerivative⟩ :=
    exists_c2_metricFamily_with_c0_endpoint_velocity (I := I) (M := M) g₀ t₀ velocity
  refine ⟨g, hInitial, ?_⟩
  intro x u w
  have hRicci : RicciFlow.intrinsicRicciTensor gConst t₀ x u w =
      RicciFlow.intrinsicRicciTensor g t₀ x u w := by
    simpa only [gConst, hInitial] using
      RicciFlow.intrinsicRicciTensor_reindex (I := I) (M := M) g (fun _ => t₀) t₀ x u w
  have hVelocity : velocity.tensor x u w =
      (-2 : ℝ) * RicciFlow.intrinsicRicciTensor g t₀ x u w := by
    change rhs x u w = _
    rw [hrhsEq x u w]
    change (-2 : ℝ) * RicciFlow.intrinsicRicciTensor gConst t₀ x u w = _
    rw [hRicci]
  simpa only [hVelocity] using hDerivative x u w

end RicciFlow.AnalyticPDE.C0Endpoint
