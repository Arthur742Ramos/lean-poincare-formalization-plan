module

public import PoincareCurvature.Analysis.LocalExtremaSecondDerivative
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ScalarLaplacian
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianChart
public import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

/-!
# Scalar Laplacians at local extrema

This file begins the intrinsic maximum-principle bridge.  In particular, a
local minimum on a boundaryless manifold is proved to be a critical point;
this is not included as an assumption in later geometric arguments.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 1500000

open Bundle FiberBundle Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

namespace CovariantDerivative

set_option backward.isDefEq.respectTransparency false

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)

/-- Chain rule along a curve whose manifold derivative is the prescribed
velocity.  The explicit tangent-space conversion is necessary because the
real line is represented as a manifold codomain by `TangentSpace 𝓘(ℝ)` before
being read back as an ordinary real number. -/
theorem deriv_comp_of_hasMFDerivAt_velocity
    {f : M → ℝ} {X : ∀ y : M, TM y} {γ : ℝ → M} {t : ℝ}
    (hf : MDiffAt f (γ t))
    (hγ : HasMFDerivAt 𝓘(ℝ) I γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t)))) :
    deriv (f ∘ γ) t =
      scalarDifferential (I := I) f (γ t) (X (γ t)) := by
  have hcomp : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) (f ∘ γ) t
      ((mfderiv I 𝓘(ℝ) f (γ t)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t)))) :=
    HasMFDerivAt.comp t hf.hasMFDerivAt hγ
  have hfrechet := hcomp.hasFDerivAt
  have hd := hfrechet.hasDerivAt
  have hc := congrArg
    (fun q : TangentSpace 𝓘(ℝ) (f (γ t)) =>
      NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := ℝ) (f (γ t)) q) hd.deriv
  change
    NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := ℝ)
        (f (γ t)) (deriv (f ∘ γ) t) =
      NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := ℝ) (f (γ t))
        (mfderiv I 𝓘(ℝ) f (γ t) (X (γ t)))
  rw [hc]
  congr 1
  change
    mfderiv I 𝓘(ℝ) f (γ t)
        (((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t))) 1) =
      mfderiv I 𝓘(ℝ) f (γ t) (X (γ t))
  congr 1
  norm_num

/-- A scalar function has zero intrinsic differential at a local minimum on
a boundaryless manifold. -/
theorem scalarDifferential_eq_zero_of_isLocalMin
    {f : M → ℝ} {x : M} (hmin : IsLocalMin f x) (hf : MDiffAt f x) :
    scalarDifferential (I := I) f x = 0 := by
  let φ := extChartAt I x
  let z := φ x
  have hxSource : x ∈ φ.source := by
    simpa [φ] using mem_extChartAt_source x
  have hzTarget : z ∈ φ.target := φ.map_source hxSource
  have hsymm : φ.symm z = x := φ.left_inv hxSource
  have hsymmCont : ContinuousAt φ.symm z := by
    simpa [φ, z] using continuousAt_extChartAt_symm (I := I) x
  have hchartMin :
      IsLocalMin (writtenInExtChartAt I 𝓘(ℝ) x f) z := by
    have hbase : IsLocalMin f (φ.symm z) := by simpa [hsymm] using hmin
    have hcomp := hbase.comp_continuous hsymmCont
    simpa [writtenInExtChartAt, φ, z, Function.comp_def,
      chartAt_self_eq] using hcomp
  have hchartCritical :
      fderiv ℝ (writtenInExtChartAt I 𝓘(ℝ) x f) z = 0 :=
    hchartMin.fderiv_eq_zero
  ext u
  let X : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x u
  calc
    scalarDifferential (I := I) f x u = mvfderiv (I := I) f x (X x) := by
      rw [scalarDifferential_apply, show X x = u by simp [X, smoothExtend_apply]]
    _ = fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ) x f) (Set.range I) z
          (VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm X
            (Set.range I) z) := by
      simpa [φ, z] using mvfderiv_apply_eq_fderivWithin_fixedChart
        (I := I) (g := f) (X := X) (p := x) (y := x) hxSource hf
    _ = 0 := by
      rw [I.range_eq_univ, fderivWithin_univ, hchartCritical]
      exact ContinuousLinearMap.zero_apply _

/-- Every diagonal value of the intrinsic scalar Hessian is nonnegative at a
local minimum.  The proof realizes the tangent vector by the local integral
curve of its canonical smooth extension and differentiates the scalar along
that actual manifold curve twice. -/
theorem scalarHessian_self_nonneg_of_isLocalMin
    (cov : CovariantDerivative I E TM) {f : M → ℝ} {x : M}
    (hmin : IsLocalMin f x)
    (hfNear : ∀ᶠ y in 𝓝 x, MDiffAt f y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (u : TM x) :
    0 ≤ scalarHessian cov f x u u := by
  let X : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x u
  have hXone : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% X) := by
    simpa [X] using
      smoothExtend_contMDiff_one (I := I) (F := E) (V := TM) x u
  obtain ⟨γ, hγzero, hγ⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
      (I := I) (v := X) (t₀ := 0) (x₀ := x) hXone.contMDiffAt
  have hlineMin : IsLocalMin (f ∘ γ) 0 := by
    have hbase : IsLocalMin f (γ 0) := by simpa only [hγzero] using hmin
    exact hbase.comp_continuous hγ.continuousAt
  have hfx : MDiffAt f x := hfNear.self_of_nhds
  have hlineCont : ContinuousAt (f ∘ γ) 0 := by
    have hfxzero : MDiffAt f (γ 0) := by simpa only [hγzero] using hfx
    exact hfxzero.continuousAt.comp hγ.continuousAt
  have hsecond : 0 ≤ deriv (deriv (f ∘ γ)) 0 :=
    hlineMin.deriv_deriv_nonneg hlineCont
  let g : M → ℝ := fun y =>
    scalarDifferential (I := I) f y (X y)
  have hγtend : Tendsto γ (𝓝 0) (𝓝 x) := by
    rw [← hγzero]
    exact hγ.continuousAt
  have hfCurve : ∀ᶠ s in 𝓝 0, MDiffAt f (γ s) :=
    hγtend.eventually hfNear
  have hfirstEq : deriv (f ∘ γ) =ᶠ[𝓝 0] g ∘ γ := by
    filter_upwards [hγ, hfCurve] with s hγs hfs
    simpa [g] using
      deriv_comp_of_hasMFDerivAt_velocity (I := I) hfs hγs
  have hXmd : MDiffAt (T% X) x :=
    (hXone x).mdifferentiableAt one_ne_zero
  have hgTotal := hdf.clm_bundle_apply hXmd
  have hg : MDiffAt g x := by
    have ht :=
      ((trivializationAt ℝ (Bundle.Trivial M ℝ) x).mdifferentiableAt_section_iff
        I g (FiberBundle.mem_baseSet_trivializationAt' x)).mp hgTotal
    simpa [Bundle.Trivial.eq_trivialization M ℝ] using ht
  have hcritical : scalarDifferential (I := I) f x = 0 :=
    scalarDifferential_eq_zero_of_isLocalMin hmin hfx
  have hsecondEq :
      deriv (deriv (f ∘ γ)) 0 = deriv (g ∘ γ) 0 :=
    Filter.EventuallyEq.deriv_eq hfirstEq
  have hgCurve : deriv (g ∘ γ) 0 = mvfderiv (I := I) g x u := by
    have hgzero : MDiffAt g (γ 0) := by simpa only [hγzero] using hg
    have h :=
      deriv_comp_of_hasMFDerivAt_velocity (I := I) hgzero hγ.hasMFDerivAt
    rw [hγzero] at h
    simpa [g, X, smoothExtend_apply] using h
  rw [scalarHessian_apply_of_mdifferentiableAt_of_differential_eq_zero
    cov f hdf hcritical u u]
  change 0 ≤ mvfderiv (I := I) g x u
  rw [← hgCurve, ← hsecondEq]
  exact hsecond

/-- The intrinsic scalar Laplacian is nonnegative at a local minimum. -/
theorem scalarLaplacian_nonneg_of_isLocalMin
    (cov : CovariantDerivative I E TM) {f : M → ℝ} {x : M}
    (hmin : IsLocalMin f x)
    (hfNear : ∀ᶠ y in 𝓝 x, MDiffAt f y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x) :
    0 ≤ scalarLaplacian cov f x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  rw [scalarLaplacian_eq_sum_orthonormalBasis cov f x
    (stdOrthonormalBasis ℝ (TM x))]
  exact Finset.sum_nonneg fun i _ =>
    scalarHessian_self_nonneg_of_isLocalMin cov hmin hfNear hdf
      ((stdOrthonormalBasis ℝ (TM x)) i)

end CovariantDerivative
