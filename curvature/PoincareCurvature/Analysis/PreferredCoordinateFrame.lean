/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import PoincareCurvature.Analysis.BoundarylessChartTransport
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Tactic.Convert

/-!
# Actual preferred coordinate frames on an open chart patch

The frame is the local frame of the preferred tangent trivialization, hence
comes from the actual differential of one fixed chart. The derivative transport
and frame commutation below are proved from chart inverse and pullback APIs.
The boundaryless assumption supplies an open coordinate domain and ordinary
Fréchet derivatives. No commuting-frame certificate is supplied as a premise.
-/

noncomputable section

open Bundle FiberBundle Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareCurvature.PreferredCoordinateFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [BoundarylessManifold I M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The preferred tangent trivialization belonging to the one fixed chart. -/
abbrev trivialization (p : M) : Trivialization E (π E TM) := trivializationAt E TM p

/-- The actual frame obtained from a basis and the fixed preferred chart. -/
abbrev frame {ι : Type*} (p : M) (b : Module.Basis ι ℝ E) (i : ι) : ∀ x : M, TM x :=
  (trivialization (I := I) p).localFrame b i

/-- Scalar coordinate readout in the same fixed chart. -/
def scalarReadout (p : M) (f : M → ℝ) : E → ℝ := f ∘ (extChartAt I p).symm

variable {ι : Type*} (p : M) (b : Module.Basis ι ℝ E)

/-- The actual frame vector is the inverse-chart differential of its basis vector. -/
theorem frame_eq_inverseChart_derivative {x : M}
    (hx : x ∈ (extChartAt I p).source) (i : ι) :
    frame (I := I) p b i x =
      mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I)
        (extChartAt I p x) ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (extChartAt I p x)).symm (b i)) := by
  have hbase : x ∈ (trivialization (I := I) p).baseSet := by
    simpa only [trivialization, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hx
  rw [frame, Bundle.Trivialization.localFrame_apply_of_mem_baseSet _ b hbase]
  change ((trivialization (I := I) p).linearEquivAt ℝ x hbase).symm (b i) = _
  rw [Bundle.Trivialization.linearEquivAt_symm_apply (R := ℝ)]
  rw [← Bundle.Trivialization.symmL_apply (R := ℝ) _ hbase]
  rw [TangentBundle.symmL_trivializationAt (by simpa only [extChartAt_source] using hx)]
  rfl

/-- The actual preferred frame has constant coordinates throughout the fixed chart target. -/
theorem mpullback_frame_eq_const {z : E} (hz : z ∈ (extChartAt I p).target) (i : ι) :
    VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm
      (frame (I := I) p b i) z =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm (b i) := by
  have hx := (extChartAt I p).map_target hz
  have hframe := frame_eq_inverseChart_derivative (I := I) p b hx i
  rw [(extChartAt I p).right_inv hz] at hframe
  simp only [VectorField.mpullback, VectorField.mpullbackWithin_apply,
    mfderivWithin_univ]
  rw [hframe]
  have hInv := isInvertible_mfderivWithin_extChartAt_symm (I := I) hz
  rw [BoundarylessChartTransport.mfderivWithin_extChartAt_symm_eq_mfderiv (I := I) p hz] at hInv ⊢
  exact ContinuousLinearMap.IsInvertible.inverse_apply_self hInv _

/-- A scalar manifold derivative along the actual coordinate frame is the
ordinary Fréchet derivative of its fixed-chart readout. -/
theorem mvfderiv_frame_eq_fderiv {f : M → ℝ} {x : M}
    (hx : x ∈ (extChartAt I p).source) (hf : MDiffAt f x) (i : ι) :
    mvfderiv (I := I) f x (frame (I := I) p b i x) =
      fderiv ℝ (scalarReadout (I := I) p f) (extChartAt I p x) (b i) := by
  have hz : extChartAt I p x ∈ (extChartAt I p).target := (extChartAt I p).map_source hx
  have hchain := mfderiv_comp_mfderivWithin_of_eq
    (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ)) hf
    (mdifferentiableWithinAt_extChartAt_symm hz)
    (I.uniqueDiffOn.uniqueDiffWithinAt
      (extChartAt_target_subset_range p hz)).uniqueMDiffWithinAt
    ((extChartAt I p).left_inv hx)
  have hrange : range I ∈ 𝓝 (extChartAt I p x) :=
    mem_interior_iff_mem_nhds.1
      (BoundarylessChartTransport.extChartAt_target_subset_interior_range (I := I) p hz)
  rw [mfderivWithin_of_mem_nhds hrange, mfderivWithin_of_mem_nhds hrange,
    mfderiv_eq_fderiv] at hchain
  simp only [mfderivWithin_univ, Function.comp_apply, (extChartAt I p).left_inv hx] at hchain
  rw [frame_eq_inverseChart_derivative (I := I) p b hx i]
  unfold mvfderiv scalarReadout
  rw [BoundarylessChartTransport.mfderivWithin_extChartAt_symm_eq_mfderiv (I := I) p hz]
  have h := congrArg
    (fun L => (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x))
      (L ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (extChartAt I p x)).symm (b i)))) hchain
  convert h.symm using 1 <;> rfl

/-- The actual preferred coordinate frame commutes on the whole fixed chart patch. -/
theorem mlieBracket_frame_eq_zero {x : M}
    (hx : x ∈ (extChartAt I p).source) (i j : ι) :
    VectorField.mlieBracket I (frame (I := I) p b i) (frame (I := I) p b j) x = 0 := by
  let z : E := extChartAt I p x
  have hz : z ∈ (extChartAt I p).target := (extChartAt I p).map_source hx
  have hbase : x ∈ (trivialization (I := I) p).baseSet := by
    simpa only [trivialization, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hx
  have hmd (k : ι) : MDiffAt (T% (frame (I := I) p b k)) x := by
    exact (((trivialization (I := I) p).contMDiffOn_localFrame_baseSet
      (I := I) (n := 2) b k) x hbase).contMDiffAt
      ((trivialization (I := I) p).open_baseSet.mem_nhds hbase) |>.mdifferentiableAt (by norm_num)
  have hinv : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I p).symm z :=
    (contMDiffWithinAt_extChartAt_symm_target p hz).contMDiffAt
      ((BoundarylessChartTransport.isOpen_extChartAt_target (I := I) p).mem_nhds hz)
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    have hsmooth : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
      simpa [minSmoothness] using
        (show (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by decide)
    exact IsManifold.of_le (I := I) (n := (∞ : WithTop ℕ∞)) hsmooth
  have hbr := VectorField.mpullback_mlieBracket
    (I := 𝓘(ℝ, E)) (I' := I)
    (by simpa only [z, (extChartAt I p).left_inv hx] using hmd i)
    (by simpa only [z, (extChartAt I p).left_inv hx] using hmd j) hinv (by norm_num)
  have hconst (k : ι) :
      VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm (frame (I := I) p b k)
        =ᶠ[𝓝 z] (fun y => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (b k)) := by
    filter_upwards [(BoundarylessChartTransport.isOpen_extChartAt_target (I := I) p).mem_nhds hz] with y hy
    exact mpullback_frame_eq_const (I := I) p b hy k
  have hzero : VectorField.mlieBracket 𝓘(ℝ, E)
      (VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm (frame (I := I) p b i))
      (VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm (frame (I := I) p b j)) z = 0 := by
    rw [Filter.EventuallyEq.mlieBracket_vectorField_eq (hconst i) (hconst j)]
    rw [← VectorField.mlieBracketWithin_univ,
      VectorField.mlieBracketWithin_eq_lieBracketWithin]
    change VectorField.lieBracketWithin ℝ (fun _ : E => b i) (fun _ : E => b j) univ z = 0
    simp [VectorField.lieBracketWithin]
  rw [hzero] at hbr
  have hInv := isInvertible_mfderivWithin_extChartAt_symm (I := I) hz
  rw [BoundarylessChartTransport.mfderivWithin_extChartAt_symm_eq_mfderiv (I := I) p hz] at hInv
  have h := (ContinuousLinearMap.IsInvertible.inverse_apply_eq hInv).1 hbr
  simp only [map_zero] at h
  change VectorField.mlieBracket I (frame (I := I) p b i)
    (frame (I := I) p b j) ((extChartAt I p).symm z) = 0 at h
  have hpoint : (extChartAt I p).symm z = x := (extChartAt I p).left_inv hx
  rw [hpoint] at h
  exact h

variable {d : ℕ}

/-- A finite basis supplies genuine continuous model coordinates, without a rank restriction. -/
def toModel (b : Module.Basis (Fin d) ℝ E) : (Fin d → ℝ) ≃L[ℝ] E :=
  b.equivFun.symm.toContinuousLinearEquiv

@[simp] theorem toModel_coordinateVector (b : Module.Basis (Fin d) ℝ E) (i : Fin d) :
    toModel b (Pi.single i 1) = b i := by
  change b.equivFun.symm (Pi.single i 1) = b i
  rw [Module.Basis.equivFun_symm_apply]
  simp

/-- Actual scalar differentiation after the finite-basis change of model. -/
theorem fderiv_comp_toModel_coordinateVector
    (b : Module.Basis (Fin d) ℝ E) {f : E → ℝ} {z : E}
    (hf : DifferentiableAt ℝ f z) (i : Fin d) :
    fderiv ℝ (f ∘ toModel b) ((toModel b).symm z) (Pi.single i 1) =
      fderiv ℝ f z (b i) := by
  have hf' : HasFDerivAt f (fderiv ℝ f z) (toModel b ((toModel b).symm z)) := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hf.hasFDerivAt
  have h := hf'.comp ((toModel b).symm z) (toModel b).hasFDerivAt
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    toModel_coordinateVector]

end PoincareCurvature.PreferredCoordinateFrame
