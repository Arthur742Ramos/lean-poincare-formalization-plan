module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TensorDivergence
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianCoordinate

/-!
# Trace and induced endomorphism connections

This file proves the local-frame trace formula needed to show that fibrewise
trace commutes with the connection induced on the endomorphism bundle.  That
compatibility is the abstract mechanism behind both curvature-to-Ricci and
Ricci-to-scalar differentiation.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Bundle FiberBundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "TEnd" => (fun x : M => TM x →L[ℝ] TM x)

/-- Fibrewise trace of a continuous endomorphism section. -/
def endomorphismTrace (A : ∀ x : M, TEnd x) (x : M) : ℝ :=
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  LinearMap.trace ℝ (TM x) (A x).toLinearMap

/-- Trace in an arbitrary genuine local frame. -/
theorem endomorphismTrace_eq_sum_localFrame
    (A : ∀ x : M, TEnd x)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet) :
    endomorphismTrace (I := I) (E := E) A x =
      ∑ i : ι, (e.localFrameCoeff I b i x) (A x (e.localFrame b i x)) := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  rw [endomorphismTrace, LinearMap.trace_eq_matrix_trace ℝ (e.basisAt b hx)]
  apply Finset.sum_congr rfl
  intro i hi
  change LinearMap.toMatrix (e.basisAt b hx) (e.basisAt b hx) (A x).toLinearMap i i = _
  rw [LinearMap.toMatrix_apply]
  simpa [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
    (e := e) (b := b) hx] using
    (Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
    (I := I) (e := e) (b := b) hx
    (fun y => A y (e.localFrame b i y)) i).symm

/-- Fibrewise trace is differentiable whenever the endomorphism section is.
This is proved in a genuine vector-bundle trivialization, rather than by
treating the varying tangent fibres as a fixed coordinate space. -/
theorem mdifferentiableAt_endomorphismTrace
    {A : ∀ x : M, TEnd x} {x : M}
    (hA : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) y (A y)) x) :
    MDiffAt (endomorphismTrace (I := I) (E := E) A) x := by
  classical
  let e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M) :=
    trivializationAt E TM x
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      MDiffAt (fun y =>
        (e.localFrameCoeff I b i y) (A y (e.localFrame b i y))) x := by
    intro i
    have hframe : MDiffAt (T% (e.localFrame b i)) x :=
      (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
        (n := 1) (i := i) (hx := hx)).mdifferentiableAt
        one_ne_zero
    have happ : MDiffAt (T% (fun y => A y (e.localFrame b i y))) x :=
      hA.clm_bundle_apply hframe
    exact mdifferentiableAt_localFrameCoeff
      (I := I) (e := e) (b := b) (s := fun y => A y (e.localFrame b i y)) hx happ i
  have hsum : MDiffAt (fun y =>
      ∑ i : Fin (Module.finrank ℝ E),
        (e.localFrameCoeff I b i y) (A y (e.localFrame b i y))) x := by
    have hs := MDifferentiableAt.sum (t := Finset.univ)
      (f := fun i y => (e.localFrameCoeff I b i y) (A y (e.localFrame b i y)))
      (fun i _ => hterm i)
    convert hs using 1 <;> ext y <;> simp
  apply hsum.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  exact endomorphismTrace_eq_sum_localFrame (I := I) (E := E) A e b hy

/-- The directional derivative of fibrewise trace is the sum of the
directional derivatives of its diagonal coefficients in any genuine local
frame.  This is the coordinate bridge used before the connection terms are
shown to cancel. -/
theorem mvfderiv_endomorphismTrace_apply_eq_sum_localFrame
    {A : ∀ x : M, TEnd x} {x : M}
    (hA : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) y (A y)) x)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (hx : x ∈ e.baseSet) (u : TM x) :
    mvfderiv (I := I) (endomorphismTrace (I := I) (E := E) A) x u =
      ∑ i : ι, mvfderiv (I := I) (fun y =>
        (e.localFrameCoeff I b i y) (A y (e.localFrame b i y))) x u := by
  have hevent :
      endomorphismTrace (I := I) (E := E) A =ᶠ[nhds x]
        (fun y => ∑ i : ι,
          (e.localFrameCoeff I b i y) (A y (e.localFrame b i y))) := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact endomorphismTrace_eq_sum_localFrame (I := I) (E := E) A e b hy
  have hmv : mvfderiv (I := I) (endomorphismTrace (I := I) (E := E) A) x =
      mvfderiv (I := I) (fun y => ∑ i : ι,
        (e.localFrameCoeff I b i y) (A y (e.localFrame b i y))) x := by
    unfold mvfderiv
    rw [hevent.eq_of_nhds, hevent.mfderiv_eq]
  rw [hmv]
  have hterm : ∀ i : ι, MDiffAt (fun y =>
      (e.localFrameCoeff I b i y) (A y (e.localFrame b i y))) x := by
    intro i
    have hframe : MDiffAt (T% (e.localFrame b i)) x :=
      (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
        (n := 1) (i := i) (hx := hx)).mdifferentiableAt one_ne_zero
    have happ : MDiffAt (T% (fun y => A y (e.localFrame b i y))) x :=
      hA.clm_bundle_apply hframe
    exact mdifferentiableAt_localFrameCoeff
      (I := I) (e := e) (b := b) (s := fun y => A y (e.localFrame b i y)) hx happ i
  let term : ι → M → ℝ := fun i y =>
    (e.localFrameCoeff I b i y) (A y (e.localFrame b i y))
  have hsumDiff (s : Finset ι) :
      MDiffAt (fun y => ∑ i ∈ s, term i y) x := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using (mdifferentiableAt_const (c := (0 : ℝ)) (x := x))
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        convert (hterm i).add ih using 1 <;> ext y <;> rfl
  have hsum (s : Finset ι) :
      mvfderiv (I := I) (fun y => ∑ i ∈ s, term i y) x =
        ∑ i ∈ s, mvfderiv (I := I) (term i) x := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [mvfderiv_const]
    | @insert i s hi ih =>
        have hiDiff : MDiffAt (term i) x := hterm i
        have hsDiff : MDiffAt (fun y => ∑ j ∈ s, term j y) x := hsumDiff s
        simp only [Finset.sum_insert hi]
        rw [show (fun y => term i y + ∑ j ∈ s, term j y) =
          term i + (fun y => ∑ j ∈ s, term j y) by rfl]
        rw [mvfderiv_add (I := I) hiDiff hsDiff, ih]
  simpa [term] using congrArg (fun L => L u) (hsum Finset.univ)

/-- The two double sums occurring in the trace computation agree after
interchanging their dummy frame indices. -/
theorem sum_mul_swap_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a Γ : ι → ι → ℝ) :
    (∑ i : ι, ∑ j : ι, a j i * Γ i j) =
      ∑ i : ι, ∑ j : ι, Γ j i * a i j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

end CovariantDerivative
