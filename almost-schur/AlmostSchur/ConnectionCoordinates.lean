module

public import AlmostSchur.Hessian
public import AlmostSchur.ChartMetric
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# The actual connection in a local tangent frame

The frame expansion is obtained from the covariant derivative axioms and
Mathlib's differentiable coefficient reconstruction, not postulated as a
coordinate connection formula.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff BigOperators

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Additivity of the actual connection over a finite family of sections
differentiable at the evaluation point. -/
theorem covariantDerivative_sum
    (cov : CovariantDerivative I E TM) {ι : Type*} (s : Finset ι)
    (σ : ι → Π x : M, TM x) (x : M)
    (hσ : ∀ i ∈ s, MDiffAt (T% (σ i)) x) :
    cov (fun y => ∑ i ∈ s, σ i y) x = ∑ i ∈ s, cov (σ i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact congrFun cov.zero x
  | @insert a s ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hσ
    simp only [Finset.sum_insert ha]
    change cov (σ a + (fun y => ∑ i ∈ s, σ i y)) x = _
    rw [cov.isCovariantDerivativeOnUniv.add hσ.1 (.sum_section hσ.2), ih hσ.2]

variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

/-- Expansion of a connection in a genuine local tangent frame. The first
term differentiates the frame, and the second differentiates the coefficients. -/
theorem covariantDerivative_localFrame
    (cov : CovariantDerivative I E TM) {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (σ : Π x : M, TM x) (x : M) (hx : x ∈ e.baseSet)
    (hσ : MDiffAt (T% σ) x) :
    cov σ x = Finset.univ.sum (fun i : ι =>
      (e.localFrameCoeff I b i x (σ x)) • cov (e.localFrame b i) x +
        (mvfderiv I (fun y => e.localFrameCoeff I b i y (σ y)) x).smulRight
          (e.localFrame b i x)) := by
  classical
  let a := fun i y => e.localFrameCoeff I b i y (σ y)
  have he (i : ι) : MDiffAt (T% (e.localFrame b i)) x :=
    (contMDiffAt_localFrame_of_mem 1 e b i hx).mdifferentiableAt (by simp)
  have ha (i : ι) : MDiffAt (a i) x := mdifferentiableAt_localFrameCoeff b hx hσ i
  have hex : cov σ x = cov (fun y => ∑ i, a i y • e.localFrame b i y) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hσ
      (.sum_section fun i _ => (ha i).smul_section (he i))
      (by simp) (e.eventually_eq_localFrame_sum_coeff_smul b hx)
  rw [hex, covariantDerivative_sum]
  · apply Finset.sum_congr rfl
    intro i _
    exact cov.isCovariantDerivativeOnUniv.leibniz (he i) (ha i)
  · exact fun i _ => (ha i).smul_section (he i)

/-- Bilinear coordinate connection coefficients obtained by applying the
actual covariant derivative to the local coordinate frame. -/
def frameConnectionCoefficients
    (cov : CovariantDerivative I E TM) {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (x : M) : E →L[ℝ] E →L[ℝ] E :=
  ∑ i : ι, ((b.coord i).toContinuousLinearMap.smulRight
    ((e.continuousLinearMapAt ℝ x).comp ((cov (e.localFrame b i) x).comp (e.symmL ℝ x)))).flip

/-- Evaluation of the connection coefficients on two coordinate vectors. -/
theorem frameConnectionCoefficients_apply
    (cov : CovariantDerivative I E TM) {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (x : M) (u v : E) :
    frameConnectionCoefficients cov e b x u v = ∑ i,
      b.repr v i • e.continuousLinearMapAt ℝ x
        (cov (e.localFrame b i) x (e.symmL ℝ x u)) := by
  simp [frameConnectionCoefficients, Module.Basis.coord_apply]

/-- A coordinate frame vector is sent back to its model basis vector. -/
theorem localFrame_coordinates {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (x : M) (hx : x ∈ e.baseSet) (i : ι) :
    e.continuousLinearMapAt ℝ x (e.localFrame b i x) = b i := by
  rw [e.localFrame_apply_of_mem_baseSet b hx]
  change e.continuousLinearMapAt ℝ x ((e.linearEquivAt ℝ x hx).symm (b i)) = b i
  rw [e.linearEquivAt_symm_apply, ← e.symmL_apply (R := ℝ) hx]
  exact e.continuousLinearMapAt_symmL hx _

/-- The actual connection in coordinates is the coefficient derivative
plus the bilinear frame-connection term. -/
theorem covariantDerivative_coordinates
    (cov : CovariantDerivative I E TM) {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    (σ : Π x : M, TM x) (x : M) (hx : x ∈ e.baseSet)
    (hσ : MDiffAt (T% σ) x) (u : E) :
    e.continuousLinearMapAt ℝ x (cov σ x (e.symmL ℝ x u)) =
      frameConnectionCoefficients cov e b x u (e.continuousLinearMapAt ℝ x (σ x)) +
        ∑ i : ι, (mvfderiv I (fun y => e.localFrameCoeff I b i y (σ y)) x
          (e.symmL ℝ x u)) • b i := by
  rw [covariantDerivative_localFrame cov e b σ x hx hσ]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    map_sum, map_add, map_smul, Finset.sum_add_distrib]
  rw [frameConnectionCoefficients_apply]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp only [e.localFrameCoeff_eq_coeff (b := b) hx,
      e.continuousLinearMapAt_apply_of_mem ℝ hx]
  · apply Finset.sum_congr rfl
    intro i _
    rw [localFrame_coordinates e b x hx]

end AlmostSchur
