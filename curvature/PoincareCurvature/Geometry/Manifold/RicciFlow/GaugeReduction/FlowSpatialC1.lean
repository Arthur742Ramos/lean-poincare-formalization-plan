/-
Concrete spatial-`C¹` packaging of the project's variational ODE flow
(roadmap point 4, Item 2).

The Banach-model flow in `ModelGaugeFlowODE` supplies, on a Picard cylinder, the two
ingredients needed for the base case of the smooth-dependence bootstrap:

* the per-point spatial Fréchet derivative of each fixed-time slice
  `y ↦ flow (y, t)` (the `ofProduct_flow_timeSlice_hasFDerivAt_*` family), whose
  derivative is the variational tangent map `tangent x t`;
* joint continuity of the base-flow/tangent pair on the initial-data ball
  (`ofProduct_flow_tangent_continuousOn_initialBall_time`).

This module wires those through the abstract open-set packaging lemma
`PoincareCurvature.VariationalSmoothness.contDiffOn_one_of_hasFDerivAt_continuousOn_isOpen`
to obtain the concrete statement `ContDiffOn ℝ 1 (fun y => flow (y, t)) (ball x₀ r)` —
the spatial-`C¹` base case that the `C¹ → C³` recursion lifts. -/
import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.ModelGaugeFlowODE
import PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.VariationalSmoothness

open Metric Set
open scoped NNReal Topology

namespace PoincareCurvature.FlowSpatialC1

open RicciFlow RicciFlow.ModelGaugeFlowODE
  RicciFlow.ModelGaugeFlowODE.VariationalLocalFlowSolution
  PoincareCurvature.VariationalSmoothness

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {f : ℝ → V → V} {Df : ℝ → V → V →L[ℝ] V}
variable {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : V} {r : ℝ≥0}

/-- **Spatial `C¹` flow slice (structure-level).** From the per-point spatial Fréchet
derivative of a variational flow time slice on the open ball and continuity of the
tangent map there, the slice `y ↦ flow (y, t)` is `ContDiffOn ℝ 1` on `ball x₀ r`. -/
theorem flow_timeSlice_contDiffOn_one_ball
    (α : VariationalLocalFlowSolution f Df t₀ x₀ r) {t : ℝ}
    (hder : ∀ x ∈ ball x₀ r,
      HasFDerivAt (fun y : V => α.flow (y, t)) (α.tangent x t) x)
    (hcont : ContinuousOn (fun x : V => α.tangent x t) (ball x₀ r)) :
    ContDiffOn ℝ 1 (fun y : V => α.flow (y, t)) (ball x₀ r) :=
  contDiffOn_one_of_hasFDerivAt_continuousOn_isOpen isOpen_ball hder hcont

/-- **Spatial `C¹` flow slice (product Picard).** For the product-derived variational
flow, the tangent-continuity hypothesis is supplied automatically by
`ofProduct_flow_tangent_continuousOn_initialBall_time`, so only the per-point spatial
derivative remains an input. The result is the concrete spatial-`C¹` base case of the
bootstrap on the open initial-data ball. -/
theorem ofProduct_flow_timeSlice_contDiffOn_one_ball
    {R : ℝ≥0}
    (α : LipschitzLocalFlowSolution (variationalVectorField f Df) t₀
      (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} (ht : t ∈ Icc tmin tmax)
    (hder : ∀ x ∈ ball x₀ r,
      HasFDerivAt
        (fun y : V =>
          (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (y, t))
        ((ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).tangent x t)
        x) :
    ContDiffOn ℝ 1
      (fun y : V =>
        (ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball).flow (y, t))
      (ball x₀ r) := by
  set β := ofProductContinuousLocalFlowSolution α.toContinuousLocalFlowSolution hball with hβ
  have hpair :
      ContinuousOn (fun x : V => (β.flow (x, t), β.tangent x t)) (closedBall x₀ r) := by
    simpa [hβ] using ofProduct_flow_tangent_continuousOn_initialBall_time α hball ht
  have hcont : ContinuousOn (fun x : V => β.tangent x t) (ball x₀ r) :=
    (continuous_snd.comp_continuousOn hpair).mono ball_subset_closedBall
  exact flow_timeSlice_contDiffOn_one_ball β hder hcont

/-! ### Prolongation chaining: the project's variational machinery runs one level up

To climb from `C¹` to `C³` the tower must instantiate the project's variational
Picard-Lindelöf construction at successively prolonged vector fields. The next two
lemmas confirm this chaining typechecks: the *level-1* augmented field is literally
`variationalVectorField F0 DF0` for the level-0 augmented field `F0` and its spatial
derivative `DF0`, so the project's generic Lipschitz/norm packaging applies verbatim
on the augmented model space `W = V × (V →L[ℝ] V)`. This reduces the level-2 Picard
hypotheses to: `F0` Lipschitz/bounded (already supplied by the project at level 1) plus
the single genuinely-new estimate — a Lipschitz/operator-norm bound on the prolongation
derivative `DF0` (which needs `D²f` controlled, i.e. spatial `C^{2,1}` on the field). -/

/-- **Level-1 augmented Lipschitz chaining.** The doubly-prolonged field
`variationalVectorField F0 DF0` is `(max KF (KDF·BA + BDF))`-Lipschitz on the augmented
ball whenever `F0` is `KF`-Lipschitz, `DF0` is `KDF`-Lipschitz, the tangent factor is
`BA`-bounded, and `DF0` is `BDF`-bounded — exactly the project's level-0 packaging,
reused at the augmented space. -/
theorem level1_augmented_lipschitzOnWith
    (F0 : ℝ → (V × (V →L[ℝ] V)) → (V × (V →L[ℝ] V)))
    (DF0 : ℝ → (V × (V →L[ℝ] V)) → ((V × (V →L[ℝ] V)) →L[ℝ] (V × (V →L[ℝ] V))))
    {t : ℝ} {w₀ : V × (V →L[ℝ] V)}
    {A₀ : (V × (V →L[ℝ] V)) →L[ℝ] (V × (V →L[ℝ] V))}
    {a KF KDF BA BDF : ℝ≥0}
    (hF0_lip : LipschitzOnWith KF (F0 t) (closedBall w₀ a))
    (hDF0_lip : LipschitzOnWith KDF (DF0 t) (closedBall w₀ a))
    (hA_bound : ∀ A ∈ closedBall A₀ a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ y ∈ closedBall w₀ a, ‖DF0 t y‖₊ ≤ BDF) :
    LipschitzOnWith (max KF (KDF * BA + BDF))
      (variationalVectorField F0 DF0 t) (closedBall (w₀, A₀) a) :=
  lipschitzOnWith_variationalVectorField_closedBall_at
    (f := F0) (Df := DF0) (t := t) hF0_lip hDF0_lip hA_bound hD_bound

/-- **Level-1 augmented norm chaining.** The doubly-prolonged field is
`(max LF (BDF·BA))`-bounded on the augmented ball from the same componentwise data —
the project's level-0 norm estimate reused at the augmented space. -/
theorem level1_augmented_norm_le
    (F0 : ℝ → (V × (V →L[ℝ] V)) → (V × (V →L[ℝ] V)))
    (DF0 : ℝ → (V × (V →L[ℝ] V)) → ((V × (V →L[ℝ] V)) →L[ℝ] (V × (V →L[ℝ] V))))
    {t : ℝ} {w₀ : V × (V →L[ℝ] V)}
    {A₀ : (V × (V →L[ℝ] V)) →L[ℝ] (V × (V →L[ℝ] V))}
    {a LF BA BDF : ℝ≥0}
    (hF0_bound : ∀ y ∈ closedBall w₀ a, ‖F0 t y‖ ≤ LF)
    (hA_bound : ∀ A ∈ closedBall A₀ a, ‖A‖₊ ≤ BA)
    (hD_bound : ∀ y ∈ closedBall w₀ a, ‖DF0 t y‖₊ ≤ BDF)
    {z : (V × (V →L[ℝ] V)) × ((V × (V →L[ℝ] V)) →L[ℝ] (V × (V →L[ℝ] V)))}
    (hz : z ∈ closedBall (w₀, A₀) a) :
    ‖variationalVectorField F0 DF0 t z‖ ≤ max LF (BDF * BA) :=
  norm_variationalVectorField_le_closedBall_at
    (f := F0) (Df := DF0) (t := t) hF0_bound hA_bound hD_bound hz

/-! ### The keystone reduction: spatial `C³` collapses every prolongation estimate

The level-2 Picard construction reduced (above) to one genuinely-new ingredient:
Lipschitz/operator-norm control of the prolongation derivative, i.e. of `fderiv f` and
`fderiv (fderiv f)`. The next lemma shows this ingredient is *free* once the gauge field
is spatially `C³`: on any closed ball — convex and (in finite dimension) compact —
`ContDiffOn.exists_lipschitzOnWith` turns `C^k` regularity into a Lipschitz constant.
So a single hypothesis `ContDiff ℝ 3 f` supplies all three Lipschitz estimates the
two-rung tower needs, with no separate second-derivative analysis. -/

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- **`C³` ⟹ prolongation Lipschitz package.** A globally spatially-`C³` field `f`
provides Lipschitz constants for `f`, `fderiv f`, and `fderiv (fderiv f)` on every
closed ball — exactly the estimates the augmented Picard-Lindelöf construction needs at
levels 0, 1, and 2 of the bootstrap. The closed ball is convex and (in finite
dimension) compact, so `ContDiffOn.exists_lipschitzOnWith` applies at each derivative
order. -/
theorem contDiff_three_prolongation_lipschitz_package
    {g : W → W} (hg : ContDiff ℝ 3 g) (w₀ : W) (a : ℝ≥0) :
    (∃ Kf, LipschitzOnWith Kf g (closedBall w₀ a)) ∧
    (∃ KDf, LipschitzOnWith KDf (fun x => fderiv ℝ g x) (closedBall w₀ a)) ∧
    (∃ KD2f, LipschitzOnWith KD2f
      (fun x => fderiv ℝ (fun y => fderiv ℝ g y) x) (closedBall w₀ a)) := by
  have hconv : Convex ℝ (closedBall w₀ (a : ℝ)) := convex_closedBall w₀ a
  have hcompact : IsCompact (closedBall w₀ (a : ℝ)) := isCompact_closedBall w₀ a
  have hDf : ContDiff ℝ 2 (fun x => fderiv ℝ g x) := (contDiff_succ_iff_fderiv.mp hg).2.2
  have hD2f : ContDiff ℝ 1 (fun x => fderiv ℝ (fun y => fderiv ℝ g y) x) :=
    (contDiff_succ_iff_fderiv.mp hDf).2.2
  refine ⟨?_, ?_, ?_⟩
  · exact hg.contDiffOn.exists_lipschitzOnWith (by norm_num) hconv hcompact
  · exact hDf.contDiffOn.exists_lipschitzOnWith (by norm_num) hconv hcompact
  · exact hD2f.contDiffOn.exists_lipschitzOnWith (by norm_num) hconv hcompact

end PoincareCurvature.FlowSpatialC1
