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
  RicciFlow.ModelGaugeFlowODE.IsPicardLindelof
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

/-- **Tangent spatial `ContDiffOn` from the augmented flow's spatial `ContDiffOn` — no
uniqueness.** If the level-1 (augmented) flow slice `z ↦ α.flow(z,t)` is `ContDiffOn n` on
the augmented ball, then the level-0 base flow's tangent map `x ↦ tangent x t` is
`ContDiffOn n` on the base ball. The tangent is *definitionally* `(α.flow((x,1),t)).2`
(by the `ofProductContinuousLocalFlowSolution` field defn), so it is the composition of the
`C^∞` embedding `x ↦ ((x,1),t)` (through `x ↦ (x,1)`), the flow, and `Prod.snd` — giving the
smoothness directly, with no flow-uniqueness argument. This is the bridge that closes the
full-flow recursion: the tangent component's smoothness reduces to the augmented flow's
own smoothness one level up. -/
theorem tangent_contDiffOn_of_augmentedFlow_contDiffOn
    {R : ℝ≥0} {n : WithTop ℕ∞}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀ (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ}
    (hαflow : ContDiffOn ℝ n (fun z : V × (V →L[ℝ] V) => α.flow (z, t))
      (closedBall (x₀, (1 : V →L[ℝ] V)) R)) :
    ContDiffOn ℝ n
      (fun x : V => (ofProductContinuousLocalFlowSolution α hball).tangent x t)
      (closedBall x₀ r) := by
  have hemb : ContDiff ℝ n (fun x : V => (x, (1 : V →L[ℝ] V))) :=
    contDiff_id.prodMk contDiff_const
  have hmaps : MapsTo (fun x : V => (x, (1 : V →L[ℝ] V)))
      (closedBall x₀ r) (closedBall (x₀, (1 : V →L[ℝ] V)) R) := hball
  have hcomp : ContDiffOn ℝ n
      (fun x : V => α.flow ((x, (1 : V →L[ℝ] V)), t)) (closedBall x₀ r) :=
    hαflow.comp (hemb.contDiffOn) hmaps
  exact contDiff_snd.comp_contDiffOn hcomp

/-- **Base-projection smoothness — companion to the tangent bridge.** If the underlying
augmented flow slice `z ↦ α.flow(z,t)` is `ContDiffOn n` on the augmented ball, then the
`ofProduct` base flow slice `x ↦ (ofProduct α hball).flow(x,t)` is `ContDiffOn n` on the
base ball. The base flow is *definitionally* `(α.flow((x,1),t)).1`, so it is the composition
`x ↦ (x,1) → α.flow(·,t) → Prod.fst`. Together with the tangent bridge this controls *both*
projections of the ofProduct flow from the underlying flow. -/
theorem baseProj_contDiffOn_of_augmentedFlow_contDiffOn
    {R : ℝ≥0} {n : WithTop ℕ∞}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀ (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ}
    (hαflow : ContDiffOn ℝ n (fun z : V × (V →L[ℝ] V) => α.flow (z, t))
      (closedBall (x₀, (1 : V →L[ℝ] V)) R)) :
    ContDiffOn ℝ n
      (fun x : V => (ofProductContinuousLocalFlowSolution α hball).flow (x, t))
      (closedBall x₀ r) := by
  have hemb : ContDiff ℝ n (fun x : V => (x, (1 : V →L[ℝ] V))) :=
    contDiff_id.prodMk contDiff_const
  have hmaps : MapsTo (fun x : V => (x, (1 : V →L[ℝ] V)))
      (closedBall x₀ r) (closedBall (x₀, (1 : V →L[ℝ] V)) R) := hball
  have hcomp : ContDiffOn ℝ n
      (fun x : V => α.flow ((x, (1 : V →L[ℝ] V)), t)) (closedBall x₀ r) :=
    hαflow.comp (hemb.contDiffOn) hmaps
  exact contDiff_fst.comp_contDiffOn hcomp

/-- **Embedded underlying-flow reconstruction.** The embedded underlying-flow slice
`x ↦ α.flow((x,1),t)` equals the pair `((ofProduct α hball).flow(x,t), tangent x t)` (by the
`ofProduct` field definitions, `rfl`), so it is `ContDiffOn n` whenever both ofProduct
projections are. This is the type-uniform recursion link: the embedded flow that the
bridges consume is exactly the pair of the next-level ofProduct projections. -/
theorem embeddedFlow_contDiffOn_of_projections
    {R : ℝ≥0} {n : WithTop ℕ∞}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀ (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} {s : Set V}
    (hbase : ContDiffOn ℝ n
      (fun x : V => (ofProductContinuousLocalFlowSolution α hball).flow (x, t)) s)
    (htan : ContDiffOn ℝ n
      (fun x : V => (ofProductContinuousLocalFlowSolution α hball).tangent x t) s) :
    ContDiffOn ℝ n (fun x : V => α.flow ((x, (1 : V →L[ℝ] V)), t)) s :=
  contDiffOn_prod_of_components hbase htan

/-- **Tangent from the embedded slice — the weakened bridge.** The `ofProduct` tangent map
`x ↦ tangent x t` is `ContDiffOn n` whenever *only the embedded slice* `x ↦ α.flow((x,1),t)`
is `ContDiffOn n` — strictly weaker than the full augmented flow on all of the augmented
ball. The tangent is definitionally `(α.flow((x,1),t)).2 = Prod.snd ∘ (embedded slice)`. This
is the decisive simplification: combined with `baseProj_from_embedded` and
`embeddedFlow_contDiffOn_of_projections`, the recursion needs only embedded-slice smoothness
at each level, which reconstructs from the next level's two projections — making the
type-changing tower a uniform recursion with no full-augmented-flow hypothesis anywhere. -/
theorem tangent_contDiffOn_of_embedded
    {R : ℝ≥0} {n : WithTop ℕ∞}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀ (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} {s : Set V}
    (hemb : ContDiffOn ℝ n (fun x : V => α.flow ((x, (1 : V →L[ℝ] V)), t)) s) :
    ContDiffOn ℝ n
      (fun x : V => (ofProductContinuousLocalFlowSolution α hball).tangent x t) s :=
  contDiff_snd.comp_contDiffOn hemb

/-- **Base projection from the embedded slice — the weakened companion.** The `ofProduct`
base flow `x ↦ (ofProduct α hball).flow(x,t)` is `ContDiffOn n` whenever only the embedded
slice `x ↦ α.flow((x,1),t)` is. Definitionally `Prod.fst ∘ (embedded slice)`. -/
theorem baseProj_contDiffOn_of_embedded
    {R : ℝ≥0} {n : WithTop ℕ∞}
    (α : ContinuousLocalFlowSolution (variationalVectorField f Df) t₀ (x₀, (1 : V →L[ℝ] V)) R)
    (hball : ∀ x ∈ closedBall x₀ r,
      (x, (1 : V →L[ℝ] V)) ∈ closedBall (x₀, (1 : V →L[ℝ] V)) R)
    {t : ℝ} {s : Set V}
    (hemb : ContDiffOn ℝ n (fun x : V => α.flow ((x, (1 : V →L[ℝ] V)), t)) s) :
    ContDiffOn ℝ n
      (fun x : V => (ofProductContinuousLocalFlowSolution α hball).flow (x, t)) s :=
  contDiff_fst.comp_contDiffOn hemb

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

/-! ### End-to-end: a spatially-`C³` autonomous field has a variational flow

For a time-independent spatially-`C³` field `g`, the keystone Lipschitz package plus the
project's generic variational Picard-Lindelöf assembler combine into an honest
`VariationalLocalFlowSolution`: the base flow `x ↦ Φ_t x` together with its tangent map
solving the variational equation `A' = (fderiv g)(Φ) ∘ A`, `A(t₀) = 1`. This is the
concrete realization of the `C¹` base case — no longer a structure hypothesis but a flow
produced from the single assumption `ContDiff ℝ 3 g`. -/

section Autonomous

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [CompleteSpace W]

omit [CompleteSpace W] in
/-- **Autonomous `C³` field ⟹ variational Picard-Lindelöf.** For a time-independent
spatially-`C³` field `g`, the variational system `(y,A)' = (g y, (fderiv g y)∘A)` is
Picard-Lindelöf on every closed ball, with constants drawn from the keystone package and
compact-ball norm bounds. The remaining hypothesis is the standard Picard time-radius
smallness on the exposed Lipschitz constant `L`. -/
theorem isPicardLindelof_autonomous_variational_of_contDiff_three
    {g : W → W} (hg : ContDiff ℝ 3 g)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (w₀ : W) (a r : ℝ≥0) :
    ∃ L K : ℝ≥0,
      (L * (max (tmax - (t₀ : ℝ)) ((t₀ : ℝ) - tmin)) ≤ (a : ℝ) - r) →
        IsPicardLindelof (variationalVectorField (fun _ : ℝ => g) (fun _ : ℝ => fderiv ℝ g))
          t₀ (w₀, (1 : W →L[ℝ] W)) a r L K := by
  obtain ⟨Kf, hKf⟩ := (contDiff_three_prolongation_lipschitz_package hg w₀ a).1
  obtain ⟨KD, hKD⟩ := (contDiff_three_prolongation_lipschitz_package hg w₀ a).2.1
  have hg_cont : Continuous g := hg.continuous
  have hDg_cont : Continuous (fun x => fderiv ℝ g x) := hg.continuous_fderiv (by norm_num)
  have hcompact : IsCompact (closedBall w₀ (a : ℝ)) := isCompact_closedBall w₀ a
  obtain ⟨Lfr, hLfr⟩ := (hcompact.bddAbove_image (continuous_norm.comp hg_cont).continuousOn)
  obtain ⟨BDr, hBDr⟩ := (hcompact.bddAbove_image (continuous_norm.comp hDg_cont).continuousOn)
  have hw0 : w₀ ∈ closedBall w₀ (a : ℝ) := mem_closedBall_self (by positivity)
  have hLf_nonneg : 0 ≤ Lfr := le_trans (norm_nonneg _) (hLfr ⟨w₀, hw0, rfl⟩)
  have hBD_nonneg : 0 ≤ BDr := le_trans (norm_nonneg _) (hBDr ⟨w₀, hw0, rfl⟩)
  set Lf : ℝ≥0 := Lfr.toNNReal with hLfdef
  set BD : ℝ≥0 := BDr.toNNReal with hBDdef
  set BA : ℝ≥0 := 1 + a with hBAdef
  refine ⟨max Lf (BD * BA), max Kf (KD * BA + BD), fun hmul => ?_⟩
  have hLf_coe : (Lf : ℝ) = Lfr := by rw [hLfdef, Real.coe_toNNReal _ hLf_nonneg]
  have hBD_coe : (BD : ℝ) = BDr := by rw [hBDdef, Real.coe_toNNReal _ hBD_nonneg]
  apply isPicardLindelof_variationalVectorField_of_component_closedBall_continuity
    (Kf := Kf) (KD := KD) (Lf := Lf) (BA := BA) (BD := BD)
  · exact fun t _ => hKf
  · exact fun t _ => hKD
  · intro t _ y hy
    rw [hLf_coe]; exact hLfr ⟨y, hy, rfl⟩
  · intro A hA
    rw [← NNReal.coe_le_coe, coe_nnnorm, hBAdef]
    have hdist : dist A (1 : W →L[ℝ] W) ≤ a := by rw [← mem_closedBall]; exact hA
    have hsub : ‖A - 1‖ ≤ (a : ℝ) := by rw [← dist_eq_norm]; exact hdist
    have hone : ‖(1 : W →L[ℝ] W)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have htri : ‖A‖ ≤ ‖(1 : W →L[ℝ] W)‖ + ‖A - 1‖ := by
      simpa [add_comm] using norm_le_norm_add_norm_sub' A (1 : W →L[ℝ] W)
    push_cast
    linarith
  · intro t _ y hy
    rw [← NNReal.coe_le_coe, coe_nnnorm, hBD_coe]; exact hBDr ⟨y, hy, rfl⟩
  · exact fun y _ => continuousOn_const
  · exact fun y _ => continuousOn_const
  · exact hmul

/-- **Autonomous `C³` field ⟹ variational flow exists.** There is a Lipschitz constant
`L` such that whenever the Picard time-radius smallness on `L` holds, the project's
`ofProductPicardLindelof` produces an honest `VariationalLocalFlowSolution` on
`closedBall w₀ r`: the base flow `x ↦ Φ_t x` paired with its tangent map solving the
variational equation. The embedding-ball hypothesis is automatic (the tangent coordinate
is fixed at the identity). -/
theorem exists_const_variationalFlow_autonomous_of_contDiff_three
    {g : W → W} (hg : ContDiff ℝ 3 g)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (w₀ : W) (a r : ℝ≥0) :
    ∃ L : ℝ≥0,
      (L * (max (tmax - (t₀ : ℝ)) ((t₀ : ℝ) - tmin)) ≤ (a : ℝ) - r) →
        Nonempty (VariationalLocalFlowSolution (fun _ : ℝ => g)
          (fun _ : ℝ => fderiv ℝ g) t₀ w₀ r) := by
  obtain ⟨L, K, hPL⟩ := isPicardLindelof_autonomous_variational_of_contDiff_three hg t₀ w₀ a r
  have hball : ∀ x ∈ closedBall w₀ r,
      (x, (1 : W →L[ℝ] W)) ∈ closedBall (w₀, (1 : W →L[ℝ] W)) r := by
    intro x hx
    rw [mem_closedBall] at hx ⊢
    rw [Prod.dist_eq]
    simp only [dist_self, max_le_iff]
    exact ⟨hx, by positivity⟩
  exact ⟨L, fun hmul => nonempty_ofProductPicardLindelof (hPL hmul) hball⟩

/-- **Genuine `HasFDerivAt` of the real flow slice from `ContDiff ℝ 3 g`.** For the
state-preserving variational flow of an autonomous `C³` field, every interior point and
forward time has the spatial Fréchet derivative equal to the variational tangent map.
All hypotheses of the project's convex-state criterion are discharged with
`state := closedBall w₀ a`: the ball is convex; the flow stays in it (state-preserving);
`‖fderiv g‖` is bounded and `fderiv g` is Lipschitz there (keystone + compactness); and
`g` is differentiable everywhere. -/
theorem stateFlow_hasFDerivAt
    {g : W → W} (hg : ContDiff ℝ 3 g)
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {w₀ : W} {a r r' L K : ℝ≥0}
    (hf : IsPicardLindelof (variationalVectorField (fun _ : ℝ => g) (fun _ : ℝ => fderiv ℝ g))
      t₀ (w₀, (1 : W →L[ℝ] W)) a r L K)
    (hball : ∀ y ∈ closedBall w₀ r',
      (y, (1 : W →L[ℝ] W)) ∈ closedBall (w₀, (1 : W →L[ℝ] W)) r)
    {x : W} (hx : x ∈ ball w₀ r') {t : ℝ} (ht : t ∈ Icc (t₀ : ℝ) tmax) :
    HasFDerivAt
      (fun y : W =>
        (ofProductContinuousLocalFlowSolution
          (toStatePreservingLipschitzLocalFlowSolution hf).toContinuousLocalFlowSolution hball).flow
            (y, t))
      ((ofProductContinuousLocalFlowSolution
          (toStatePreservingLipschitzLocalFlowSolution hf).toContinuousLocalFlowSolution hball).tangent
            x t)
      x := by
  set β := toStatePreservingLipschitzLocalFlowSolution hf with hβ
  obtain ⟨KDf, hKDf⟩ := (contDiff_three_prolongation_lipschitz_package hg w₀ a).2.1
  have hg_cont : Continuous (fun x => fderiv ℝ g x) := hg.continuous_fderiv (by norm_num)
  have hcompact : IsCompact (closedBall w₀ (a : ℝ)) := isCompact_closedBall w₀ a
  obtain ⟨KB, hKB⟩ := (hcompact.bddAbove_image (continuous_norm.comp hg_cont).continuousOn)
  have hgdiff : ∀ z : W, HasFDerivAt g (fderiv ℝ g z) z := fun z =>
    (hg.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  apply ofProduct_flow_timeSlice_hasFDerivAt_of_Df_lipschitzOnWith_on_convex_state_forward_Icc_of_mem_ball
    (β := β) (K := KB) (KD := KDf) (state := fun _ => closedBall w₀ a) hball hx ht
  · exact fun τ _ => convex_closedBall w₀ a
  · intro y hy τ hτ
    exact ofProductStatePreservingPicardLindelof_flow_mem_base_closedBall_forward_Icc
      hf hball hy hτ
  · intro τ _ z hz
    exact hKB ⟨z, hz, rfl⟩
  · intro τ _
    exact hKDf
  · intro τ _ z _
    exact (hgdiff z).hasFDerivWithinAt

/-- **Concrete spatial-`C¹` flow slice from `ContDiff ℝ 3 g` alone.** Combining the
genuine per-point `HasFDerivAt` (all hypotheses discharged from `C³`) with the automatic
tangent-continuity of the product flow, the state-preserving variational flow's time
slice `y ↦ Φ_t y` is `ContDiffOn ℝ 1` on the open ball — the spatial-`C¹` base case,
produced from nothing but `C³`-regularity of the field plus the Picard data. -/
theorem stateFlow_contDiffOn_one
    {g : W → W} (hg : ContDiff ℝ 3 g)
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {w₀ : W} {a r r' L K : ℝ≥0}
    (hf : IsPicardLindelof (variationalVectorField (fun _ : ℝ => g) (fun _ : ℝ => fderiv ℝ g))
      t₀ (w₀, (1 : W →L[ℝ] W)) a r L K)
    (hball : ∀ y ∈ closedBall w₀ r',
      (y, (1 : W →L[ℝ] W)) ∈ closedBall (w₀, (1 : W →L[ℝ] W)) r)
    {t : ℝ} (ht : t ∈ Icc (t₀ : ℝ) tmax) :
    ContDiffOn ℝ 1
      (fun y : W =>
        (ofProductContinuousLocalFlowSolution
          (toStatePreservingLipschitzLocalFlowSolution hf).toContinuousLocalFlowSolution hball).flow
            (y, t))
      (ball w₀ r') := by
  have htbig : t ∈ Icc tmin tmax := ⟨le_trans t₀.2.1 ht.1, ht.2⟩
  exact ofProduct_flow_timeSlice_contDiffOn_one_ball
    (toStatePreservingLipschitzLocalFlowSolution hf) hball htbig
    (fun x hx => stateFlow_hasFDerivAt hg hf hball hx ht)

/-! #### Minimal-regularity (`C²`) reusable forms

The HasFDerivAt extraction and the Picard construction each consume only `g` and
`fderiv g` being Lipschitz/bounded — facts available already at `C²`. Stating them at the
minimal `C²` hypothesis (rather than `C³`) makes them reusable at *each* prolongation
level of the bootstrap: the level-1 augmented field `(g, fderiv g)` is `C²` when `g` is
`C³`, so these same lemmas apply to it. -/

omit [CompleteSpace W] in
/-- `fderiv g` is Lipschitz on every closed ball when `g` is `C²`. This is the only
keystone ingredient the flow-derivative extraction consumes, isolated at minimal
regularity for reuse at every prolongation level. -/
theorem fderiv_lipschitzOnWith_of_contDiff_two
    {g : W → W} (hg : ContDiff ℝ 2 g) (w₀ : W) (a : ℝ≥0) :
    ∃ K, LipschitzOnWith K (fun x => fderiv ℝ g x) (closedBall w₀ a) := by
  have hconv : Convex ℝ (closedBall w₀ (a : ℝ)) := convex_closedBall w₀ a
  have hcompact : IsCompact (closedBall w₀ (a : ℝ)) := isCompact_closedBall w₀ a
  have hDf : ContDiff ℝ 1 (fun x => fderiv ℝ g x) := (contDiff_succ_iff_fderiv.mp hg).2.2
  exact hDf.contDiffOn.exists_lipschitzOnWith (by norm_num) hconv hcompact

omit [CompleteSpace W] in
/-- C²-minimal variational Picard-Lindelöf: needs only `g` and `fderiv g` Lipschitz +
bounded, all available at `C²`. -/
theorem isPicardLindelof_autonomous_variational_of_contDiff_two
    {g : W → W} (hg : ContDiff ℝ 2 g)
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (w₀ : W) (a r : ℝ≥0) :
    ∃ L K : ℝ≥0,
      (L * (max (tmax - (t₀ : ℝ)) ((t₀ : ℝ) - tmin)) ≤ (a : ℝ) - r) →
        IsPicardLindelof (variationalVectorField (fun _ : ℝ => g) (fun _ : ℝ => fderiv ℝ g))
          t₀ (w₀, (1 : W →L[ℝ] W)) a r L K := by
  have hconv : Convex ℝ (closedBall w₀ (a : ℝ)) := convex_closedBall w₀ a
  have hcompact : IsCompact (closedBall w₀ (a : ℝ)) := isCompact_closedBall w₀ a
  obtain ⟨Kf, hKf⟩ := hg.contDiffOn.exists_lipschitzOnWith (by norm_num) hconv hcompact
  obtain ⟨KD, hKD⟩ := fderiv_lipschitzOnWith_of_contDiff_two hg w₀ a
  have hg_cont : Continuous g := hg.continuous
  have hDg_cont : Continuous (fun x => fderiv ℝ g x) := hg.continuous_fderiv (by norm_num)
  obtain ⟨Lfr, hLfr⟩ := (hcompact.bddAbove_image (continuous_norm.comp hg_cont).continuousOn)
  obtain ⟨BDr, hBDr⟩ := (hcompact.bddAbove_image (continuous_norm.comp hDg_cont).continuousOn)
  have hw0 : w₀ ∈ closedBall w₀ (a : ℝ) := mem_closedBall_self (by positivity)
  have hLf_nonneg : 0 ≤ Lfr := le_trans (norm_nonneg _) (hLfr ⟨w₀, hw0, rfl⟩)
  have hBD_nonneg : 0 ≤ BDr := le_trans (norm_nonneg _) (hBDr ⟨w₀, hw0, rfl⟩)
  set Lf : ℝ≥0 := Lfr.toNNReal with hLfdef
  set BD : ℝ≥0 := BDr.toNNReal with hBDdef
  set BA : ℝ≥0 := 1 + a with hBAdef
  refine ⟨max Lf (BD * BA), max Kf (KD * BA + BD), fun hmul => ?_⟩
  have hLf_coe : (Lf : ℝ) = Lfr := by rw [hLfdef, Real.coe_toNNReal _ hLf_nonneg]
  have hBD_coe : (BD : ℝ) = BDr := by rw [hBDdef, Real.coe_toNNReal _ hBD_nonneg]
  apply isPicardLindelof_variationalVectorField_of_component_closedBall_continuity
    (Kf := Kf) (KD := KD) (Lf := Lf) (BA := BA) (BD := BD)
  · exact fun t _ => hKf
  · exact fun t _ => hKD
  · intro t _ y hy
    rw [hLf_coe]; exact hLfr ⟨y, hy, rfl⟩
  · intro A hA
    rw [← NNReal.coe_le_coe, coe_nnnorm, hBAdef]
    have hdist : dist A (1 : W →L[ℝ] W) ≤ a := by rw [← mem_closedBall]; exact hA
    have hsub : ‖A - 1‖ ≤ (a : ℝ) := by rw [← dist_eq_norm]; exact hdist
    have hone : ‖(1 : W →L[ℝ] W)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have htri : ‖A‖ ≤ ‖(1 : W →L[ℝ] W)‖ + ‖A - 1‖ := by
      simpa [add_comm] using norm_le_norm_add_norm_sub' A (1 : W →L[ℝ] W)
    push_cast
    linarith
  · intro t _ y hy
    rw [← NNReal.coe_le_coe, coe_nnnorm, hBD_coe]; exact hBDr ⟨y, hy, rfl⟩
  · exact fun y _ => continuousOn_const
  · exact fun y _ => continuousOn_const
  · exact hmul

/-- C²-minimal flow-derivative extraction: the real state-preserving flow slice has
spatial Fréchet derivative = the variational tangent map, needing only `g` to be `C²`. -/
theorem stateFlow_hasFDerivAt_two
    {g : W → W} (hg : ContDiff ℝ 2 g)
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {w₀ : W} {a r r' L K : ℝ≥0}
    (hf : IsPicardLindelof (variationalVectorField (fun _ : ℝ => g) (fun _ : ℝ => fderiv ℝ g))
      t₀ (w₀, (1 : W →L[ℝ] W)) a r L K)
    (hball : ∀ y ∈ closedBall w₀ r',
      (y, (1 : W →L[ℝ] W)) ∈ closedBall (w₀, (1 : W →L[ℝ] W)) r)
    {x : W} (hx : x ∈ ball w₀ r') {t : ℝ} (ht : t ∈ Icc (t₀ : ℝ) tmax) :
    HasFDerivAt
      (fun y : W =>
        (ofProductContinuousLocalFlowSolution
          (toStatePreservingLipschitzLocalFlowSolution hf).toContinuousLocalFlowSolution hball).flow
            (y, t))
      ((ofProductContinuousLocalFlowSolution
          (toStatePreservingLipschitzLocalFlowSolution hf).toContinuousLocalFlowSolution hball).tangent
            x t)
      x := by
  obtain ⟨KDf, hKDf⟩ := fderiv_lipschitzOnWith_of_contDiff_two hg w₀ a
  have hg_cont : Continuous (fun x => fderiv ℝ g x) := hg.continuous_fderiv (by norm_num)
  have hcompact : IsCompact (closedBall w₀ (a : ℝ)) := isCompact_closedBall w₀ a
  obtain ⟨KB, hKB⟩ := (hcompact.bddAbove_image (continuous_norm.comp hg_cont).continuousOn)
  have hgdiff : ∀ z : W, HasFDerivAt g (fderiv ℝ g z) z := fun z =>
    (hg.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  apply ofProduct_flow_timeSlice_hasFDerivAt_of_Df_lipschitzOnWith_on_convex_state_forward_Icc_of_mem_ball
    (β := toStatePreservingLipschitzLocalFlowSolution hf)
    (K := KB) (KD := KDf) (state := fun _ => closedBall w₀ a) hball hx ht
  · exact fun τ _ => convex_closedBall w₀ a
  · intro y hy τ hτ
    exact ofProductStatePreservingPicardLindelof_flow_mem_base_closedBall_forward_Icc
      hf hball hy hτ
  · intro τ _ z hz
    exact hKB ⟨z, hz, rfl⟩
  · intro τ _
    exact hKDf
  · intro τ _ z _
    exact (hgdiff z).hasFDerivWithinAt

/-- C²-minimal concrete spatial-`C¹` flow slice: from `ContDiff ℝ 2 g` plus the Picard
data, the real state-preserving flow slice is `ContDiffOn ℝ 1` on the ball. -/
theorem stateFlow_contDiffOn_one_two
    {g : W → W} (hg : ContDiff ℝ 2 g)
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {w₀ : W} {a r r' L K : ℝ≥0}
    (hf : IsPicardLindelof (variationalVectorField (fun _ : ℝ => g) (fun _ : ℝ => fderiv ℝ g))
      t₀ (w₀, (1 : W →L[ℝ] W)) a r L K)
    (hball : ∀ y ∈ closedBall w₀ r',
      (y, (1 : W →L[ℝ] W)) ∈ closedBall (w₀, (1 : W →L[ℝ] W)) r)
    {t : ℝ} (ht : t ∈ Icc (t₀ : ℝ) tmax) :
    ContDiffOn ℝ 1
      (fun y : W =>
        (ofProductContinuousLocalFlowSolution
          (toStatePreservingLipschitzLocalFlowSolution hf).toContinuousLocalFlowSolution hball).flow
            (y, t))
      (ball w₀ r') := by
  have htbig : t ∈ Icc tmin tmax := ⟨le_trans t₀.2.1 ht.1, ht.2⟩
  exact ofProduct_flow_timeSlice_contDiffOn_one_ball
    (toStatePreservingLipschitzLocalFlowSolution hf) hball htbig
    (fun x hx => stateFlow_hasFDerivAt_two hg hf hball hx ht)

/-- **One real-flow recursion step.** If the level-0 augmented flow slice `z ↦ Ψ0 z`
(the product flow whose 2nd projection at `(x,1)` is — definitionally — the base flow's
tangent map) is `ContDiffOn n` on the augmented ball, then the real base flow slice
`x ↦ Φ_t x` is `ContDiffOn (n+1)` on the base ball. The base flow's per-point
`HasFDerivAt` (equal to the tangent) comes from `g : C²` via `stateFlow_hasFDerivAt_two`;
the tangent equals `(Ψ0 (x,1)).2` by definitional unfolding of
`ofProductContinuousLocalFlowSolution`, so the abstract rung lemma
`contDiffOn_succ_of_augmented_flow_contDiffOn_isOpen` closes it. This is the genuine
engine step on the real flow objects; applied twice it yields spatial `C³`. -/
theorem baseFlow_contDiffOn_succ_of_augmented_contDiffOn
    {g : W → W} (hg : ContDiff ℝ 2 g)
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {w₀ : W} {a r r' L K : ℝ≥0}
    (hf : IsPicardLindelof (variationalVectorField (fun _ : ℝ => g) (fun _ : ℝ => fderiv ℝ g))
      t₀ (w₀, (1 : W →L[ℝ] W)) a r L K)
    (hball : ∀ y ∈ closedBall w₀ r',
      (y, (1 : W →L[ℝ] W)) ∈ closedBall (w₀, (1 : W →L[ℝ] W)) r)
    {t : ℝ} (ht : t ∈ Icc (t₀ : ℝ) tmax) {n : ℕ}
    (hΨ : ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun z : W × (W →L[ℝ] W) =>
        (toStatePreservingLipschitzLocalFlowSolution hf).toContinuousLocalFlowSolution.flow (z, t))
      (closedBall (w₀, (1 : W →L[ℝ] W)) r)) :
    ContDiffOn ℝ ((n : WithTop ℕ∞) + 1)
      (fun y : W =>
        (ofProductContinuousLocalFlowSolution
          (toStatePreservingLipschitzLocalFlowSolution hf).toContinuousLocalFlowSolution hball).flow
            (y, t))
      (ball w₀ r') := by
  apply contDiffOn_succ_of_augmented_flow_contDiffOn_isOpen
    (Ψ := fun z _ =>
      (toStatePreservingLipschitzLocalFlowSolution hf).toContinuousLocalFlowSolution.flow (z, t))
    (S := closedBall (w₀, (1 : W →L[ℝ] W)) r) (t := t) isOpen_ball
  · intro x hx
    exact stateFlow_hasFDerivAt_two hg hf hball hx ht
  · intro x hx
    exact hball x (ball_subset_closedBall hx)
  · exact hΨ

/-- **Recursion step keyed on the tangent.** The base flow slice is `ContDiffOn (n+1)`
whenever its *tangent* map `x ↦ tangent x t` is `ContDiffOn n` on the base ball. This is
the weakened, directly-controllable form of the recursion: the rung
`contDiffOn_succ_of_jacobian_contDiffOn_isOpen` only ever needs the Jacobian (= the tangent,
on the embedded slice), not the full augmented flow. The base flow's per-point `HasFDerivAt`
(equal to the tangent) comes from `g : C²` via `stateFlow_hasFDerivAt_two`. Combined with
`tangent_contDiffOn_of_augmentedFlow_contDiffOn` (which gives the tangent's smoothness from
the augmented flow one level up), this closes the bootstrap recursion. -/
theorem baseFlow_contDiffOn_succ_of_tangent_contDiffOn
    {g : W → W} (hg : ContDiff ℝ 2 g)
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {w₀ : W} {a r r' L K : ℝ≥0}
    (hf : IsPicardLindelof (variationalVectorField (fun _ : ℝ => g) (fun _ : ℝ => fderiv ℝ g))
      t₀ (w₀, (1 : W →L[ℝ] W)) a r L K)
    (hball : ∀ y ∈ closedBall w₀ r',
      (y, (1 : W →L[ℝ] W)) ∈ closedBall (w₀, (1 : W →L[ℝ] W)) r)
    {t : ℝ} (ht : t ∈ Icc (t₀ : ℝ) tmax) {n : ℕ}
    (htan : ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun x : W =>
        (ofProductContinuousLocalFlowSolution
          (toStatePreservingLipschitzLocalFlowSolution hf).toContinuousLocalFlowSolution hball).tangent
            x t)
      (ball w₀ r')) :
    ContDiffOn ℝ ((n : WithTop ℕ∞) + 1)
      (fun y : W =>
        (ofProductContinuousLocalFlowSolution
          (toStatePreservingLipschitzLocalFlowSolution hf).toContinuousLocalFlowSolution hball).flow
            (y, t))
      (ball w₀ r') := by
  apply contDiffOn_succ_of_jacobian_contDiffOn_isOpen (n := n) isOpen_ball
  · intro x hx
    exact stateFlow_hasFDerivAt_two hg hf hball hx ht
  · exact htan

/-- **Conditional spatial-`C³` of the real base flow.** If the level-0 augmented flow
slice is `ContDiffOn 2` on the augmented ball, the real base flow slice is `ContDiffOn 3`
on the base ball — the spatial-`C³` target for the gauge-flow diffeomorphism. This is the
recursion step at `n = 2` (cast `2 + 1 = 3`). The hypothesis is the precise honest modular
boundary, supplied by recursing the same step at the augmented level. -/
theorem baseFlow_contDiffOn_three_of_augmented_contDiffOn_two
    {g : W → W} (hg : ContDiff ℝ 2 g)
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {w₀ : W} {a r r' L K : ℝ≥0}
    (hf : IsPicardLindelof (variationalVectorField (fun _ : ℝ => g) (fun _ : ℝ => fderiv ℝ g))
      t₀ (w₀, (1 : W →L[ℝ] W)) a r L K)
    (hball : ∀ y ∈ closedBall w₀ r',
      (y, (1 : W →L[ℝ] W)) ∈ closedBall (w₀, (1 : W →L[ℝ] W)) r)
    {t : ℝ} (ht : t ∈ Icc (t₀ : ℝ) tmax)
    (hΨ : ContDiffOn ℝ (2 : ℕ)
      (fun z : W × (W →L[ℝ] W) =>
        (toStatePreservingLipschitzLocalFlowSolution hf).toContinuousLocalFlowSolution.flow (z, t))
      (closedBall (w₀, (1 : W →L[ℝ] W)) r)) :
    ContDiffOn ℝ 3
      (fun y : W =>
        (ofProductContinuousLocalFlowSolution
          (toStatePreservingLipschitzLocalFlowSolution hf).toContinuousLocalFlowSolution hball).flow
            (y, t))
      (ball w₀ r') := by
  have h := baseFlow_contDiffOn_succ_of_augmented_contDiffOn (n := 2) hg hf hball ht
    (by simpa using hΨ)
  simpa using h

/-- **Base flow is `ContDiffOn 2`** given the full augmented flow's `ContDiffOn 1`. The
recursion step at `n = 1` (cast `1 + 1 = 2`) — the first genuine gain above the `C¹` base.
The hypothesis is the *full* augmented (product) flow slice being `ContDiffOn 1`, assembled
from its base and tangent projections via `augmentedFlow_contDiffOn_one_of_components`. -/
theorem baseFlow_contDiffOn_two_of_augmented_contDiffOn_one
    {g : W → W} (hg : ContDiff ℝ 2 g)
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {w₀ : W} {a r r' L K : ℝ≥0}
    (hf : IsPicardLindelof (variationalVectorField (fun _ : ℝ => g) (fun _ : ℝ => fderiv ℝ g))
      t₀ (w₀, (1 : W →L[ℝ] W)) a r L K)
    (hball : ∀ y ∈ closedBall w₀ r',
      (y, (1 : W →L[ℝ] W)) ∈ closedBall (w₀, (1 : W →L[ℝ] W)) r)
    {t : ℝ} (ht : t ∈ Icc (t₀ : ℝ) tmax)
    (hΨ : ContDiffOn ℝ (1 : ℕ)
      (fun z : W × (W →L[ℝ] W) =>
        (toStatePreservingLipschitzLocalFlowSolution hf).toContinuousLocalFlowSolution.flow (z, t))
      (closedBall (w₀, (1 : W →L[ℝ] W)) r)) :
    ContDiffOn ℝ 2
      (fun y : W =>
        (ofProductContinuousLocalFlowSolution
          (toStatePreservingLipschitzLocalFlowSolution hf).toContinuousLocalFlowSolution hball).flow
            (y, t))
      (ball w₀ r') := by
  have h := baseFlow_contDiffOn_succ_of_augmented_contDiffOn (n := 1) hg hf hball ht
    (by simpa using hΨ)
  simpa using h

omit [FiniteDimensional ℝ W] in
/-- The full augmented flow slice's `ContDiffOn 1` assembled from its base and tangent
projections (via `contDiffOn_prod_of_components`). The base projection is
`stateFlow_contDiffOn_one_two` at the augmented level; the tangent projection `htan` is the
base projection of the doubly-augmented flow — the next tower level. -/
theorem augmentedFlow_contDiffOn_one_of_components
    {g : W → W}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {w₀ : W} {a r L K : ℝ≥0}
    (hf : IsPicardLindelof (variationalVectorField (fun _ : ℝ => g) (fun _ : ℝ => fderiv ℝ g))
      t₀ (w₀, (1 : W →L[ℝ] W)) a r L K) {t : ℝ}
    (hbase : ContDiffOn ℝ (1 : ℕ)
      (fun z : W × (W →L[ℝ] W) =>
        ((toStatePreservingLipschitzLocalFlowSolution hf).toContinuousLocalFlowSolution.flow (z, t)).1)
      (closedBall (w₀, (1 : W →L[ℝ] W)) r))
    (htan : ContDiffOn ℝ (1 : ℕ)
      (fun z : W × (W →L[ℝ] W) =>
        ((toStatePreservingLipschitzLocalFlowSolution hf).toContinuousLocalFlowSolution.flow (z, t)).2)
      (closedBall (w₀, (1 : W →L[ℝ] W)) r)) :
    ContDiffOn ℝ (1 : ℕ)
      (fun z : W × (W →L[ℝ] W) =>
        (toStatePreservingLipschitzLocalFlowSolution hf).toContinuousLocalFlowSolution.flow (z, t))
      (closedBall (w₀, (1 : W →L[ℝ] W)) r) :=
  contDiffOn_prod_of_components hbase htan

/-- **Unconditional base flow `ContDiffOn 2`** (modulo the dischargeable augmented-flow
input). Given the level-0 augmented flow's `ContDiffOn 1` (`hα0`, supplied at the augmented
level by `stateFlow_contDiffOn_one_two`), the real base flow slice is `ContDiffOn 2` on the
ball — with no flow-uniqueness and no over-strong hypothesis. The chain: the tangent's
`ContDiffOn 1` comes from `hα0` via `tangent_contDiffOn_of_augmentedFlow_contDiffOn` (a pure
composition, the tangent being definitionally `(α0.flow((x,1),t)).2`), then the
tangent-keyed recursion step lifts the base flow to `ContDiffOn 2`. -/
theorem baseFlow_contDiffOn_two
    {g : W → W} (hg : ContDiff ℝ 3 g)
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {w₀ : W} {a0 r0 r0' L0 K0 : ℝ≥0}
    (hf0 : IsPicardLindelof
      (variationalVectorField (fun _ : ℝ => g) (fun _ : ℝ => fderiv ℝ g))
      t₀ (w₀, (1 : W →L[ℝ] W)) a0 r0 L0 K0)
    (hball0 : ∀ y ∈ closedBall w₀ r0',
      (y, (1 : W →L[ℝ] W)) ∈ closedBall (w₀, (1 : W →L[ℝ] W)) r0)
    {t : ℝ} (ht : t ∈ Icc (t₀ : ℝ) tmax)
    (hα0 : ContDiffOn ℝ (1 : ℕ)
      (fun z : W × (W →L[ℝ] W) =>
        (toStatePreservingLipschitzLocalFlowSolution hf0).toContinuousLocalFlowSolution.flow (z, t))
      (closedBall (w₀, (1 : W →L[ℝ] W)) r0)) :
    ContDiffOn ℝ 2
      (fun y : W =>
        (ofProductContinuousLocalFlowSolution
          (toStatePreservingLipschitzLocalFlowSolution hf0).toContinuousLocalFlowSolution hball0).flow
            (y, t))
      (ball w₀ r0') := by
  have hg2 : ContDiff ℝ 2 g := hg.of_le (by norm_num)
  have htan : ContDiffOn ℝ (1 : WithTop ℕ∞)
      (fun x : W =>
        (ofProductContinuousLocalFlowSolution
          (toStatePreservingLipschitzLocalFlowSolution hf0).toContinuousLocalFlowSolution hball0).tangent
            x t)
      (ball w₀ r0') := by
    have hb := tangent_contDiffOn_of_augmentedFlow_contDiffOn
      (f := fun _ : ℝ => g) (Df := fun _ : ℝ => fderiv ℝ g)
      (x₀ := w₀) (r := r0')
      (toStatePreservingLipschitzLocalFlowSolution hf0).toContinuousLocalFlowSolution hball0
      (by simpa using hα0)
    exact hb.mono ball_subset_closedBall
  have h := baseFlow_contDiffOn_succ_of_tangent_contDiffOn (n := 1) hg2 hf0 hball0 ht
    (by simpa using htan)
  simpa using h

/-- **Base flow `ContDiffOn 2` from the embedded augmented slice** — the correctly-weakened
interface. The hypothesis is only the *embedded* slice `x ↦ (underlying flow)((x,1),t)` being
`ContDiffOn 1` on `ball w₀ r0'` (not the full augmented flow on the whole augmented ball).
This is the minimal input the recursion actually consumes: the tangent and the base flow's
own packaging both factor through the embedded slice via `tangent_contDiffOn_of_embedded`.
This is the right interface for the final tower discharge — the embedded slice reconstructs
from the next level's two `ofProduct` projections. -/
theorem baseFlow_contDiffOn_two_from_embedded
    {g : W → W} (hg : ContDiff ℝ 3 g)
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {w₀ : W} {a0 r0 r0' L0 K0 : ℝ≥0}
    (hf0 : IsPicardLindelof
      (variationalVectorField (fun _ : ℝ => g) (fun _ : ℝ => fderiv ℝ g))
      t₀ (w₀, (1 : W →L[ℝ] W)) a0 r0 L0 K0)
    (hball0 : ∀ y ∈ closedBall w₀ r0',
      (y, (1 : W →L[ℝ] W)) ∈ closedBall (w₀, (1 : W →L[ℝ] W)) r0)
    {t : ℝ} (ht : t ∈ Icc (t₀ : ℝ) tmax)
    (hemb0 : ContDiffOn ℝ (1 : WithTop ℕ∞)
      (fun x : W =>
        (toStatePreservingLipschitzLocalFlowSolution hf0).toContinuousLocalFlowSolution.flow
          ((x, (1 : W →L[ℝ] W)), t))
      (ball w₀ r0')) :
    ContDiffOn ℝ 2
      (fun y : W =>
        (ofProductContinuousLocalFlowSolution
          (toStatePreservingLipschitzLocalFlowSolution hf0).toContinuousLocalFlowSolution hball0).flow
            (y, t))
      (ball w₀ r0') := by
  have hg2 : ContDiff ℝ 2 g := hg.of_le (by norm_num)
  have htan : ContDiffOn ℝ (1 : WithTop ℕ∞)
      (fun x : W =>
        (ofProductContinuousLocalFlowSolution
          (toStatePreservingLipschitzLocalFlowSolution hf0).toContinuousLocalFlowSolution hball0).tangent
            x t)
      (ball w₀ r0') :=
    tangent_contDiffOn_of_embedded
      (toStatePreservingLipschitzLocalFlowSolution hf0).toContinuousLocalFlowSolution hball0 hemb0
  have h := baseFlow_contDiffOn_succ_of_tangent_contDiffOn (n := 1) hg2 hf0 hball0 ht
    (by simpa using htan)
  simpa using h

end Autonomous

/-! ### Prolongation level: the augmented flow is spatially `C¹` by instantiation

The flow-derivative extraction `stateFlow_*_two` is generic in the model space, so it
applies verbatim at the *augmented* space `V × (V →L[ℝ] V)`. The level-1 augmented field
`(g, fderiv g)` is `C²` whenever `g` is `C³`, so the augmented (product) flow `Ψ0` that
the bootstrap tower consumes is itself spatially `C¹` — with no new lemma, only an
instantiation. This is the concrete confirmation that the tower's higher-level inputs are
reachable. -/

section Prolongation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [CompleteSpace V]

open PoincareCurvature.VariationalSmoothness

omit [FiniteDimensional ℝ V] [CompleteSpace V] in
/-- The level-1 augmented field `(g, fderiv g)` is `C²` when `g` is `C³`. -/
theorem augmentedField_contDiff_two
    {g : V → V} (hg : ContDiff ℝ 3 g) :
    ContDiff ℝ 2 (fun z : V × (V →L[ℝ] V) => (g z.1, (fderiv ℝ g z.1).comp z.2)) := by
  have hg2 : ContDiff ℝ 2 g := hg.of_le (by norm_num)
  have hDg2 : ContDiff ℝ 2 (fun x => fderiv ℝ g x) := (contDiff_succ_iff_fderiv.mp hg).2.2
  exact contDiff_variationalField hg2 hDg2

/-- **The level-1 augmented flow is spatially `C¹`.** Instantiating the generic
`stateFlow_contDiffOn_one_two` at the augmented space `V × (V →L[ℝ] V)` with the level-1
field `G1 = (g, fderiv g)` (which is `C²` from `g : C³`), the flow of `G1` — the product
flow `Ψ0` of the bootstrap — is `ContDiffOn 1` on its ball. Reachable purely by
instantiation, no new lemma. -/
theorem level1_flow_contDiffOn_one
    {g : V → V} (hg : ContDiff ℝ 3 g)
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {w₀ : V × (V →L[ℝ] V)} {a r r' L K : ℝ≥0}
    (G1 : (V × (V →L[ℝ] V)) → (V × (V →L[ℝ] V)))
    (hG1 : G1 = fun z : V × (V →L[ℝ] V) => (g z.1, (fderiv ℝ g z.1).comp z.2))
    (hf : IsPicardLindelof
      (variationalVectorField (fun _ : ℝ => G1) (fun _ : ℝ => fderiv ℝ G1))
      t₀ (w₀, (1 : (V × (V →L[ℝ] V)) →L[ℝ] (V × (V →L[ℝ] V)))) a r L K)
    (hball : ∀ y ∈ closedBall w₀ r',
      (y, (1 : (V × (V →L[ℝ] V)) →L[ℝ] (V × (V →L[ℝ] V)))) ∈
        closedBall (w₀, (1 : (V × (V →L[ℝ] V)) →L[ℝ] (V × (V →L[ℝ] V)))) r)
    {t : ℝ} (ht : t ∈ Icc (t₀ : ℝ) tmax) :
    ContDiffOn ℝ 1
      (fun y : V × (V →L[ℝ] V) =>
        (ofProductContinuousLocalFlowSolution
          (toStatePreservingLipschitzLocalFlowSolution hf).toContinuousLocalFlowSolution hball).flow
            (y, t))
      (ball w₀ r') := by
  have hG1_c2 : ContDiff ℝ 2 G1 := by rw [hG1]; exact augmentedField_contDiff_two hg
  exact stateFlow_contDiffOn_one_two hG1_c2 hf hball ht

end Prolongation

end PoincareCurvature.FlowSpatialC1
