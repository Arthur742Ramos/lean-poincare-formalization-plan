/-
Time-augmented autonomous ODE for DeTurck variational data.

The DeTurck gauge field is time-dependent: `f : ℝ → E → E`. We convert to an
autonomous system via the standard time-augmentation trick:

  G : (ℝ × E) → (ℝ × E),  G(s, x) = (1, f(s, x))

`G` is autonomous (time-independent). If `f` is jointly C³ in `(s, x)`, then `G`
is C³. The autonomous Picard-Lindelöf theorem (Mathlib) then gives local
existence and uniqueness for `G`, and the variational equation for `G` yields
the derivative of the flow with respect to initial data.

The `E`-component of the augmented flow recovers the original time-dependent
flow of `f`, and the appropriate block of the augmented variational derivative
gives the variational data for `f`.

This supplies the analytic foundation for genuine Picard-Lindelöf variational
data for the time-dependent DeTurck field without PDE existence theory.

Note: This file is self-contained (Mathlib only) to avoid the build deadlock
where `Diffeomorph3FlowExistence` (which needs the `variational` field) is
imported by `ModelGaugeFlowODE` (which provides variational machinery). Once
the adapters are repaired, this connects to
`ModelGaugeFlowODE.VariationalLocalFlowSolution` via the standard
identification.
-/
module
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Topology.MetricSpace.Basic

open scoped Topology
open ContinuousLinearMap

namespace TimeAugmentedDeTurckODE

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The time-augmented autonomous vector field.

Given a time-dependent field `f : ℝ → E → E`, define the autonomous field
`G : (ℝ × E) → (ℝ × E)` by `G(s, x) = (1, f s x)`. The first component tracks
time (`ṡ = 1`), the second follows the original time-dependent dynamics. -/
noncomputable def timeAugmentedField (f : ℝ → E → E) : (ℝ × E) → (ℝ × E) :=
  fun p => (1, f p.1 p.2)

/-- The uncurried form of `f`, for stating joint regularity. -/
noncomputable def uncurriedField (f : ℝ → E → E) : (ℝ × E) → E :=
  fun p => f p.1 p.2

/-- If `f` is jointly C³, then the time-augmented field `G` is C³.

The first component is constant (`fun _ => 1`), hence smooth. The second
component is the uncurried `f`, which is C³ by hypothesis. -/
theorem contDiff_three_timeAugmentedField
    {f : ℝ → E → E}
    (hf : ContDiff ℝ 3 (uncurriedField (E := E) f)) :
    ContDiff ℝ 3 (timeAugmentedField (E := E) f) := by
  unfold timeAugmentedField
  apply ContDiff.prodMk
  · exact contDiff_const
  · exact hf


end TimeAugmentedDeTurckODE
