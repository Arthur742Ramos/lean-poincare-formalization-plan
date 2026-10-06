# Finite-basis regularity bridge

`RicciFlow.SmoothForward.jointlySmoothOn_iff_basis` compares the published
all-vector chart regularity condition with the condition on every pair from
an arbitrary finite real basis. Both sides use exactly
`Ico a terminal ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet`.

The forward implication specializes the two model vectors to basis elements.
For the reverse implication, `chartGramComponent_eq_sum_basis` expands each
vector with `Module.Basis.sum_repr`. On the chart base set, `symmL_apply`
identifies the chart inverse with a continuous linear map. Bilinearity of the
metric then expresses an arbitrary component as a finite double sum of basis
components with constant coefficients. Finite sums and products preserve
`ContMDiffOn`; its congruence theorem transfers that regularity to the original
component on the same domain.

The theorem requires `[Fintype ι]` and a basis `Module.Basis ι ℝ E`. It adds no
positive-rank, compactness, inner-product-model, global-boundaryless or PDE
hypothesis to the published regularity interface. Empty indices are included:
the sum becomes zero, and `Basis.sum_repr` identifies every model vector with
zero. The probe explicitly specializes the result to a basis indexed by
`Fin 0`. An empty manifold makes the chart-point quantifier vacuous.

The interface source is the exact PR135 commit
`229533f83c83e45e8b7725adda50b53d88699aba`. The Mathlib API sources were compared
with commit `db584cd6d46c92f209a44c0f1c829460d327499d`. Compilation uses the
official Lean 4.33 executable and the admitted one-CPU, 3 GiB budget. Each
compiler stage has a five-minute deadline and owned-process cleanup receipts.
The copied Mathlib dependency objects retain their previous development-only
status; this work does not qualify their native source binding.

This equivalence supplies the finite-basis regularity shape needed for a later
upstream comparison. Metric, Ricci, connection and time-API identification and
general Ricci-flow existence remain separate proofs. Both general Point-4
targets remain OPEN. No public source, guard, workflow or prior evidence is
changed by this packet.
