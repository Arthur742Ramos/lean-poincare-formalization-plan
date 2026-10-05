# Independent source-only derivative review

Reviewed on 2026-10-05. This is a source inspection, not Lean elaboration,
kernel verification, or a completed Poincaré campaign proof. No compiler,
proof runtime, toolchain, installation, download, cache, publication, CI, or
repository-tree action was used. Only this review file was added to the
isolated artifact.

## Reviewed source identity

- `WeightedDuhamelHessianDerivative.lean`, 154 lines, SHA256
  `19e8ec44954e3c1ad6b75042465a2251de48124ab0ea923a1b90dd24e422a381`
- `WeightedDuhamelFrechet.lean`, 304 lines, including the direct `fderiv`
  compatibility addition, SHA256
  `a817cc34a6be25422e6bef2f30faaba65aaccea706b0204eab671b5e9b02c900`

The four inherited candidate files were inspected. Dependency inspection
included the retained db584 `ParametricIntervalIntegral`, `ParametricIntegral`,
and `ContDiff.Defs` snapshots, the exact project `EuclideanDuhamelFrechet` and
`FiniteCoordinateFrechet` snapshots, and the relevant Gaussian derivative,
moment, measurability, and first-Duhamel-derivative declarations in the retained
project snapshots. The scalar integral and real-power API call sites were
also compared with the retained pinned source.

## Finding

Favorable source-level review: no concrete mathematical error, assumption
smuggling, or identified pinned-API signature mismatch was found. The new
source supplies a coherent proof candidate for the requested actual weighted
coordinate derivative, actual second Fréchet derivative, and fixed-time
`ContDiff ℝ 2` claims. It does not establish that Lean accepts the source.

1. **Forcing hypotheses.** Every analytic theorem retains only `t₀ < t`,
   `0 < α < 1`, continuous BCF-valued forcing, its actual global bound,
   `L ≥ 0`, and the weighted coordinate Hölder condition on `Ioo t₀ t`.
   There is no derivative witness, solver identity, pre-assumed envelope
   integrability, solver/inverse bound, uniform unweighted Hölder constant,
   initial positive-Hölder premise, or positive-dimension premise.
2. **Actual differentiation.** Derivative lines 40–100 instantiate the exact
   pinned `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
   signature. Base gradient integrability follows from the bounded-forcing
   project theorem. The positive-time derivative is the project's genuine
   Gaussian Hessian derivative; the new domination follows from Gaussian
   cancellation and the inherited proved-integrable weighted envelope.
3. **Quantifier order.** The derivative bound and derivative existence are
   proved as `∀ᵐ s, s ∈ Ι t₀ t → ∀ a ∈ univ, ...` on a single full-measure
   time set. This matches the pinned theorem and does not exchange an
   uncountable spatial quantifier with an almost-everywhere quantifier.
4. **Endpoints.** `Ι t₀ t = Ioc t₀ t` follows from `ht.le`. The lower endpoint
   is excluded by the carrier, and only the terminal singleton is deleted
   using its zero volume. Integrability near both endpoints is independently
   supplied by the scalar two-half-interval argument. No neighborhood is
   deleted, and neither endpoint's Hölder value is assumed.
5. **Diagonal and orientation.** The actual Gaussian theorem covers both
   `j = k` and `j ≠ k`. The partial derivative theorem needs no distinctness
   premise. Differentiating gradient component `k` in coordinate `j` yields
   entry `Hjk`; the curried operator is `H(v)(w) = Σj,k Hjk vj wk`. The
   explicit `coordinateHessianCLM_single_left` row lemma agrees with the
   existing project definitions, and its use inside `HasFDerivAt` is
   definitionally compatible with the summed row functional.
6. **Actual second derivative.** Fréchet lines 204–241 first prove
   `fderiv ℝ U = heatDuhamelGradientCLM` at every point from the genuine
   first-derivative theorem. They then differentiate that function identity
   and state the resulting iterated `fderiv` equality. The additional
   hypotheses are unchanged. The `ContDiff` assembly matches the exact
   db584 successor and order-one characterizations.
7. **Rank zero.** The finite-coordinate bridge explicitly proves its
   `n = 0` case using the subsingleton domain and zero linear map. The new
   operator and norm statements use empty finite sums and no dimension
   lower bound. Coordinate-entry statements are vacuous at rank zero, but
   the Fréchet and `ContDiff` statements are not excluded.

## Remaining verification boundary

Lean 4.33.0/db584 elaboration of all six files and their project imports is
still required. Import visibility, coercions, local operator-space instances,
simplifier behavior, and tactic goals remain untested. The inherited
dominated-continuity, `Integrable.mono'`, and BCF-constructor patterns agree
with the exact project source, but their complete independent Mathlib files
are not present here. No complete transitive API audit is claimed.

This leaf is fixed-final-time spatial regularity. It proves no strong C²
zero trace, time/slab Hölder estimate, evolution identity, weighted solver
construction, compact-atlas result, metric positivity, geometric readout,
endpoint derivative contract, or weak-competitor uniqueness theorem. The
interval-length-independent Hessian bound alone does not vanish as
`t → t₀`. Point 4 remains open.
