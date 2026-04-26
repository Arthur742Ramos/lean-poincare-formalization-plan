# Lean Formalization Roadmap for the Poincare Conjecture

This repository is a working plan for a serious Lean formalization effort around
the 3-dimensional Poincare Conjecture, with the proof route understood as
Perelman's Ricci-flow-with-surgery program.

The point of this repo is not to claim that the theorem is already formalized.
It is not. The goal here is to break the project into chunks that are large
enough to be independently meaningful, and in many cases paper-worthy in the
style of the Annals of Formalized Mathematics.

## Contents

- `docs/roadmap.md`: the main roadmap, with AFM-scale project slices
- `docs/dependencies.md`: dependency structure and a suggested execution order
- `curvature/`: Lean/mathlib subproject for the front-end connection and
  curvature layers of the roadmap

## Current framing

The roadmap assumes:

- public Lean/mathlib does not yet contain a completed formal proof of the
  Poincare Conjecture
- the real difficulty is not just the final theorem, but the missing geometric
  analysis infrastructure required to even state Perelman's arguments cleanly
- several intermediate deliverables would already be major formalization papers

## Completion standard

A roadmap point counts as complete only when the target mathematical statements
have been fully formalized and proved in Lean. Reusing existing theorems from
mathlib or other Lean libraries is completely acceptable; what matters is that
the final result is backed by actual Lean proofs.

The following do **not** count as completing a roadmap point on their own:

- interfaces or theorem boundaries without proofs
- added axioms or unchecked assumptions
- `sorry` or any other placeholder proof term
- documentation-only or API-only scaffolding

So throughout this repository, “done” means **proved**, not merely packaged or
anticipated.

## Scope

This is intentionally a research-program repository, not an implementation
repository.

The current exception is `curvature/`, which now contains a concrete Lean
package for covariant derivatives along vector fields, the raw curvature
commutator, a bundled curvature tensor, Ricci/scalar curvature, metric
compatibility, Levi-Civita existence and uniqueness, sectional curvature, the
first and second Bianchi identities, and a time-dependent geometry layer for
one-parameter families of sections, connections, smooth metrics, Levi-Civita
families, curvature quantities, and a proof-bearing section-smoothing layer:
local-to-global gluing for smooth vector-bundle sections valued in fiberwise
convex sets, trivial-bundle and open-set smoothing theorems, local smoothing in
bundle trivializations, and a global theorem smoothing continuous bundle
sections while staying inside open fiberwise convex subsets of the total space,
as well as an intrinsic fiberwise-`ε` approximation theorem for continuous
sections of smooth Riemannian vector bundles. There is also an internal
preparatory
point-4 Ricci-flow scaffold file, but it is not part of the public package
boundary and does **not** count as completing point 4 under this repository's
proof-only standard, even though it now contains genuine stationary Ricci-flat,
zero-velocity, and Ricci-tensor-zero special-case theorems at both the metric
and Levi-Civita-connection levels. It also now proves that, once a connection
family is known to be Levi-Civita for a metric family, the Ricci tensor,
Ricci-flow right-hand side, and Ricci-flow equation are independent of which
Levi-Civita family is used, and it packages intrinsic metric-only solution /
local-solution / compact theorem-package wrappers with conversions to and from
the older connection-parametrized boundary. The same intrinsic side now also
packages the canonical stationary local solution attached to
   `InitialValueProblem.IsRicciFlat`, together with metric-only comparison lemmas
   against arbitrary intrinsic zero-velocity or intrinsic-Ricci-zero local
   solutions. A new internal `Geometry.Manifold.RicciFlow.DeTurck` layer also
   packages the intrinsic DeTurck one-form, vector field, correction term, and
   gauge-fixed Ricci-DeTurck right-hand side, together with reduction lemmas
   showing that this gauge-fixed equation collapses back to intrinsic Ricci flow
   whenever the chosen background family is Levi-Civita for the evolving metric.
   That same DeTurck side now also packages background-explicit intrinsic
   Ricci-DeTurck solution / local-solution wrappers, conversions from intrinsic
   Ricci-flow solutions using the chosen Levi-Civita family, and chosen-background
   Ricci-flat stationary comparison lemmas against arbitrary zero-velocity or
   intrinsic-Ricci-zero DeTurck local solutions with Levi-Civita background. It
   now also mirrors the common-time connection-equality consequences on that
   Levi-Civita-background DeTurck side and packages a chosen-background DeTurck
   local-existence/uniqueness theorem package equivalent to the current intrinsic
   Ricci-flow package. A further internal
  `Geometry.Manifold.RicciFlow.GaugeTransport` layer now packages time-dependent
  bundled `C^1` self-map families together with pullback of tangent-bundle
  bilinear tensor fields and evolving metric tensors, proving identity,
  composition, symmetry-preservation, and initial-time invariance lemmas for
  that transport, and it also defines time-dependent gauge-flow / anchored-map
  predicates tying those pullbacks to integral-curve data. It now also packages
  bundled `C^1` self-diffeomorphisms and time-dependent diffeomorphism families,
  together with tangent pushforward / pullback maps and inverse lemmas for the
  induced transport of tangent-vector fields. The diffeomorphism pullback is now
  also identified with mathlib's manifold `VectorField.mpullback`, and a further
  internal `C^2` diffeomorphism layer now packages time-dependent `C^2` gauge
  families, proves that both pullback and pushforward preserve `C^1`
  tangent-vector-field regularity, and records the corresponding pointwise
  differentiability corollaries needed before defining affine-connection
  transport. A first internal
  `Geometry.Manifold.RicciFlow.GaugeReduction` wrapper now specializes those
  objects to the intrinsic DeTurck vector field and proves that anchored gauge
  pullbacks preserve the prescribed initial metric tensor for intrinsic
  Ricci-DeTurck local solutions; it also now has a diffeomorphism-valued DeTurck
  gauge wrapper reducing back to the map-valued one. The internal `C^2`
  diffeomorphism layer has now also crossed onto the connection side: it defines
  a bundled pullback of tangent-bundle covariant derivatives, proves inverse
  identities for pullback/pushforward of vector fields, identifies transport of
  `∇_X Y` under that pullback, proves the corresponding torsion transport
  formula, shows torsion-free affine connections stay torsion-free after
  pullback (under the ambient Riemannian tangent-bundle hypotheses already used
  by the Levi-Civita layer), transports affine-connection difference tensors,
  proves metric compatibility is preserved whenever a chosen target smooth
  metric realizes the pulled-back inner product, lifts that
  metric-compatibility statement slice by slice to time-dependent `C^2`
  diffeomorphism/connection families, now also lifts torsion-free transport
  slice by slice to those time-dependent connection families, specializes that
  family metric-compatibility statement to the actual slicewise pulled-back
  `C^1` metric object, and transports the raw curvature commutator under both
  static and family pullback of the connection, including pointwise formulas
  after applying `pullbackTangent`/`pushforwardTangent`. It now also pushes the
  pulled-back `ricciEndomorphism` forward to the corresponding target-side raw
  curvature operator and identifies the pulled-back `ricciCurvature` with the
  trace of the tangent-map-conjugated endomorphism, again both statically and
  slice by slice for connection families. That new metric is built as a bundled
  `ContMDiffRiemannianMetric I 1`, with coordinate-level `C^1` regularity for
  the pulled-back bilinear form and a wrapper that discharges the earlier
  metric-compatibility hypothesis automatically. Bundled Levi-Civita pullback
  transport now feeds the gauge-reduction layer, where identity diffeomorphism
  gauges convert smooth Levi-Civita-background Ricci-DeTurck local-solution
  packages back into intrinsic Ricci-flow local-existence/uniqueness packages.
  The conditional gauge-reduced package now records the exact non-identity
  gauge obligations whose discharge yields intrinsic and ordinary point-4 theorem
  packages, re-packages the transformed metric as a pulled-back Ricci-DeTurck
  local solution with Levi-Civita pulled-back background, converts that data to
  the generic Levi-Civita-background DeTurck package, compares pulled-back
  backgrounds on common intervals, exposes the gauge ODE and transformed
  Ricci-flow/DeTurck equations on the actual local interval, expands the source
  DeTurck equation into its background-Ricci plus DeTurck-correction form,
  exposes the pointwise gauge-flow derivative, and rewrites transformed velocity
  as `-2` times the trace of the pulled-back Ricci endomorphism in the
  trace-conjugation form supplied by connection transport. The same transport
  layer now also carries connection-difference trace endomorphisms through
  time-dependent pullback and identifies the corresponding pulled-back
  chosen-Levi-Civita/source-background trace with the source DeTurck one-form.
  It also includes a
  theorem-family reduction for all initial data. The
  remaining gap to full point 4 is therefore proving those
  non-identity gauge-equation obligations and the quasilinear parabolic PDE
  existence/uniqueness step needed to produce Ricci-DeTurck solutions.
 The public vector-bundle layer also now
 packages continuous and smooth Riemannian metrics as honest sections of the
bilinear-form hom bundle, with pointwise extensionality lemmas for metric
equality. It also proves finite-dimensional coercivity and operator-norm
open-ball lemmas for positive-definite continuous bilinear forms, lifts that
openness to compact continuous families in `C(K, ·)` and
`BoundedContinuousFunction`, and then transfers it through preferred bundle
trivialization coordinates to the finite-cover `ContinuousSectionSpace` model:
actual positive-definite bilinear-form sections form an open subset there, and
the symmetric locus is now closed there, with continuous Riemannian metrics
landing in the refined symmetric positive-definite locus inside that model. In
particular, the metric locus is now packaged as an open subset of the closed
symmetric section subtype. The same public layer
now also proves existence of global `C^1` affine connections on `C^2` bundle
data and provides the first section-level `C^1` regularity lemmas for the
Levi-Civita correction ingredients (`toDual`, fiberwise composition,
`metricDefectAux`, and torsion on `C^2` vector fields, with the torsion lemma
currently stated on `C^3` manifolds). This still does not prove the actual
Ricci-flow local existence/uniqueness theorem, so point 4 remains open.
