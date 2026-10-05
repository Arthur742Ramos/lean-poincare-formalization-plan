# Supporting two-sided initial heat derivative

Status: source candidate only, **not compiled**. Independent review and an
actual Lean 4.33.0 exact-head CI run remain required. This document does not
qualify the source as verified, publish it, or close Point 4.

## Literal construction

For `D : EuclideanBoundedC2Data n`, let

`g = ∑ k : Fin n, D.second k k`.

The `D.second` entries are the bounded continuous **actual** successive
coordinate derivatives from the inherited data structure. The new function
is a bounded-continuous spatial function at every real time:

- `t ≥ 0`: exactly `heatFlowPathBcf D.value t`, the inherited closed heat path
- `t < 0`: `D.value + t • heatSemigroupNDbcf (-t) g`

Thus the literal value at zero and actual positive-time Euclidean heat
semigroup are preserved. The negative-time branch evaluates the heat
semigroup only at strictly positive heat time `-t`; it never solves backward
heat and does not impose differentiability on `g`.

## Genuine proof route

The source reads and uses the existing theorem bodies, including:

1. `EuclideanBoundedC2Data.hasDerivWithinAt_heatFlowPathBcf_apply_zero`:
   the existing right initial derivative is the actual diagonal Hessian trace
2. `tendstoUniformlyOn_heatSemigroupND_zero`: the Gaussian approximate
   identity is proved from the actual normalized product kernel and its
   finite coordinate moments, using an arbitrary continuity modulus
3. `heatSmoothedC2Data`: actual derivative witnesses for positive heat
   smoothing, established from the Gaussian gradient and Hessian formulas
4. `norm_heatSemigroupNDbcf_le`: the actual heat maximum principle gives
   a norm bound for the negative-time perturbation

On the left, the difference quotient is exactly `heat(-t) g`. Its limit at
each fixed spatial point is `g` by the approximate identity on the compact
singleton. The source joins that left derivative to the inherited right
derivative through the unchanged ordinary `HasDerivAt` interface.

The pointwise ordinary derivative theorem requires only literal bounded C²
data, a slightly stronger result than the campaign's uniformly continuous
Hessian scope. The separate theorem
`uniformContinuous_initialLaplacianBcf` derives uniform continuity of `g`
from uniform continuity of the actual Hessian entries. It assumes neither
spatial differentiability nor a positive Hölder exponent for the generator.

## Slice regularity and rank zero

`negativeHeatC2Data` combines the original bounded actual first and second
coordinate derivatives with the corresponding **actual** derivatives of
`heat(-t) g`. `twoSidedHeatC2Data` gives the same kind of bounded C² witness
for every fixed real time. Its value is proved equal to the defined path.

The inherited smoothing constructor accepts exponent zero, using the
oscillation bound derived here from boundedness. This is no positive initial
Hölder hypothesis. The empty-coordinate case is proved separately by equality
of all points in `Fin 0 → ℝ`, rather than assuming a positive dimension.
The focused probe explicitly checks ordinary derivative zero and negative
slice witnesses in rank zero.

The negative perturbation satisfies

`‖path(t) - D.value‖ ≤ |t| * ‖g‖`.

This yields value sup-norm continuity at zero and can support later local
positivity arguments. A cutoff for far-negative times, global positivity,
and sup-norm convergence of the *negative-time Hessian* have not been proved
in this module. Fixed-slice C² regularity is distinct from two-sided C²
path continuity.

## Boundaries and remaining gates

This module is a supporting **linear Euclidean** heat continuation. It is
not a canonical nonlinear or manifold solution and proves no gauge bridge.
Weak competitors, common closed intervals, ordinary derivative requirements,
the canonical target, inherited pins, root imports/metadata, and all inherited
workflows remain untouched. The release integration changes only the inherited
C2 inventory guard by a digest-pinned, count-one insertion; every existing
source/evidence gate is retained. No change is made to active PR 130 or the manifold heat bridge.

Before integration or qualification:

- Independently review the mathematical and source-level continuation
- Compile the module and focused probe using the pinned Lean 4.33.0 toolchain
- Check the compiled axiom surfaces, allowing only `propext`,
  `Classical.choice`, and `Quot.sound`
- Run the unchanged full Point-4 audit on the exact candidate and preserve
  its honest OPEN/CLOSED result
- Keep public publication and any registry action separate; this source-only
  work performs neither

## Source provenance

The candidate is isolated on exact verified master
`e6b54dd0d7e73a51eb8efb083764b68ae8305a5a` of
`Arthur742Ramos/lean-poincare-formalization-plan`. All 1,640 inherited files other than the C2 inventory guard are
inherited verbatim, with modes preserved. The sole guard insertion is exactly
reconstructed from the immutable master guard by the new source guard. The new module imports existing verified heat results;
it is not a new registry subproject or a submission identity. If a separate
submission is later proposed, the repository's structured provenance and
new-entry rules apply at that time.

The original isolated R1 patch remains historical and unchanged (SHA256
`aeb8a459b25e3eb45bf05dc8763f7ec00552a01136e4fe992d19f52e152bd1c6`).
Its module and full probe are byte-identical in this source-only release.
See [release integration](two-sided-heat-release-integration.md) and the
[structured source dossier](two-sided-initial-heat/formalization.yaml) for
the exact inherited boundary and pending verification gates.
