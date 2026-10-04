# Literal C² metric and fixed-background local tensor heat

This supporting source candidate builds on immutable master
`99aa49484f8decc5a6344591d5e319011ebea73b`. Structured same-repository
builds-on provenance is recorded in `curvature/formalization.yaml`; existing
attribution, licensing, registry selections and completion gates are preserved.
No registry intake, new submission identity or registration is included.

## Constructed endpoint

`RicciFlow.AnalyticPDE.exists_fixedBackground_actualLocalTensorHeat` takes an
arbitrary `Bundle.ContMDiffRiemannianMetric I 2 E TM`. It installs precisely
`RiemannianBundle ⟨g₀.toRiemannianMetric⟩` and its C²/C¹ metric instances.
It does not replace or smooth `g₀`, require Hölder continuity of its Hessian,
or take an ambient Riemannian metric as input.

The remaining geometric premises are a finite-dimensional complete real model,
a smooth Hausdorff sigma-compact manifold, and `I.Boundaryless`. Tangent-bundle
C³ and C² regularity are derived from manifold smoothness. Neither compactness,
nonemptiness, positive rank, a connection, induced-connection regularity,
assembled coefficient regularity nor a local solver is supplied by the caller.

The proof first chooses one actual global C² affine connection from
`exists_contMDiffAffineConnection_two`. It returns its C¹ downgrade, the actual
induced two-tensor C²/C¹ connections and three-tensor C¹ connection. This choice
precedes the universal chart, frame, finite model basis and interval parameters.
The auxiliary connection is not asserted to be the Levi--Civita connection of
`g₀`, metric compatible, or torsion free.

For every center and atlas frame containing that center, it then derives C¹
regularity of the actual principal, first-order and zeroth-order coefficient
fields on the chart/frame domain. The principal field has no connection
argument: its inverse Gram matrix is computed from the literal metric `g₀`.
The first/zero fields use that same metric and the single chosen connection.

For each interval `t₀ < T` and exponent `0 < α < 1`, the theorem constructs
localized quantitative coefficient data, a cutoff equal to one on the
normalized closed unit ball, and a positive radius. Every smaller positive
scale has exact scale-correct actual-field agreement on that ball and a bounded
linear map

- from `ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α` on the finite cylinder
- to `FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α`

The actual localized coordinate Cauchy operator composed with this map is the
identity, and the initial trace composed with the map is zero. Scaling and
physical-domain agreement are supplied by the existing
`FieldsAgreeOnUnitBall` predicate, without substituting an unscaled operator.

## Verification boundary

No Lean elaboration, axiom check or package build has been run for this source
candidate locally: the geometric imported oleans and official Lean 4.33 are
not available, and a heavy dependency rebuild was intentionally avoided.
A lexical forbidden-term scan and fast unchanged completion audit can check
source hygiene and the OPEN boundary only; they do not certify this theorem.
The new exact-head workflow builds the producer under pinned Lean 4.33, prints
its full inferred type, checks its axiom surface, and runs the unchanged full
package audit. Exact-head independent source review and actual Lean-4.33
verification remain required before publication/merge decisions.

The historical candidate `3f41e03fc6481a9b41abb27a2af8bac1f864a861`
reached an actual Lean-4.33 hosted producer build. Its imported geometric,
regularity and localization modules compiled, but the new producer failed:
its three-tensor fiber instance aliases needed the Riemannian metric before
they were installed, finite coefficient norm aliases were missing, and the
actual coefficient-regularity theorem was referenced in the wrong namespace.
The repair installs the tensor instances inside the literal `g₀` metric scope,
uses the existing finite coefficient norms, and corrects that namespace.
No input hypotheses, source spaces, coefficient formulas, or solver conclusions
were weakened. The repaired source still requires independent review and a
fresh actual Lean-4.33 build; the historical failed run is not certification.

## Still open

This is local linear theory with the existing unweighted Hölder source/solution
spaces. It supplies no arbitrary-C² initial extension, weighted positive-time
nonlinear source estimates, finite-atlas gluing of a Ricci--DeTurck solution,
metric positivity, joint parabolic regularity, gauge construction, or general
Ricci-flow local existence/uniqueness.

`I.Boundaryless` is stronger than the canonical theorem's approved
`BoundarylessManifold I M` premise. No implication between them is asserted or
installed as a global instance. The canonical theorem and its contract are
untouched. Point 4 remains **OPEN**.
