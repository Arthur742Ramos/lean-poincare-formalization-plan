# Conventional Ricci--DeTurck principal/remainder split

The candidate supporting file
`RicciFlow/AnalyticPDE/RicciDeTurckPrincipalRemainder.lean` proves an algebraic
principal-part milestone for the actual finite-dimensional reaction defined in
`GenuineRicciDeTurckFiberMap.lean`. It does not construct a PDE solution.

## Statement and dependency map

The existing coordinate vector is the positive conventional contraction

`W^k = sum_{a,b} g^{ab} (Gamma^k_{ab} - GammaBar^k_{ab})`.

The negative recovery gauge is separate. The legacy intrinsic raised-trace field
has a different slot contraction and is not substituted for this vector.

The proof uses the existing `RicciDeTurckLinearization.lean` building blocks:

- `phiRDMatrix_pureSecondJet_affine`: the finite reaction is affine when only
  its independent Hessian slot changes
- `dRicci2_bridge` and `dCorrection2_bridge`: actual coordinate second-order
  terms in cancellation normal form
- `invMetricOfJet_contract` and `invMetricOfJet_symm`: actual inverse-metric
  contraction and symmetry, derived from a symmetric invertible metric value
- `deturckPrincipalPart_identity`: finite-sum cancellation of the Ricci and
  conventional DeTurck second-order terms

`firstOrderJet j` retains `j.val` and `j.deriv1` and sets `j.deriv2` to zero.
`secondJetLinearReaction_eq_principal` isolates the algebraic cancellation,
and `phiRDOfJet_eq_principal_add_lowerOrder` then proves

`Phi(j)_{ik} = sum_{p,q} g^{pq} H_{pqik} + Phi(firstOrderJet j)_{ik}`.

The proof requires the metric value to be symmetric and invertible, and requires
both explicit Hessian symmetries:

- derivative-slot interchange: `H_{abce} = H_{bace}`
- tensor-slot interchange: `H_{abce} = H_{abec}`

No first-jet symmetry or derivative compatibility is needed for this algebraic
identity, and no such compatibility is claimed. The theorem that the lower-order
reaction is unchanged when the value and first-derivative slots agree makes its
Hessian independence explicit.

## Background-first-jet correction

In the existing fiber map, `GammaBar` is held constant while forming the spatial
W-derivative. For a spatially varying fixed background connection, the product
rule instead contributes

`-sum_{a,b} g^{ab} partial_m GammaBar^k_{ab}`.

The new `derivDeTurckVectorWithBackgroundJetOfJet` retains this term with an
explicit background-first-jet slot `GammaBar1_{mkab}`. The corresponding
`deTurckCorrectionWithBackgroundJetOfJet` includes all three coordinate
Lie-derivative contributions. Consequently the corrected reaction equals the
existing reaction minus

`sum_l [ g_{lk} sum_{a,b} g^{ab} GammaBar1_{ilab}
       + g_{il} sum_{a,b} g^{ab} GammaBar1_{klab} ]`.

Both terms and their negative sign are proved by expanding those actual
coordinate expressions. The ordinary component product-rule theorem
`hasDerivAt_conventionalContraction` explains the sign using explicitly displayed
primitive component derivative certificates. It does not produce metric or
Christoffel derivative certificates from geometric data.

These background-first-jet terms contain no Hessian slot. The corrected
principal split therefore has the same `g^{-1} H` principal part. Setting the
background-first-jet slots to zero recovers the original fiber map exactly.

## Frozen coefficient remainder

For any fixed coefficient matrix `A`, the theorem
`phiRDWithBackgroundJetOfJet_eq_frozenPrincipal_add_remainder` proves

`Phi_corrected(j) = A:H + (g^{-1} - A):H + lowerOrder_corrected(j)`.

The remainder is explicitly the coefficient-error Hessian term plus the
second-order-free reaction. It is not itself second-order-free unless the
coefficient error vanishes. A finite-sum estimate bounds an output component of
the Hessian error by

`epsilon * sum_{p,q} |H_{pqik}|`

when every inverse-metric coefficient error has absolute value at most epsilon.
No solution-region or smallness estimate is assumed proved by this identity.

## Verification and remaining boundary

The principal/remainder module has not been compiled. A development-only
Lean-4.35.0-rc2 closure attempt stopped in the unchanged `HeatKernel1D` dependency
on upstream typeclass and finite-product API incompatibilities, before reaching
this module. This is not a theorem verdict or final verification.
The independent exact Lean-4.33 workflow
`.github/workflows/point4-principal-remainder.yml` first compiles the pure jet
module and checks its eleven principal/remainder axiom surfaces before running
the unchanged full-package Point-4 audit. It does not import or verify the
separate new metric-contraction adapter. Verification remains pending until
that exact-head run succeeds.

The following remain separate mathematical obligations:

- construct actual holonomic coordinate jets from sufficiently regular metrics
- derive the inverse-metric and Christoffel derivative slots from those metrics
- produce background-first-jet slots from the fixed background connection
- identify the corrected coordinate expressions with the actual conventional
  manifold connection difference, Ricci tensor, and Lie derivative
- identify the selected frozen contraction with the existing tensor-heat
  generator in the same chart/frame and account for lower-order frame terms
- prove the required nonlinear estimates, positive-metric invariant region, and
  quasilinear parabolic existence/uniqueness theorem

The independent-slot `Jet2Section` carrier supplies none of these identities by
itself. The canonical target and completion auditor are unchanged. Point 4
remains **OPEN**.
