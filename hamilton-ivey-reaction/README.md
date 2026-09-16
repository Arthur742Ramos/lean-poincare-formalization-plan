# Hamilton--Ivey curvature-ODE pinching

This standalone Lean project formalizes the nonlinear pointwise calculation at
the heart of the three-dimensional Hamilton--Ivey pinching estimate.  It uses
the normalization of Chen--Xu--Zhang: if
`lambda >= mu >= nu` are the curvature-operator eigenvalues, the operator's
value on a tangent plane is twice its sectional curvature and

```text
R = lambda + mu + nu
```

is scalar curvature.

For `K > 0`, `t >= 0`, and `nu < 0`, define the Hamilton--Ivey defect

```text
w = R/(-nu) - log(-nu) + 3 + log(K/(1 + Kt)).
```

The development expands the quotient and logarithm chain rules along the
diagonal three-dimensional curvature reaction ODE

```text
lambda' = lambda^2 + mu*nu
mu'     = mu^2 + lambda*nu
nu'     = nu^2 + lambda*mu
```

and proves that the resulting derivative is exactly

```text
-2*nu - K/(1 + Kt)
  + ((lambda - nu)(mu - nu)/nu^2) R.
```

It proves that, assuming the scalar lower barrier
`R >= -3K/(1 + Kt)`, a negative defect
forces `K/(1 + Kt) < -nu` and makes this complete reaction term at least
`(-nu)/9`, hence strictly positive.  The proof includes the global analytic
inequality

```text
exp(2) * (log s)^2 <= 4s,  s > 1,
```

and the ordered-eigenvalue arithmetic-mean estimate used in the published
maximum-principle argument. The selected theorem then applies a proved
one-dimensional invariant-region principle: every differentiable ordered
solution of the displayed curvature ODE that stays in `nu < 0` and starts with
`nu(0) >= -K` satisfies both the scalar lower barrier and `w(t) >= 0`
throughout its interval.

## Exact status

This is a proved Hamilton--Ivey **curvature-ODE pinching theorem**, not yet the
full geometric Hamilton--Ivey estimate for Ricci flows.  The full theorem also
requires:

1. the curvature-operator evolution equation for an intrinsic
   three-dimensional Ricci flow;
2. a scalar-curvature lower-barrier maximum principle; and
3. a tensor/eigenvalue parabolic maximum principle, with localization for the
   complete noncompact theorem.

Those layers do not currently exist in this repository and are not hidden in
the theorem's hypotheses.  The new general one-dimensional barrier lemma in
`HamiltonIveyReaction/Reaction.lean` is groundwork for the ODE/invariant-region
stage, but it does not substitute for the geometric PDE maximum principle.

## Independence

The proof was developed from the primary mathematical argument and depends
only on pinned Mathlib.  It does not import, vendor, copy, or adapt code from
any external Ricci-flow formalization repository.  See `PROVENANCE.md`.

## Reproduction

```sh
lake exe cache get
lake build
python3 scripts/check-package.py
python3 scripts/check-axioms.py
lake env lean scripts/check-closed-statement.lean
```

The Comparator-selected declaration is
`HamiltonIveyChallenge.hamiltonIveyODEPinching`; its complete closed
statement is `HamiltonIveyChallenge.completeStatement`.

Preparation and local verification do not authorize a Palomar intake or
public registration.
