# Scalar logarithmic resonance milestone

`RicciFlow.C2Resonance` proves four scalar statements: two derivative
formulas, the logarithmic Euler-operator identity, and divergence of the
profile for positive perturbation. The derivative and operator statements
explicitly assume `L ≠ 0`; divergence explicitly assumes `0 < ε`.
The formulas use the real logarithm on its actual Lean domain. A geometric
application would separately require `L = log(1/r) > 0`.

The exact source was compiled with Lean 4.33.0 against the parent-verified
Mathlib db584cd6d46c92f209a44c0f1c829460d327499d cache. Its SHA256 is
f2c0f2ec234e570e626e0ae436a5de156465b15d17b4ca3d73e8ec10b4df61cc.
All four declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
An independent source review approved these scalar statements. A separate
reviewer compiler attempt timed out after 120 seconds with no output, so it
does not constitute an independent build pass. The committed exact-head
import probe, inherited full builds and audits remain mandatory CI gates.

An owned exact rational Fourier calculation independently obtained the
cos(2θ) coefficient `-6/L - 5/(2L²) - 1/(2L³)` for the proposed `f_yy`.
The formal scalar operator identity has the opposite sign, as required by
the proposed radial equation. That symbolic result is algebraic evidence;
the Fourier differentiation itself is not a theorem in this module.

These results do not construct a torus, metric, weak flow, Baire slab,
strong time quotient, Hölder estimate, or nonlinear error bound. They do not
formalize the proposed existence obstruction or refute a contract in Lean.
The original literal-C² contract and canonical Point 4 remain OPEN and
unchanged. The separately named smooth target remains a separate proposal.

The supporting module has no root import. The dedicated workflow builds it
explicitly, checks all four full types and axiom records, and retains the
inherited exact source, full-library, canonical negative and OPEN-audit gates.
Source fixtures exercise rejection logic and supply no kernel evidence.

Immutable dependencies: [repository baseline](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/a0132cd55e2540b2fd26adecea9a07b51f1b8292/curvature)
and [Mathlib calculus](https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis).
This is a supporting milestone and is not a registry submission.

The concrete published smooth support dependency is [PR 135](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/pull/135),
[commit 229533f83c83e45e8b7725adda50b53d88699aba](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/229533f83c83e45e8b7725adda50b53d88699aba/curvature),
tree `5aa2971a0b54b77aaa1bc711b435795d86db6467`. It supplies the reviewed inventory adapter and
actual inherited-main fixtures. Publication of that draft is recorded without
assuming a merge or promoting either general geometric target.
