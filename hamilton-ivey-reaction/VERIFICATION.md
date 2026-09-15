# Verification

Current local checks:

- `lake build`: Challenge, Solution, and proof library compile;
- `scripts/check-package.py`: source boundary, proof-hole, pin, and Comparator
  selection checks;
- `scripts/check-axioms.py`: the selected Solution theorem uses exactly
  `propext`, `Classical.choice`, and `Quot.sound`, with a forbidden-axiom
  negative control.
- `scripts/check-closed-statement.lean`: the compiled closed proposition has
  no reachable candidate-defined mathematical data.
- Comparator and NanoDa: an explicit unsandboxed macOS development replay at
  Comparator commit `575674928e239f5bc452aab72d1dd7b0f1326494`,
  Lean4Export commit `15f6055e299ad5b89345e533cc2192f4cc00f659`, and
  NanoDa commit `68d5ca9db226849b41a6fff59d796ff19d0a8840` accepted the solution in both
  NanoDa and Lean's default kernel.

The intentional `sorry` occurs only in `Challenge.lean`.  The implementation
and Solution contain no `sorry`, `admit`, or user axiom.

The real Linux Landrun Comparator replay and the pinned Linux Palomar renderer
remain separate release gates. They must be run against the exact candidate
commit before any intake. No intake or registration is authorized by this
file.
