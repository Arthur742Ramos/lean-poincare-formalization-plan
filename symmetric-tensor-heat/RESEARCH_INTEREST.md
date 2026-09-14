# Research-interest case

The connection heat equation on tensor fields is the linear analytic model
behind geometric parabolic equations. For a Levi-Civita connection, its
principal part is the scalar heat operator in every local frame, while the
connection and chart transitions contribute coupled lower-order terms.
Turning that classical sentence into a checked theorem requires a coherent
finite atlas, tensor-frame reconstruction, parabolic Holder Banach spaces,
local Schauder inverses, commutator transport between charts, a small-time
Neumann correction, initial-trace control, and symmetry preservation.

The selected theorem connects those layers in one certificate. Its
Mathlib-only surface states the actual geometric equation: the supplied
two- and three-tensor connections obey their Leibniz formulas, and the rough
Laplacian is the orthonormal trace of the second covariant derivative. The
conclusion constructs the finite-atlas coefficient spaces and proves:

- existence for every symmetric represented spatial datum and source;
- uniqueness of the higher-coefficient witness in the constructed classical
  solution class;
- fiberwise symmetry and the correct initial trace;
- the inhomogeneous geometric tensor heat equation; and
- a global finite-atlas Schauder estimate with the standard linear dependence
  on initial size and source norm.

This is useful infrastructure for Ricci-DeTurck arguments, stability analyses,
and other geometric evolution equations. Hamilton's foundational paper uses
geometric parabolic systems, and DeTurck's reduction makes strict parabolicity
the engine of Ricci-flow local existence. Huang gives a direct modern account
of linear strongly parabolic systems and Schauder estimates on vector bundles
over closed manifolds.

The scope is intentionally narrower than the classical abstract theorem. The
inputs are represented finite-atlas Holder data, uniqueness is within the
constructed coefficient class, and the endpoint is existentially short. No
surjectivity theorem for arbitrary intrinsic Holder sections, arbitrary-time
continuation, nonlinear Ricci-flow theorem, or mathematical novelty is
claimed. Palomar editors remain responsible for assessing research interest.
