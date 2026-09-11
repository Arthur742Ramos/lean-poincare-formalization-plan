# Research-interest case

Bonnet--Myers is a foundational global theorem in Riemannian geometry: a local
positive Ricci lower bound forces the global metric consequences of a sharp
diameter bound and compactness. Myers' 1941 paper introduced the Ricci-curvature
form of the theorem, which remains a basic prototype for converting curvature
information into topology and global metric control.

The selected Lean result is not a scalar proxy or a theorem with the hard
geometry assumed. Its statement quantifies over a smooth Riemannian metric,
constructs the Levi--Civita connection and actual curvature commutator, forms
Ricci as the ordinary trace of `z |-> R(z,a)a`, assumes only metric
completeness plus the classical lower bound, and concludes the sharp diameter
estimate and compactness.

The formalization is substantial because the pinned Mathlib layer does not
provide this end-to-end theorem. The development connects several delicate
interfaces: chart ODEs to global geodesics, intrinsic path length to the induced
distance, completeness to minimizing segments, chartwise broken variations to
the intrinsic second variation, and finite parallel-frame index sums to the
Ricci trace. The selected theorem exposes the whole mathematical result while
the Challenge remains a short Mathlib-only statement.

The result is classical, source-based, and independently proved here. No claim
of mathematical novelty, first formalization, equality rigidity, or sphere
classification is made. Its research interest lies in the complete
kernel-checked formalization of a central global differential-geometric theorem
and in the reusable geodesic/variation infrastructure required to reach it.
