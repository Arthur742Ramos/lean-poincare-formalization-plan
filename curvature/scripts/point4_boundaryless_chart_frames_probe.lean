import PoincareCurvature.Analysis.PreferredCoordinateFrame

#print axioms PoincareCurvature.BoundarylessChartTransport.isOpen_extChartAt_target
#print axioms PoincareCurvature.BoundarylessChartTransport.extChartAt_target_subset_interior_range
#print axioms PoincareCurvature.BoundarylessChartTransport.mfderivWithin_extChartAt_symm_eq_mfderiv
#print axioms PoincareCurvature.BoundarylessChartTransport.mpullbackWithin_extChartAt_symm_eq_mpullback
#print axioms PoincareCurvature.PreferredCoordinateFrame.frame_eq_inverseChart_derivative
#print axioms PoincareCurvature.PreferredCoordinateFrame.mpullback_frame_eq_const
#print axioms PoincareCurvature.PreferredCoordinateFrame.mvfderiv_frame_eq_fderiv
#print axioms PoincareCurvature.PreferredCoordinateFrame.mlieBracket_frame_eq_zero
#print axioms PoincareCurvature.PreferredCoordinateFrame.toModel_coordinateVector
#print axioms PoincareCurvature.PreferredCoordinateFrame.fderiv_comp_toModel_coordinateVector

#eval IO.println "BOUNDARYLESS_TYPES_BEGIN"
#check @PoincareCurvature.BoundarylessChartTransport.isOpen_extChartAt_target
#check @PoincareCurvature.BoundarylessChartTransport.extChartAt_target_subset_interior_range
#check @PoincareCurvature.BoundarylessChartTransport.mfderivWithin_extChartAt_symm_eq_mfderiv
#check @PoincareCurvature.BoundarylessChartTransport.mpullbackWithin_extChartAt_symm_eq_mpullback
#check @PoincareCurvature.PreferredCoordinateFrame.mpullback_frame_eq_const
#check @PoincareCurvature.PreferredCoordinateFrame.mvfderiv_frame_eq_fderiv
#check @PoincareCurvature.PreferredCoordinateFrame.mlieBracket_frame_eq_zero

#eval IO.println "BOUNDARYLESS_TYPES_END"

open Set
open scoped Manifold ContDiff

-- Existing callers with a boundaryless model obtain the weaker instance.
section ModelBoundarylessRegression
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [I.Boundaryless]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

example : BoundarylessManifold I M := inferInstance

example (p : M) : IsOpen (extChartAt I p).target :=
  PoincareCurvature.BoundarylessChartTransport.isOpen_extChartAt_target p

example {ι : Type*} (p : M) (b : Module.Basis ι ℝ E) {x : M}
    (hx : x ∈ (extChartAt I p).source) (i j : ι) :
    VectorField.mlieBracket I
      (PoincareCurvature.PreferredCoordinateFrame.frame (I := I) p b i)
      (PoincareCurvature.PreferredCoordinateFrame.frame (I := I) p b j) x = 0 :=
  PoincareCurvature.PreferredCoordinateFrame.mlieBracket_frame_eq_zero p b hx i j
end ModelBoundarylessRegression
