module

public import LichnerowiczObata.StatementEquivalence

@[expose] public noncomputable section

namespace LichnerowiczObataEntry.Geometry

universe u v w

/-- The full theorem follows from the original geometric proof through the
proved definitional equivalence; no hypotheses or conclusions are changed. -/
theorem lichnerowiczObata : completeStatement.{u,v,w} := by
  exact completeStatement_proved

end LichnerowiczObataEntry.Geometry
