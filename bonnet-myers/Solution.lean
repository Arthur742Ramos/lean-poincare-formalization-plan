import BonnetMyers.Complete

noncomputable section

namespace BonnetMyersEntry

universe u v w

/-- The full independently developed Bonnet--Myers theorem closes the exact
Mathlib-only statement selected in `Challenge.lean`. -/
theorem bonnet_myers : completeStatement.{u,v,w} := by
  exact completeStatement_proved

end BonnetMyersEntry
