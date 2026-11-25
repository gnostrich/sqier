module

public import Mathlib
public import Squier.GrowthDefs

@[expose] public section

namespace Squier

/-- Words avoiding a finite set of factors have a rational generating function. -/
theorem avoidCount_rational {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (List α)) :
    HasRationalGF fun n => (avoidCount F n : ℤ) := by
  sorry

end Squier
