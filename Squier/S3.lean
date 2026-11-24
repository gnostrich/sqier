module

public import Mathlib
public import Squier.Main
public import Squier.CriticalPair
@[expose] public section

/-! # The example `S₃`: non-degeneracy, convergence, explicit homotopy basis -/

namespace Squier

theorem homotopy_nondegenerate :
    ¬ Homotopic (∅ : Set (Cell s3)) s3StepAAALeft.toPath s3StepAAARight.toPath := by
  sorry

theorem s3_convergent : Terminating s3 ∧ Confluent s3 := by
  sorry

theorem s3_homotopy_basis : IsHomotopyBasis s3Basis := by
  sorry

end Squier
