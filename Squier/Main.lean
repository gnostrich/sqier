module

public import Mathlib
public import Squier.Branching
@[expose] public section

/-! # Squier's theorem: generating confluences form a homotopy basis -/

namespace Squier

variable {α : Type*}

theorem squier_homotopy_basis (R : Finset (List α × List α)) (hR : Terminating R)
    (B : Set (Cell R)) (hB : ∀ b ∈ criticalBranchings R, Resolves B b) :
    IsHomotopyBasis B := by
  sorry

theorem squier_finiteDerivationType [Finite α] (R : Finset (List α × List α))
    (hR : Terminating R) (hc : Confluent R) : FiniteDerivationType R := by
  sorry

end Squier
