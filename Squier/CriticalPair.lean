module

public import Mathlib
public import Squier.Newman
public import Squier.Branching
@[expose] public section

/-! # The critical pair lemma -/

namespace Squier

variable {α : Type*}

theorem critical_pair_lemma (R : Finset (List α × List α)) :
    LocallyConfluent R ↔ ∀ b ∈ criticalBranchings R, Joinable R b.tgt₁ b.tgt₂ := by
  sorry

theorem confluent_iff_criticalPairs_joinable (R : Finset (List α × List α))
    (hR : Terminating R) :
    Confluent R ↔ ∀ b ∈ criticalBranchings R, Joinable R b.tgt₁ b.tgt₂ := by
  sorry

end Squier
