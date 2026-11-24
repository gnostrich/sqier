module

public import Mathlib
public import Squier.Defs
@[expose] public section

/-! # Classification of local branchings; finiteness of critical branchings -/

namespace Squier

variable {α : Type*}

/-- Every local branching is either trivial (the same step twice), independent, or a critical
branching whiskered by a context `(x, y)`. -/
theorem branching_cases {R : Finset (List α × List α)} {w v₁ v₂ : List α}
    (s₁ : Step R w v₁) (s₂ : Step R w v₂) :
    (s₁.pre = s₂.pre ∧ s₁.rule = s₂.rule) ∨ s₁.Independent s₂ ∨
      ∃ (x y : List α) (b : Branching R), b.IsCritical ∧
        s₁.pre = x ++ b.left.pre ∧ s₁.rule = b.left.rule ∧ s₁.suf = b.left.suf ++ y ∧
        s₂.pre = x ++ b.right.pre ∧ s₂.rule = b.right.rule ∧ s₂.suf = b.right.suf ++ y := by
  sorry

theorem criticalBranchings_finite [Finite α] (R : Finset (List α × List α)) :
    (criticalBranchings R).Finite := by
  sorry

end Squier
