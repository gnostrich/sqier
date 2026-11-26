module

public import Mathlib
public import Squier.Defs
@[expose] public section

/-! # Classification of local branchings; finiteness of critical branchings -/

namespace Squier

variable {α : Type*}

/-- Two factorizations of a word have a longest common prefix of their left parts. -/
theorem exists_common_prefix {x₁ x₂ m₁ m₂ : List α} (h : x₁ ++ m₁ = x₂ ++ m₂) :
    ∃ x a₁ a₂ : List α, x₁ = x ++ a₁ ∧ x₂ = x ++ a₂ ∧ (a₁ = [] ∨ a₂ = []) ∧
      a₁ ++ m₁ = a₂ ++ m₂ := by
  rcases List.append_eq_append_iff.1 h with ⟨a, rfl, rfl⟩ | ⟨c, rfl, rfl⟩
  · exact ⟨x₁, [], a, by simp, rfl, Or.inl rfl, by simp⟩
  · exact ⟨x₂, c, [], rfl, by simp, Or.inr rfl, by simp⟩

/-- Two factorizations of a word have a longest common suffix of their right parts. -/
theorem exists_common_suffix {y₁ y₂ m₁ m₂ : List α} (h : m₁ ++ y₁ = m₂ ++ y₂) :
    ∃ y b₁ b₂ : List α, y₁ = b₁ ++ y ∧ y₂ = b₂ ++ y ∧ (b₁ = [] ∨ b₂ = []) ∧
      m₁ ++ b₁ = m₂ ++ b₂ := by
  rcases List.append_eq_append_iff.1 h with ⟨a, rfl, h'⟩ | ⟨c, rfl, h'⟩
  · subst h'
    exact ⟨y₂, a, [], by simp, by simp, Or.inr rfl, by simp⟩
  · subst h'
    exact ⟨y₁, [], c, by simp, by simp, Or.inl rfl, by simp⟩

/-- Every local branching is either trivial (the same step twice), independent, or a critical
branching whiskered by a context `(x, y)`. -/
theorem branching_cases {R : Finset (List α × List α)} {w v₁ v₂ : List α}
    (s₁ : Step R w v₁) (s₂ : Step R w v₂) :
    (s₁.pre = s₂.pre ∧ s₁.rule = s₂.rule) ∨ s₁.Independent s₂ ∨
      ∃ (x y : List α) (b : Branching R), b.IsCritical ∧
        s₁.pre = x ++ b.left.pre ∧ s₁.rule = b.left.rule ∧ s₁.suf = b.left.suf ++ y ∧
        s₂.pre = x ++ b.right.pre ∧ s₂.rule = b.right.rule ∧ s₂.suf = b.right.suf ++ y := by
  by_cases hsame : s₁.pre = s₂.pre ∧ s₁.rule = s₂.rule
  · exact Or.inl hsame
  by_cases hind : s₁.Independent s₂
  · exact Or.inr (Or.inl hind)
  refine Or.inr (Or.inr ?_)
  obtain ⟨x₁, ρ₁, m₁, y₁, rfl, rfl⟩ := s₁
  obtain ⟨x₂, ρ₂, m₂, y₂, h, rfl⟩ := s₂
  simp only [Step.Independent] at hsame hind ⊢
  obtain ⟨x, a₁, a₂, rfl, rfl, ha, h'⟩ :=
    exists_common_prefix (m₁ := ρ₁.1 ++ y₁) (m₂ := ρ₂.1 ++ y₂) (by simpa using h)
  obtain ⟨y, b₁, b₂, rfl, rfl, hb, h''⟩ :=
    exists_common_suffix (m₁ := a₁ ++ ρ₁.1) (m₂ := a₂ ++ ρ₂.1) (by simpa using h')
  refine ⟨x, y, ⟨a₁ ++ ρ₁.1 ++ b₁, a₁ ++ ρ₁.2 ++ b₁, a₂ ++ ρ₂.2 ++ b₂,
    ⟨a₁, ρ₁, m₁, b₁, rfl, rfl⟩, ⟨a₂, ρ₂, m₂, b₂, h'', rfl⟩⟩, ⟨?_, ?_, ha, hb⟩,
    rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only
    by_contra hc
    push Not at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact hsame ⟨rfl, rfl⟩
  · simp only [Step.Independent]
    rintro (⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩)
    · exact hind (Or.inl ⟨c, by simp [hc1], by simp [hc2]⟩)
    · exact hind (Or.inr ⟨c, by simp [hc1], by simp [hc2]⟩)

/-- The source of a critical branching is no longer than the two left-hand sides together. -/
theorem Branching.IsCritical.src_length_le {R : Finset (List α × List α)} {b : Branching R}
    (hb : b.IsCritical) :
    b.src.length ≤ b.left.rule.1.length + b.right.rule.1.length := by
  obtain ⟨src, t₁, t₂, ⟨p₁, r₁, m₁, s₁, rfl, rfl⟩, ⟨p₂, r₂, m₂, s₂, e, rfl⟩⟩ := b
  obtain ⟨-, hind, hp, hs⟩ := hb
  simp only [Step.Independent] at hind hp hs ⊢
  have hl := congrArg List.length e
  simp only [List.length_append] at hl
  rcases hp with rfl | rfl <;> rcases hs with rfl | rfl
  · simp
  · simp only [List.nil_append, List.append_nil] at e ⊢
    rcases List.append_eq_append_iff.1 e with ⟨c, rfl, rfl⟩ | ⟨c, -, hc⟩
    · exact absurd (Or.inl ⟨c, by simp, by simp⟩) hind
    · have := congrArg List.length hc
      simp only [List.length_append, List.length_nil] at this hl ⊢; omega
  · simp only [List.nil_append, List.append_nil] at e ⊢
    rcases List.append_eq_append_iff.1 e.symm with ⟨c, rfl, rfl⟩ | ⟨c, -, hc⟩
    · exact absurd (Or.inr ⟨c, by simp, by simp⟩) hind
    · have := congrArg List.length hc
      simp only [List.length_append, List.length_nil] at this hl ⊢; omega
  · simp only [List.length_append, List.length_nil] at hl ⊢; omega

/-- A branching is determined by the fields of its two steps. -/
theorem Branching.ext_fields {R : Finset (List α × List α)} {b b' : Branching R}
    (h₁ : b.left.pre = b'.left.pre) (h₂ : b.left.rule = b'.left.rule)
    (h₃ : b.left.suf = b'.left.suf) (h₄ : b.right.pre = b'.right.pre)
    (h₅ : b.right.rule = b'.right.rule) (h₆ : b.right.suf = b'.right.suf) : b = b' := by
  obtain ⟨src, t₁, t₂, ⟨p₁, r₁, m₁, s₁, rfl, rfl⟩, ⟨p₂, r₂, m₂, s₂, e, rfl⟩⟩ := b
  obtain ⟨src', t₁', t₂', ⟨p₁', r₁', m₁', s₁', rfl, rfl⟩, ⟨p₂', r₂', m₂', s₂', e', rfl⟩⟩ := b'
  simp only at h₁ h₂ h₃ h₄ h₅ h₆
  subst h₁ h₂ h₃ h₄ h₅ h₆
  rfl

theorem criticalBranchings_finite [Finite α] (R : Finset (List α × List α)) :
    (criticalBranchings R).Finite := by
  classical
  set N := R.sup fun ρ => ρ.1.length
  have hN : ∀ ρ ∈ R, ρ.1.length ≤ N := fun ρ hρ =>
    Finset.le_sup (f := fun ρ : List α × List α => ρ.1.length) hρ
  set S : Set (List α) := {l | l.length ≤ N + N}
  have hS : S.Finite := List.finite_length_le α (N + N)
  let f : Branching R → List α × (List α × List α) × List α × List α × (List α × List α) ×
      List α := fun b =>
    (b.left.pre, b.left.rule, b.left.suf, b.right.pre, b.right.rule, b.right.suf)
  let T := S ×ˢ (R : Set (List α × List α)) ×ˢ S ×ˢ S ×ˢ (R : Set (List α × List α)) ×ˢ S
  have hT : T.Finite :=
    hS.prod (R.finite_toSet.prod (hS.prod (hS.prod (R.finite_toSet.prod hS))))
  have hinj : Function.Injective f := by
    intro b b' h
    simp only [f, Prod.mk.injEq] at h
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
    exact Branching.ext_fields h₁ h₂ h₃ h₄ h₅ h₆
  refine (hT.preimage hinj.injOn).subset ?_
  intro b hb
  have hlen := Branching.IsCritical.src_length_le hb
  have hl₁ := hN _ b.left.mem
  have hl₂ := hN _ b.right.mem
  have e₁ := congrArg List.length b.left.src_eq
  have e₂ := congrArg List.length b.right.src_eq
  simp only [List.length_append] at e₁ e₂
  simp only [Set.mem_preimage, f, T, S, Set.mem_prod, Set.mem_ofPred_eq, Finset.mem_coe,
    b.left.mem, b.right.mem, true_and]
  omega

end Squier
