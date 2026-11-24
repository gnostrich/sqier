module

public import Mathlib
public import Squier.Newman
public import Squier.Branching
@[expose] public section

/-! # The critical pair lemma -/

namespace Squier

variable {α : Type*}

/-- Whiskering preserves the one-step rewriting relation. -/
theorem rewrites_whisker {R : Finset (List α × List α)} {p q : List α} (x y : List α)
    (h : Rewrites R p q) : Rewrites R (x ++ p ++ y) (x ++ q ++ y) :=
  h.map (Step.whisker x y)

/-- Whiskering preserves multi-step rewriting. -/
theorem reflTransGen_whisker {R : Finset (List α × List α)} {p q : List α} (x y : List α)
    (h : Relation.ReflTransGen (Rewrites R) p q) :
    Relation.ReflTransGen (Rewrites R) (x ++ p ++ y) (x ++ q ++ y) :=
  h.lift (fun t => x ++ t ++ y) (fun _ _ h => rewrites_whisker x y h)

/-- An independent branching (first step on the left) is joinable. -/
theorem joinable_of_independent_left {R : Finset (List α × List α)} {u v w : List α}
    (s₁ : Step R u v) (s₂ : Step R u w)
    (h : ∃ c : List α, s₂.pre = s₁.pre ++ s₁.rule.1 ++ c ∧ s₁.suf = c ++ s₂.rule.1 ++ s₂.suf) :
    Joinable R v w := by
  obtain ⟨c, hpre, hsuf⟩ := h
  refine ⟨s₁.pre ++ s₁.rule.2 ++ c ++ s₂.rule.2 ++ s₂.suf, ?_, ?_⟩
  · exact Relation.ReflTransGen.single
      ⟨⟨s₁.pre ++ s₁.rule.2 ++ c, s₂.rule, s₂.mem, s₂.suf,
        s₁.tgt_eq.trans (by rw [hsuf]; simp), rfl⟩⟩
  · exact Relation.ReflTransGen.single
      ⟨⟨s₁.pre, s₁.rule, s₁.mem, c ++ s₂.rule.2 ++ s₂.suf,
        s₂.tgt_eq.trans (by rw [hpre]; simp), by simp⟩⟩

theorem critical_pair_lemma (R : Finset (List α × List α)) :
    LocallyConfluent R ↔ ∀ b ∈ criticalBranchings R, Joinable R b.tgt₁ b.tgt₂ := by
  constructor
  · intro hloc b _
    exact hloc ⟨b.left⟩ ⟨b.right⟩
  · intro hcrit u v w ⟨s₁⟩ ⟨s₂⟩
    rcases branching_cases s₁ s₂ with ⟨hpre, hrule⟩ | hind | ⟨x, y, b, hb, h1, h2, h3, h4, h5, h6⟩
    · have hsrc := s₁.src_eq.symm.trans s₂.src_eq
      rw [hpre, hrule] at hsrc
      have hsuf : s₁.suf = s₂.suf := by simpa using hsrc
      have hvw : v = w :=
        s₁.tgt_eq.trans ((by rw [hpre, hrule, hsuf] :
          s₁.pre ++ s₁.rule.2 ++ s₁.suf = s₂.pre ++ s₂.rule.2 ++ s₂.suf).trans s₂.tgt_eq.symm)
      subst hvw
      exact ⟨v, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
    · rcases hind with h | h
      · exact joinable_of_independent_left s₁ s₂ h
      · obtain ⟨d, hwd, hvd⟩ := joinable_of_independent_left s₂ s₁ h
        exact ⟨d, hvd, hwd⟩
    · have hv : v = x ++ b.tgt₁ ++ y :=
        calc v = s₁.pre ++ s₁.rule.2 ++ s₁.suf := s₁.tgt_eq
          _ = x ++ (b.left.pre ++ b.left.rule.2 ++ b.left.suf) ++ y := by
              rw [h1, h2, h3]; simp
          _ = x ++ b.tgt₁ ++ y := by rw [← b.left.tgt_eq]
      have hw : w = x ++ b.tgt₂ ++ y :=
        calc w = s₂.pre ++ s₂.rule.2 ++ s₂.suf := s₂.tgt_eq
          _ = x ++ (b.right.pre ++ b.right.rule.2 ++ b.right.suf) ++ y := by
              rw [h4, h5, h6]; simp
          _ = x ++ b.tgt₂ ++ y := by rw [← b.right.tgt_eq]
      obtain ⟨d, hd₁, hd₂⟩ := hcrit b hb
      rw [hv, hw]
      exact ⟨x ++ d ++ y, reflTransGen_whisker x y hd₁, reflTransGen_whisker x y hd₂⟩

theorem confluent_iff_criticalPairs_joinable (R : Finset (List α × List α))
    (hR : Terminating R) :
    Confluent R ↔ ∀ b ∈ criticalBranchings R, Joinable R b.tgt₁ b.tgt₂ := by
  rw [← critical_pair_lemma]
  constructor
  · intro h u v w h₁ h₂
    exact h (Relation.ReflTransGen.single h₁) (Relation.ReflTransGen.single h₂)
  · intro h
    exact newman (r := Rewrites R) hR h

end Squier
