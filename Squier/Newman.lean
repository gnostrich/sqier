module

public import Mathlib

@[expose] public section

/-! # Newman's lemma for an arbitrary relation -/

namespace Squier

theorem newman {β : Type*} {r : β → β → Prop} (hwf : WellFounded fun b a => r a b)
    (hloc : ∀ ⦃a b c : β⦄, r a b → r a c → Relation.Join (Relation.ReflTransGen r) b c) :
    ∀ ⦃a b c : β⦄, Relation.ReflTransGen r a b → Relation.ReflTransGen r a c →
      Relation.Join (Relation.ReflTransGen r) b c := by
  sorry

end Squier
