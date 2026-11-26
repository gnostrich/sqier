module

public import Mathlib

@[expose] public section

/-! # Newman's lemma for an arbitrary relation -/

namespace Squier

theorem newman {β : Type*} {r : β → β → Prop} (hwf : WellFounded fun b a => r a b)
    (hloc : ∀ ⦃a b c : β⦄, r a b → r a c → Relation.Join (Relation.ReflTransGen r) b c) :
    ∀ ⦃a b c : β⦄, Relation.ReflTransGen r a b → Relation.ReflTransGen r a c →
      Relation.Join (Relation.ReflTransGen r) b c := by
  intro a
  induction a using hwf.induction with
  | _ a ih =>
  intro b c hab hac
  rcases Relation.ReflTransGen.cases_head hab with rfl | ⟨b₁, hab₁, hb₁b⟩
  · exact ⟨c, hac, Relation.ReflTransGen.refl⟩
  rcases Relation.ReflTransGen.cases_head hac with rfl | ⟨c₁, hac₁, hc₁c⟩
  · exact ⟨b, Relation.ReflTransGen.refl, hab⟩
  obtain ⟨d, hb₁d, hc₁d⟩ := hloc hab₁ hac₁
  obtain ⟨e, hbe, hde⟩ := ih b₁ hab₁ hb₁b hb₁d
  obtain ⟨f, hcf, hef⟩ := ih c₁ hac₁ hc₁c (hc₁d.trans hde)
  exact ⟨f, hbe.trans hef, hcf⟩

end Squier
