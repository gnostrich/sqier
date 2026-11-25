module

public import Mathlib
public import Kontsevich.Defs

@[expose] public section

/-!
# Auxiliary lemmas for graph polynomials of compositions

General facts about the relation `Joined` of a multigraph: induction principle, transport along
vertex maps, the forest inequality `|V| ≤ |S| + |R|` whenever every vertex is joined to one of
the roots in `R`, and the splitting of sums over subsets of a disjoint union of edge sets.
-/

set_option linter.unusedSectionVars false

namespace Kontsevich

open MvPolynomial

section Joined

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {ends : E → V × V} {S : Finset E}

theorem Joined.refl' (u : V) : Joined ends S u u := Relation.ReflTransGen.refl

theorem Joined.trans' {u v w : V} (h₁ : Joined ends S u v) (h₂ : Joined ends S v w) :
    Joined ends S u w := Relation.ReflTransGen.trans h₁ h₂

theorem Joined.edge {e : E} (he : e ∈ S) : Joined ends S (ends e).1 (ends e).2 :=
  Relation.ReflTransGen.single ⟨e, he, Or.inl rfl⟩

/-- Induction principle for `Joined`: any reflexive transitive relation containing all edges of
`S` (in both directions) contains `Joined ends S`. -/
theorem Joined.induct (r : V → V → Prop) (hrefl : ∀ x, r x x)
    (htrans : ∀ x y z, r x y → r y z → r x z)
    (hstep : ∀ e ∈ S, r (ends e).1 (ends e).2 ∧ r (ends e).2 (ends e).1)
    {u v : V} (h : Joined ends S u v) : r u v := by
  induction h with
  | refl => exact hrefl _
  | tail _ hst ih =>
    obtain ⟨e, he, h | h⟩ := hst
    · exact htrans _ _ _ ih (by simpa [h] using (hstep e he).1)
    · exact htrans _ _ _ ih (by simpa [h] using (hstep e he).2)

theorem Joined.symm' {u v : V} (h : Joined ends S u v) : Joined ends S v u :=
  Joined.induct (fun x y => Joined ends S y x) (fun _ => Joined.refl' _)
    (fun _ _ _ h₁ h₂ => h₂.trans' h₁)
    (fun _ he => ⟨Relation.ReflTransGen.single ⟨_, he, Or.inr rfl⟩, Joined.edge he⟩) h

/-- Transport of `Joined` along a vertex map sending each edge of `S` to a single vertex or to
an edge of `S'`. -/
theorem Joined.map {V' E' : Type} [Fintype V'] [DecidableEq V'] [Fintype E'] [DecidableEq E']
    {ends' : E' → V' × V'} {S' : Finset E'} (p : V → V')
    (h : ∀ e ∈ S, p (ends e).1 = p (ends e).2 ∨
      ∃ e' ∈ S', ends' e' = (p (ends e).1, p (ends e).2))
    {u v : V} (huv : Joined ends S u v) : Joined ends' S' (p u) (p v) := by
  refine Joined.induct (fun x y => Joined ends' S' (p x) (p y)) (fun _ => Joined.refl' _)
    (fun _ _ _ h₁ h₂ => h₁.trans' h₂) ?_ huv
  intro e he
  rcases h e he with h | ⟨e', he', h⟩
  · exact ⟨by simp [h, Joined.refl'], by simp [h, Joined.refl']⟩
  · have := Joined.edge (ends := ends') he'
    rw [h] at this
    exact ⟨this, this.symm'⟩

theorem Joined.mono {S' : Finset E} (hS : S ⊆ S') {u v : V} (h : Joined ends S u v) :
    Joined ends S' u v := by
  have := Joined.map (ends' := ends) (S' := S') id
    (fun e he => Or.inr ⟨e, hS he, rfl⟩) h
  simpa using this

theorem Joined.empty {u v : V} (h : Joined ends ∅ u v) : u = v :=
  Joined.induct (fun x y => x = y) (fun _ => rfl) (fun _ _ _ h₁ h₂ => h₁.trans h₂)
    (by simp) h

theorem Joined.edge_iff {e : E} (he : e ∈ S) (c : V) :
    Joined ends S (ends e).1 c ↔ Joined ends S (ends e).2 c :=
  ⟨fun h => (Joined.edge he).symm'.trans' h, fun h => (Joined.edge he).trans' h⟩

/-- Joined in the graph where `a` and `b` are identified. -/
def JoinedMod (ends : E → V × V) (S : Finset E) (a b u v : V) : Prop :=
  Joined ends S u v ∨
    ((Joined ends S u a ∨ Joined ends S u b) ∧ (Joined ends S v a ∨ Joined ends S v b))

theorem JoinedMod.refl (a b u : V) : JoinedMod ends S a b u u := Or.inl (Joined.refl' u)

theorem JoinedMod.trans {a b u v w : V} (h₁ : JoinedMod ends S a b u v)
    (h₂ : JoinedMod ends S a b v w) : JoinedMod ends S a b u w := by
  rcases h₁ with h₁ | ⟨hu, hv⟩ <;> rcases h₂ with h₂ | ⟨hv', hw⟩
  · exact Or.inl (h₁.trans' h₂)
  · right
    refine ⟨?_, hw⟩
    rcases hv' with h | h
    · exact Or.inl (h₁.trans' h)
    · exact Or.inr (h₁.trans' h)
  · right
    refine ⟨hu, ?_⟩
    rcases hv with h | h
    · exact Or.inl (h₂.symm'.trans' h)
    · exact Or.inr (h₂.symm'.trans' h)
  · exact Or.inr ⟨hu, hw⟩

theorem JoinedMod.of_mem {a b u v : V} (hu : u = a ∨ u = b) (hv : v = a ∨ v = b) :
    JoinedMod ends S a b u v := by
  right
  constructor
  · rcases hu with rfl | rfl
    · exact Or.inl (Joined.refl' _)
    · exact Or.inr (Joined.refl' _)
  · rcases hv with rfl | rfl
    · exact Or.inl (Joined.refl' _)
    · exact Or.inr (Joined.refl' _)

theorem JoinedMod.of_left {a b v : V} (h : JoinedMod ends S a b a v) :
    Joined ends S a v ∨ Joined ends S b v := by
  rcases h with h | ⟨_, h | h⟩
  · exact Or.inl h
  · exact Or.inl h.symm'
  · exact Or.inr h.symm'

theorem Joined.insert_cases {e : E} {u v : V} (h : Joined ends (insert e S) u v) :
    JoinedMod ends S (ends e).1 (ends e).2 u v := by
  refine Joined.induct (fun x y => JoinedMod ends S (ends e).1 (ends e).2 x y)
    (fun _ => JoinedMod.refl _ _ _) (fun _ _ _ h₁ h₂ => h₁.trans h₂) ?_ h
  intro e' he'
  rcases Finset.mem_insert.1 he' with rfl | he'
  · exact ⟨JoinedMod.of_mem (Or.inl rfl) (Or.inr rfl), JoinedMod.of_mem (Or.inr rfl) (Or.inl rfl)⟩
  · exact ⟨Or.inl (Joined.edge he'), Or.inl (Joined.edge he').symm'⟩

variable (ends) in
/-- The setoid of vertices joined within `S`. -/
def joinedSetoid (S : Finset E) : Setoid V where
  r := Joined ends S
  iseqv := ⟨fun _ => Joined.refl' _, fun h => h.symm', fun h₁ h₂ => h₁.trans' h₂⟩

variable (ends) in
/-- The number of connected components of `(V, S)`. -/
noncomputable def ncomp (S : Finset E) : ℕ := Nat.card (Quotient (joinedSetoid ends S))

theorem ncomp_le_insert (e : E) (S : Finset E) :
    ncomp ends S ≤ ncomp ends (insert e S) + 1 := by
  classical
  let B : Quotient (joinedSetoid ends S) := Quotient.mk _ (ends e).2
  let q : Quotient (joinedSetoid ends S) → Quotient (joinedSetoid ends (insert e S)) :=
    Quotient.map id (fun _ _ h => Joined.mono (Finset.subset_insert _ _) h)
  let f : Quotient (joinedSetoid ends S) → Option (Quotient (joinedSetoid ends (insert e S))) :=
    fun x => if x = B then none else some (q x)
  have hf : Function.Injective f := by
    intro x y hxy
    induction x using Quotient.inductionOn with | h u => ?_
    induction y using Quotient.inductionOn with | h v => ?_
    by_cases hx : (Quotient.mk _ u : Quotient (joinedSetoid ends S)) = B <;>
      by_cases hy : (Quotient.mk _ v : Quotient (joinedSetoid ends S)) = B <;>
      simp only [f, hx, hy, ite_true, ite_false, reduceCtorEq, Option.some.injEq] at hxy
    · rw [hx, hy]
    · have huv : Joined ends (insert e S) u v := Quotient.exact hxy
      have hu : ¬ Joined ends S u (ends e).2 := fun h => hx (Quotient.sound h)
      have hv : ¬ Joined ends S v (ends e).2 := fun h => hy (Quotient.sound h)
      apply Quotient.sound
      rcases huv.insert_cases with h | ⟨h₁ | h₁, h₂ | h₂⟩
      · exact h
      · exact h₁.trans' h₂.symm'
      · exact absurd h₂ hv
      · exact absurd h₁ hu
      · exact absurd h₁ hu
  have := Nat.card_le_card_of_injective f hf
  rw [Finite.card_option] at this
  exact this

theorem card_le_ncomp_empty : Fintype.card V ≤ ncomp ends (∅ : Finset E) := by
  rw [← Nat.card_eq_fintype_card]
  refine Nat.card_le_card_of_injective (fun v => Quotient.mk (joinedSetoid ends ∅) v) ?_
  intro u v h
  exact Joined.empty (Quotient.exact h)

theorem card_le_card_add_ncomp (S : Finset E) :
    Fintype.card V ≤ S.card + ncomp ends S := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using card_le_ncomp_empty
  | insert e S he ih =>
    rw [Finset.card_insert_of_notMem he]
    have := ncomp_le_insert (ends := ends) e S
    omega

theorem ncomp_le_of_roots (R : Finset V) (h : ∀ v, ∃ r ∈ R, Joined ends S r v) :
    ncomp ends S ≤ R.card := by
  have := Nat.card_le_card_of_surjective
    (fun r : R => Quotient.mk (joinedSetoid ends S) r.1) ?_
  · simpa [ncomp] using this
  · intro x
    induction x using Quotient.inductionOn with | h v => ?_
    obtain ⟨r, hr, hrv⟩ := h v
    exact ⟨⟨r, hr⟩, Quotient.sound hrv⟩

/-- The forest inequality. -/
theorem card_le_of_roots (R : Finset V) (h : ∀ v, ∃ r ∈ R, Joined ends S r v) :
    Fintype.card V ≤ S.card + R.card :=
  (card_le_card_add_ncomp S).trans (Nat.add_le_add_left (ncomp_le_of_roots R h) _)

theorem card_le_one_of_conn (a : V) (h : ∀ v, Joined ends S a v) :
    Fintype.card V ≤ S.card + 1 := by
  simpa using card_le_of_roots (S := S) {a} (by simpa using h)

theorem card_le_two_of_conn (a b : V) (h : ∀ v, Joined ends S a v ∨ Joined ends S b v) :
    Fintype.card V ≤ S.card + 2 := by
  have := card_le_of_roots (S := S) {a, b} (by simpa using h)
  have h2 : ({a, b} : Finset V).card ≤ 2 := Finset.card_le_two
  omega

end Joined

section Sums

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The monomial attached to a set of edges: the product of the variables of the other edges. -/
noncomputable def mon {E : Type} [Fintype E] [DecidableEq E] (S : Finset E) :
    MvPolynomial E ℤ := ∏ e ∈ Sᶜ, X e

theorem compl_disjSum (a : Finset A) (b : Finset B) :
    (a.disjSum b)ᶜ = aᶜ.disjSum bᶜ := by
  ext x
  cases x <;> simp

theorem mon_disjSum (a : Finset A) (b : Finset B) :
    mon (a.disjSum b) = rename Sum.inl (mon a) * rename Sum.inr (mon b) := by
  simp [mon, compl_disjSum, Finset.prod_disjSum, map_prod, rename_X]

theorem sum_finset_sum {M : Type} [AddCommMonoid M] (F : Finset (A ⊕ B) → M) :
    ∑ S, F S = ∑ a : Finset A, ∑ b : Finset B, F (a.disjSum b) := by
  rw [← Fintype.sum_prod_type' (f := fun a b => F (Finset.disjSum a b))]
  exact Fintype.sum_equiv Finset.sumEquiv.toEquiv _ _ (fun S => by
    simp [Finset.sumEquiv, Finset.toLeft_disjSum_toRight])

open Classical in
theorem kirchhoffPoly_eq {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (ends : E → V × V) :
    kirchhoffPoly ends = ∑ T, if IsSpanningTree ends T then mon T else 0 := by
  rw [kirchhoffPoly, Finset.sum_filter]
  rfl

open Classical in
theorem forestPoly_eq {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (ends : E → V × V) (s t : V) :
    forestPoly ends s t = ∑ F, if IsSeparatingForest ends s t F then mon F else 0 := by
  rw [forestPoly, Finset.sum_filter]
  rfl

end Sums

end Kontsevich
