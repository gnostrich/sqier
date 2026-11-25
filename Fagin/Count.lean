module

public import Mathlib
public import Fagin.Defs

@[expose] public section

/-!
# Counting graphs

We count the simple graphs on `Fin n` (`card_simpleGraph`) and prove that, for each `k`, almost
every finite graph has the `k`-extension property (`extension_almost_sure`).

A simple graph on `V` is encoded by its edge indicator function on the off-diagonal elements of
`Sym2 V` (`graphEquiv`). In the space of such functions `X → Bool` we use the uniform proportion
`prop P = #{f | P f} / 2 ^ |X|`. Conditions depending on disjoint blocks of coordinates are
independent (`prop_and`, `prop_forall`), and the condition that `f` agrees with a fixed function
on a block `T` has proportion `(1/2) ^ |T|` (`prop_agree`). For fixed disjoint `A, B`, the events
"`z` is not a witness for `(A, B)`" for the different `z ∉ A ∪ B` depend on disjoint blocks of
edges, which yields the bound `(1 - 2^(-(k+1))) ^ (n - k)` for the proportion of graphs without a
witness. A union bound over the polynomially many pairs `(A, B)` finishes the proof.
-/

namespace Fagin

open FirstOrder FirstOrder.Language Filter Topology

section Generic

lemma natCard_add_natCard_compl {α : Type*} [Finite α] (P : α → Prop) :
    Nat.card {a // P a} + Nat.card {a // ¬ P a} = Nat.card α := by
  classical
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl]
  have := Fintype.card_subtype_le P
  omega

variable {X : Type*} [Fintype X]

/-- Uniform proportion of the functions `X → Bool` satisfying `P`. -/
noncomputable def prop (P : (X → Bool) → Prop) : ℝ :=
  (Nat.card {f // P f} : ℝ) / 2 ^ Fintype.card X

lemma natCard_fun_bool : Nat.card (X → Bool) = 2 ^ Fintype.card X := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Bool), Nat.card_eq_fintype_card]
  rfl

lemma prop_congr {P Q : (X → Bool) → Prop} (h : ∀ f, P f ↔ Q f) : prop P = prop Q := by
  have : P = Q := funext fun f => propext (h f)
  rw [this]

lemma prop_true : prop (fun _ : X → Bool => True) = 1 := by
  unfold prop
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)), natCard_fun_bool]
  push_cast
  exact div_self (by positivity)

lemma prop_not (P : (X → Bool) → Prop) : prop (fun f => ¬ P f) = 1 - prop P := by
  unfold prop
  have h := natCard_add_natCard_compl P
  rw [natCard_fun_bool] at h
  have h' : (Nat.card {f // ¬ P f} : ℝ) = 2 ^ Fintype.card X - Nat.card {f // P f} := by
    rw [eq_sub_iff_add_eq, add_comm]; exact_mod_cast h
  rw [h', sub_div, div_self (by positivity)]

/-- Splice two functions: `f` on `T` and `g` off `T`. -/
noncomputable def splice (T : Set X) (f g : X → Bool) : X → Bool :=
  open Classical in fun x => if x ∈ T then f x else g x

lemma splice_of_mem {T : Set X} {f g : X → Bool} {x : X} (hx : x ∈ T) : splice T f g x = f x := by
  simp [splice, hx]

lemma splice_of_notMem {T : Set X} {f g : X → Bool} {x : X} (hx : x ∉ T) :
    splice T f g x = g x := by
  simp [splice, hx]

lemma splice_splice (T : Set X) (f g : X → Bool) :
    splice T (splice T f g) (splice T g f) = f := by
  funext x
  by_cases hx : x ∈ T
  · rw [splice_of_mem hx, splice_of_mem hx]
  · rw [splice_of_notMem hx, splice_of_notMem hx]

/-- Independence of conditions depending on complementary sets of coordinates. -/
lemma natCard_and_mul (T : Set X) (P Q : (X → Bool) → Prop)
    (hP : ∀ f g, (∀ x ∈ T, f x = g x) → P f → P g)
    (hQ : ∀ f g, (∀ x ∉ T, f x = g x) → Q f → Q g) :
    Nat.card {f // P f ∧ Q f} * Nat.card (X → Bool) =
      Nat.card {f // P f} * Nat.card {f // Q f} := by
  rw [← Nat.card_prod, ← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun p => (⟨splice T p.1.1 p.2,
          hP _ _ (fun x hx => (splice_of_mem hx).symm) p.1.2.1⟩,
        ⟨splice T p.2 p.1.1, hQ _ _ (fun x hx => (splice_of_notMem hx).symm) p.1.2.2⟩)
      invFun := fun q => (⟨splice T q.1.1 q.2.1,
          hP _ _ (fun x hx => (splice_of_mem hx).symm) q.1.2,
          hQ _ _ (fun x hx => (splice_of_notMem hx).symm) q.2.2⟩,
        splice T q.2.1 q.1.1)
      left_inv := fun p => ?_
      right_inv := fun q => ?_ }
  · ext1
    · exact Subtype.ext (splice_splice T _ _)
    · exact splice_splice T _ _
  · ext1
    · exact Subtype.ext (splice_splice T _ _)
    · exact Subtype.ext (splice_splice T _ _)

lemma prop_and (T : Set X) (P Q : (X → Bool) → Prop)
    (hP : ∀ f g, (∀ x ∈ T, f x = g x) → P f → P g)
    (hQ : ∀ f g, (∀ x ∉ T, f x = g x) → Q f → Q g) :
    prop (fun f => P f ∧ Q f) = prop P * prop Q := by
  have h := natCard_and_mul T P Q hP hQ
  rw [natCard_fun_bool] at h
  have h' : (Nat.card {f // P f ∧ Q f} : ℝ) * 2 ^ Fintype.card X =
      Nat.card {f // P f} * Nat.card {f // Q f} := by exact_mod_cast h
  unfold prop
  have hpos : (0 : ℝ) < 2 ^ Fintype.card X := by positivity
  field_simp
  linear_combination h'

lemma prop_forall {ι : Type*} (Z : Finset ι) (T : ι → Set X)
    (hT : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → Disjoint (T i) (T j))
    (P : ι → (X → Bool) → Prop)
    (hP : ∀ i ∈ Z, ∀ f g, (∀ x ∈ T i, f x = g x) → P i f → P i g) :
    prop (fun f => ∀ i ∈ Z, P i f) = ∏ i ∈ Z, prop (P i) := by
  classical
  induction Z using Finset.induction_on with
  | empty => simpa using prop_true
  | insert a Z ha ih =>
    rw [Finset.prod_insert ha, ← ih (fun i hi j hj hij => hT i (by simp [hi]) j (by simp [hj]) hij)
      (fun i hi => hP i (by simp [hi]))]
    rw [prop_congr (Q := fun f => P a f ∧ ∀ i ∈ Z, P i f) (fun f => by simp)]
    refine prop_and (T a) _ _ (hP a (by simp)) ?_
    intro f g hfg hf i hi
    refine hP i (by simp [hi]) f g (fun x hx => hfg x ?_) (hf i hi)
    have hne : a ≠ i := fun h => ha (h ▸ hi)
    exact Set.disjoint_left.1 (hT a (by simp) i (by simp [hi]) hne).symm hx

lemma prop_agree (T : Finset X) (c : X → Bool) :
    prop (fun f => ∀ x ∈ T, f x = c x) = (1 / 2) ^ T.card := by
  classical
  have e : {f : X → Bool // ∀ x ∈ T, f x = c x} ≃ ({x // x ∉ T} → Bool) :=
    { toFun := fun f x => f.1 x.1
      invFun := fun g => ⟨fun x => if h : x ∈ T then c x else g ⟨x, h⟩,
        fun x hx => by simp [hx]⟩
      left_inv := fun f => by
        ext x
        by_cases hx : x ∈ T
        · simp [hx, f.2 x hx]
        · simp [hx]
      right_inv := fun g => by
        funext x
        simp [x.2] }
  have hc : Nat.card {x // x ∉ T} = Fintype.card X - T.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_coe]
  have hT : T.card ≤ Fintype.card X := Finset.card_le_univ T
  unfold prop
  rw [Nat.card_congr e, Nat.card_fun, hc, Nat.card_eq_fintype_card (α := Bool)]
  simp only [Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  rw [div_eq_iff (by positivity), ← Nat.sub_add_cancel hT, pow_add]
  rw [Nat.add_sub_cancel]
  field_simp

end Generic

section Graphs

variable {V : Type*}

/-- A simple graph is determined by its edge indicator function on off-diagonal pairs. -/
noncomputable def graphEquiv (V : Type*) :
    SimpleGraph V ≃ ({e : Sym2 V // ¬ e.IsDiag} → Bool) :=
  open Classical in
  { toFun := fun G x => decide (x.1 ∈ G.edgeSet)
    invFun := fun f => SimpleGraph.fromEdgeSet {e | ∃ h : ¬ e.IsDiag, f ⟨e, h⟩ = true}
    left_inv := fun G => by
      ext u v
      simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_setOf_eq, decide_eq_true_eq,
        SimpleGraph.mem_edgeSet, Sym2.mk_isDiag_iff]
      constructor
      · rintro ⟨⟨_, h⟩, _⟩; exact h
      · intro h; exact ⟨⟨G.ne_of_adj h, h⟩, G.ne_of_adj h⟩
    right_inv := fun f => by
      funext ⟨e, he⟩
      simp only [SimpleGraph.edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_setOf_eq,
        Sym2.mem_diagSet_iff_isDiag, he, not_false_eq_true, exists_true_left, and_true,
        decide_eq_true_eq]
      cases f ⟨e, he⟩ <;> simp }

lemma graphEquiv_apply (G : SimpleGraph V) (x : {e : Sym2 V // ¬ e.IsDiag}) :
    graphEquiv V G x = true ↔ x.1 ∈ G.edgeSet := by
  classical
  simp [graphEquiv]

end Graphs

/-- There are `2^(n choose 2)` simple graphs on `n` labelled vertices. -/
theorem card_simpleGraph (n : ℕ) : Nat.card (SimpleGraph (Fin n)) = 2 ^ n.choose 2 := by
  rw [Nat.card_congr (graphEquiv (Fin n)), Nat.card_fun, Sym2.natCard_subtype_not_diag,
    Nat.card_eq_fintype_card (α := Bool), Nat.card_fin]
  rfl

/-- For each `k`, the proportion of graphs on `n` vertices with the `k`-extension property
tends to `1`. -/
theorem extension_almost_sure (k : ℕ) :
    Tendsto (fun n : ℕ =>
      (Nat.card {G : SimpleGraph (Fin n) // ExtensionProperty G k} : ℝ) / 2 ^ n.choose 2)
      atTop (𝓝 1) := by
  sorry

end Fagin
