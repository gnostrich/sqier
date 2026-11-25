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

omit [Fintype X] in
lemma splice_of_mem {T : Set X} {f g : X → Bool} {x : X} (hx : x ∈ T) : splice T f g x = f x := by
  simp [splice, hx]

omit [Fintype X] in
lemma splice_of_notMem {T : Set X} {f g : X → Bool} {x : X} (hx : x ∉ T) :
    splice T f g x = g x := by
  simp [splice, hx]

omit [Fintype X] in
lemma splice_splice (T : Set X) (f g : X → Bool) :
    splice T (splice T f g) (splice T g f) = f := by
  funext x
  by_cases hx : x ∈ T
  · rw [splice_of_mem hx, splice_of_mem hx]
  · rw [splice_of_notMem hx, splice_of_notMem hx]

omit [Fintype X] in
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
  rw [Nat.add_sub_cancel, mul_comm (2 ^ (Fintype.card X - T.card) : ℝ), ← mul_assoc, ← mul_pow]
  norm_num

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
      simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_ofPred_eq, decide_eq_true_eq,
        SimpleGraph.mem_edgeSet, Sym2.mk_isDiag_iff]
      constructor
      · rintro ⟨⟨_, h⟩, _⟩; exact h
      · intro h; exact ⟨⟨G.ne_of_adj h, h⟩, G.ne_of_adj h⟩
    right_inv := fun f => by
      funext ⟨e, he⟩
      by_cases h : f ⟨e, he⟩ = true <;> simp [SimpleGraph.edgeSet_fromEdgeSet, he, h] }

lemma graphEquiv_apply (G : SimpleGraph V) (x : {e : Sym2 V // ¬ e.IsDiag}) :
    graphEquiv V G x = true ↔ x.1 ∈ G.edgeSet := by
  classical
  simp [graphEquiv]

end Graphs

section Extension

variable {n : ℕ}

/-- The (off-diagonal) edges from `z` to the vertices of `S`. -/
noncomputable def blk (z : Fin n) (S : Finset (Fin n)) :
    Finset {e : Sym2 (Fin n) // ¬ e.IsDiag} :=
  open Classical in Finset.univ.filter (fun x => ∃ a ∈ S, x.1 = s(z, a))

/-- The edge pattern making `z` a witness for `A` (adjacent exactly to the vertices of `A`). -/
noncomputable def col (z : Fin n) (A : Finset (Fin n)) : {e : Sym2 (Fin n) // ¬ e.IsDiag} → Bool :=
  open Classical in fun x => decide (∃ a ∈ A, x.1 = s(z, a))

lemma mem_blk {z : Fin n} {S : Finset (Fin n)} {x : {e : Sym2 (Fin n) // ¬ e.IsDiag}} :
    x ∈ blk z S ↔ ∃ a ∈ S, x.1 = s(z, a) := by
  unfold blk
  simp

lemma col_eq_true {z : Fin n} {A : Finset (Fin n)} {x : {e : Sym2 (Fin n) // ¬ e.IsDiag}} :
    col z A x = true ↔ ∃ a ∈ A, x.1 = s(z, a) := by
  unfold col
  simp

lemma card_blk_le (z : Fin n) (S : Finset (Fin n)) : (blk z S).card ≤ S.card := by
  classical
  calc (blk z S).card ≤ (S.image (fun a => s(z, a))).card :=
        Finset.card_le_card_of_injOn (fun x => x.1)
          (fun x hx => by
            obtain ⟨a, ha, h⟩ := mem_blk.1 hx
            simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
            exact ⟨a, ha, h.symm⟩)
          (fun x _ y _ h => Subtype.ext h)
    _ ≤ S.card := Finset.card_image_le

lemma disjoint_blk {z z' : Fin n} {S : Finset (Fin n)} (hz : z ∉ S) (hne : z ≠ z') :
    Disjoint (blk z S : Set {e : Sym2 (Fin n) // ¬ e.IsDiag}) (blk z' S : Set _) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨a, ha, h⟩ := mem_blk.1 (Finset.mem_coe.1 hx)
  obtain ⟨b, hb, h'⟩ := mem_blk.1 (Finset.mem_coe.1 hx')
  rw [h] at h'
  rcases Sym2.eq_iff.1 h' with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact hne h1
  · exact hz (h1 ▸ hb)

lemma wit_iff {A B : Finset (Fin n)} (hAB : Disjoint A B) {z : Fin n} (hzA : z ∉ A)
    (hzB : z ∉ B) (G : SimpleGraph (Fin n)) :
    ((∀ a ∈ A, G.Adj z a) ∧ ∀ b ∈ B, ¬ G.Adj z b) ↔
      ∀ x ∈ blk z (A ∪ B), graphEquiv (Fin n) G x = col z A x := by
  have key : ∀ (a : Fin n) (x : {e : Sym2 (Fin n) // ¬ e.IsDiag}), x.1 = s(z, a) →
      (graphEquiv (Fin n) G x = true ↔ G.Adj z a) ∧ (col z A x = true ↔ a ∈ A) := by
    intro a x hx
    rw [graphEquiv_apply, col_eq_true, hx, SimpleGraph.mem_edgeSet]
    refine ⟨Iff.rfl, ?_⟩
    simp only [Sym2.congr_right]
    constructor
    · rintro ⟨b, hb, rfl⟩; exact hb
    · intro h; exact ⟨a, h, rfl⟩
  constructor
  · rintro ⟨hA, hB⟩ x hx
    obtain ⟨a, ha, hxa⟩ := mem_blk.1 hx
    obtain ⟨k1, k2⟩ := key a x hxa
    rw [Bool.eq_iff_iff, k1, k2]
    rcases Finset.mem_union.1 ha with ha | ha
    · exact iff_of_true (hA a ha) ha
    · exact iff_of_false (hB a ha) (Finset.disjoint_right.1 hAB ha)
  · intro h
    have mk : ∀ a ∈ A ∪ B, ∃ x, x ∈ blk z (A ∪ B) ∧ x.1 = s(z, a) := by
      intro a ha
      have hne : z ≠ a := by
        rintro rfl
        rcases Finset.mem_union.1 ha with h | h
        exacts [hzA h, hzB h]
      exact ⟨⟨s(z, a), by simpa using hne⟩, mem_blk.2 ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · obtain ⟨x, hx, hxa⟩ := mk a (Finset.mem_union_left _ ha)
      obtain ⟨k1, k2⟩ := key a x hxa
      exact k1.1 ((Bool.eq_iff_iff.1 (h x hx)).2 (k2.2 ha))
    · obtain ⟨x, hx, hxa⟩ := mk b (Finset.mem_union_right _ hb)
      obtain ⟨k1, k2⟩ := key b x hxa
      intro hadj
      exact Finset.disjoint_right.1 hAB hb (k2.1 ((Bool.eq_iff_iff.1 (h x hx)).1 (k1.2 hadj)))

/-- No vertex outside `A ∪ B` is a witness for the pair `(A, B)`. -/
def NoWitness (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) : Prop :=
  ∀ z, z ∉ A → z ∉ B → ¬ ((∀ a ∈ A, G.Adj z a) ∧ ∀ b ∈ B, ¬ G.Adj z b)

lemma noWitness_bound (k : ℕ) {A B : Finset (Fin n)} (hAB : Disjoint A B)
    (hk : A.card + B.card ≤ k) :
    (Nat.card {G : SimpleGraph (Fin n) // NoWitness G A B} : ℝ) / 2 ^ n.choose 2 ≤
      (1 - (1 / 2) ^ (k + 1)) ^ (n - k) := by
  classical
  set S := A ∪ B with hS
  set Z : Finset (Fin n) := Sᶜ with hZ
  have hcard : Nat.card {G : SimpleGraph (Fin n) // NoWitness G A B} =
      Nat.card {f : {e : Sym2 (Fin n) // ¬ e.IsDiag} → Bool //
        ∀ z ∈ Z, ¬ ∀ x ∈ blk z S, f x = col z A x} := by
    refine Nat.card_congr ((graphEquiv (Fin n)).subtypeEquiv fun G => ?_)
    simp only [NoWitness, hZ, hS, Finset.mem_compl, Finset.mem_union, not_or]
    exact ⟨fun h z ⟨hzA, hzB⟩ => (wit_iff hAB hzA hzB G).not.1 (h z hzA hzB),
      fun h z hzA hzB => (wit_iff hAB hzA hzB G).not.2 (h z ⟨hzA, hzB⟩)⟩
  have hX : Fintype.card {e : Sym2 (Fin n) // ¬ e.IsDiag} = n.choose 2 := by
    rw [← Nat.card_eq_fintype_card, Sym2.natCard_subtype_not_diag, Nat.card_fin]
  have hprop := prop_forall Z (fun z => (blk z S : Set _))
    (fun i hi j _ hij => disjoint_blk (by simpa [hZ] using hi) hij)
    (fun z f => ¬ ∀ x ∈ blk z S, f x = col z A x)
    (fun z _ f g hfg hf hg => hf fun x hx => (hfg x hx).trans (hg x hx))
  beta_reduce at hprop
  rw [hcard, ← hX]
  change prop (fun f => ∀ z ∈ Z, ¬ ∀ x ∈ blk z S, f x = col z A x) ≤ _
  rw [hprop]
  have hr0 : 0 ≤ 1 - (1 / 2 : ℝ) ^ (k + 1) := by
    have : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hr1 : 1 - (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := by
    have : 0 ≤ (1 / 2 : ℝ) ^ (k + 1) := by positivity
    linarith
  have hSk : S.card ≤ k := (Finset.card_union_le A B).trans hk
  have hZc : n - k ≤ Z.card := by
    rw [hZ, Finset.card_compl, Fintype.card_fin]
    omega
  calc ∏ z ∈ Z, prop (fun f => ¬ ∀ x ∈ blk z S, f x = col z A x)
      = ∏ z ∈ Z, (1 - (1 / 2 : ℝ) ^ (blk z S).card) :=
        Finset.prod_congr rfl fun z _ => by rw [prop_not, prop_agree]
    _ ≤ ∏ _z ∈ Z, (1 - (1 / 2 : ℝ) ^ (k + 1)) := by
        refine Finset.prod_le_prod₀ (fun z _ => ?_) (fun z _ => ?_)
        · have : (1 / 2 : ℝ) ^ (blk z S).card ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
          linarith
        · have : (1 / 2 : ℝ) ^ (k + 1) ≤ (1 / 2 : ℝ) ^ (blk z S).card :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num)
              (by have := card_blk_le z S; omega)
          linarith
    _ = (1 - (1 / 2 : ℝ) ^ (k + 1)) ^ Z.card := Finset.prod_const _
    _ ≤ _ := pow_le_pow_of_le_one hr0 hr1 hZc

end Extension

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
  classical
  set r : ℝ := 1 - (1 / 2) ^ (k + 1) with hr
  have hr0 : 0 < r := by
    have : (1 / 2 : ℝ) ^ (k + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    linarith
  have hr1 : r < 1 := by
    have : 0 < (1 / 2 : ℝ) ^ (k + 1) := by positivity
    linarith
  set F : ℕ → ℝ := fun n =>
    (Nat.card {G : SimpleGraph (Fin n) // ¬ ExtensionProperty G k} : ℝ) / 2 ^ n.choose 2
    with hF
  have hsplit : ∀ n : ℕ,
      (Nat.card {G : SimpleGraph (Fin n) // ExtensionProperty G k} : ℝ) / 2 ^ n.choose 2 =
        1 - F n := by
    intro n
    have h := natCard_add_natCard_compl (fun G : SimpleGraph (Fin n) => ExtensionProperty G k)
    rw [card_simpleGraph] at h
    have h' : (Nat.card {G : SimpleGraph (Fin n) // ExtensionProperty G k} : ℝ) =
        2 ^ n.choose 2 - Nat.card {G : SimpleGraph (Fin n) // ¬ ExtensionProperty G k} := by
      rw [eq_sub_iff_add_eq]; exact_mod_cast h
    rw [hF, h', sub_div, div_self (by positivity)]
  have hbound : ∀ n : ℕ, 1 ≤ n → k ≤ n →
      F n ≤ ((k + 1) ^ 2 * (r ^ k)⁻¹) * ((n : ℝ) ^ (2 * k) * r ^ n) := by
    intro n hn1 hkn
    set small : Finset (Finset (Fin n)) := Finset.univ.filter (fun A => A.card ≤ k) with hsm
    set Pairs := (small ×ˢ small).filter
      (fun p : Finset (Fin n) × Finset (Fin n) => Disjoint p.1 p.2 ∧ p.1.card + p.2.card ≤ k)
      with hPairs
    have hsmall : (small.card : ℝ) ≤ (k + 1) * n ^ k := by
      have : small.card ≤ (k + 1) * n ^ k := by
        calc small.card ≤ ((Finset.range (k + 1)).biUnion
              (fun i => Finset.powersetCard i (Finset.univ : Finset (Fin n)))).card := by
              apply Finset.card_le_card
              intro A hA
              simp only [hsm, Finset.mem_filter, Finset.mem_univ, true_and] at hA
              simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
              exact ⟨A.card, by omega, Finset.subset_univ _, rfl⟩
          _ ≤ ∑ i ∈ Finset.range (k + 1),
              (Finset.powersetCard i (Finset.univ : Finset (Fin n))).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _i ∈ Finset.range (k + 1), n ^ k := Finset.sum_le_sum fun i hi => by
              rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
              exact (Nat.choose_le_pow n i).trans
                (Nat.pow_le_pow_right hn1 (by simp at hi; omega))
          _ = (k + 1) * n ^ k := by simp
      exact_mod_cast this
    have hfail : F n ≤ ∑ p ∈ Pairs,
        (Nat.card {G : SimpleGraph (Fin n) // NoWitness G p.1 p.2} : ℝ) / 2 ^ n.choose 2 := by
      rw [← Finset.sum_div, hF]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : Nat.card {G : SimpleGraph (Fin n) // ¬ ExtensionProperty G k} ≤
          ∑ p ∈ Pairs, Nat.card {G : SimpleGraph (Fin n) // NoWitness G p.1 p.2} := by
        simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
        refine (Finset.card_le_card ?_).trans Finset.card_biUnion_le
        intro G hG
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hG ⊢
        unfold ExtensionProperty at hG
        push Not at hG
        obtain ⟨A, B, hAB, hk, h⟩ := hG
        refine ⟨(A, B), ?_, fun z hzA hzB hw => ?_⟩
        · simp only [hPairs, hsm, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
            true_and]
          exact ⟨⟨by omega, by omega⟩, hAB, hk⟩
        · obtain ⟨b, hb, hadj⟩ := h z hzA hzB hw.1
          exact hw.2 b hb hadj
      exact_mod_cast this
    calc F n ≤ ∑ _p ∈ Pairs, r ^ (n - k) := hfail.trans (Finset.sum_le_sum fun p hp => by
            simp only [hPairs, Finset.mem_filter] at hp
            exact noWitness_bound k hp.2.1 hp.2.2)
      _ = Pairs.card * r ^ (n - k) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((k + 1) * n ^ k) ^ 2 * r ^ (n - k) := by
          gcongr
          calc (Pairs.card : ℝ) ≤ (small ×ˢ small).card := by
                exact_mod_cast Finset.card_filter_le _ _
            _ = small.card * small.card := by rw [Finset.card_product]; push_cast; ring
            _ ≤ ((k + 1) * n ^ k) * ((k + 1) * n ^ k) := by gcongr
            _ = _ := by ring
      _ = _ := by
          have : r ^ n = r ^ (n - k) * r ^ k := by rw [← pow_add, Nat.sub_add_cancel hkn]
          rw [this]
          field_simp
          ring
  have hFlim : Tendsto F atTop (𝓝 0) := by
    have hlim := (tendsto_pow_const_mul_const_pow_of_abs_lt_one (2 * k) (r := r)
      (by rw [abs_lt]; constructor <;> linarith)).const_mul ((k + 1) ^ 2 * (r ^ k)⁻¹ : ℝ)
    rw [mul_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · exact Eventually.of_forall fun n => by rw [hF]; positivity
    · filter_upwards [eventually_ge_atTop (max 1 k)] with n hn
      exact hbound n (le_of_max_le_left hn) (le_of_max_le_right hn)
  have := hFlim.const_sub 1
  rw [sub_zero] at this
  exact this.congr fun n => (hsplit n).symm

end Fagin
