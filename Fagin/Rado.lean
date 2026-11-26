module

public import Mathlib
public import Fagin.Defs

@[expose] public section

/-!
# The Rado graph

We prove that the Rado graph `radoGraph` has every extension property, and that any two countable
graphs with every extension property are isomorphic (by a back-and-forth argument).
-/

namespace Fagin

open FirstOrder FirstOrder.Language Filter Topology

theorem testBit_sum_two_pow (s : Finset ℕ) (x : ℕ) :
    Nat.testBit (∑ i ∈ s, 2 ^ i) x = true ↔ x ∈ s := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow]

/-- The Rado graph has every extension property. -/
theorem radoGraph_extension (k : ℕ) : ExtensionProperty radoGraph k := by
  intro A B _ _
  set N := (A ∪ B).sup id + 1 with hN
  have hlt : ∀ x ∈ A ∪ B, x < N := fun x hx => by
    have := Finset.le_sup (f := id) hx
    simp only [id] at this
    omega
  set z := ∑ i ∈ insert N A, 2 ^ i with hz
  have hNz : N < z := (Nat.lt_two_pow_self).trans_le
    (Finset.single_le_sum (f := fun i => 2 ^ i) (by simp) (Finset.mem_insert_self _ _))
  have key : ∀ x ∈ A ∪ B, (radoGraph.Adj z x ↔ x ∈ A) := by
    intro x hx
    have hxz : x < z := (hlt x hx).trans hNz
    change z ≠ x ∧ Nat.testBit (max z x) (min z x) = true ↔ _
    rw [max_eq_left hxz.le, min_eq_right hxz.le, hz, testBit_sum_two_pow, Finset.mem_insert]
    have := hlt x hx
    constructor
    · rintro ⟨-, h | h⟩
      · omega
      · exact h
    · intro h; exact ⟨by omega, Or.inr h⟩
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · intro h; have := hlt z (Finset.mem_union_left _ h); omega
  · intro h; have := hlt z (Finset.mem_union_right _ h); omega
  · intro a ha; exact (key a (Finset.mem_union_left _ ha)).2 ha
  · intro b hb h
    have := (key b (Finset.mem_union_right _ hb)).1 h
    exact Finset.disjoint_left.1 ‹Disjoint A B› this hb

/-- A finite set of pairs is a partial isomorphism between `G` and `H`. -/
def IsPartialIso {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (p : Finset (V × W)) :
    Prop :=
  ∀ q ∈ p, ∀ r ∈ p, (q.1 = r.1 ↔ q.2 = r.2) ∧ (G.Adj q.1 r.1 ↔ H.Adj q.2 r.2)

theorem IsPartialIso.swap {V W : Type*} [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}
    {p : Finset (V × W)} (hp : IsPartialIso G H p) :
    IsPartialIso H G (p.image Prod.swap) := by
  intro q hq r hr
  simp only [Finset.mem_image] at hq hr
  obtain ⟨q, hq, rfl⟩ := hq
  obtain ⟨r, hr, rfl⟩ := hr
  obtain ⟨h1, h2⟩ := hp q hq r hr
  exact ⟨h1.symm, h2.symm⟩

theorem IsPartialIso.forth {V W : Type*} [DecidableEq V] [DecidableEq W] {G : SimpleGraph V}
    {H : SimpleGraph W} (hH : ∀ k, ExtensionProperty H k) {p : Finset (V × W)}
    (hp : IsPartialIso G H p) (v : V) : ∃ w, IsPartialIso G H (insert (v, w) p) := by
  classical
  by_cases hv : ∃ w, (v, w) ∈ p
  · obtain ⟨w, hw⟩ := hv
    exact ⟨w, by rwa [Finset.insert_eq_of_mem hw]⟩
  push Not at hv
  set A := (p.filter (fun q => G.Adj v q.1)).image Prod.snd
  set B := (p.filter (fun q => ¬ G.Adj v q.1)).image Prod.snd
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro b hA hB
    simp only [A, B, Finset.mem_image, Finset.mem_filter] at hA hB
    obtain ⟨q, ⟨hq, hq'⟩, rfl⟩ := hA
    obtain ⟨r, ⟨hr, hr'⟩, hrq⟩ := hB
    have := ((hp q hq r hr).1).2 hrq.symm
    rw [this] at hq'
    exact hr' hq'
  obtain ⟨z, hzA, hzB, hzA', hzB'⟩ := hH (A.card + B.card) A B hAB le_rfl
  have hmem : ∀ r ∈ p, (G.Adj v r.1 → r.2 ∈ A) ∧ (¬ G.Adj v r.1 → r.2 ∈ B) := by
    intro r hr
    exact ⟨fun h => Finset.mem_image.2 ⟨r, Finset.mem_filter.2 ⟨hr, h⟩, rfl⟩,
      fun h => Finset.mem_image.2 ⟨r, Finset.mem_filter.2 ⟨hr, h⟩, rfl⟩⟩
  have new : ∀ r ∈ p, (v = r.1 ↔ z = r.2) ∧ (G.Adj v r.1 ↔ H.Adj z r.2) := by
    intro r hr
    have hne1 : v ≠ r.1 := fun h => hv r.2 (by rw [h]; exact hr)
    have hne2 : z ≠ r.2 := by
      intro h
      by_cases hadj : G.Adj v r.1
      · exact hzA (h ▸ (hmem r hr).1 hadj)
      · exact hzB (h ▸ (hmem r hr).2 hadj)
    refine ⟨⟨fun h => absurd h hne1, fun h => absurd h hne2⟩, ?_⟩
    constructor
    · intro hadj; exact hzA' _ ((hmem r hr).1 hadj)
    · intro hadj
      by_contra hn
      exact hzB' _ ((hmem r hr).2 hn) hadj
  refine ⟨z, ?_⟩
  intro q hq r hr
  rw [Finset.mem_insert] at hq hr
  rcases hq with rfl | hq <;> rcases hr with rfl | hr
  · simp
  · exact new r hr
  · obtain ⟨h1, h2⟩ := new q hq
    exact ⟨by rw [eq_comm, h1, eq_comm], by rw [G.adj_comm, h2, H.adj_comm]⟩
  · exact hp q hq r hr

theorem IsPartialIso.back {V W : Type*} [DecidableEq V] [DecidableEq W] {G : SimpleGraph V}
    {H : SimpleGraph W} (hG : ∀ k, ExtensionProperty G k) {p : Finset (V × W)}
    (hp : IsPartialIso G H p) (w : W) : ∃ v, IsPartialIso G H (insert (v, w) p) := by
  obtain ⟨v, hv⟩ := hp.swap.forth hG w
  refine ⟨v, ?_⟩
  have := hv.swap
  rwa [Finset.image_insert, Finset.image_image, Prod.swap_swap_eq, Finset.image_id] at this

/-- Any two countable graphs with every extension property are isomorphic. -/
theorem nonempty_iso_of_extension {V W : Type*} [Countable V] [Countable W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hG : ∀ k, ExtensionProperty G k)
    (hH : ∀ k, ExtensionProperty H k) : Nonempty (G ≃g H) := by
  classical
  have : Nonempty V := by
    obtain ⟨z, -⟩ := hG 0 ∅ ∅ (by simp) (by simp)
    exact ⟨z⟩
  have : Nonempty W := by
    obtain ⟨z, -⟩ := hH 0 ∅ ∅ (by simp) (by simp)
    exact ⟨z⟩
  obtain ⟨eV, heV⟩ := exists_surjective_nat V
  obtain ⟨eW, heW⟩ := exists_surjective_nat W
  let P := {p : Finset (V × W) // IsPartialIso G H p}
  have hstep : ∀ (p : P) (n : ℕ), ∃ q : P, p.1 ⊆ q.1 ∧ (∃ w, (eV n, w) ∈ q.1) ∧
      ∃ v, (v, eW n) ∈ q.1 := by
    intro p n
    obtain ⟨w, hw⟩ := p.2.forth hH (eV n)
    obtain ⟨v, hv⟩ := hw.back hG (eW n)
    refine ⟨⟨_, hv⟩, ?_, ⟨w, ?_⟩, ⟨v, Finset.mem_insert_self _ _⟩⟩
    · exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  choose step hsub hdom hcod using hstep
  let seq : ℕ → P := fun n => Nat.rec ⟨∅, by simp [IsPartialIso]⟩ (fun n p => step p n) n
  have hseq : ∀ n, seq (n + 1) = step (seq n) n := fun n => rfl
  have hmono : Monotone (fun n => (seq n).1) :=
    monotone_nat_of_le_succ (fun n => by rw [hseq]; exact hsub _ _)
  let R : V → W → Prop := fun v w => ∃ n, (v, w) ∈ (seq n).1
  -- any two pairs in `R` lie in a common partial isomorphism
  have hcommon : ∀ v w v' w', R v w → R v' w' →
      (v = v' ↔ w = w') ∧ (G.Adj v v' ↔ H.Adj w w') := by
    rintro v w v' w' ⟨n, hn⟩ ⟨m, hm⟩
    exact (seq (max n m)).2 (v, w) (hmono (le_max_left n m) hn) (v', w')
      (hmono (le_max_right n m) hm)
  have htot : ∀ v, ∃ w, R v w := by
    intro v
    obtain ⟨n, rfl⟩ := heV v
    obtain ⟨w, hw⟩ := hdom (seq n) n
    exact ⟨w, n + 1, by rw [hseq]; exact hw⟩
  have hsurj : ∀ w, ∃ v, R v w := by
    intro w
    obtain ⟨n, rfl⟩ := heW w
    obtain ⟨v, hv⟩ := hcod (seq n) n
    exact ⟨v, n + 1, by rw [hseq]; exact hv⟩
  choose f hf using htot
  have hinj : Function.Injective f := fun v v' h =>
    ((hcommon _ _ _ _ (hf v) (hf v')).1).2 h
  have hfsurj : Function.Surjective f := by
    intro w
    obtain ⟨v, hv⟩ := hsurj w
    exact ⟨v, ((hcommon _ _ _ _ (hf v) hv).1).1 rfl⟩
  exact ⟨⟨Equiv.ofBijective f ⟨hinj, hfsurj⟩, fun {a b} =>
    ((hcommon _ _ _ _ (hf a) (hf b)).2).symm⟩⟩

end Fagin
