module

public import Mathlib
public import Squier.Transfer
public import Squier.CriticalPair
public import Squier.S3Aux

@[expose] public section

/-!
# Growth series of monoids presented by complete rewriting systems

* the Thue congruence: two words represent the same element of the presented monoid iff they
  are related by the equivalence closure of the rewriting relation;
* for a terminating confluent system, every element has a unique normal form, a word is a
  normal form iff it avoids every left-hand side, and so the growth function is a count of
  words avoiding finitely many factors, whose generating function is rational;
* the examples `s3` (growth `1 + 2z + 2z² + z³`, six elements) and `comm2` (growth `n + 1`).
-/

namespace Squier

namespace GrowthAux

variable {α : Type*}

/-! ### The Thue congruence -/

theorem eqvGen_whisker {R : Finset (List α × List α)} {u v : List α} (x y : List α)
    (h : Relation.EqvGen (Rewrites R) u v) :
    Relation.EqvGen (Rewrites R) (x ++ u ++ y) (x ++ v ++ y) := by
  induction h with
  | rel a b h => exact .rel _ _ (rewrites_whisker x y h)
  | refl a => exact .refl _
  | symm a b _ ih => exact .symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

theorem eqvGen_of_conGen {R : Finset (List α × List α)} {x y : FreeMonoid α}
    (h : conGen (presentedRels R) x y) :
    Relation.EqvGen (Rewrites R) x.toList y.toList := by
  change ConGen.Rel _ x y at h
  induction h with
  | of x y h => exact .rel _ _ ⟨⟨[], (x.toList, y.toList), h, [], by simp, by simp⟩⟩
  | refl x => exact .refl _
  | symm _ ih => exact .symm _ _ ih
  | trans _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
  | @mul w x y z _ _ ih₁ ih₂ =>
    simp only [FreeMonoid.toList_mul]
    exact .trans _ _ _ (by simpa using eqvGen_whisker [] y.toList ih₁)
      (by simpa using eqvGen_whisker x.toList [] ih₂)

theorem conGen_of_eqvGen {R : Finset (List α × List α)} {u v : List α}
    (h : Relation.EqvGen (Rewrites R) u v) :
    conGen (presentedRels R) (FreeMonoid.ofList u) (FreeMonoid.ofList v) := by
  induction h with
  | rel u v h =>
    obtain ⟨s⟩ := h
    rw [s.src_eq, s.tgt_eq]
    simp only [FreeMonoid.ofList_append]
    refine (conGen _).mul ((conGen _).mul ((conGen _).refl _) (ConGen.Rel.of _ _ ?_))
      ((conGen _).refl _)
    simpa [presentedRels] using s.mem
  | refl u => exact (conGen _).refl _
  | symm u v _ ih => exact (conGen _).symm ih
  | trans u v w _ _ ih₁ ih₂ => exact (conGen _).trans ih₁ ih₂

theorem mk_eq_mk_iff {R : Finset (List α × List α)} {u v : List α} :
    PresentedMonoid.mk (presentedRels R) (FreeMonoid.ofList u) =
        PresentedMonoid.mk (presentedRels R) (FreeMonoid.ofList v) ↔
      Relation.EqvGen (Rewrites R) u v := by
  rw [PresentedMonoid.mk_eq_mk_iff]
  exact ⟨fun h => eqvGen_of_conGen h, conGen_of_eqvGen⟩

/-! ### Normal forms -/

theorem eqvGen_of_reflTransGen {R : Finset (List α × List α)} {u v : List α}
    (h : Relation.ReflTransGen (Rewrites R) u v) : Relation.EqvGen (Rewrites R) u v := by
  induction h with
  | refl => exact .refl _
  | tail _ h ih => exact .trans _ _ _ ih (.rel _ _ h)

theorem exists_normalForm {R : Finset (List α × List α)} (hR : Terminating R) (u : List α) :
    ∃ v, Relation.ReflTransGen (Rewrites R) u v ∧ IsNormalForm R v := by
  induction u using hR.induction with
  | _ u ih =>
  by_cases h : IsNormalForm R u
  · exact ⟨u, .refl, h⟩
  · simp only [IsNormalForm, not_forall, not_not] at h
    obtain ⟨v, hv⟩ := h
    obtain ⟨w, hw, hnf⟩ := ih v hv
    exact ⟨w, .head hv hw, hnf⟩

theorem joinable_of_eqvGen {R : Finset (List α × List α)} (hc : Confluent R) {u v : List α}
    (h : Relation.EqvGen (Rewrites R) u v) : Joinable R u v := by
  induction h with
  | rel u v h => exact ⟨v, .single h, .refl⟩
  | refl u => exact ⟨u, .refl, .refl⟩
  | symm u v _ ih =>
    obtain ⟨w, h₁, h₂⟩ := ih
    exact ⟨w, h₂, h₁⟩
  | trans u v w _ _ ih₁ ih₂ =>
    obtain ⟨a, hua, hva⟩ := ih₁
    obtain ⟨b, hvb, hwb⟩ := ih₂
    obtain ⟨c, hac, hbc⟩ := hc hva hvb
    exact ⟨c, hua.trans hac, hwb.trans hbc⟩

theorem eq_of_normalForm {R : Finset (List α × List α)} {u v : List α} (hu : IsNormalForm R u)
    (h : Relation.ReflTransGen (Rewrites R) u v) : u = v := by
  rcases h.cases_head with h | ⟨w, huw, _⟩
  · exact h
  · exact absurd huw (hu w)

theorem isNormalForm_iff [DecidableEq α] (R : Finset (List α × List α)) (w : List α) :
    IsNormalForm R w ↔ ∀ l ∈ R.image Prod.fst, ¬ l <:+: w := by
  simp only [Finset.mem_image]
  constructor
  · rintro h l ⟨ρ, hρ, rfl⟩ ⟨s, t, hst⟩
    exact h _ ⟨⟨s, ρ, hρ, t, hst.symm, rfl⟩⟩
  · rintro h v ⟨s⟩
    exact h _ ⟨s.rule, s.mem, rfl⟩ ⟨s.pre, s.suf, s.src_eq.symm⟩

end GrowthAux

open GrowthAux

/-- For a terminating, confluent system, every element of the presented monoid has exactly one
normal-form representative. -/
theorem unique_normalForm {α : Type*} (R : Finset (List α × List α)) (hR : Terminating R)
    (hc : Confluent R) (m : PresentedMonoid (presentedRels R)) :
    ∃! w : List α, IsNormalForm R w ∧
      PresentedMonoid.mk (presentedRels R) (FreeMonoid.ofList w) = m := by
  obtain ⟨x, rfl⟩ := PresentedMonoid.surjective_mk m
  rw [← FreeMonoid.ofList_toList x]
  obtain ⟨v, hxv, hnf⟩ := exists_normalForm hR x.toList
  refine ⟨v, ⟨hnf, mk_eq_mk_iff.2 (eqvGen_of_reflTransGen hxv).symm⟩, ?_⟩
  rintro w ⟨hw, hwm⟩
  have hwv : Relation.EqvGen (Rewrites R) w v :=
    .trans _ _ _ (mk_eq_mk_iff.1 hwm) (eqvGen_of_reflTransGen hxv)
  obtain ⟨c, hwc, hvc⟩ := joinable_of_eqvGen hc hwv
  exact (eq_of_normalForm hw hwc).trans (eq_of_normalForm hnf hvc).symm

/-- The number of elements with a normal form of length `n` is the number of words of length
`n` avoiding every left-hand side. -/
theorem growth_eq_avoidCount {α : Type*} [Fintype α] [DecidableEq α]
    (R : Finset (List α × List α)) (hR : Terminating R) (hc : Confluent R) (n : ℕ) :
    growth R n = avoidCount (R.image Prod.fst) n := by
  unfold growth avoidCount
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun v => ⟨PresentedMonoid.mk (presentedRels R) (FreeMonoid.ofList v.1.toList),
      v.1.toList, v.1.toList_length, (isNormalForm_iff R _).2 v.2, rfl⟩) ⟨?_, ?_⟩)
  · rintro ⟨v₁, h₁⟩ ⟨v₂, h₂⟩ h
    simp only [Subtype.mk.injEq] at h
    obtain ⟨w, -, hw⟩ := unique_normalForm R hR hc
      (PresentedMonoid.mk (presentedRels R) (FreeMonoid.ofList v₁.toList))
    have e₁ := hw _ ⟨(isNormalForm_iff R _).2 h₁, rfl⟩
    have e₂ := hw _ ⟨(isNormalForm_iff R _).2 h₂, h.symm⟩
    exact Subtype.ext (List.Vector.toList_injective (e₁.trans e₂.symm))
  · rintro ⟨m, w, hl, hnf, rfl⟩
    exact ⟨⟨⟨w, hl⟩, (isNormalForm_iff R w).1 hnf⟩, rfl⟩

/-- The growth series of a monoid with a finite complete rewriting system over a finite
alphabet (with respect to normal-form length) is rational. -/
theorem growth_rational {α : Type*} [Fintype α] [DecidableEq α]
    (R : Finset (List α × List α)) (hR : Terminating R) (hc : Confluent R) :
    HasRationalGF fun n => (growth R n : ℤ) := by
  have h : (fun n => (growth R n : ℤ)) = fun n => (avoidCount (R.image Prod.fst) n : ℤ) :=
    funext fun n => by rw [growth_eq_avoidCount R hR hc n]
  rw [h]
  exact avoidCount_rational _

namespace GrowthAux

/-! ### The example `s3` -/

theorem s3_confluent : Confluent s3 :=
  (confluent_iff_criticalPairs_joinable s3 S3Aux.terminating).mpr S3Aux.joinable

theorem s3_lhs : s3.image Prod.fst = {[0, 0], [1, 1], [1, 0, 1]} := by decide

/-- The six normal forms of `s3`. -/
def s3NF : Finset (List (Fin 2)) := {[], [0], [1], [0, 1], [1, 0], [0, 1, 0]}

theorem s3_long (w : List (Fin 2)) (h : 4 ≤ w.length) :
    ∃ f ∈ ({[0, 0], [1, 1], [1, 0, 1]} : Finset (List (Fin 2))), f <:+: w := by
  rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, w⟩⟩⟩⟩
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · have key : ∀ a b c d : Fin 2,
        ∃ f ∈ ({[0, 0], [1, 1], [1, 0, 1]} : Finset (List (Fin 2))), f <:+: [a, b, c, d] := by
      decide
    obtain ⟨f, hf, hi⟩ := key a b c d
    exact ⟨f, hf, hi.trans (List.prefix_append [a, b, c, d] w).isInfix⟩

theorem s3_avoid_iff (w : List (Fin 2)) :
    (∀ f ∈ ({[0, 0], [1, 1], [1, 0, 1]} : Finset (List (Fin 2))), ¬ f <:+: w) ↔ w ∈ s3NF := by
  rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, w⟩⟩⟩⟩
  · decide
  · revert a; decide
  · revert a b; decide
  · revert a b c; decide
  · constructor
    · intro h
      obtain ⟨f, hf, hi⟩ := s3_long (a :: b :: c :: d :: w) (by simp)
      exact absurd hi (h f hf)
    · intro h
      simp [s3NF] at h

end GrowthAux

/-- The growth series of `S₃` with respect to `s3` is `1 + 2z + 2z² + z³`. -/
theorem s3_growth (n : ℕ) : growth s3 n = [1, 2, 2, 1].getD n 0 := by
  rw [growth_eq_avoidCount s3 S3Aux.terminating s3_confluent, s3_lhs]
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | n + 4 =>
    simp only [List.getD_eq_getElem?_getD, List.length_cons, List.length_nil,
      List.getElem?_eq_none (by omega : 4 ≤ n + 4), Option.getD_none]
    unfold avoidCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v _ h
    obtain ⟨f, hf, hi⟩ := s3_long v.toList (by simp)
    exact h f hf hi

/-- The monoid presented by `s3` has six elements. -/
theorem s3_card : Nat.card (PresentedMonoid (presentedRels s3)) = 6 := by
  have e : PresentedMonoid (presentedRels s3) ≃ {w // w ∈ s3NF} := by
    refine (Equiv.ofBijective
      (fun w : {w // w ∈ s3NF} => PresentedMonoid.mk (presentedRels s3) (FreeMonoid.ofList w.1))
      ⟨?_, ?_⟩).symm
    · rintro ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h
      have n₁ : IsNormalForm s3 w₁ := by
        rw [isNormalForm_iff, s3_lhs, s3_avoid_iff]; exact h₁
      have n₂ : IsNormalForm s3 w₂ := by
        rw [isNormalForm_iff, s3_lhs, s3_avoid_iff]; exact h₂
      obtain ⟨w, -, hw⟩ := unique_normalForm s3 S3Aux.terminating s3_confluent
        (PresentedMonoid.mk (presentedRels s3) (FreeMonoid.ofList w₁))
      exact Subtype.ext ((hw _ ⟨n₁, rfl⟩).trans (hw _ ⟨n₂, h.symm⟩).symm)
    · intro m
      obtain ⟨w, ⟨hw, hwm⟩, -⟩ := unique_normalForm s3 S3Aux.terminating s3_confluent m
      rw [isNormalForm_iff, s3_lhs, s3_avoid_iff] at hw
      exact ⟨⟨w, hw⟩, hwm⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  rfl

namespace GrowthAux

/-! ### The example `comm2` -/

/-- The number of inversions (pairs `true` before `false`) of a word. -/
def inversions : List Bool → ℕ
  | [] => 0
  | b :: w => (if b then w.count false else 0) + inversions w

theorem inversions_append (x y : List Bool) :
    inversions (x ++ y) = inversions x + inversions y + x.count true * y.count false := by
  induction x with
  | nil => simp [inversions]
  | cons b x ih =>
    simp only [List.cons_append, inversions, ih, List.count_append, List.count_cons]
    cases b <;> simp <;> ring

theorem inversions_lt {u v : List Bool} (s : Step comm2 u v) : inversions v < inversions u := by
  obtain ⟨pre, ρ, mem, suf, rfl, rfl⟩ := s
  simp only [comm2, Finset.mem_singleton] at mem
  subst mem
  simp only [inversions_append, List.count_append]
  simp [inversions]

theorem comm2_terminating : Terminating comm2 :=
  Subrelation.wf (r := InvImage (· < ·) inversions)
    (fun {_ _} h => h.elim fun s => inversions_lt s) (InvImage.wf inversions wellFounded_lt)

theorem comm2_overlap {p₂ s₁ s₂ : List Bool}
    (h : [true, false] ++ s₁ = p₂ ++ [true, false] ++ s₂) (hp : p₂ ≠ []) :
    ∃ b, p₂ = [] ++ [true, false] ++ b ∧ s₁ = b ++ [true, false] ++ s₂ := by
  rcases p₂ with _ | ⟨c, _ | ⟨d, p⟩⟩
  · exact absurd rfl hp
  · simp at h
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl, h⟩ := h
    exact ⟨p, rfl, by simpa using h⟩

theorem comm2_confluent : Confluent comm2 := by
  refine (confluent_iff_criticalPairs_joinable comm2 comm2_terminating).mpr ?_
  rintro ⟨src, t₁, t₂, ⟨p₁, r₁, m₁, s₁, hs₁, ht₁⟩, ⟨p₂, r₂, m₂, s₂, hs₂, ht₂⟩⟩
    ⟨hne, hni, hp, -⟩
  exfalso
  simp only [comm2, Finset.mem_singleton] at m₁ m₂
  subst m₁ m₂
  simp only [ne_eq, not_true_eq_false, or_false] at hne
  have hsrc := hs₁.symm.trans hs₂
  simp only [Step.Independent] at hni
  rcases hp with rfl | rfl
  · exact hni (Or.inl (comm2_overlap (by simpa using hsrc) (Ne.symm hne)))
  · exact hni (Or.inr (comm2_overlap (by simpa using hsrc.symm) hne))

theorem comm2_lhs : comm2.image Prod.fst = {[true, false]} := by decide

theorem eq_replicate_of_avoid (w : List Bool) (h : ¬ [true, false] <:+: w) :
    ∃ i j, w = List.replicate i false ++ List.replicate j true := by
  induction w with
  | nil => exact ⟨0, 0, rfl⟩
  | cons a w ih =>
    obtain ⟨i, j, rfl⟩ := ih fun hi => h (hi.trans (List.suffix_cons a _).isInfix)
    cases a
    · exact ⟨i + 1, j, by simp [List.replicate_succ]⟩
    · rcases i with _ | i
      · exact ⟨0, j + 1, by simp [List.replicate_succ]⟩
      · exact absurd ⟨[], List.replicate i false ++ List.replicate j true, by
          simp [List.replicate_succ]⟩ h

theorem avoid_replicate (i j : ℕ) :
    ¬ [true, false] <:+: List.replicate i false ++ List.replicate j true := by
  have hp : (List.replicate i false ++ List.replicate j true).Pairwise (· ≤ ·) := by
    simp [List.pairwise_append, List.pairwise_replicate]
  intro hi
  have := hp.sublist hi.sublist
  simp at this

theorem comm2_avoidCount (n : ℕ) : avoidCount {[true, false]} n = n + 1 := by
  unfold avoidCount
  have himg : (Finset.univ.filter fun w : List.Vector Bool n =>
      ∀ f ∈ ({[true, false]} : Finset (List Bool)), ¬ f <:+: w.toList) =
      Finset.univ.image fun i : Fin (n + 1) =>
        (⟨List.replicate i false ++ List.replicate (n - i) true, by
          simp only [List.length_append, List.length_replicate]; omega⟩ : List.Vector Bool n) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, forall_eq,
      Finset.mem_image]
    constructor
    · intro h
      obtain ⟨i, j, hij⟩ := eq_replicate_of_avoid v.toList h
      have hl := congrArg List.length hij
      simp only [List.Vector.toList_length, List.length_append, List.length_replicate] at hl
      refine ⟨⟨i, by omega⟩, Subtype.ext ?_⟩
      change _ = v.toList
      rw [hij]
      congr 2
      omega
    · rintro ⟨i, rfl⟩
      exact avoid_replicate _ _
  rw [himg, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro i₁ i₂ h
  have := congrArg (fun v : List.Vector Bool n => v.toList.count false) h
  simp [List.Vector.toList] at this
  exact Fin.ext this

end GrowthAux

/-- The free commutative monoid on two generators, presented by `ba → ab`, has `n + 1`
elements of normal-form length `n`. -/
theorem comm2_growth (n : ℕ) : growth comm2 n = n + 1 := by
  rw [growth_eq_avoidCount comm2 comm2_terminating comm2_confluent, comm2_lhs]
  exact comm2_avoidCount n

end Squier
