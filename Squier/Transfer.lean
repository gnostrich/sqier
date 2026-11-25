module

public import Mathlib
public import Squier.GrowthDefs

@[expose] public section

/-!
# Rationality of the generating function of words avoiding finitely many factors

We prove that for a finite set `F` of forbidden factors over a finite alphabet, the number of
words of length `n` avoiding every element of `F` has a rational generating function.

The proof goes through a transfer matrix:
* `hasRationalGF_of_rec`: a sequence satisfying, from some point on, a linear recurrence whose
  characteristic polynomial is monic has a rational generating function;
* `hasRationalGF_of_matrix`: by Cayley–Hamilton, any sequence of the form
  `a (n + N) = u ⬝ᵥ (M ^ n *ᵥ v)` satisfies such a recurrence;
* `avoidCount_rational`: with `k` the maximal length of a forbidden word, the states are the
  words of length `k`, and the number of avoiding extensions of a state satisfies a transfer
  matrix recursion.
-/

namespace Squier

/-- A sequence satisfying eventually a linear recurrence with monic characteristic polynomial
has a rational generating function. -/
theorem hasRationalGF_of_rec (a : ℕ → ℤ) (c : Polynomial ℤ) (hc : c.Monic) (N : ℕ)
    (h : ∀ m, ∑ j ∈ Finset.range (c.natDegree + 1), c.coeff j * a (m + j + N) = 0) :
    HasRationalGF a := by
  set d := c.natDegree with hd
  refine ⟨PowerSeries.trunc (N + d) ((c.reverse : PowerSeries ℤ) * PowerSeries.mk a),
    c.reverse, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_reverse]; exact hc
  · ext n
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hn
    · rfl
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + N + d := ⟨n - N - d, by omega⟩
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [Polynomial.coeff_coe, PowerSeries.coeff_mk]
      rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : d + 1 ≤ m + N + d + 1))]
      · rw [← Finset.sum_range_reflect, ← h m]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [Polynomial.coeff_reverse, ← hd, Polynomial.revAt_le (by omega),
          show d - (d + 1 - 1 - j) = j by omega,
          show m + N + d - (d + 1 - 1 - j) = m + j + N by omega]
      · intro i _ hi
        rw [Finset.mem_range] at hi
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt, zero_mul]
        calc c.reverse.natDegree ≤ d := Polynomial.natDegree_reverse c
          _ < i := by omega

/-- A sequence given by a transfer matrix, from some offset on, has a rational generating
function (Cayley–Hamilton). -/
theorem hasRationalGF_of_matrix {S : Type*} [Fintype S] [DecidableEq S] (a : ℕ → ℤ) (N : ℕ)
    (M : Matrix S S ℤ) (u v : S → ℤ) (h : ∀ n, a (n + N) = u ⬝ᵥ (M ^ n *ᵥ v)) :
    HasRationalGF a := by
  refine hasRationalGF_of_rec a M.charpoly (Matrix.charpoly_monic M) N fun m => ?_
  have h0 : ∑ j ∈ Finset.range (M.charpoly.natDegree + 1), M.charpoly.coeff j • M ^ j = 0 := by
    rw [← Polynomial.aeval_eq_sum_range]; exact Matrix.aeval_self_charpoly M
  have key : ∀ j, M.charpoly.coeff j * a (m + j + N) =
      u ⬝ᵥ ((M ^ m * (M.charpoly.coeff j • M ^ j)) *ᵥ v) := by
    intro j
    rw [h, Matrix.mul_smul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, pow_add]
  simp_rw [key]
  have hsum : ∀ (s : Finset ℕ) (A : ℕ → Matrix S S ℤ),
      ∑ j ∈ s, u ⬝ᵥ (A j *ᵥ v) = u ⬝ᵥ ((∑ j ∈ s, A j) *ᵥ v) := by
    intro s A
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih => simp [Finset.sum_insert hx, ih, Matrix.add_mulVec, dotProduct_add]
  rw [hsum, ← Finset.mul_sum, h0, mul_zero]
  simp

/-- Splitting off the head of a vector. -/
def vectorConsEquiv (α : Type*) (n : ℕ) : α × List.Vector α n ≃ List.Vector α (n + 1) where
  toFun p := p.1 ::ᵥ p.2
  invFun v := (v.head, v.tail)
  left_inv p := by simp
  right_inv v := by simp

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The number of words `w` of length `n` such that `l ++ w` avoids `F`. -/
def extCount (F : Finset (List α)) (n : ℕ) (l : List α) : ℤ :=
  ∑ w : List.Vector α n, if ∀ f ∈ F, ¬ f <:+: l ++ w.toList then 1 else 0

theorem avoidCount_eq_extCount (F : Finset (List α)) (n : ℕ) :
    (avoidCount F n : ℤ) = extCount F n [] := by
  simp [avoidCount, extCount, Finset.card_filter]

theorem extCount_succ (F : Finset (List α)) (n : ℕ) (l : List α) :
    extCount F (n + 1) l = ∑ x : α, extCount F n (l ++ [x]) := by
  unfold extCount
  rw [← (vectorConsEquiv α n).sum_comp, Fintype.sum_prod_type]
  simp [vectorConsEquiv]

theorem extCount_add (F : Finset (List α)) (n : ℕ) :
    ∀ (j : ℕ) (l : List α),
      extCount F (n + j) l = ∑ s : List.Vector α j, extCount F n (l ++ s.toList)
  | 0, l => by
    rw [Fintype.sum_subsingleton _ List.Vector.nil]
    simp
  | j + 1, l => by
    rw [← add_assoc, extCount_succ]
    simp_rw [extCount_add F n j]
    rw [← (vectorConsEquiv α j).sum_comp, Fintype.sum_prod_type]
    simp [vectorConsEquiv]

theorem extCount_cons (F : Finset (List α)) (n : ℕ) (l : List α) (hl : l ≠ [])
    (hF : ∀ f ∈ F, f.length ≤ l.length) :
    extCount F n l = (if ∀ f ∈ F, ¬ f <+: l then 1 else 0) * extCount F n l.tail := by
  obtain ⟨b, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  have hiff : ∀ w : List α, (∀ f ∈ F, ¬ f <:+: b :: l' ++ w) ↔
      (∀ f ∈ F, ¬ f <+: b :: l') ∧ (∀ f ∈ F, ¬ f <:+: l' ++ w) := by
    intro w
    constructor
    · intro H
      refine ⟨fun f hf hp => H f hf ?_, fun f hf hi => H f hf ?_⟩
      · exact (hp.trans (List.prefix_append _ _)).isInfix
      · exact List.infix_cons_iff.2 (Or.inr (by simpa using hi))
    · rintro ⟨H1, H2⟩ f hf hi
      rw [List.cons_append, List.infix_cons_iff] at hi
      rcases hi with hp | hi
      · refine H1 f hf (List.prefix_of_prefix_length_le hp ?_ (hF f hf))
        rw [← List.cons_append]; exact List.prefix_append _ _
      · exact H2 f hf hi
  unfold extCount
  simp_rw [hiff]
  by_cases h1 : ∀ f ∈ F, ¬ f <+: b :: l'
  · simp [h1]
  · simp [h1]

/-- The transfer matrix on states of length `k`. -/
def nextState (k : ℕ) (s : List.Vector α k) (x : α) : List.Vector α k :=
  ⟨(s.toList ++ [x]).tail, by simp⟩

/-- The transfer matrix. -/
def transferMatrix (F : Finset (List α)) (k : ℕ) : Matrix (List.Vector α k) (List.Vector α k) ℤ :=
  fun s t => ∑ x : α, if (∀ f ∈ F, ¬ f <+: s.toList ++ [x]) ∧ t = nextState k s x then 1 else 0

theorem extCount_transfer (F : Finset (List α)) (k : ℕ) (hk : ∀ f ∈ F, f.length ≤ k) (n : ℕ) :
    (fun s : List.Vector α k => extCount F (n + 1) s.toList) =
      transferMatrix F k *ᵥ fun s => extCount F n s.toList := by
  funext s
  rw [extCount_succ]
  simp only [Matrix.mulVec, dotProduct, transferMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [extCount_cons F n _ (by simp) (fun f hf => by simpa using (hk f hf).trans (Nat.le_succ k))]
  by_cases h1 : ∀ f ∈ F, ¬ f <+: s.toList ++ [x]
  · simp only [h1, true_and, if_true, one_mul, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ]
    rfl
  · simp [h1]

theorem extCount_pow (F : Finset (List α)) (k : ℕ) (hk : ∀ f ∈ F, f.length ≤ k) (n : ℕ) :
    (fun s : List.Vector α k => extCount F n s.toList) =
      transferMatrix F k ^ n *ᵥ fun s => extCount F 0 s.toList := by
  induction n with
  | zero => simp
  | succ n ih => rw [extCount_transfer F k hk, ih, Matrix.mulVec_mulVec, ← pow_succ']

/-- Words avoiding a finite set of factors have a rational generating function. -/
theorem avoidCount_rational {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (List α)) :
    HasRationalGF fun n => (avoidCount F n : ℤ) := by
  set k := F.sup List.length
  have hk : ∀ f ∈ F, f.length ≤ k := fun f hf => Finset.le_sup (f := List.length) hf
  refine hasRationalGF_of_matrix _ k (transferMatrix F k) (fun _ => 1)
    (fun s => extCount F 0 s.toList) fun n => ?_
  rw [← extCount_pow F k hk, avoidCount_eq_extCount, extCount_add]
  simp [dotProduct]

end Squier
