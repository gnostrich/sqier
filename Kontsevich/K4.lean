module

public import Mathlib
public import Kontsevich.Defs

@[expose] public section

/-!
# The point count of the graph hypersurface of `K₄`

We show that the affine graph hypersurface of the complete graph `K₄` has `q²(q³ + q - 1)`
points over a finite field with `q` elements.

* The spanning trees of `K₄` are the sixteen three-edge subsets which are not triangles. We
  decide connectivity by a computable reachability set (three rounds of neighbour expansion
  from vertex `0`), proved sound and complete.
* Hence, with `a, b, c, d, e, f` the variables of the edges `01, 02, 03, 12, 13, 23`,
  `Ψ = a g + h` with `g = f (b + c + d + e) + (b + c)(d + e)` and
  `h = f (b + d)(c + e) + (bcd + bce + bde + cde)`.
* The zeros are counted by repeated elimination of a variable occurring linearly
  (`cnt_lin`): `#{x g + h = 0} = q #{g = h = 0} + #{g ≠ 0}`.
-/

namespace Kontsevich

open MvPolynomial

/-! ### Spanning trees of `K₄` -/

/-- Adjacency of two vertices of `K₄` through an edge of `T`. -/
def k4adj (T : Finset (Fin 6)) (x y : Fin 4) : Prop :=
  ∃ e ∈ T, k4Ends e = (x, y) ∨ k4Ends e = (y, x)

instance (T : Finset (Fin 6)) (x y : Fin 4) : Decidable (k4adj T x y) := by
  unfold k4adj; infer_instance

/-- One round of neighbour expansion. -/
def k4step (T : Finset (Fin 6)) (S : Finset (Fin 4)) : Finset (Fin 4) :=
  S ∪ Finset.univ.filter (fun y => ∃ x ∈ S, k4adj T x y)

/-- The vertices reachable from `0` in at most three steps. -/
def k4R (T : Finset (Fin 6)) : Finset (Fin 4) := k4step T (k4step T (k4step T {0}))

theorem k4R_closed : ∀ T : Finset (Fin 6), k4step T (k4R T) ⊆ k4R T := by decide

theorem k4R_zero : ∀ T : Finset (Fin 6), (0 : Fin 4) ∈ k4R T := by decide

theorem k4step_sound (T : Finset (Fin 6)) (S : Finset (Fin 4))
    (hS : ∀ v ∈ S, Joined k4Ends T 0 v) : ∀ v ∈ k4step T S, Joined k4Ends T 0 v := by
  intro v hv
  simp only [k4step, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with hv | ⟨x, hx, hxv⟩
  · exact hS v hv
  · exact Relation.ReflTransGen.tail (hS x hx) hxv

theorem k4R_sound (T : Finset (Fin 6)) : ∀ v ∈ k4R T, Joined k4Ends T 0 v := by
  refine k4step_sound _ _ (k4step_sound _ _ (k4step_sound _ _ ?_))
  intro v hv
  rw [Finset.mem_singleton] at hv
  subst hv
  exact Relation.ReflTransGen.refl

theorem k4R_complete (T : Finset (Fin 6)) (v : Fin 4) (h : Joined k4Ends T 0 v) :
    v ∈ k4R T := by
  unfold Joined at h
  induction h with
  | refl => exact k4R_zero T
  | tail _ hbc ih =>
    apply k4R_closed T
    simp only [k4step, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inr ⟨_, ih, hbc⟩

theorem k4_joined_symm {T : Finset (Fin 6)} {u v : Fin 4} (h : Joined k4Ends T u v) :
    Joined k4Ends T v u := by
  unfold Joined at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    obtain ⟨e, he, h'⟩ := hbc
    exact Relation.ReflTransGen.head ⟨e, he, h'.symm⟩ ih

theorem isSpanningTree_k4_iff (T : Finset (Fin 6)) :
    IsSpanningTree k4Ends T ↔ T.card = 3 ∧ ∀ v, v ∈ k4R T := by
  unfold IsSpanningTree
  rw [Fintype.card_fin]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, fun v => k4R_complete T v (h2 0 v)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨by omega, fun u v => ?_⟩
    exact Relation.ReflTransGen.trans (k4_joined_symm (k4R_sound T u (h2 u)))
      (k4R_sound T v (h2 v))

/-- The complements of the spanning trees of `K₄`: the three-edge subsets which are not
stars. -/
def k4u : Fin 16 → Finset (Fin 6) :=
  ![{0, 1, 3}, {0, 1, 4}, {0, 1, 5}, {0, 2, 3}, {0, 2, 4}, {0, 2, 5}, {0, 3, 5}, {0, 4, 5},
    {1, 2, 3}, {1, 2, 4}, {1, 2, 5}, {1, 3, 4}, {1, 4, 5}, {2, 3, 4}, {2, 3, 5}, {3, 4, 5}]

theorem k4_class : ∀ T : Finset (Fin 6),
    (T.card = 3 ∧ ∀ v, v ∈ k4R T) ↔ ∃ i, (k4u i)ᶜ = T := by decide

theorem k4u_inj : ∀ i j, (k4u i)ᶜ = (k4u j)ᶜ → i = j := by decide

open Classical in
theorem k4_trees :
    Finset.univ.filter (IsSpanningTree k4Ends) = Finset.univ.image (fun i => (k4u i)ᶜ) := by
  ext T
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    isSpanningTree_k4_iff, k4_class]

theorem kirchhoff_k4 :
    kirchhoffPoly k4Ends = ∑ i : Fin 16, ∏ e ∈ k4u i, (X e : MvPolynomial (Fin 6) ℤ) := by
  unfold kirchhoffPoly
  rw [k4_trees, Finset.sum_image (fun i _ j _ h => k4u_inj i j h)]
  simp only [compl_compl]

/-! ### The explicit polynomial -/

section Poly

variable {F : Type} [Field F]

/-- `b + c + d + e`. -/
def sS (b c d e : F) : F := b + c + d + e
/-- `(b + c)(d + e)`. -/
def sP (b c d e : F) : F := (b + c) * (d + e)
/-- `(b + d)(c + e)`. -/
def sH1 (b c d e : F) : F := (b + d) * (c + e)
/-- `bcd + bce + bde + cde`. -/
def sH0 (b c d e : F) : F := b * c * d + b * c * e + b * d * e + c * d * e
/-- `be - cd`. -/
def sD (b c d e : F) : F := b * e - c * d
/-- The coefficient of `a` in `Ψ_{K₄}`. -/
def gK (f b c d e : F) : F := f * sS b c d e + sP b c d e
/-- The part of `Ψ_{K₄}` free of `a`. -/
def hK (f b c d e : F) : F := f * sH1 b c d e + sH0 b c d e

theorem aeval_k4 (a : Fin 6 → F) :
    aeval a (kirchhoffPoly k4Ends) =
      a 0 * gK (a 5) (a 1) (a 2) (a 3) (a 4) + hK (a 5) (a 1) (a 2) (a 3) (a 4) := by
  rw [kirchhoff_k4]
  simp [Fin.sum_univ_succ, k4u, Finset.prod_insert]
  simp only [gK, hK, sS, sP, sH1, sH0]
  ring

theorem alg_c2 (b c d e : F) :
    sS b c d e = 0 ∧ sP b c d e = 0 ↔ b + (c + d + e) = 0 ∧ d + e = 0 := by
  simp only [sS, sP]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : (d + e) * (d + e) = 0 := by linear_combination (d + e) * h1 - h2
    exact ⟨by linear_combination h1, mul_self_eq_zero.mp h3⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linear_combination h1, by linear_combination (b + c) * h2⟩

theorem alg_c4 (b c d e : F) :
    sS b c d e = 0 ∧ sD b c d e = 0 ↔ b + (c + d + e) = 0 ∧ (d + e) * (c + e) = 0 := by
  simp only [sS, sD]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linear_combination h1, by linear_combination e * h1 - h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linear_combination h1, by linear_combination e * h1 - h2⟩

theorem alg_c6 (b c d e : F) :
    sH1 b c d e = 0 ∧ sS b c d e = 0 ∧ sP b c d e = 0 ↔
      b + c = 0 ∧ (c + -d = 0 ∧ d + e = 0) := by
  simp only [sH1, sS, sP]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hbc' : (b + c) * (b + c) = 0 := by linear_combination (b + c) * h2 - h3
    have hbc := mul_self_eq_zero.mp hbc'
    have hde : d + e = 0 := by linear_combination h2 - hbc
    have hbd' : (b + d) * (b + d) = 0 := by linear_combination (b + d) * h2 - h1
    have hbd := mul_self_eq_zero.mp hbd'
    exact ⟨hbc, by linear_combination hbc - hbd, hde⟩
  · rintro ⟨h1, h2, h3⟩
    have hc : c = -b := by linear_combination h1
    have hd : d = -b := by linear_combination h1 - h2
    have he : e = b := by linear_combination h3 - h1 + h2
    subst hc hd he
    exact ⟨by ring, by ring, by ring⟩

theorem alg_c5 (b c d e : F) :
    sH1 b c d e = 0 ∧ sH0 b c d e = 0 ∧ sS b c d e = 0 ∧ sP b c d e = 0 ↔
      b + c = 0 ∧ (c + -d = 0 ∧ d + e = 0) := by
  constructor
  · rintro ⟨h1, -, h3⟩
    exact (alg_c6 b c d e).mp ⟨h1, h3⟩
  · intro h
    have h' := (alg_c6 b c d e).mpr h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h'.1, ?_, h'.2⟩
    have hc : c = -b := by linear_combination h1
    have hd : d = -b := by linear_combination h1 - h2
    have he : e = b := by linear_combination h3 - h1 + h2
    subst hc hd he
    simp only [sH0]
    ring

theorem alg_B (f b c d e : F) :
    (gK f b c d e = 0 ∧ hK f b c d e = 0) ∧ sS b c d e = 0 ↔
      f * sH1 b c d e + sH0 b c d e = 0 ∧ (sS b c d e = 0 ∧ sP b c d e = 0) := by
  simp only [gK, hK]
  constructor
  · rintro ⟨⟨hg, hh⟩, hS⟩
    rw [hS, mul_zero, zero_add] at hg
    exact ⟨hh, hS, hg⟩
  · rintro ⟨hh, hS, hP⟩
    exact ⟨⟨by rw [hS, hP]; ring, hh⟩, hS⟩

theorem alg_A (f b c d e : F) :
    (gK f b c d e = 0 ∧ hK f b c d e = 0) ∧ ¬ sS b c d e = 0 ↔
      f * sS b c d e + sP b c d e = 0 ∧ (sD b c d e = 0 ∧ sS b c d e ≠ 0) := by
  simp only [gK, hK, sS, sP, sH1, sH0, sD]
  constructor
  · rintro ⟨⟨hg, hh⟩, hS⟩
    have h : (b * e - c * d) * (b * e - c * d) = 0 := by
      linear_combination ((b + d) * (c + e)) * hg - (b + c + d + e) * hh
    exact ⟨hg, mul_self_eq_zero.mp h, hS⟩
  · rintro ⟨hg, hD, hS⟩
    have h : (b + c + d + e) *
        (f * ((b + d) * (c + e)) + (b * c * d + b * c * e + b * d * e + c * d * e)) = 0 := by
      linear_combination ((b + d) * (c + e)) * hg - (b * e - c * d) * hD
    exact ⟨⟨hg, (mul_eq_zero.mp h).resolve_left hS⟩, hS⟩

end Poly

/-! ### Counting -/

/-- The number of points satisfying a predicate, as an integer. -/
noncomputable def cnt {α : Type} (P : α → Prop) : ℤ := (Nat.card {x // P x} : ℤ)

section Count

variable {α β : Type} [Fintype α]

theorem cnt_congr_eq {P Q : α → Prop} {n : ℤ} (h : ∀ x, P x ↔ Q x) (hQ : cnt Q = n) :
    cnt P = n := by
  have : P = Q := funext fun x => propext (h x)
  rw [this, hQ]

theorem cnt_equiv {P : α → Prop} {Q : β → Prop} (e : α ≃ β) (h : ∀ x, P x ↔ Q (e x)) :
    cnt P = cnt Q := by
  unfold cnt
  rw [Nat.card_congr (e.subtypeEquiv h)]

open Classical in
theorem cnt_eq_sum (P : α → Prop) : cnt P = ∑ x, if P x then (1 : ℤ) else 0 := by
  unfold cnt
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  push_cast
  rfl

theorem cnt_split_eq (P Q : α → Prop) {A B n : ℤ} (hA : cnt (fun x => P x ∧ Q x) = A)
    (hB : cnt (fun x => P x ∧ ¬ Q x) = B) (hn : A + B = n) : cnt P = n := by
  classical
  rw [← hn, ← hA, ← hB]
  simp only [cnt_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hP : P x <;> by_cases hQ : Q x <;> simp [hP, hQ]

theorem cnt_univ_eq {n : ℤ} (h : (Fintype.card α : ℤ) = n) :
    cnt (fun _ : α => True) = n := by
  rw [← h, cnt_eq_sum]
  simp

theorem cnt_false {P : α → Prop} (h : ∀ x, ¬ P x) : cnt P = 0 := by
  simp [cnt_eq_sum, h]

theorem cnt_ne_eq {F : Type} [Field F] {g : α → F} {R : α → Prop} {A B n : ℤ}
    (hA : cnt R = A) (hB : cnt (fun y => g y = 0 ∧ R y) = B) (hn : A - B = n) :
    cnt (fun y => g y ≠ 0 ∧ R y) = n := by
  have := cnt_split_eq R (fun y => g y = 0) (A := B) (B := cnt (fun y => g y ≠ 0 ∧ R y))
    (cnt_congr_eq (fun y => and_comm) hB) (cnt_congr_eq (fun y => and_comm) rfl) rfl
  rw [hA] at this
  linarith

theorem cnt_ne'_eq {F : Type} [Field F] {g : α → F} {B n : ℤ}
    (hB : cnt (fun y => g y = 0) = B) (hn : (Fintype.card α : ℤ) - B = n) :
    cnt (fun y => g y ≠ 0) = n := by
  have := cnt_ne_eq (g := g) (R := fun _ => True) (cnt_univ_eq rfl)
    (cnt_congr_eq (fun y => by simp) hB) hn
  exact cnt_congr_eq (fun y => by simp) this

variable {F : Type} [Field F] [Fintype F]

local notation "q" => (Fintype.card F : ℤ)

theorem cnt_lin {P : F × α → Prop} (g h : α → F) (R : α → Prop)
    (hP : ∀ x y, P (x, y) ↔ x * g y + h y = 0 ∧ R y) :
    cnt P = q * cnt (fun y => g y = 0 ∧ h y = 0 ∧ R y) + cnt (fun y => g y ≠ 0 ∧ R y) := by
  classical
  rw [cnt_eq_sum, cnt_eq_sum, cnt_eq_sum, Fintype.sum_prod_type, Finset.sum_comm,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [hP]
  by_cases hR : R y
  · by_cases hg : g y = 0
    · by_cases hh : h y = 0
      · simp [hR, hg, hh]
      · simp [hR, hg, hh]
    · have key : ∀ x, (x * g y + h y = 0 ↔ x = -h y / g y) := by
        intro x
        rw [eq_div_iff hg]
        constructor
        · intro hx; linear_combination hx
        · intro hx; linear_combination hx
      simp [hR, hg, key]
  · simp [hR]

theorem cnt_lin_eq {P : F × α → Prop} (g h : α → F) (R : α → Prop)
    (hP : ∀ x y, P (x, y) ↔ x * g y + h y = 0 ∧ R y) {A B n : ℤ}
    (hA : cnt (fun y => g y = 0 ∧ h y = 0 ∧ R y) = A) (hB : cnt (fun y => g y ≠ 0 ∧ R y) = B)
    (hn : q * A + B = n) : cnt P = n := by
  rw [← hn, ← hA, ← hB, cnt_lin g h R hP]

theorem cnt_lin'_eq {P : F × α → Prop} (g h : α → F)
    (hP : ∀ x y, P (x, y) ↔ x * g y + h y = 0) {A B n : ℤ}
    (hA : cnt (fun y => g y = 0 ∧ h y = 0) = A) (hB : cnt (fun y => g y ≠ 0) = B)
    (hn : q * A + B = n) : cnt P = n :=
  cnt_lin_eq g h (fun _ => True) (fun x y => by simpa using hP x y)
    (cnt_congr_eq (fun y => by simp) hA) (cnt_congr_eq (fun y => by simp) hB) hn

theorem cnt_solve_eq {P : F × α → Prop} (h : α → F) (R : α → Prop)
    (hP : ∀ x y, P (x, y) ↔ x + h y = 0 ∧ R y) {n : ℤ} (hR : cnt R = n) : cnt P = n :=
  cnt_lin_eq (fun _ => 1) h R (fun x y => by rw [hP, mul_one])
    (cnt_false (fun y => by simp)) (cnt_congr_eq (fun y => by simp) hR) (by ring)

theorem cnt_indep_eq {P : F × α → Prop} (R : α → Prop)
    (hP : ∀ x y, P (x, y) ↔ R y) {A n : ℤ} (hR : cnt R = A) (hn : q * A = n) : cnt P = n :=
  cnt_lin_eq (fun _ => 0) (fun _ => 0) R (fun x y => by rw [hP]; simp)
    (cnt_congr_eq (fun y => by simp) hR) (cnt_false (fun y => by simp)) (by rw [← hn]; ring)

/-! #### Small counts -/

theorem cV1 : cnt (fun w : F × Unit => w.1 = 0) = 1 :=
  cnt_solve_eq (fun _ => 0) (fun _ => True) (fun x y => by simp) (cnt_univ_eq (by simp))

theorem cV2 : cnt (fun w : F × F × Unit => w.1 + w.2.1 = 0) = q :=
  cnt_solve_eq (fun v => v.1) (fun _ => True) (fun x y => by simp) (cnt_univ_eq (by simp))

theorem cV2e : cnt (fun w : F × F × Unit => w.2.1 = 0) = q :=
  cnt_indep_eq (fun v => v.1 = 0) (fun _ _ => Iff.rfl) cV1 (by ring)

theorem cV2de : cnt (fun w : F × F × Unit => w.1 = 0 ∧ w.2.1 = 0) = 1 :=
  cnt_solve_eq (fun _ => 0) (fun v => v.1 = 0) (fun x y => by simp) cV1

theorem cV2dne : cnt (fun w : F × F × Unit => w.1 ≠ 0 ∧ w.2.1 = 0) = q - 1 :=
  cnt_ne_eq (g := fun w => w.1) cV2e cV2de rfl

theorem cV3e : cnt (fun u : F × F × F × Unit => u.2.2.1 = 0) = q ^ 2 :=
  cnt_indep_eq (fun w => w.2.1 = 0) (fun _ _ => Iff.rfl) cV2e (by ring)

theorem cV3ne : cnt (fun u : F × F × F × Unit => u.2.2.1 ≠ 0) = q ^ 3 - q ^ 2 :=
  cnt_ne'_eq cV3e (by push_cast [Fintype.card_prod, Fintype.card_unit]; ring)

theorem cV3cd :
    cnt (fun u : F × F × F × Unit => u.2.2.1 = 0 ∧ -(u.1 * u.2.1) = 0) = 2 * q - 1 :=
  cnt_lin_eq (fun w => w.1) (fun _ => 0) (fun w => w.2.1 = 0)
    (fun x y => by simp only [neg_eq_zero, add_zero]; exact and_comm)
    (cnt_congr_eq (fun w => by simp) cV2de) cV2dne (by ring)

theorem cV3c4 :
    cnt (fun u : F × F × F × Unit => (u.2.1 + u.2.2.1) * (u.1 + u.2.2.1) = 0) =
      2 * q ^ 2 - q :=
  cnt_lin'_eq (fun w => w.1 + w.2.1) (fun w => w.2.1 * (w.1 + w.2.1))
    (fun x y => by constructor <;> intro h <;> linear_combination h)
    (cnt_congr_eq (fun w => ⟨fun h => h.1, fun h => ⟨h, by rw [h, mul_zero]⟩⟩) cV2)
    (cnt_ne'_eq (n := q ^ 2 - q) cV2 (by push_cast [Fintype.card_prod, Fintype.card_unit]; ring))
    (by ring)

/-! #### Counts in the four variables `b c d e` -/

theorem c1 :
    cnt (fun z : F × F × F × F × Unit => sS z.1 z.2.1 z.2.2.1 z.2.2.2.1 = 0) = q ^ 3 :=
  cnt_solve_eq (fun u => u.1 + u.2.1 + u.2.2.1) (fun _ => True)
    (fun x y => by simp only [sS, add_assoc, and_true])
    (cnt_univ_eq (by push_cast [Fintype.card_prod, Fintype.card_unit]; ring))

theorem c1ne :
    cnt (fun z : F × F × F × F × Unit => sS z.1 z.2.1 z.2.2.1 z.2.2.2.1 ≠ 0) = q ^ 4 - q ^ 3 :=
  cnt_ne'_eq c1 (by push_cast [Fintype.card_prod, Fintype.card_unit]; ring)

theorem c2 :
    cnt (fun z : F × F × F × F × Unit =>
      sS z.1 z.2.1 z.2.2.1 z.2.2.2.1 = 0 ∧ sP z.1 z.2.1 z.2.2.1 z.2.2.2.1 = 0) = q ^ 2 :=
  cnt_congr_eq (fun z => alg_c2 z.1 z.2.1 z.2.2.1 z.2.2.2.1) <|
    cnt_solve_eq (fun u => u.1 + u.2.1 + u.2.2.1) (fun u => u.2.1 + u.2.2.1 = 0)
      (fun _ _ => Iff.rfl) <|
    cnt_indep_eq (fun w => w.1 + w.2.1 = 0) (fun _ _ => Iff.rfl) cV2 (by ring)

theorem c3 :
    cnt (fun z : F × F × F × F × Unit => sD z.1 z.2.1 z.2.2.1 z.2.2.2.1 = 0) =
      q ^ 3 + q ^ 2 - q :=
  cnt_lin'_eq (fun u => u.2.2.1) (fun u => -(u.1 * u.2.1))
    (fun x y => by simp only [sD, sub_eq_add_neg]) cV3cd cV3ne (by ring)

theorem c4 :
    cnt (fun z : F × F × F × F × Unit =>
      sS z.1 z.2.1 z.2.2.1 z.2.2.2.1 = 0 ∧ sD z.1 z.2.1 z.2.2.1 z.2.2.2.1 = 0) =
      2 * q ^ 2 - q :=
  cnt_congr_eq (fun z => alg_c4 z.1 z.2.1 z.2.2.1 z.2.2.2.1) <|
    cnt_solve_eq (fun u => u.1 + u.2.1 + u.2.2.1)
      (fun u => (u.2.1 + u.2.2.1) * (u.1 + u.2.2.1) = 0) (fun _ _ => Iff.rfl) cV3c4

theorem c6 :
    cnt (fun z : F × F × F × F × Unit =>
      sH1 z.1 z.2.1 z.2.2.1 z.2.2.2.1 = 0 ∧ sS z.1 z.2.1 z.2.2.1 z.2.2.2.1 = 0 ∧
        sP z.1 z.2.1 z.2.2.1 z.2.2.2.1 = 0) = q :=
  cnt_congr_eq (fun z => alg_c6 z.1 z.2.1 z.2.2.1 z.2.2.2.1) <|
    cnt_solve_eq (fun u => u.1) (fun u => u.1 + -u.2.1 = 0 ∧ u.2.1 + u.2.2.1 = 0)
      (fun _ _ => Iff.rfl) <|
    cnt_solve_eq (fun w => -w.1) (fun w => w.1 + w.2.1 = 0) (fun _ _ => Iff.rfl) cV2

theorem c5 :
    cnt (fun z : F × F × F × F × Unit =>
      sH1 z.1 z.2.1 z.2.2.1 z.2.2.2.1 = 0 ∧ sH0 z.1 z.2.1 z.2.2.1 z.2.2.2.1 = 0 ∧
        sS z.1 z.2.1 z.2.2.1 z.2.2.2.1 = 0 ∧ sP z.1 z.2.1 z.2.2.1 z.2.2.2.1 = 0) = q :=
  cnt_congr_eq (fun z => alg_c5 z.1 z.2.1 z.2.2.1 z.2.2.2.1) <|
    cnt_solve_eq (fun u => u.1) (fun u => u.1 + -u.2.1 = 0 ∧ u.2.1 + u.2.2.1 = 0)
      (fun _ _ => Iff.rfl) <|
    cnt_solve_eq (fun w => -w.1) (fun w => w.1 + w.2.1 = 0) (fun _ _ => Iff.rfl) cV2

/-! #### Counts in the five variables `f b c d e` -/

theorem cg :
    cnt (fun y : F × F × F × F × F × Unit =>
      gK y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1 = 0) = q ^ 4 :=
  by
  refine cnt_lin'_eq (A := q ^ 2) (B := q ^ 4 - q ^ 3) (fun z => sS z.1 z.2.1 z.2.2.1 z.2.2.2.1)
    (fun z => sP z.1 z.2.1 z.2.2.1 z.2.2.2.1) ?_ ?_ ?_ ?_
  · intro x y; exact Iff.rfl
  · exact c2
  · exact c1ne
  · ring

theorem cgne :
    cnt (fun y : F × F × F × F × F × Unit =>
      gK y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1 ≠ 0) = q ^ 5 - q ^ 4 :=
  cnt_ne'_eq cg (by push_cast [Fintype.card_prod, Fintype.card_unit]; ring)

theorem cgh :
    cnt (fun y : F × F × F × F × F × Unit =>
      gK y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1 = 0 ∧
        hK y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1 = 0) = q ^ 3 + q ^ 2 - q := by
  refine cnt_split_eq _ (fun y => sS y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1 = 0)
    (A := 2 * q ^ 2 - q) (B := q ^ 3 - q ^ 2) ?_ ?_ (by ring)
  · refine cnt_lin_eq (A := q) (B := q ^ 2 - q) (fun z => sH1 z.1 z.2.1 z.2.2.1 z.2.2.2.1)
      (fun z => sH0 z.1 z.2.1 z.2.2.1 z.2.2.2.1)
      (fun z => sS z.1 z.2.1 z.2.2.1 z.2.2.2.1 = 0 ∧ sP z.1 z.2.1 z.2.2.1 z.2.2.2.1 = 0)
      ?_ ?_ ?_ (by ring)
    · exact fun x y => alg_B x y.1 y.2.1 y.2.2.1 y.2.2.2.1
    · exact c5
    · exact cnt_ne_eq c2 c6 (by ring)
  · refine cnt_lin_eq (A := 0) (B := q ^ 3 - q ^ 2) (fun z => sS z.1 z.2.1 z.2.2.1 z.2.2.2.1)
      (fun z => sP z.1 z.2.1 z.2.2.1 z.2.2.2.1)
      (fun z => sD z.1 z.2.1 z.2.2.1 z.2.2.2.1 = 0 ∧ sS z.1 z.2.1 z.2.2.1 z.2.2.2.1 ≠ 0)
      ?_ ?_ ?_ (by ring)
    · exact fun x y => alg_A x y.1 y.2.1 y.2.2.1 y.2.2.2.1
    · exact cnt_false (fun z h => h.2.2.2 h.1)
    exact cnt_congr_eq (fun z => ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, h.1⟩⟩)
      (cnt_ne_eq (R := fun z : F × F × F × F × Unit => sD z.1 z.2.1 z.2.2.1 z.2.2.2.1 = 0)
        c3 c4 (by ring))

/-! #### The six variables -/

theorem cfinal :
    cnt (fun p : F × F × F × F × F × F × Unit =>
      p.1 * gK p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 +
        hK p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 = 0) = q ^ 5 + q ^ 3 - q ^ 2 :=
  by
  refine cnt_lin'_eq (A := q ^ 3 + q ^ 2 - q) (B := q ^ 5 - q ^ 4)
    (fun y => gK y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1)
    (fun y => hK y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1) ?_ ?_ ?_ ?_
  · intro x y; exact Iff.rfl
  · exact cgh
  · exact cgne
  · ring

/-- Reordering the coordinates as `(a, f, b, c, d, e)`. -/
def k4Equiv : (Fin 6 → F) ≃ F × F × F × F × F × F × Unit where
  toFun a := (a 0, a 5, a 1, a 2, a 3, a 4, ())
  invFun p := ![p.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.1]
  left_inv a := by ext i; fin_cases i <;> rfl
  right_inv p := rfl

end Count

/-- The graph hypersurface of `K₄` has `q²(q³ + q - 1)` points over a field with `q`
elements. -/
theorem k4_count (F : Type) [Field F] [Fintype F] :
    (pointCount k4Ends F : ℤ) =
      (Fintype.card F : ℤ) ^ 2 * ((Fintype.card F : ℤ) ^ 3 + (Fintype.card F : ℤ) - 1) := by
  have h1 : (pointCount k4Ends F : ℤ) =
      cnt (fun a : Fin 6 → F => aeval a (kirchhoffPoly k4Ends) = 0) := rfl
  rw [h1, cnt_equiv (Q := fun p : F × F × F × F × F × F × Unit =>
      p.1 * gK p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 +
        hK p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 = 0) k4Equiv
      (fun a => by rw [aeval_k4]; rfl), cfinal]
  ring

end Kontsevich
