module

public import Mathlib
public import Kontsevich.Polys

@[expose] public section

namespace Kontsevich

open MvPolynomial

/-!
# Point counts of series–parallel graph hypersurfaces

For a two-terminal graph and a finite field `F` with `q` elements, every point `a : E → F`
has a *profile* `(Ψ(a), Φ(a)) ∈ F × F`. We track the following counts of points:
`N` (all points), `Z` (`Ψ = 0`), `A` (`Ψ = Φ = 0`), `C` (`Ψ ≠ 0`, `Φ = 0`) and, for each
`r ≠ 0`, the number of points with `Ψ ≠ 0` and `Φ = r Ψ`, which (by homogeneity, but here
proved by induction) does not depend on `r`; call it `d`. Series and parallel composition
transform these counts by explicit polynomial formulas in `q`, so by induction all of them,
in particular the point count `Z`, are polynomials in `q` with integer coefficients.
-/

namespace Count

section Abstract

variable {F : Type} [Field F]

/-- Number of points `x` whose profile `f x` satisfies `P`. -/
noncomputable def cnt {X : Type} (f : X → F × F) (P : F × F → Prop) : ℤ :=
  Nat.card {x // P (f x)}

/-- `Ψ = 0`. -/
def pZ (u : F × F) : Prop := u.1 = 0

/-- `Ψ = Φ = 0`. -/
def pA (u : F × F) : Prop := u.1 = 0 ∧ u.2 = 0

/-- `Ψ ≠ 0` and `Φ = r Ψ`. -/
def pR (r : F) (u : F × F) : Prop := u.1 ≠ 0 ∧ u.2 = r * u.1

/-- Profile of a series composition. -/
def ser (u v : F × F) : F × F := (u.1 * v.1, u.2 * v.1 + u.1 * v.2)

/-- Exchange of `Ψ` and `Φ`. -/
def sw (u : F × F) : F × F := (u.2, u.1)

/-- The counts of the profile map `f` are `N, Z, A, C, d`. -/
def Good {X : Type} (f : X → F × F) (N Z A C d : ℤ) : Prop :=
  (Nat.card X : ℤ) = N ∧ cnt f pZ = Z ∧ cnt f pA = A ∧ cnt f (pR 0) = C ∧
    ∀ r : F, r ≠ 0 → cnt f (pR r) = d

theorem cnt_eq_sum {X : Type} [Fintype X] (f : X → F × F) (P : F × F → Prop)
    [DecidablePred P] : cnt f P = ∑ x, if P (f x) then (1 : ℤ) else 0 := by
  rw [cnt, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  push_cast
  rfl

theorem cnt_congr {X : Type} (f : X → F × F) {P Q : F × F → Prop} (h : ∀ u, P u ↔ Q u) :
    cnt f P = cnt f Q := by
  have : P = Q := funext fun u => propext (h u)
  rw [this]

theorem card_eq_sum (X : Type) [Fintype X] : (Nat.card X : ℤ) = ∑ _x : X, (1 : ℤ) := by
  simp [Nat.card_eq_fintype_card]

theorem sum_prod_mul {X Y : Type} [Fintype X] [Fintype Y] (a : X → ℤ) (b : Y → ℤ) :
    ∑ p : X × Y, a p.1 * b p.2 = (∑ x, a x) * ∑ y, b y := by
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

theorem good_congr {X : Type} {f g : X → F × F} {N Z A C d N' Z' A' C' d' : ℤ}
    (hfg : ∀ x, f x = g x) (h : Good f N Z A C d) (hN : N = N') (hZ : Z = Z') (hA : A = A')
    (hC : C = C') (hd : d = d') : Good g N' Z' A' C' d' := by
  have : f = g := funext hfg
  subst this hN hZ hA hC hd
  exact h

theorem good_equiv {X Y : Type} {f : X → F × F} (e : Y ≃ X) {N Z A C d : ℤ}
    (h : Good f N Z A C d) : Good (f ∘ e) N Z A C d := by
  have hc : ∀ P : F × F → Prop, cnt (f ∘ e) P = cnt f P := fun P => by
    unfold cnt
    exact congrArg _ (Nat.card_congr (e.subtypeEquiv (p := fun y => P ((f ∘ e) y))
      (q := fun x => P (f x)) fun _ => Iff.rfl))
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by rw [Nat.card_congr e, h1], by rw [hc, h2], by rw [hc, h3], by rw [hc, h4],
    fun r hr => by rw [hc, h5 r hr]⟩

/-- Evaluation of the convolution of two "uniform" ratio distributions. -/
theorem conv_sum [Fintype F] [DecidableEq F] (C₁ d₁ C₂ d₂ : ℤ) (a b : F → ℤ)
    (ha : ∀ s, a s = if s = 0 then C₁ else d₁) (hb : ∀ s, b s = if s = 0 then C₂ else d₂)
    (r : F) : ∑ s, a s * b (r - s) =
      if r = 0 then C₁ * C₂ + (Fintype.card F - 1) * d₁ * d₂
      else C₁ * d₂ + d₁ * C₂ + (Fintype.card F - 2) * d₁ * d₂ := by
  have e : ∀ s, a s * b (r - s) = d₁ * d₂ + (if s = r then d₁ * (C₂ - d₂) else 0) +
      (if s = 0 then (C₁ - d₁) * d₂ else 0) +
      (if s = 0 then (if r = 0 then (C₁ - d₁) * (C₂ - d₂) else 0) else 0) := by
    intro s
    rw [ha, hb]
    by_cases h0 : s = 0 <;> by_cases hr : s = r
    · subst h0; subst hr; simp; ring
    · subst h0
      have : ¬ r = 0 := fun h => hr h.symm
      have : ¬ (0 : F) = r := hr
      simp [*]
    · subst hr; simp [h0]; ring
    · have : ¬ r - s = 0 := fun h => hr (sub_eq_zero.mp h).symm
      simp [h0, hr, this]
  rw [Finset.sum_congr rfl fun s _ => e s]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  split_ifs with hr
  · ring
  · ring

variable [Fintype F]

theorem good_ser {X Y : Type} [Finite X] [Finite Y] {f : X → F × F} {g : Y → F × F}
    {N₁ Z₁ A₁ C₁ d₁ N₂ Z₂ A₂ C₂ d₂ : ℤ} (h₁ : Good f N₁ Z₁ A₁ C₁ d₁)
    (h₂ : Good g N₂ Z₂ A₂ C₂ d₂) :
    Good (fun p : X × Y => ser (f p.1) (g p.2)) (N₁ * N₂) (Z₁ * N₂ + N₁ * Z₂ - Z₁ * Z₂)
      (Z₁ * Z₂ + A₁ * (N₂ - Z₂) + (N₁ - Z₁) * A₂)
      (C₁ * C₂ + (Fintype.card F - 1) * d₁ * d₂)
      (C₁ * d₂ + d₁ * C₂ + (Fintype.card F - 2) * d₁ * d₂) := by
  classical
  have := Fintype.ofFinite X
  have := Fintype.ofFinite Y
  obtain ⟨hN₁, hZ₁, hA₁, hC₁, hd₁⟩ := h₁
  obtain ⟨hN₂, hZ₂, hA₂, hC₂, hd₂⟩ := h₂
  -- the ratio counts as a convolution
  have hR : ∀ r : F, cnt (fun p : X × Y => ser (f p.1) (g p.2)) (pR r) =
      ∑ s, cnt f (pR s) * cnt g (pR (r - s)) := by
    intro r
    simp only [cnt_eq_sum, Finset.sum_mul_sum]
    rw [Fintype.sum_prod_type]
    conv_rhs => rw [Finset.sum_comm]
    conv_rhs => arg 2; ext x; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    dsimp only
    set u := f x
    set v := g y
    by_cases hu : u.1 = 0
    · have : ¬ pR r (ser u v) := by simp [pR, ser, hu]
      rw [if_neg this]
      refine (Finset.sum_eq_zero fun s _ => ?_).symm
      have : ¬ pR s u := by simp [pR, hu]
      rw [if_neg this, zero_mul]
    by_cases hv : v.1 = 0
    · have : ¬ pR r (ser u v) := by simp [pR, ser, hv]
      rw [if_neg this]
      refine (Finset.sum_eq_zero fun s _ => ?_).symm
      have : ¬ pR (r - s) v := by simp [pR, hv]
      rw [if_neg this, mul_zero]
    rw [Finset.sum_eq_single (u.2 / u.1)]
    · have h1 : pR (u.2 / u.1) u := ⟨hu, (div_mul_cancel₀ _ hu).symm⟩
      rw [if_pos h1, one_mul]
      have e1 : pR (r - u.2 / u.1) v ↔ pR r (ser u v) := by
        simp only [pR, ser, ne_eq, mul_eq_zero, hu, hv, or_self, not_false_eq_true,
          true_and]
        constructor
        · intro h; rw [h]; field_simp; ring
        · intro h; field_simp; linear_combination h
      by_cases h : pR r (ser u v)
      · rw [if_pos h, if_pos (e1.mpr h)]
      · rw [if_neg h, if_neg (fun h' => h (e1.mp h'))]
    · intro s _ hs
      have : ¬ pR s u := by
        rintro ⟨-, h⟩
        exact hs (by rw [h, mul_div_cancel_right₀ _ hu])
      rw [if_neg this, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hcR : ∀ {W : Type} (h : W → F × F) (C d : ℤ), cnt h (pR 0) = C → (∀ r : F, r ≠ 0 → cnt h (pR r) = d)
      → ∀ s, cnt h (pR s) = if s = 0 then C else d := by
    intro h C d hC hd s
    split_ifs with hs
    · rw [hs, hC]
    · exact hd s hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_prod, ← hN₁, ← hN₂]; push_cast; ring
  · rw [← hN₁, ← hN₂, ← hZ₁, ← hZ₂, card_eq_sum X, card_eq_sum Y]
    simp only [cnt_eq_sum]
    simp only [← sum_prod_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases ha : (f p.1).1 = 0 <;> by_cases hb : (g p.2).1 = 0 <;> simp [pZ, ser, ha, hb]
  · rw [← hN₁, ← hN₂, ← hZ₁, ← hZ₂, ← hA₁, ← hA₂, card_eq_sum X, card_eq_sum Y]
    simp only [cnt_eq_sum]
    simp only [← Finset.sum_sub_distrib, ← sum_prod_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases ha : (f p.1).1 = 0 <;> by_cases hb : (g p.2).1 = 0 <;>
      by_cases hc : (f p.1).2 = 0 <;> by_cases he : (g p.2).2 = 0 <;>
      simp [pZ, pA, ser, ha, hb, hc, he]
  · rw [hR, conv_sum C₁ d₁ C₂ d₂ _ _ (hcR f C₁ d₁ hC₁ hd₁) (hcR g C₂ d₂ hC₂ hd₂), if_pos rfl]
  · intro r hr
    rw [hR, conv_sum C₁ d₁ C₂ d₂ _ _ (hcR f C₁ d₁ hC₁ hd₁) (hcR g C₂ d₂ hC₂ hd₂), if_neg hr]

theorem good_sw {X : Type} [Finite X] {f : X → F × F} {N Z A C d : ℤ}
    (h : Good f N Z A C d) : Good (fun x => sw (f x)) N (A + C) A (Z - A) d := by
  classical
  have := Fintype.ofFinite X
  obtain ⟨hN, hZ, hA, hC, hd⟩ := h
  refine ⟨hN, ?_, ?_, ?_, ?_⟩
  · rw [← hA, ← hC]
    simp only [cnt_eq_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases ha : (f x).1 = 0 <;> by_cases hb : (f x).2 = 0 <;> simp [pZ, pA, pR, sw, ha, hb]
  · rw [← hA]
    show cnt f (fun u => pA (sw u)) = cnt f pA
    exact cnt_congr f fun u => by simp only [pA, sw]; exact and_comm
  · rw [← hZ, ← hA]
    simp only [cnt_eq_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases ha : (f x).1 = 0 <;> by_cases hb : (f x).2 = 0 <;> simp [pZ, pA, pR, sw, ha, hb]
  · intro r hr
    rw [← hd r⁻¹ (inv_ne_zero hr)]
    show cnt f (fun u => pR r (sw u)) = cnt f (pR r⁻¹)
    refine cnt_congr f fun u => ?_
    simp only [pR, sw]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [h2]; exact mul_ne_zero hr h1, ?_⟩
      rw [h2, ← mul_assoc, inv_mul_cancel₀ hr, one_mul]
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [h2]; exact mul_ne_zero (inv_ne_zero hr) h1, ?_⟩
      rw [h2, ← mul_assoc, mul_inv_cancel₀ hr, one_mul]

end Abstract

section Graphs

/-- The profile `(Ψ(a), Φ(a))` of a point `a` of a two-terminal graph over `F`. -/
noncomputable def prof (G : TTGraph) (F : Type) [Field F] (a : G.E → F) : F × F :=
  (aeval a (kirchhoffPoly G.ends), aeval a (forestPoly G.ends G.src G.tgt))

theorem prof_series (G H : TTGraph) (hG : G.src ≠ G.tgt) (hH : H.src ≠ H.tgt) (F : Type)
    [Field F] (a : G.E ⊕ H.E → F) :
    prof (G.series H) F a = ser (prof G F (a ∘ Sum.inl)) (prof H F (a ∘ Sum.inr)) := by
  simp only [prof, kirchhoff_series, forest_series G H hG hH, map_mul, map_add, aeval_rename,
    ser]

theorem prof_parallel (G H : TTGraph) (hG : G.src ≠ G.tgt) (hH : H.src ≠ H.tgt) (F : Type)
    [Field F] (a : G.E ⊕ H.E → F) :
    prof (G.parallel H) F a =
      sw (ser (sw (prof G F (a ∘ Sum.inl))) (sw (prof H F (a ∘ Sum.inr)))) := by
  simp only [prof, kirchhoff_parallel G H hG hH, forest_parallel G H hG hH, map_mul, map_add,
    aeval_rename, ser, sw]
  ext
  · simp only; ring
  · simp only; ring

theorem kirchhoff_edge : kirchhoffPoly TTGraph.edge.ends = 1 := by
  unfold kirchhoffPoly
  have hV : Fintype.card TTGraph.edge.V = 2 := rfl
  have hE : Fintype.card TTGraph.edge.E = 1 := rfl
  rw [Finset.sum_eq_single Finset.univ]
  · simp
  · intro T hT hne
    rw [Finset.mem_filter] at hT
    exact absurd (Finset.eq_univ_of_card T (by have := hT.2.1; omega)) hne
  · intro h
    exfalso
    apply h
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, by rw [Finset.card_univ, hE, hV], ?_⟩
    intro u v
    have step : Relation.ReflTransGen
        (fun x y => ∃ e ∈ (Finset.univ : Finset TTGraph.edge.E),
          TTGraph.edge.ends e = (x, y) ∨ TTGraph.edge.ends e = (y, x)) false true :=
      Relation.ReflTransGen.single ⟨(), Finset.mem_univ _, Or.inl rfl⟩
    cases u <;> cases v
    · exact Relation.ReflTransGen.refl
    · exact step
    · exact Relation.ReflTransGen.single ⟨(), Finset.mem_univ _, Or.inr rfl⟩
    · exact Relation.ReflTransGen.refl

theorem forest_edge :
    forestPoly TTGraph.edge.ends TTGraph.edge.src TTGraph.edge.tgt = X () := by
  unfold forestPoly
  have hV : Fintype.card TTGraph.edge.V = 2 := rfl
  rw [Finset.sum_eq_single ∅]
  · rw [Finset.compl_empty]
    exact Finset.prod_singleton (fun e : Unit => (X e : MvPolynomial Unit ℤ)) ()
  · intro T hT hne
    rw [Finset.mem_filter] at hT
    exact absurd (Finset.card_eq_zero.mp (by have := hT.2.1; omega)) hne
  · intro h
    exfalso
    apply h
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, by rw [Finset.card_empty, hV], ?_, ?_⟩
    · intro v
      cases v
      · exact Or.inl Relation.ReflTransGen.refl
      · exact Or.inr Relation.ReflTransGen.refl
    · intro hj
      have := (Relation.reflTransGen_iff_eq (fun b => ?_)).mp hj
      · exact Bool.noConfusion this
      · rintro ⟨e, he, -⟩
        exact Finset.notMem_empty e he

theorem good_edge (F : Type) [Field F] [Fintype F] :
    Good (prof TTGraph.edge F) (Fintype.card F) 0 0 1 1 := by
  have hp : ∀ a, prof TTGraph.edge F a = (1, a ()) := fun a => by
    simp [prof, kirchhoff_edge, forest_edge]
  have hR : ∀ r : F, cnt (prof TTGraph.edge F) (pR r) = 1 := by
    intro r
    unfold cnt
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨fun _ => r, ?_⟩⟩⟩
    · obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      rw [hp] at ha hb
      simp only [pR, mul_one] at ha hb
      congr
      funext u
      exact ha.2.trans hb.2.symm
    · rw [hp]; simp [pR]
  refine ⟨?_, ?_, ?_, hR 0, fun r _ => hR r⟩
  · rw [Nat.card_congr (Equiv.funUnique Unit F), Nat.card_eq_fintype_card]
  · unfold cnt
    rw [Nat.card_eq_zero]
    left
    exact ⟨fun ⟨a, ha⟩ => by rw [hp] at ha; simp [pZ] at ha⟩
  · unfold cnt
    rw [Nat.card_eq_zero]
    left
    exact ⟨fun ⟨a, ha⟩ => by rw [hp] at ha; simp [pA] at ha⟩

open Polynomial in
theorem key (s : SP) : s.toGraph.src ≠ s.toGraph.tgt ∧
    ∃ QN QZ QA QC Qd : Polynomial ℤ, ∀ (F : Type) [Field F] [Fintype F],
      Good (prof s.toGraph F) (QN.eval (Fintype.card F : ℤ)) (QZ.eval (Fintype.card F : ℤ))
        (QA.eval (Fintype.card F : ℤ)) (QC.eval (Fintype.card F : ℤ))
        (Qd.eval (Fintype.card F : ℤ)) := by
  induction s with
  | edge =>
    refine ⟨Bool.false_ne_true, X, 0, 0, 1, 1, fun F _ _ => ?_⟩
    exact good_congr (fun _ => rfl) (good_edge F) (by simp) (by simp) (by simp) (by simp)
      (by simp)
  | series s t ihs iht =>
    obtain ⟨hs, QN₁, QZ₁, QA₁, QC₁, Qd₁, h₁⟩ := ihs
    obtain ⟨ht, QN₂, QZ₂, QA₂, QC₂, Qd₂, h₂⟩ := iht
    refine ⟨?_, QN₁ * QN₂, QZ₁ * QN₂ + QN₁ * QZ₂ - QZ₁ * QZ₂,
      QZ₁ * QZ₂ + QA₁ * (QN₂ - QZ₂) + (QN₁ - QZ₁) * QA₂,
      QC₁ * QC₂ + (X - 1) * Qd₁ * Qd₂, QC₁ * Qd₂ + Qd₁ * QC₂ + (X - 2) * Qd₁ * Qd₂,
      fun F _ _ => ?_⟩
    · show (s.toGraph.series t.toGraph).src ≠ (s.toGraph.series t.toGraph).tgt
      simp [TTGraph.series, Ne.symm ht]
    · show Good (prof (s.toGraph.series t.toGraph) F) _ _ _ _ _
      have h := good_equiv (Equiv.sumArrowEquivProdArrow s.toGraph.E t.toGraph.E F)
        (good_ser (h₁ F) (h₂ F))
      refine good_congr (fun a => ?_) h ?_ ?_ ?_ ?_ ?_
      · rw [prof_series _ _ hs ht]; rfl
      all_goals simp only [eval_add, eval_sub, eval_mul, eval_X, eval_one, eval_ofNat]
  | parallel s t ihs iht =>
    obtain ⟨hs, QN₁, QZ₁, QA₁, QC₁, Qd₁, h₁⟩ := ihs
    obtain ⟨ht, QN₂, QZ₂, QA₂, QC₂, Qd₂, h₂⟩ := iht
    refine ⟨?_, QN₁ * QN₂,
      ((QA₁ + QC₁) * (QA₂ + QC₂) + QA₁ * (QN₂ - (QA₂ + QC₂)) + (QN₁ - (QA₁ + QC₁)) * QA₂) +
        ((QZ₁ - QA₁) * (QZ₂ - QA₂) + (X - 1) * Qd₁ * Qd₂),
      (QA₁ + QC₁) * (QA₂ + QC₂) + QA₁ * (QN₂ - (QA₂ + QC₂)) + (QN₁ - (QA₁ + QC₁)) * QA₂,
      ((QA₁ + QC₁) * QN₂ + QN₁ * (QA₂ + QC₂) - (QA₁ + QC₁) * (QA₂ + QC₂)) -
        ((QA₁ + QC₁) * (QA₂ + QC₂) + QA₁ * (QN₂ - (QA₂ + QC₂)) + (QN₁ - (QA₁ + QC₁)) * QA₂),
      (QZ₁ - QA₁) * Qd₂ + Qd₁ * (QZ₂ - QA₂) + (X - 2) * Qd₁ * Qd₂,
      fun F _ _ => ?_⟩
    · show (s.toGraph.parallel t.toGraph).src ≠ (s.toGraph.parallel t.toGraph).tgt
      simp [TTGraph.parallel, hs]
    · show Good (prof (s.toGraph.parallel t.toGraph) F) _ _ _ _ _
      have h := good_equiv (Equiv.sumArrowEquivProdArrow s.toGraph.E t.toGraph.E F)
        (good_sw (good_ser (good_sw (h₁ F)) (good_sw (h₂ F))))
      refine good_congr (fun a => ?_) h ?_ ?_ ?_ ?_ ?_
      · rw [prof_parallel _ _ hs ht]; rfl
      all_goals simp only [eval_add, eval_sub, eval_mul, eval_X, eval_one, eval_ofNat]

end Graphs

end Count

/-- Kontsevich's conjecture holds for series–parallel graphs: the number of points of the
affine graph hypersurface over a finite field with `q` elements is a polynomial in `q` with
integer coefficients, independent of the field. -/
theorem kontsevich_seriesParallel (s : SP) :
    ∃ P : Polynomial ℤ, ∀ (F : Type) [Field F] [Fintype F],
      (pointCount s.toGraph.ends F : ℤ) = P.eval (Fintype.card F : ℤ) := by
  obtain ⟨-, -, QZ, -, -, -, h⟩ := Count.key s
  exact ⟨QZ, fun F _ _ => (h F).2.1⟩

end Kontsevich
