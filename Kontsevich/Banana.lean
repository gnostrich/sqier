module

public import Mathlib
public import Kontsevich.Polys

@[expose] public section

namespace Kontsevich

open MvPolynomial

namespace BananaAux

/-! ### The polynomials of a single edge -/

lemma edge_src_ne_tgt : TTGraph.edge.src ≠ TTGraph.edge.tgt := by
  show (false : Bool) ≠ true
  decide

lemma kirchhoff_edge : kirchhoffPoly TTGraph.edge.ends = 1 := by
  unfold kirchhoffPoly
  rw [Finset.sum_filter, Fintype.sum_eq_single (Finset.univ : Finset TTGraph.edge.E)]
  · rw [if_pos]
    · simp
    · refine ⟨rfl, fun u v => ?_⟩
      change Bool at u v
      cases u <;> cases v
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single ⟨(), Finset.mem_univ _, Or.inl rfl⟩
      · exact Relation.ReflTransGen.single ⟨(), Finset.mem_univ _, Or.inr rfl⟩
      · exact Relation.ReflTransGen.refl
  · intro T hT
    rw [if_neg]
    rintro ⟨h, -⟩
    apply hT
    apply Finset.eq_univ_of_card
    have h2 : Fintype.card TTGraph.edge.V = 2 := rfl
    have h1 : Fintype.card Unit = 1 := rfl
    change T.card + 1 = Fintype.card TTGraph.edge.V at h
    change T.card = Fintype.card Unit
    omega

lemma forest_edge :
    forestPoly TTGraph.edge.ends TTGraph.edge.src TTGraph.edge.tgt = X (R := ℤ) (σ := TTGraph.edge.E) () := by
  unfold forestPoly
  rw [Finset.sum_filter, Fintype.sum_eq_single (∅ : Finset TTGraph.edge.E)]
  · rw [if_pos]
    · rw [Finset.compl_empty]
      exact Finset.prod_singleton (fun x => (X x : MvPolynomial TTGraph.edge.E ℤ)) ()
    · refine ⟨rfl, fun v => ?_, ?_⟩
      · change Bool at v
        cases v
        · exact Or.inl Relation.ReflTransGen.refl
        · exact Or.inr Relation.ReflTransGen.refl
      · intro h
        rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, -, e, he, -⟩
        · exact absurd h (by decide)
        · simp at he
  · intro T hT
    rw [if_neg]
    rintro ⟨h, -⟩
    apply hT
    have h2 : Fintype.card TTGraph.edge.V = 2 := rfl
    change T.card + 2 = Fintype.card TTGraph.edge.V at h
    exact Finset.card_eq_zero.mp (by omega)

lemma kirchhoff_edge' : kirchhoffPoly SP.edge.toGraph.ends = 1 := kirchhoff_edge

lemma forest_edge' :
    forestPoly SP.edge.toGraph.ends SP.edge.toGraph.src SP.edge.toGraph.tgt =
      X (R := ℤ) (σ := SP.edge.toGraph.E) () := forest_edge

/-! ### Evaluations for the banana graphs -/

lemma banana_src_ne_tgt (n : ℕ) : (banana n).toGraph.src ≠ (banana n).toGraph.tgt := by
  induction n with
  | zero => exact edge_src_ne_tgt
  | succ n ih =>
    intro h
    exact ih (Sum.inl_injective h)

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Evaluation of the Kirchhoff polynomial of the banana graph. -/
noncomputable def psi (n : ℕ) (a : (banana n).toGraph.E → F) : F :=
  aeval a (kirchhoffPoly (banana n).toGraph.ends)

/-- Evaluation of the 2-forest polynomial of the banana graph. -/
noncomputable def phi (n : ℕ) (a : (banana n).toGraph.E → F) : F :=
  aeval a (forestPoly (banana n).toGraph.ends (banana n).toGraph.src (banana n).toGraph.tgt)

lemma psi_zero (a : (banana 0).toGraph.E → F) : psi 0 a = 1 :=
  (congrArg (aeval a) kirchhoff_edge).trans (map_one _)

lemma phi_zero (a : (banana 0).toGraph.E → F) : phi 0 a = a () :=
  (congrArg (aeval a) forest_edge).trans (aeval_X _ _)

lemma aeval_kirchhoff_edge (b : SP.edge.toGraph.E → F) :
    aeval b (kirchhoffPoly SP.edge.toGraph.ends) = 1 := by
  rw [kirchhoff_edge', map_one]

lemma aeval_forest_edge (b : SP.edge.toGraph.E → F) :
    aeval b (forestPoly SP.edge.toGraph.ends SP.edge.toGraph.src SP.edge.toGraph.tgt) = b () := by
  rw [forest_edge']
  exact aeval_X b ()

lemma aeval_kirchhoff_parallel (G H : TTGraph) (hG : G.src ≠ G.tgt) (hH : H.src ≠ H.tgt)
    (a : G.E ⊕ H.E → F) :
    aeval (σ := G.E ⊕ H.E) a (kirchhoffPoly (G.parallel H).ends) =
      aeval (a ∘ Sum.inl) (kirchhoffPoly G.ends) * aeval (a ∘ Sum.inr) (forestPoly H.ends H.src H.tgt) +
      aeval (a ∘ Sum.inl) (forestPoly G.ends G.src G.tgt) * aeval (a ∘ Sum.inr) (kirchhoffPoly H.ends) := by
  have h1 := congrArg (aeval (R := ℤ) (σ := G.E ⊕ H.E) a) (kirchhoff_parallel G H hG hH)
  have h2 : aeval (σ := G.E ⊕ H.E) a
      (rename Sum.inl (kirchhoffPoly G.ends) * rename Sum.inr (forestPoly H.ends H.src H.tgt) +
        rename Sum.inl (forestPoly G.ends G.src G.tgt) * rename Sum.inr (kirchhoffPoly H.ends)) =
      aeval (a ∘ Sum.inl) (kirchhoffPoly G.ends) * aeval (a ∘ Sum.inr) (forestPoly H.ends H.src H.tgt) +
      aeval (a ∘ Sum.inl) (forestPoly G.ends G.src G.tgt) * aeval (a ∘ Sum.inr) (kirchhoffPoly H.ends) := by
    simp only [map_add, map_mul, aeval_rename]
  exact h1.trans h2

lemma aeval_forest_parallel (G H : TTGraph) (hG : G.src ≠ G.tgt) (hH : H.src ≠ H.tgt)
    (a : G.E ⊕ H.E → F) :
    aeval (σ := G.E ⊕ H.E) a
        (forestPoly (G.parallel H).ends (G.parallel H).src (G.parallel H).tgt) =
      aeval (a ∘ Sum.inl) (forestPoly G.ends G.src G.tgt) *
        aeval (a ∘ Sum.inr) (forestPoly H.ends H.src H.tgt) := by
  have h1 := congrArg (aeval (R := ℤ) (σ := G.E ⊕ H.E) a) (forest_parallel G H hG hH)
  have h2 : aeval (σ := G.E ⊕ H.E) a
      (rename Sum.inl (forestPoly G.ends G.src G.tgt) *
        rename Sum.inr (forestPoly H.ends H.src H.tgt)) =
      aeval (a ∘ Sum.inl) (forestPoly G.ends G.src G.tgt) *
        aeval (a ∘ Sum.inr) (forestPoly H.ends H.src H.tgt) := by
    simp only [map_mul, aeval_rename]
  exact h1.trans h2

lemma psi_succ (n : ℕ) (a : (banana n).toGraph.E ⊕ SP.edge.toGraph.E → F) :
    psi (n + 1) a = psi n (a ∘ Sum.inl) * a (Sum.inr ()) + phi n (a ∘ Sum.inl) := by
  have h := aeval_kirchhoff_parallel (banana n).toGraph SP.edge.toGraph (banana_src_ne_tgt n)
    edge_src_ne_tgt a
  refine h.trans ?_
  rw [aeval_kirchhoff_edge, aeval_forest_edge, mul_one]
  rfl

lemma phi_succ (n : ℕ) (a : (banana n).toGraph.E ⊕ SP.edge.toGraph.E → F) :
    phi (n + 1) a = phi n (a ∘ Sum.inl) * a (Sum.inr ()) := by
  have h := aeval_forest_parallel (banana n).toGraph SP.edge.toGraph (banana_src_ne_tgt n)
    edge_src_ne_tgt a
  refine h.trans ?_
  rw [aeval_forest_edge]
  rfl

/-! ### Counting in one variable -/

lemma sum_eq_ind (c : F) : ∑ x : F, (if x = c then (1 : ℤ) else 0) = 1 := by
  simp

lemma sum_ne_ind (c : F) :
    ∑ x : F, (if x = c then (0 : ℤ) else 1) = (Fintype.card F : ℤ) - 1 := by
  have h : ∀ x : F, (if x = c then (0 : ℤ) else 1) = 1 - if x = c then 1 else 0 := by
    intro x
    by_cases hx : x = c <;> simp [hx]
  simp only [h, Finset.sum_sub_distrib, sum_eq_ind]
  simp

lemma sum_ne2_ind (c : F) (hc : c ≠ 0) :
    ∑ x : F, (if ¬x = 0 ∧ ¬x = c then (1 : ℤ) else 0) = (Fintype.card F : ℤ) - 2 := by
  have h : ∀ x : F, (if ¬x = 0 ∧ ¬x = c then (1 : ℤ) else 0) =
      1 - (if x = 0 then 1 else 0) - if x = c then 1 else 0 := by
    intro x
    by_cases h0 : x = 0
    · subst h0
      simp [hc.symm]
    · by_cases hx : x = c <;> simp [h0, hx, hc]
  simp only [h, Finset.sum_sub_distrib, sum_eq_ind]
  simp
  ring

lemma lin_iff {u v x : F} (hu : u ≠ 0) : u * x + v = 0 ↔ x = -v / u := by
  rw [eq_div_iff hu]
  constructor <;> intro h <;> linear_combination h

lemma fibA (u v : F) :
    ∑ x : F, (if u * x + v = 0 ∧ v * x = 0 then (1 : ℤ) else 0) =
      (Fintype.card F : ℤ) * (if u = 0 ∧ v = 0 then 1 else 0) +
        (if ¬u = 0 ∧ v = 0 then 1 else 0) := by
  rcases eq_or_ne u 0 with rfl | hu <;> rcases eq_or_ne v 0 with rfl | hv
  · simp
  · simp [hv]
  · simp [hu]
  · have h : ∀ x : F, ¬(u * x + v = 0 ∧ v * x = 0) := by
      rintro x ⟨h1, h2⟩
      rcases mul_eq_zero.mp h2 with h2 | h2
      · exact hv h2
      · subst h2
        simp at h1
        exact hv h1
    rw [Finset.sum_eq_zero (fun x _ => if_neg (h x))]
    simp [hu, hv]

lemma fibB (u v : F) :
    ∑ x : F, (if u * x + v = 0 ∧ ¬v * x = 0 then (1 : ℤ) else 0) =
      (if ¬u = 0 ∧ ¬v = 0 then 1 else 0) := by
  rcases eq_or_ne u 0 with rfl | hu <;> rcases eq_or_ne v 0 with rfl | hv
  · simp
  · simp [hv]
  · simp
  · have h : ∀ x : F, (u * x + v = 0 ∧ ¬v * x = 0) ↔ x = -v / u := by
      intro x
      rw [lin_iff hu]
      constructor
      · exact fun h => h.1
      · rintro rfl
        refine ⟨rfl, ?_⟩
        simp [hu, hv]
    simp only [h]
    simp [hu, hv]

lemma fibC (u v : F) :
    ∑ x : F, (if ¬u * x + v = 0 ∧ v * x = 0 then (1 : ℤ) else 0) =
      (if u = 0 ∧ ¬v = 0 then 1 else 0) +
        ((Fintype.card F : ℤ) - 1) * (if ¬u = 0 ∧ v = 0 then 1 else 0) +
        (if ¬u = 0 ∧ ¬v = 0 then 1 else 0) := by
  rcases eq_or_ne u 0 with rfl | hu <;> rcases eq_or_ne v 0 with rfl | hv
  · simp
  · simp [hv]
  · simp [hu, sum_ne_ind]
  · have h : ∀ x : F, (¬u * x + v = 0 ∧ v * x = 0) ↔ x = 0 := by
      intro x
      constructor
      · rintro ⟨-, h2⟩
        exact (mul_eq_zero.mp h2).resolve_left hv
      · rintro rfl
        simp [hv]
    simp only [h]
    simp [hu, hv]

lemma fibD (u v : F) :
    ∑ x : F, (if ¬u * x + v = 0 ∧ ¬v * x = 0 then (1 : ℤ) else 0) =
      ((Fintype.card F : ℤ) - 1) * (if u = 0 ∧ ¬v = 0 then 1 else 0) +
        ((Fintype.card F : ℤ) - 2) * (if ¬u = 0 ∧ ¬v = 0 then 1 else 0) := by
  rcases eq_or_ne u 0 with rfl | hu <;> rcases eq_or_ne v 0 with rfl | hv
  · simp
  · simp [hv, sum_ne_ind]
  · simp
  · have h : ∀ x : F, (¬u * x + v = 0 ∧ ¬v * x = 0) ↔ (¬x = 0 ∧ ¬x = -v / u) := by
      intro x
      rw [lin_iff hu, mul_eq_zero, not_or]
      tauto
    simp only [h]
    rw [sum_ne2_ind _ (by simp [hu, hv])]
    simp [hu, hv]

/-! ### Counting points of the banana graphs -/

/-- Splitting off the last edge of `banana (n + 1)`. -/
def splitEquiv (n : ℕ) : ((banana (n + 1)).toGraph.E → F) ≃ ((banana n).toGraph.E → F) × F where
  toFun a := (fun e => a (Sum.inl e), a (Sum.inr ()))
  invFun p := Sum.elim p.1 (fun _ => p.2)
  left_inv a := by
    funext i
    rcases i with i | ⟨⟩ <;> rfl
  right_inv p := rfl

lemma sum_succ (n : ℕ) (g : F → F → ℤ) :
    ∑ a : (banana (n + 1)).toGraph.E → F, g (psi (n + 1) a) (phi (n + 1) a) =
      ∑ b : (banana n).toGraph.E → F, ∑ x : F, g (psi n b * x + phi n b) (phi n b * x) := by
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (splitEquiv n) _ _ (fun a => ?_)
  exact congrArg₂ g (psi_succ n a) (phi_succ n a)

/-- The edge-variable map of `banana 0`. -/
def zeroEquiv : ((banana 0).toGraph.E → F) ≃ F where
  toFun a := a ()
  invFun x := fun _ => x
  left_inv a := by
    funext i
    rcases i with ⟨⟩
    rfl
  right_inv x := rfl

lemma sum_zero (g : F → F → ℤ) :
    ∑ a : (banana 0).toGraph.E → F, g (psi 0 a) (phi 0 a) = ∑ x : F, g 1 x := by
  refine Fintype.sum_equiv zeroEquiv _ _ (fun a => ?_)
  rw [psi_zero, phi_zero]
  rfl

variable (F) in
/-- Points where both polynomials vanish. -/
noncomputable def cA (n : ℕ) : ℤ :=
  ∑ a : (banana n).toGraph.E → F, if psi n a = 0 ∧ phi n a = 0 then 1 else 0

variable (F) in
/-- Points where only the Kirchhoff polynomial vanishes. -/
noncomputable def cB (n : ℕ) : ℤ :=
  ∑ a : (banana n).toGraph.E → F, if psi n a = 0 ∧ ¬phi n a = 0 then 1 else 0

variable (F) in
/-- Points where only the forest polynomial vanishes. -/
noncomputable def cC (n : ℕ) : ℤ :=
  ∑ a : (banana n).toGraph.E → F, if ¬psi n a = 0 ∧ phi n a = 0 then 1 else 0

variable (F) in
/-- Points where neither polynomial vanishes. -/
noncomputable def cD (n : ℕ) : ℤ :=
  ∑ a : (banana n).toGraph.E → F, if ¬psi n a = 0 ∧ ¬phi n a = 0 then 1 else 0

lemma cA_zero : cA F 0 = 0 := by
  rw [cA, sum_zero (fun u v => if u = 0 ∧ v = 0 then (1 : ℤ) else 0)]
  simp

lemma cB_zero : cB F 0 = 0 := by
  rw [cB, sum_zero (fun u v => if u = 0 ∧ ¬v = 0 then (1 : ℤ) else 0)]
  simp

lemma cC_zero : cC F 0 = 1 := by
  rw [cC, sum_zero (fun u v => if ¬u = 0 ∧ v = 0 then (1 : ℤ) else 0)]
  simp

lemma cD_zero : cD F 0 = (Fintype.card F : ℤ) - 1 := by
  rw [cD, sum_zero (fun u v => if ¬u = 0 ∧ ¬v = 0 then (1 : ℤ) else 0)]
  simp [sum_ne_ind]

lemma cA_succ (n : ℕ) : cA F (n + 1) = (Fintype.card F : ℤ) * cA F n + cC F n := by
  rw [cA, sum_succ n (fun u v => if u = 0 ∧ v = 0 then (1 : ℤ) else 0)]
  simp only [fibA, Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl

lemma cB_succ (n : ℕ) : cB F (n + 1) = cD F n := by
  rw [cB, sum_succ n (fun u v => if u = 0 ∧ ¬v = 0 then (1 : ℤ) else 0)]
  simp only [fibB]
  rfl

lemma cC_succ (n : ℕ) :
    cC F (n + 1) = cB F n + ((Fintype.card F : ℤ) - 1) * cC F n + cD F n := by
  rw [cC, sum_succ n (fun u v => if ¬u = 0 ∧ v = 0 then (1 : ℤ) else 0)]
  simp only [fibC, Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl

lemma cD_succ (n : ℕ) :
    cD F (n + 1) = ((Fintype.card F : ℤ) - 1) * cB F n + ((Fintype.card F : ℤ) - 2) * cD F n := by
  rw [cD, sum_succ n (fun u v => if ¬u = 0 ∧ ¬v = 0 then (1 : ℤ) else 0)]
  simp only [fibD, Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl

lemma closed (n : ℕ) :
    cA F n = (Fintype.card F : ℤ) ^ (n + 1) - ((Fintype.card F : ℤ) - 1) ^ (n + 1) -
        ((n : ℤ) + 1) * ((Fintype.card F : ℤ) - 1) ^ n ∧
      (Fintype.card F : ℤ) * cB F n =
        ((Fintype.card F : ℤ) - 1) ^ (n + 1) + (-1) ^ (n + 1) * ((Fintype.card F : ℤ) - 1) ∧
      cC F n = ((n : ℤ) + 1) * ((Fintype.card F : ℤ) - 1) ^ n ∧
      cB F n + cD F n = ((Fintype.card F : ℤ) - 1) ^ (n + 1) := by
  induction n with
  | zero =>
    rw [cA_zero, cB_zero, cC_zero, cD_zero]
    refine ⟨by ring, by ring, by ring, by ring⟩
  | succ n ih =>
    obtain ⟨hA, hB, hC, hBD⟩ := ih
    rw [cA_succ, cB_succ, cC_succ, cD_succ]
    push_cast
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination (Fintype.card F : ℤ) * hA + hC
    · linear_combination (Fintype.card F : ℤ) * hBD - hB
    · linear_combination hBD + ((Fintype.card F : ℤ) - 1) * hC
    · linear_combination ((Fintype.card F : ℤ) - 1) * hBD

lemma pointCount_eq (n : ℕ) :
    (pointCount (banana n).toGraph.ends F : ℤ) = cA F n + cB F n := by
  rw [pointCount, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.natCast_card_filter,
    cA, cB, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  change (if psi n a = 0 then (1 : ℤ) else 0) = _
  by_cases h1 : psi n a = 0 <;> by_cases h2 : phi n a = 0 <;> simp [h1, h2]

end BananaAux

open BananaAux in
/-- The point count of the graph hypersurface of the banana graph with `m = n + 1` parallel
edges, multiplied by `q`. -/
theorem banana_count (n : ℕ) (F : Type) [Field F] [Fintype F] :
    (Fintype.card F : ℤ) * pointCount (banana n).toGraph.ends F =
      (Fintype.card F : ℤ) ^ (n + 2) -
        (Fintype.card F : ℤ) * ((Fintype.card F : ℤ) - 1) ^ (n + 1) -
        ((n : ℤ) + 1) * (Fintype.card F : ℤ) * ((Fintype.card F : ℤ) - 1) ^ n +
        ((Fintype.card F : ℤ) - 1) ^ (n + 1) +
        (-1) ^ (n + 1) * ((Fintype.card F : ℤ) - 1) := by
  classical
  obtain ⟨hA, hB, -, -⟩ := closed (F := F) n
  rw [pointCount_eq]
  linear_combination (Fintype.card F : ℤ) * hA + hB

end Kontsevich
