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
  rw [kirchhoff_edge', forest_edge', map_one, mul_one]
  erw [aeval_X]
  rfl

lemma phi_succ (n : ℕ) (a : (banana n).toGraph.E ⊕ SP.edge.toGraph.E → F) :
    phi (n + 1) a = phi n (a ∘ Sum.inl) * a (Sum.inr ()) := by
  have h := aeval_forest_parallel (banana n).toGraph SP.edge.toGraph (banana_src_ne_tgt n)
    edge_src_ne_tgt a
  refine h.trans ?_
  rw [forest_edge']
  erw [aeval_X]
  rfl

end BananaAux

end Kontsevich
