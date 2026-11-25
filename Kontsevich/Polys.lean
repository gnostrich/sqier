module

public import Mathlib
public import Kontsevich.Defs
public import Kontsevich.PolysAux

@[expose] public section

namespace Kontsevich

open MvPolynomial

/-! ## Series composition -/

section Series

variable (G H : TTGraph)

/-- The vertex map from `H` into the series composition. -/
def sR (y : H.V) : G.V ⊕ {v : H.V // v ≠ H.src} :=
  if h : y = H.src then Sum.inl G.tgt else Sum.inr ⟨y, h⟩

/-- Projection of the series composition onto `G`. -/
def sPG (w : G.V ⊕ {v : H.V // v ≠ H.src}) : G.V := Sum.elim id (fun _ => G.tgt) w

/-- Projection of the series composition onto `H`. -/
def sPH (w : G.V ⊕ {v : H.V // v ≠ H.src}) : H.V := Sum.elim (fun _ => H.src) Subtype.val w

theorem sR_src : sR G H H.src = Sum.inl G.tgt := dite_eq_left rfl

theorem sPG_inl (x : G.V) : sPG G H (Sum.inl x) = x := rfl

theorem sPH_inl (x : G.V) : sPH G H (Sum.inl x) = H.src := rfl

theorem sPG_sR (y : H.V) : sPG G H (sR G H y) = G.tgt := by
  by_cases h : y = H.src
  · rw [sR, dite_eq_left h]; rfl
  · rw [sR, dite_eq_right h]; rfl

theorem sPH_sR (y : H.V) : sPH G H (sR G H y) = y := by
  by_cases h : y = H.src
  · rw [sR, dite_eq_left h]; exact h.symm
  · rw [sR, dite_eq_right h]; rfl

theorem series_cover (w : G.V ⊕ {v : H.V // v ≠ H.src}) :
    (∃ x, w = Sum.inl x) ∨ ∃ y, w = sR G H y := by
  rcases w with x | ⟨y, hy⟩
  · exact Or.inl ⟨x, rfl⟩
  · exact Or.inr ⟨y, by rw [sR, dite_eq_right hy]⟩

theorem series_card :
    Fintype.card (G.series H).V + 1 = Fintype.card G.V + Fintype.card H.V := by
  have h1 : Fintype.card (G.series H).V = Fintype.card (G.V ⊕ {v : H.V // v ≠ H.src}) :=
    Fintype.card_congr (Equiv.refl _)
  have h2 : Fintype.card {v : H.V // v ≠ H.src} + 1 = Fintype.card H.V := by
    rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
    have : 0 < Fintype.card H.V := Fintype.card_pos_iff.2 ⟨H.src⟩
    omega
  rw [h1, Fintype.card_sum]
  omega

variable {G H} (a : Finset G.E) (b : Finset H.E)

theorem series_card_edges :
    Finset.card (α := (G.series H).E) (a.disjSum b) = a.card + b.card :=
  Finset.card_disjSum a b

theorem series_push_G {x y : G.V} (h : Joined G.ends a x y) :
    Joined (G.series H).ends (a.disjSum b) (Sum.inl x) (Sum.inl y) :=
  Joined.map (ends' := (G.series H).ends) (S' := a.disjSum b)
    (fun x : G.V => (Sum.inl x : (G.series H).V))
    (fun e he => Or.inr ⟨Sum.inl e, Finset.inl_mem_disjSum.2 he, rfl⟩) h

theorem series_push_H {x y : H.V} (h : Joined H.ends b x y) :
    Joined (G.series H).ends (a.disjSum b) (sR G H x) (sR G H y) :=
  Joined.map (ends' := (G.series H).ends) (S' := a.disjSum b) (sR G H)
    (fun e he => Or.inr ⟨Sum.inr e, Finset.inr_mem_disjSum.2 he, rfl⟩) h

theorem series_proj_G {u v : (G.series H).V}
    (h : Joined (G.series H).ends (a.disjSum b) u v) :
    Joined G.ends a (sPG G H u) (sPG G H v) := by
  refine Joined.map (sPG G H) (fun e he => ?_) h
  rcases e with e | e
  · exact Or.inr ⟨e, Finset.inl_mem_disjSum.1 he, rfl⟩
  · left
    change sPG G H (sR G H (H.ends e).1) = sPG G H (sR G H (H.ends e).2)
    rw [sPG_sR, sPG_sR]

theorem series_proj_H {u v : (G.series H).V}
    (h : Joined (G.series H).ends (a.disjSum b) u v) :
    Joined H.ends b (sPH G H u) (sPH G H v) := by
  refine Joined.map (sPH G H) (fun e he => ?_) h
  rcases e with e | e
  · exact Or.inl rfl
  · right
    refine ⟨e, Finset.inr_mem_disjSum.1 he, ?_⟩
    change H.ends e = (sPH G H (sR G H (H.ends e).1), sPH G H (sR G H (H.ends e).2))
    rw [sPH_sR, sPH_sR]

theorem series_tree_iff :
    IsSpanningTree (G.series H).ends (a.disjSum b) ↔
      IsSpanningTree G.ends a ∧ IsSpanningTree H.ends b := by
  have hc := series_card G H
  have he := series_card_edges (H := H) a b
  unfold IsSpanningTree
  constructor
  · rintro ⟨hcS, hconn⟩
    have hG : ∀ x, Joined G.ends a G.src x := fun x => by
      simpa [sPG_inl] using series_proj_G a b (hconn (Sum.inl G.src) (Sum.inl x))
    have hH : ∀ y, Joined H.ends b H.src y := fun y => by
      simpa [sPH_sR] using series_proj_H a b (hconn (sR G H H.src) (sR G H y))
    have h1 := card_le_one_of_conn _ hG
    have h2 := card_le_one_of_conn _ hH
    exact ⟨⟨by omega, fun u v => (hG u).symm'.trans' (hG v)⟩,
      ⟨by omega, fun u v => (hH u).symm'.trans' (hH v)⟩⟩
  · rintro ⟨⟨hca, hGc⟩, ⟨hcb, hHc⟩⟩
    refine ⟨by omega, ?_⟩
    have key : ∀ w, Joined (G.series H).ends (a.disjSum b) (Sum.inl G.src) w := by
      intro w
      rcases series_cover G H w with ⟨x, rfl⟩ | ⟨y, rfl⟩
      · exact series_push_G a b (hGc _ _)
      · have h := series_push_H a b (hHc H.src y)
        rw [sR_src] at h
        exact (series_push_G a b (hGc G.src G.tgt)).trans' h
    intro u v
    exact (key u).symm'.trans' (key v)

end Series

/-- Series composition multiplies graph polynomials. -/
theorem kirchhoff_series (G H : TTGraph) :
    kirchhoffPoly (G.series H).ends =
      rename Sum.inl (kirchhoffPoly G.ends) * rename Sum.inr (kirchhoffPoly H.ends) := by
  rw [kirchhoffPoly_eq, kirchhoffPoly_eq, kirchhoffPoly_eq]
  exact (sum_split _ _ series_tree_iff).trans (sum_prod _ _).symm

/-- The 2-forest polynomial of a series composition. -/
theorem forest_series (G H : TTGraph) (hG : G.src ≠ G.tgt) (hH : H.src ≠ H.tgt) :
    forestPoly (G.series H).ends (G.series H).src (G.series H).tgt =
      rename Sum.inl (forestPoly G.ends G.src G.tgt) * rename Sum.inr (kirchhoffPoly H.ends) +
        rename Sum.inl (kirchhoffPoly G.ends) * rename Sum.inr (forestPoly H.ends H.src H.tgt) := by
  sorry

/-- The graph polynomial of a parallel composition. -/
theorem kirchhoff_parallel (G H : TTGraph) (hG : G.src ≠ G.tgt) (hH : H.src ≠ H.tgt) :
    kirchhoffPoly (G.parallel H).ends =
      rename Sum.inl (kirchhoffPoly G.ends) * rename Sum.inr (forestPoly H.ends H.src H.tgt) +
        rename Sum.inl (forestPoly G.ends G.src G.tgt) * rename Sum.inr (kirchhoffPoly H.ends) := by
  sorry

/-- The 2-forest polynomial of a parallel composition. -/
theorem forest_parallel (G H : TTGraph) (hG : G.src ≠ G.tgt) (hH : H.src ≠ H.tgt) :
    forestPoly (G.parallel H).ends (G.parallel H).src (G.parallel H).tgt =
      rename Sum.inl (forestPoly G.ends G.src G.tgt) *
        rename Sum.inr (forestPoly H.ends H.src H.tgt) := by
  sorry

end Kontsevich
