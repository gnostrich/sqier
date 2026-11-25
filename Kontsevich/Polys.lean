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

theorem series_forest_iff :
    IsSeparatingForest (G.series H).ends (G.series H).src (G.series H).tgt (a.disjSum b) ↔
      (IsSeparatingForest G.ends G.src G.tgt a ∧ IsSpanningTree H.ends b) ∨
        (IsSpanningTree G.ends a ∧ IsSeparatingForest H.ends H.src H.tgt b) := by
  have hc := series_card G H
  have he := series_card_edges (H := H) a b
  have ht : (G.series H).tgt = sR G H H.tgt := rfl
  have hs : (G.series H).src = Sum.inl G.src := rfl
  have htG : sPG G H (sR G H H.tgt) = G.tgt := sPG_sR G H _
  have hsH : sPH G H (Sum.inl G.src) = H.src := rfl
  have hm := sR_src G H
  rw [ht, hs]
  unfold IsSeparatingForest IsSpanningTree
  constructor
  · rintro ⟨hcS, hcov, hst⟩
    have hGcov : ∀ x, Joined G.ends a G.src x ∨ Joined G.ends a G.tgt x := fun x => by
      rcases hcov (Sum.inl x) with h | h
      · exact Or.inl (by simpa [sPG_inl] using series_proj_G a b h)
      · exact Or.inr (by simpa [sPG_inl, htG] using series_proj_G a b h)
    have hHcov : ∀ y, Joined H.ends b H.src y ∨ Joined H.ends b H.tgt y := fun y => by
      rcases hcov (sR G H y) with h | h
      · exact Or.inl (by simpa [sPH_sR, hsH] using series_proj_H a b h)
      · exact Or.inr (by simpa [sPH_sR] using series_proj_H a b h)
    rcases hcov (Sum.inl G.tgt) with h | h
    · -- the middle vertex lies on the side of the first terminal
      have hGst : Joined G.ends a G.src G.tgt := by
        simpa [sPG_inl] using series_proj_G a b h
      have hHst : ¬ Joined H.ends b H.src H.tgt := fun h' => by
        have := series_push_H a b h'
        rw [hm] at this
        exact hst (h.trans' this)
      have hGc : ∀ x, Joined G.ends a G.src x := fun x =>
        (hGcov x).elim id (fun h' => hGst.trans' h')
      have h1 := card_le_one_of_conn _ hGc
      have h2 := card_le_two_of_conn _ _ hHcov
      right
      exact ⟨⟨by omega, fun u v => (hGc u).symm'.trans' (hGc v)⟩, by omega, hHcov, hHst⟩
    · have hHst : Joined H.ends b H.src H.tgt := by
        rw [← hm] at h
        simpa [sPH_sR] using (series_proj_H a b h).symm'
      have hGst : ¬ Joined G.ends a G.src G.tgt := fun h' => by
        exact hst ((series_push_G a b h').trans' h.symm')
      have hHc : ∀ y, Joined H.ends b H.src y := fun y =>
        (hHcov y).elim id (fun h' => hHst.trans' h')
      have h1 := card_le_two_of_conn _ _ hGcov
      have h2 := card_le_one_of_conn _ hHc
      left
      exact ⟨⟨by omega, hGcov, hGst⟩, by omega, fun u v => (hHc u).symm'.trans' (hHc v)⟩
  · rintro (⟨⟨hca, hGcov, hGst⟩, ⟨hcb, hHc⟩⟩ | ⟨⟨hca, hGc⟩, ⟨hcb, hHcov, hHst⟩⟩)
    · refine ⟨by omega, fun w => ?_, fun h => hGst ?_⟩
      · have hmt : Joined (G.series H).ends (a.disjSum b) (sR G H H.tgt) (Sum.inl G.tgt) := by
          have := series_push_H a b (hHc H.tgt H.src)
          rwa [hm] at this
        rcases series_cover G H w with ⟨x, rfl⟩ | ⟨y, rfl⟩
        · rcases hGcov x with h | h
          · exact Or.inl (series_push_G a b h)
          · exact Or.inr (hmt.trans' (series_push_G a b h))
        · exact Or.inr (series_push_H a b (hHc _ _))
      · simpa [sPG_inl, htG] using series_proj_G a b h
    · refine ⟨by omega, fun w => ?_, fun h => hHst ?_⟩
      · rcases series_cover G H w with ⟨x, rfl⟩ | ⟨y, rfl⟩
        · exact Or.inl (series_push_G a b (hGc _ _))
        · rcases hHcov y with h | h
          · have := series_push_H a b h
            rw [hm] at this
            exact Or.inl ((series_push_G a b (hGc _ _)).trans' this)
          · exact Or.inr (series_push_H a b h)
      · simpa [sPH_sR, hsH] using series_proj_H a b h

end Series

/-! ## Parallel composition -/

section Parallel

variable (G H : TTGraph)

/-- The vertex map from `H` into the parallel composition. -/
def pR (y : H.V) : G.V ⊕ {v : H.V // v ≠ H.src ∧ v ≠ H.tgt} :=
  if h₁ : y = H.src then Sum.inl G.src else
    if h₂ : y = H.tgt then Sum.inl G.tgt else Sum.inr ⟨y, h₁, h₂⟩

/-- Projection onto `G`, sending the inner vertices of `H` to the first terminal. -/
def pPG (w : G.V ⊕ {v : H.V // v ≠ H.src ∧ v ≠ H.tgt}) : G.V := Sum.elim id (fun _ => G.src) w

/-- Projection onto `H`, sending the vertices of `G` to the terminals. -/
def pPH (w : G.V ⊕ {v : H.V // v ≠ H.src ∧ v ≠ H.tgt}) : H.V :=
  Sum.elim (fun x => if x = G.tgt then H.tgt else H.src) Subtype.val w

open Classical in
/-- Projection onto `G`, sending each inner vertex of `H` to the terminal it is attached to
within `b`. -/
noncomputable def qPG (b : Finset H.E) (w : G.V ⊕ {v : H.V // v ≠ H.src ∧ v ≠ H.tgt}) : G.V :=
  Sum.elim id (fun y => if Joined H.ends b y.1 H.src then G.src else G.tgt) w

open Classical in
/-- Projection onto `H`, sending each vertex of `G` to the terminal it is attached to
within `a`. -/
noncomputable def qPH (a : Finset G.E) (w : G.V ⊕ {v : H.V // v ≠ H.src ∧ v ≠ H.tgt}) : H.V :=
  Sum.elim (fun x => if Joined G.ends a x G.src then H.src else H.tgt) Subtype.val w

variable {G H}

theorem pR_src : pR G H H.src = Sum.inl G.src := dite_eq_left rfl

theorem pR_tgt (hH : H.src ≠ H.tgt) : pR G H H.tgt = Sum.inl G.tgt := by
  rw [pR, dite_eq_right (Ne.symm hH), dite_eq_left rfl]

theorem parallel_cover (w : G.V ⊕ {v : H.V // v ≠ H.src ∧ v ≠ H.tgt}) :
    (∃ x, w = Sum.inl x) ∨ ∃ y, w = pR G H y := by
  rcases w with x | ⟨y, h₁, h₂⟩
  · exact Or.inl ⟨x, rfl⟩
  · exact Or.inr ⟨y, by rw [pR, dite_eq_right h₁, dite_eq_right h₂]⟩

theorem parallel_card (hH : H.src ≠ H.tgt) :
    Fintype.card (G.parallel H).V + 2 = Fintype.card G.V + Fintype.card H.V := by
  have h1 : Fintype.card (G.parallel H).V =
      Fintype.card (G.V ⊕ {v : H.V // v ≠ H.src ∧ v ≠ H.tgt}) :=
    Fintype.card_congr (Equiv.refl _)
  have h2 : Fintype.card {v : H.V // v ≠ H.src ∧ v ≠ H.tgt} + 2 = Fintype.card H.V := by
    rw [Fintype.card_subtype]
    have hf : (Finset.univ.filter fun v : H.V => v ≠ H.src ∧ v ≠ H.tgt) =
        (Finset.univ.erase H.src).erase H.tgt := by
      ext v; simp [and_comm]
    rw [hf, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hH, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have : ({H.src, H.tgt} : Finset H.V).card ≤ Fintype.card H.V := Finset.card_le_univ _
    rw [Finset.card_pair hH] at this
    omega
  rw [h1, Fintype.card_sum]
  omega

theorem pPG_pR (y : H.V) : pPG G H (pR G H y) = G.src ∨ pPG G H (pR G H y) = G.tgt := by
  unfold pR
  by_cases h₁ : y = H.src
  · rw [dite_eq_left h₁]; exact Or.inl rfl
  · rw [dite_eq_right h₁]
    by_cases h₂ : y = H.tgt
    · rw [dite_eq_left h₂]; exact Or.inr rfl
    · rw [dite_eq_right h₂]; exact Or.inl rfl

theorem pPH_pR (hG : G.src ≠ G.tgt) (y : H.V) :
    pPH G H (pR G H y) = y := by
  unfold pR
  by_cases h₁ : y = H.src
  · rw [dite_eq_left h₁]
    change (if G.src = G.tgt then H.tgt else H.src) = y
    rw [ite_eq_right hG, h₁]
  · rw [dite_eq_right h₁]
    by_cases h₂ : y = H.tgt
    · rw [dite_eq_left h₂]
      change (if G.tgt = G.tgt then H.tgt else H.src) = y
      rw [ite_eq_left rfl, h₂]
    · rw [dite_eq_right h₂]; rfl

theorem pPH_inl (x : G.V) : pPH G H (Sum.inl x) = H.src ∨ pPH G H (Sum.inl x) = H.tgt := by
  change (if x = G.tgt then H.tgt else H.src) = H.src ∨
    (if x = G.tgt then H.tgt else H.src) = H.tgt
  by_cases h : x = G.tgt
  · rw [ite_eq_left h]; exact Or.inr rfl
  · rw [ite_eq_right h]; exact Or.inl rfl

variable (a : Finset G.E) (b : Finset H.E)

open Classical in
theorem qPG_pR (hb : ¬ Joined H.ends b H.src H.tgt) (y : H.V) :
    qPG G H b (pR G H y) = if Joined H.ends b y H.src then G.src else G.tgt := by
  classical
  unfold pR
  by_cases h₁ : y = H.src
  · rw [dite_eq_left h₁, h₁, ite_eq_left (Joined.refl' _)]; rfl
  · rw [dite_eq_right h₁]
    by_cases h₂ : y = H.tgt
    · rw [dite_eq_left h₂, h₂, ite_eq_right (fun h => hb h.symm')]; rfl
    · rw [dite_eq_right h₂]; rfl

theorem qPH_pR (ha : ¬ Joined G.ends a G.src G.tgt) (y : H.V) :
    qPH G H a (pR G H y) = y := by
  classical
  unfold pR
  by_cases h₁ : y = H.src
  · rw [dite_eq_left h₁]
    change (if Joined G.ends a G.src G.src then H.src else H.tgt) = y
    rw [ite_eq_left (Joined.refl' _), h₁]
  · rw [dite_eq_right h₁]
    by_cases h₂ : y = H.tgt
    · rw [dite_eq_left h₂]
      change (if Joined G.ends a G.tgt G.src then H.src else H.tgt) = y
      rw [ite_eq_right (fun h => ha h.symm'), h₂]
    · rw [dite_eq_right h₂]; rfl

theorem qPH_inl_src : qPH G H a (Sum.inl G.src) = H.src := by
  classical
  change (if Joined G.ends a G.src G.src then H.src else H.tgt) = H.src
  rw [ite_eq_left (Joined.refl' _)]

theorem qPH_inl_tgt (ha : ¬ Joined G.ends a G.src G.tgt) :
    qPH G H a (Sum.inl G.tgt) = H.tgt := by
  classical
  change (if Joined G.ends a G.tgt G.src then H.src else H.tgt) = H.tgt
  rw [ite_eq_right (fun h => ha h.symm')]

theorem parallel_card_edges :
    Finset.card (α := (G.parallel H).E) (a.disjSum b) = a.card + b.card :=
  Finset.card_disjSum a b

theorem parallel_push_G {x y : G.V} (h : Joined G.ends a x y) :
    Joined (G.parallel H).ends (a.disjSum b) (Sum.inl x) (Sum.inl y) :=
  Joined.map (ends' := (G.parallel H).ends) (S' := a.disjSum b)
    (fun x : G.V => (Sum.inl x : (G.parallel H).V))
    (fun e he => Or.inr ⟨Sum.inl e, Finset.inl_mem_disjSum.2 he, rfl⟩) h

theorem parallel_push_H {x y : H.V} (h : Joined H.ends b x y) :
    Joined (G.parallel H).ends (a.disjSum b) (pR G H x) (pR G H y) :=
  Joined.map (ends' := (G.parallel H).ends) (S' := a.disjSum b) (pR G H)
    (fun e he => Or.inr ⟨Sum.inr e, Finset.inr_mem_disjSum.2 he, rfl⟩) h

theorem parallel_projMod_G {u v : (G.parallel H).V}
    (h : Joined (G.parallel H).ends (a.disjSum b) u v) :
    JoinedMod G.ends a G.src G.tgt (pPG G H u) (pPG G H v) := by
  refine Joined.induct (fun u v => JoinedMod G.ends a G.src G.tgt (pPG G H u) (pPG G H v))
    (fun _ => JoinedMod.refl _ _ _) (fun _ _ _ h₁ h₂ => h₁.trans h₂) (fun e he => ?_) h
  rcases e with e | e
  · have he' := Finset.inl_mem_disjSum.1 he
    exact ⟨Or.inl (Joined.edge he'), Or.inl (Joined.edge he').symm'⟩
  · exact ⟨JoinedMod.of_mem (pPG_pR _) (pPG_pR _), JoinedMod.of_mem (pPG_pR _) (pPG_pR _)⟩

theorem parallel_projMod_H (hG : G.src ≠ G.tgt)
    {u v : (G.parallel H).V} (h : Joined (G.parallel H).ends (a.disjSum b) u v) :
    JoinedMod H.ends b H.src H.tgt (pPH G H u) (pPH G H v) := by
  refine Joined.induct (fun u v => JoinedMod H.ends b H.src H.tgt (pPH G H u) (pPH G H v))
    (fun _ => JoinedMod.refl _ _ _) (fun _ _ _ h₁ h₂ => h₁.trans h₂) (fun e he => ?_) h
  rcases e with e | e
  · exact ⟨JoinedMod.of_mem (pPH_inl _) (pPH_inl _), JoinedMod.of_mem (pPH_inl _) (pPH_inl _)⟩
  · have he' := Finset.inr_mem_disjSum.1 he
    change JoinedMod H.ends b H.src H.tgt (pPH G H (pR G H (H.ends e).1))
        (pPH G H (pR G H (H.ends e).2)) ∧
      JoinedMod H.ends b H.src H.tgt (pPH G H (pR G H (H.ends e).2))
        (pPH G H (pR G H (H.ends e).1))
    rw [pPH_pR hG, pPH_pR hG]
    exact ⟨Or.inl (Joined.edge he'), Or.inl (Joined.edge he').symm'⟩

theorem parallel_proj_G (hb : ¬ Joined H.ends b H.src H.tgt)
    {u v : (G.parallel H).V} (h : Joined (G.parallel H).ends (a.disjSum b) u v) :
    Joined G.ends a (qPG G H b u) (qPG G H b v) := by
  classical
  refine Joined.map (qPG G H b) (fun e he => ?_) h
  rcases e with e | e
  · exact Or.inr ⟨e, Finset.inl_mem_disjSum.1 he, rfl⟩
  · left
    have he' := Finset.inr_mem_disjSum.1 he
    change qPG G H b (pR G H (H.ends e).1) = qPG G H b (pR G H (H.ends e).2)
    rw [qPG_pR b hb, qPG_pR b hb]
    by_cases h₁ : Joined H.ends b (H.ends e).1 H.src
    · rw [ite_eq_left h₁, ite_eq_left ((Joined.edge_iff he' _).1 h₁)]
    · rw [ite_eq_right h₁, ite_eq_right (fun h => h₁ ((Joined.edge_iff he' _).2 h))]

theorem parallel_proj_H (ha : ¬ Joined G.ends a G.src G.tgt)
    {u v : (G.parallel H).V} (h : Joined (G.parallel H).ends (a.disjSum b) u v) :
    Joined H.ends b (qPH G H a u) (qPH G H a v) := by
  classical
  refine Joined.map (qPH G H a) (fun e he => ?_) h
  rcases e with e | e
  · left
    have he' := Finset.inl_mem_disjSum.1 he
    change (if Joined G.ends a (G.ends e).1 G.src then H.src else H.tgt) =
      (if Joined G.ends a (G.ends e).2 G.src then H.src else H.tgt)
    by_cases h₁ : Joined G.ends a (G.ends e).1 G.src
    · rw [ite_eq_left h₁, ite_eq_left ((Joined.edge_iff he' _).1 h₁)]
    · rw [ite_eq_right h₁, ite_eq_right (fun h => h₁ ((Joined.edge_iff he' _).2 h))]
  · right
    refine ⟨e, Finset.inr_mem_disjSum.1 he, ?_⟩
    change H.ends e = (qPH G H a (pR G H (H.ends e).1), qPH G H a (pR G H (H.ends e).2))
    rw [qPH_pR a ha, qPH_pR a ha]

theorem parallel_tree_iff (hG : G.src ≠ G.tgt) (hH : H.src ≠ H.tgt) :
    IsSpanningTree (G.parallel H).ends (a.disjSum b) ↔
      (IsSpanningTree G.ends a ∧ IsSeparatingForest H.ends H.src H.tgt b) ∨
        (IsSeparatingForest G.ends G.src G.tgt a ∧ IsSpanningTree H.ends b) := by
  have hc := parallel_card (G := G) hH
  have he := parallel_card_edges (G := G) (H := H) a b
  have hs := pR_src (G := G) (H := H)
  have ht := pR_tgt (G := G) hH
  unfold IsSeparatingForest IsSpanningTree
  constructor
  · rintro ⟨hcS, hconn⟩
    have hGcov : ∀ x, Joined G.ends a G.src x ∨ Joined G.ends a G.tgt x := fun x =>
      (parallel_projMod_G a b (hconn (Sum.inl G.src) (Sum.inl x))).of_left
    have hHcov : ∀ y, Joined H.ends b H.src y ∨ Joined H.ends b H.tgt y := fun y => by
      have := parallel_projMod_H a b hG (hconn (pR G H H.src) (pR G H y))
      rw [pPH_pR hG, pPH_pR hG] at this
      exact this.of_left
    by_cases hGst : Joined G.ends a G.src G.tgt
    · have hGc : ∀ x, Joined G.ends a G.src x := fun x =>
        (hGcov x).elim id (fun h' => hGst.trans' h')
      have h1 := card_le_one_of_conn _ hGc
      have hHst : ¬ Joined H.ends b H.src H.tgt := fun hHst => by
        have hHc : ∀ y, Joined H.ends b H.src y := fun y =>
          (hHcov y).elim id (fun h' => hHst.trans' h')
        have h2 := card_le_one_of_conn _ hHc
        omega
      have h2 := card_le_two_of_conn _ _ hHcov
      left
      exact ⟨⟨by omega, fun u v => (hGc u).symm'.trans' (hGc v)⟩, by omega, hHcov, hHst⟩
    · have hHst : Joined H.ends b H.src H.tgt := by
        have := parallel_proj_H a b hGst (hconn (pR G H H.src) (pR G H H.tgt))
        rwa [qPH_pR a hGst, qPH_pR a hGst] at this
      have hHc : ∀ y, Joined H.ends b H.src y := fun y =>
        (hHcov y).elim id (fun h' => hHst.trans' h')
      have h1 := card_le_two_of_conn _ _ hGcov
      have h2 := card_le_one_of_conn _ hHc
      right
      exact ⟨⟨by omega, hGcov, hGst⟩, by omega, fun u v => (hHc u).symm'.trans' (hHc v)⟩
  · rintro (⟨⟨hca, hGc⟩, ⟨hcb, hHcov, hHst⟩⟩ | ⟨⟨hca, hGcov, hGst⟩, ⟨hcb, hHc⟩⟩)
    · refine ⟨by omega, ?_⟩
      have key : ∀ w, Joined (G.parallel H).ends (a.disjSum b) (Sum.inl G.src) w := by
        intro w
        rcases parallel_cover w with ⟨x, rfl⟩ | ⟨y, rfl⟩
        · exact parallel_push_G a b (hGc _ _)
        · rcases hHcov y with h | h
          · have := parallel_push_H a b h
            rwa [hs] at this
          · have := parallel_push_H a b h
            rw [ht] at this
            exact (parallel_push_G a b (hGc _ _)).trans' this
      intro u v
      exact (key u).symm'.trans' (key v)
    · refine ⟨by omega, ?_⟩
      have hst : Joined (G.parallel H).ends (a.disjSum b) (Sum.inl G.src) (Sum.inl G.tgt) := by
        have := parallel_push_H a b (hHc H.src H.tgt)
        rwa [hs, ht] at this
      have key : ∀ w, Joined (G.parallel H).ends (a.disjSum b) (Sum.inl G.src) w := by
        intro w
        rcases parallel_cover w with ⟨x, rfl⟩ | ⟨y, rfl⟩
        · rcases hGcov x with h | h
          · exact parallel_push_G a b h
          · exact hst.trans' (parallel_push_G a b h)
        · have := parallel_push_H a b (hHc H.src y)
          rwa [hs] at this
      intro u v
      exact (key u).symm'.trans' (key v)

theorem parallel_forest_iff (hH : H.src ≠ H.tgt) :
    IsSeparatingForest (G.parallel H).ends (G.parallel H).src (G.parallel H).tgt
        (a.disjSum b) ↔
      IsSeparatingForest G.ends G.src G.tgt a ∧ IsSeparatingForest H.ends H.src H.tgt b := by
  have hc := parallel_card (G := G) hH
  have he := parallel_card_edges (G := G) (H := H) a b
  have hs := pR_src (G := G) (H := H)
  have ht := pR_tgt (G := G) hH
  have hs' : (G.parallel H).src = Sum.inl G.src := rfl
  have ht' : (G.parallel H).tgt = Sum.inl G.tgt := rfl
  rw [hs', ht']
  unfold IsSeparatingForest
  constructor
  · rintro ⟨hcS, hcov, hst⟩
    have hGst : ¬ Joined G.ends a G.src G.tgt := fun h => hst (parallel_push_G a b h)
    have hHst : ¬ Joined H.ends b H.src H.tgt := fun h => by
      have := parallel_push_H a b h
      rw [hs, ht] at this
      exact hst this
    have hGcov : ∀ x, Joined G.ends a G.src x ∨ Joined G.ends a G.tgt x := fun x => by
      rcases hcov (Sum.inl x) with h | h
      · exact Or.inl (parallel_proj_G a b hHst h)
      · exact Or.inr (parallel_proj_G a b hHst h)
    have hHcov : ∀ y, Joined H.ends b H.src y ∨ Joined H.ends b H.tgt y := fun y => by
      rcases hcov (pR G H y) with h | h
      · have := parallel_proj_H a b hGst h
        rw [qPH_inl_src, qPH_pR a hGst] at this
        exact Or.inl this
      · have := parallel_proj_H a b hGst h
        rw [qPH_inl_tgt a hGst, qPH_pR a hGst] at this
        exact Or.inr this
    have h1 := card_le_two_of_conn _ _ hGcov
    have h2 := card_le_two_of_conn _ _ hHcov
    exact ⟨⟨by omega, hGcov, hGst⟩, by omega, hHcov, hHst⟩
  · rintro ⟨⟨hca, hGcov, hGst⟩, ⟨hcb, hHcov, hHst⟩⟩
    refine ⟨by omega, fun w => ?_, fun h => hGst (parallel_proj_G a b hHst h)⟩
    rcases parallel_cover w with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · rcases hGcov x with h | h
      · exact Or.inl (parallel_push_G a b h)
      · exact Or.inr (parallel_push_G a b h)
    · rcases hHcov y with h | h
      · have := parallel_push_H a b h
        rw [hs] at this
        exact Or.inl this
      · have := parallel_push_H a b h
        rw [ht] at this
        exact Or.inr this

end Parallel

/-- Series composition multiplies graph polynomials. -/
theorem kirchhoff_series (G H : TTGraph) :
    kirchhoffPoly (G.series H).ends =
      rename Sum.inl (kirchhoffPoly G.ends) * rename Sum.inr (kirchhoffPoly H.ends) := by
  rw [kirchhoffPoly_eq, kirchhoffPoly_eq, kirchhoffPoly_eq]
  exact sum_split_prod _ _ _ series_tree_iff

/-- The 2-forest polynomial of a series composition. -/
theorem forest_series (G H : TTGraph) (hG : G.src ≠ G.tgt) (hH : H.src ≠ H.tgt) :
    forestPoly (G.series H).ends (G.series H).src (G.series H).tgt =
      rename Sum.inl (forestPoly G.ends G.src G.tgt) * rename Sum.inr (kirchhoffPoly H.ends) +
        rename Sum.inl (kirchhoffPoly G.ends) * rename Sum.inr (forestPoly H.ends H.src H.tgt) := by
  rw [forestPoly_eq, forestPoly_eq, forestPoly_eq, kirchhoffPoly_eq, kirchhoffPoly_eq]
  exact sum_split_prod₂ _ _ _ _ _ (fun _ h => h.1.2.2 (h.2.2 _ _)) series_forest_iff

/-- The graph polynomial of a parallel composition. -/
theorem kirchhoff_parallel (G H : TTGraph) (hG : G.src ≠ G.tgt) (hH : H.src ≠ H.tgt) :
    kirchhoffPoly (G.parallel H).ends =
      rename Sum.inl (kirchhoffPoly G.ends) * rename Sum.inr (forestPoly H.ends H.src H.tgt) +
        rename Sum.inl (forestPoly G.ends G.src G.tgt) * rename Sum.inr (kirchhoffPoly H.ends) := by
  rw [forestPoly_eq, forestPoly_eq, kirchhoffPoly_eq, kirchhoffPoly_eq, kirchhoffPoly_eq]
  exact sum_split_prod₂ _ _ _ _ _ (fun _ h => h.2.2.2 (h.1.2 _ _))
    (parallel_tree_iff · · hG hH)

/-- The 2-forest polynomial of a parallel composition. -/
theorem forest_parallel (G H : TTGraph) (hG : G.src ≠ G.tgt) (hH : H.src ≠ H.tgt) :
    forestPoly (G.parallel H).ends (G.parallel H).src (G.parallel H).tgt =
      rename Sum.inl (forestPoly G.ends G.src G.tgt) *
        rename Sum.inr (forestPoly H.ends H.src H.tgt) := by
  rw [forestPoly_eq, forestPoly_eq, forestPoly_eq]
  exact sum_split_prod _ _ _ (parallel_forest_iff · · hH)

end Kontsevich
