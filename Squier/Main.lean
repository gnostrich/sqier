module

public import Mathlib
public import Squier.Branching
public import Squier.PathLemmas
@[expose] public section

/-! # Squier's theorem: generating confluences form a homotopy basis

The proof follows Squier (and Guiraud–Malbos). For a terminating system we choose, for each
word `u`, a path `nfPath u` from `u` to a normal form, starting with some step out of `u` when
there is one. Using the classification of local branchings, every local branching is resolved
up to homotopy (modulo the independence squares and the cells of `B` resolving the critical
branchings). By noetherian induction, `s · nfPath v ≈ nfPath u` for every step `s : u → v`
(in particular, the normal forms agree), hence `p · nfPath v ≈ nfPath u` for every zig-zag
path `p : u → v`, and any two parallel paths are homotopic.
-/

namespace Squier

variable {α : Type*} {R : Finset (List α × List α)}

open Relation

/-! ## Homotopy of paths with a common source and possibly different targets -/

/-- Two paths from `u` are homotopic up to an identification of their targets. -/
def HomEq (B : Set (Cell R)) {u t₁ t₂ : List α} (p : Path R u t₁) (q : Path R u t₂) : Prop :=
  ∃ h : t₁ = t₂, Homotopic B (p.cast rfl h) q

namespace HomEq

variable {B : Set (Cell R)}

theorem of_homotopic {u t : List α} {p q : Path R u t} (h : Homotopic B p q) : HomEq B p q :=
  ⟨rfl, h⟩

theorem homotopic {u t : List α} {p q : Path R u t} (h : HomEq B p q) : Homotopic B p q := by
  obtain ⟨_, h⟩ := h
  exact h

theorem refl {u t : List α} (p : Path R u t) : HomEq B p p := of_homotopic (.refl p)

theorem symm {u t₁ t₂ : List α} {p : Path R u t₁} {q : Path R u t₂} (h : HomEq B p q) :
    HomEq B q p := by
  obtain ⟨rfl, h⟩ := h
  exact ⟨rfl, h.symm⟩

theorem trans {u t₁ t₂ t₃ : List α} {p : Path R u t₁} {q : Path R u t₂} {r : Path R u t₃}
    (h : HomEq B p q) (h' : HomEq B q r) : HomEq B p r := by
  obtain ⟨rfl, h⟩ := h
  obtain ⟨rfl, h'⟩ := h'
  exact ⟨rfl, h.trans h'⟩

theorem comp_left {u v t₁ t₂ : List α} (p : Path R u v) {q : Path R v t₁} {q' : Path R v t₂}
    (h : HomEq B q q') : HomEq B (p.comp q) (p.comp q') := by
  obtain ⟨rfl, h⟩ := h
  exact ⟨rfl, .comp (.refl p) h⟩

end HomEq

/-! ## Resolution of local branchings -/

/-- A local branching `(s₁, s₂)` is resolved up to homotopy modulo `B`. -/
def Resolvable (B : Set (Cell R)) {u v₁ v₂ : List α} (s₁ : Step R u v₁) (s₂ : Step R u v₂) :
    Prop :=
  ∃ (t : List α) (ρ₁ : Path R v₁ t) (ρ₂ : Path R v₂ t), ρ₁.Positive ∧ ρ₂.Positive ∧
    Homotopic B (s₁.toPath.comp ρ₁) (s₂.toPath.comp ρ₂)

namespace Resolvable

variable {B : Set (Cell R)}

theorem symm {u v₁ v₂ : List α} {s₁ : Step R u v₁} {s₂ : Step R u v₂}
    (h : Resolvable B s₁ s₂) : Resolvable B s₂ s₁ := by
  obtain ⟨t, ρ₁, ρ₂, h₁, h₂, h⟩ := h
  exact ⟨t, ρ₂, ρ₁, h₂, h₁, h.symm⟩

theorem self {u v : List α} (s : Step R u v) : Resolvable B s s :=
  ⟨v, Path.nil v, Path.nil v, trivial, trivial, .refl _⟩

/-- Resolvability only depends on the contexts and rules of the two steps. -/
theorem of_fields {u v₁ v₂ u' v₁' v₂' : List α} {s₁ : Step R u v₁} {s₂ : Step R u v₂}
    {s₁' : Step R u' v₁'} {s₂' : Step R u' v₂'} (h : Resolvable B s₁' s₂')
    (h₁ : s₁.pre = s₁'.pre) (h₁' : s₁.rule = s₁'.rule) (h₁'' : s₁.suf = s₁'.suf)
    (h₂ : s₂.pre = s₂'.pre) (h₂' : s₂.rule = s₂'.rule) (h₂'' : s₂.suf = s₂'.suf) :
    Resolvable B s₁ s₂ := by
  have hu := Step.src_eq_of_fields h₁ h₁' h₁''
  have hv₁ := Step.tgt_eq_of_fields h₁ h₁' h₁''
  have hv₂ := Step.tgt_eq_of_fields h₂ h₂' h₂''
  subst hu hv₁ hv₂
  obtain rfl := Step.eq_of_fields h₁ h₁' h₁''
  obtain rfl := Step.eq_of_fields h₂ h₂' h₂''
  exact h

/-- Independent branchings are resolved by the independence square. -/
theorem of_independent {u v₁ v₂ : List α} (s₁ : Step R u v₁) (s₂ : Step R u v₂) (b : List α)
    (h : s₂.pre = s₁.pre ++ s₁.rule.1 ++ b) (h' : s₁.suf = b ++ s₂.rule.1 ++ s₂.suf) :
    Resolvable B s₁ s₂ := by
  obtain ⟨a, r₁, m₁, f₁, hu₁, hv₁⟩ := s₁
  obtain ⟨p₂, r₂, m₂, c, hu₂, hv₂⟩ := s₂
  dsimp only at h h'
  subst h h'
  have hu : u = a ++ r₁.1 ++ b ++ r₂.1 ++ c := by rw [hu₁]; simp
  have hv₁' : v₁ = a ++ r₁.2 ++ b ++ r₂.1 ++ c := by rw [hv₁]; simp
  subst hu hv₁' hv₂
  exact ⟨_, (⟨a ++ r₁.2 ++ b, r₂, m₂, c, rfl, rfl⟩ : Step R _ _).toPath,
    (⟨a, r₁, m₁, b ++ r₂.2 ++ c, by simp, by simp⟩ : Step R _ _).toPath, Step.toPath_positive _,
    Step.toPath_positive _, Homotopic.indep a b c m₁ m₂⟩

/-- Whiskered critical branchings are resolved by the whiskered cells of `B`. -/
theorem of_critical (hB : ∀ b ∈ criticalBranchings R, Resolves B b) {b : Branching R}
    (hb : b.IsCritical) (x y : List α) :
    Resolvable B (b.left.whisker x y) (b.right.whisker x y) := by
  obtain ⟨t, ρ₁, ρ₂, h₁, h₂, hc⟩ := hB b hb
  have H : Homotopic B (b.left.toPath.comp ρ₁) (b.right.toPath.comp ρ₂) := by
    rcases hc with hc | hc
    · exact .basis hc
    · exact (Homotopic.basis hc).symm
  refine ⟨x ++ t ++ y, ρ₁.whisker x y, ρ₂.whisker x y, h₁.whisker x y, h₂.whisker x y, ?_⟩
  have := Homotopic.whisker x y H
  rwa [Path.whisker_comp, Path.whisker_comp, Step.toPath_whisker, Step.toPath_whisker] at this

end Resolvable

/-- Every local branching is resolved up to homotopy, given resolutions of the critical
branchings in `B`. -/
theorem resolvable {B : Set (Cell R)} (hB : ∀ b ∈ criticalBranchings R, Resolves B b)
    {u v₁ v₂ : List α} (s₁ : Step R u v₁) (s₂ : Step R u v₂) : Resolvable B s₁ s₂ := by
  rcases branching_cases s₁ s₂ with ⟨hp, hr⟩ | (⟨b, h, h'⟩ | ⟨b, h, h'⟩) |
    ⟨x, y, b, hb, h₁, h₂, h₃, h₄, h₅, h₆⟩
  · have hs : s₁.suf = s₂.suf := by
      have := s₁.src_eq.symm.trans s₂.src_eq
      rw [hp, hr] at this
      exact List.append_cancel_left this
    exact Resolvable.of_fields (Resolvable.self s₂) hp hr hs rfl rfl rfl
  · exact Resolvable.of_independent s₁ s₂ b h h'
  · exact (Resolvable.of_independent s₂ s₁ b h h').symm
  · exact Resolvable.of_fields (Resolvable.of_critical hB hb x y) h₁ h₂ h₃ h₄ h₅ h₆

/-! ## Paths to normal forms -/

open Classical in
/-- One unfolding of `nfPath`: follow a chosen step out of `u`, if any. -/
noncomputable def nfPathStep (u : List α) (ih : ∀ v, Rewrites R u v → Σ t, Path R v t) :
    Σ t, Path R u t :=
  if h : ∃ v, Rewrites R u v then
    ⟨(ih _ h.choose_spec).1, h.choose_spec.some.toPath.comp (ih _ h.choose_spec).2⟩
  else ⟨u, Path.nil u⟩

/-- For a terminating system, a path from `u` to a normal form, starting with a chosen step out
of `u` when there is one. -/
noncomputable def nfPath (hR : Terminating R) : (u : List α) → Σ t, Path R u t :=
  WellFounded.fix hR nfPathStep

theorem nfPath_eq (hR : Terminating R) (u : List α) :
    nfPath hR u = nfPathStep u (fun v _ => nfPath hR v) :=
  WellFounded.fix_eq hR nfPathStep u

theorem nfPath_step (hR : Terminating R) {u v : List α} (s : Step R u v) :
    ∃ (v₀ : List α) (s₀ : Step R u v₀),
      nfPath hR u = ⟨(nfPath hR v₀).1, s₀.toPath.comp (nfPath hR v₀).2⟩ := by
  have h : ∃ v, Rewrites R u v := ⟨v, ⟨s⟩⟩
  refine ⟨h.choose, h.choose_spec.some, ?_⟩
  conv_lhs => rw [nfPath_eq]
  rw [nfPathStep, dite_eq_left h]

/-! ## The key lemma -/

section Key

variable {B : Set (Cell R)} (hR : Terminating R)

/-- The property proved by noetherian induction: every step out of `u` followed by the chosen
normal form path is homotopic to the chosen normal form path of `u`. -/
def KeyProp (B : Set (Cell R)) (u : List α) : Prop :=
  ∀ (v : List α) (s : Step R u v), HomEq B (s.toPath.comp (nfPath hR v).2) (nfPath hR u).2

include hR in
theorem keyProp_positive {v : List α}
    (H : ∀ w, ReflTransGen (Rewrites R) v w → KeyProp hR B w) {t : List α} (ρ : Path R v t)
    (hρ : ρ.Positive) : HomEq B (ρ.comp (nfPath hR t).2) (nfPath hR v).2 := by
  induction ρ with
  | nil => rw [Path.nil_comp]; exact .refl _
  | fwd ρ s ih =>
    rw [Path.fwd_eq_comp, Path.comp_assoc]
    exact ((H _ (Path.reflTransGen_of_positive ρ hρ) _ s).comp_left ρ).trans (ih hρ)
  | bwd _ _ => exact hρ.elim

theorem keyProp (hB : ∀ b ∈ criticalBranchings R, Resolves B b) (u : List α) :
    KeyProp hR B u := by
  induction u using (WellFounded.transGen hR).induction with
  | _ u IH =>
  intro v s
  obtain ⟨v₀, s₀, hσ⟩ := nfPath_step hR s
  rw [hσ]
  obtain ⟨t, ρ, ρ₀, hρ, hρ₀, hh⟩ := resolvable hB s s₀
  have desc : ∀ {v' : List α} (_ : Step R u v') (w : List α), ReflTransGen (Rewrites R) v' w →
      KeyProp hR B w := fun s' w hw =>
    IH w (transGen_swap.mpr (TransGen.head' ⟨s'⟩ hw))
  have e₁ := (keyProp_positive hR (desc s) ρ hρ).comp_left s.toPath
  have e₂ := (keyProp_positive hR (desc s₀) ρ₀ hρ₀).comp_left s₀.toPath
  have e₃ : HomEq B (s.toPath.comp (ρ.comp (nfPath hR t).2))
      (s₀.toPath.comp (ρ₀.comp (nfPath hR t).2)) := by
    rw [← Path.comp_assoc, ← Path.comp_assoc]
    exact .of_homotopic (.comp_right hh _)
  exact (e₁.symm.trans e₃).trans e₂

/-- Every zig-zag path followed by the chosen normal form path of its target is homotopic to
the chosen normal form path of its source. -/
theorem homEq_nfPath (hB : ∀ b ∈ criticalBranchings R, Resolves B b) {u v : List α}
    (p : Path R u v) : HomEq B (p.comp (nfPath hR v).2) (nfPath hR u).2 := by
  induction p with
  | nil => rw [Path.nil_comp]; exact .refl _
  | fwd p s ih =>
    rw [Path.fwd_eq_comp, Path.comp_assoc]
    exact ((keyProp hR hB _ _ s).comp_left p).trans ih
  | bwd p s ih =>
    rw [Path.bwd_eq_comp, Path.comp_assoc]
    refine HomEq.trans (HomEq.comp_left p ?_) ih
    refine (((keyProp hR hB _ _ s).symm).comp_left ((Path.nil _).bwd s)).trans ?_
    rw [← Path.comp_assoc]
    refine .of_homotopic (.trans (.comp_right (.bwd_fwd s) _) ?_)
    rw [Path.nil_comp]
    exact .refl _

end Key

theorem squier_homotopy_basis (R : Finset (List α × List α)) (hR : Terminating R)
    (B : Set (Cell R)) (hB : ∀ b ∈ criticalBranchings R, Resolves B b) :
    IsHomotopyBasis B := by
  intro u v p q
  have hpq : Homotopic B (p.comp (nfPath hR v).2) (q.comp (nfPath hR v).2) :=
    ((homEq_nfPath hR hB p).trans (homEq_nfPath hR hB q).symm).homotopic
  have key : ∀ r : Path R u v, Homotopic B r
      ((r.comp (nfPath hR v).2).comp (nfPath hR v).2.inv) := fun r => by
    rw [Path.comp_assoc]
    exact (Homotopic.comp_left r (Homotopic.comp_inv _)).symm
  exact ((key p).trans (.comp_right hpq _)).trans (key q).symm

theorem squier_finiteDerivationType [Finite α] (R : Finset (List α × List α))
    (hR : Terminating R) (hc : Confluent R) : FiniteDerivationType R := by
  have hres : ∀ b : Branching R, ∃ c : Cell R, ∃ (t : List α) (ρ₁ : Path R b.tgt₁ t)
      (ρ₂ : Path R b.tgt₂ t), ρ₁.Positive ∧ ρ₂.Positive ∧
        c = Cell.mk b.src t (b.left.toPath.comp ρ₁) (b.right.toPath.comp ρ₂) := by
    intro b
    obtain ⟨t, h₁, h₂⟩ := hc (ReflTransGen.single ⟨b.left⟩) (ReflTransGen.single ⟨b.right⟩)
    obtain ⟨ρ₁, hρ₁⟩ := Path.exists_positive_of_reflTransGen h₁
    obtain ⟨ρ₂, hρ₂⟩ := Path.exists_positive_of_reflTransGen h₂
    exact ⟨_, t, ρ₁, ρ₂, hρ₁, hρ₂, rfl⟩
  choose f hf using hres
  refine ⟨f '' criticalBranchings R, (criticalBranchings_finite R).image f,
    squier_homotopy_basis R hR _ fun b hb => ?_⟩
  obtain ⟨t, ρ₁, ρ₂, hρ₁, hρ₂, he⟩ := hf b
  exact ⟨t, ρ₁, ρ₂, hρ₁, hρ₂, Or.inl (he ▸ ⟨b, hb, rfl⟩)⟩

end Squier
