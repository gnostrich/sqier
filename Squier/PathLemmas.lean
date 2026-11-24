module

public import Mathlib
public import Squier.Defs

@[expose] public section

/-!
# Generic lemmas on zig-zag paths and their homotopy

Concatenation is associative and unital, homotopy is a congruence, a path composed with its
inverse is homotopic to the empty path, positivity and whiskering are compatible with
concatenation, transport of paths along equalities of words (`Path.cast`), and positive paths
correspond to the reflexive-transitive closure of the rewriting relation.
-/

namespace Squier

variable {α : Type*} {R : Finset (List α × List α)}

/-! ## Steps -/

namespace Step

/-- Two steps between the same words with the same context and rule are equal. -/
theorem eq_of_fields {u v : List α} {s s' : Step R u v} (h₁ : s.pre = s'.pre)
    (h₂ : s.rule = s'.rule) (h₃ : s.suf = s'.suf) : s = s' := by
  obtain ⟨p, r, m, f, hs, ht⟩ := s
  obtain ⟨p', r', m', f', hs', ht'⟩ := s'
  dsimp only at h₁ h₂ h₃
  subst h₁ h₂ h₃
  rfl

/-- Two steps with the same context and rule have the same source. -/
theorem src_eq_of_fields {u v u' v' : List α} {s : Step R u v} {s' : Step R u' v'}
    (h₁ : s.pre = s'.pre) (h₂ : s.rule = s'.rule) (h₃ : s.suf = s'.suf) : u = u' := by
  rw [s.src_eq, s'.src_eq, h₁, h₂, h₃]

/-- Two steps with the same context and rule have the same target. -/
theorem tgt_eq_of_fields {u v u' v' : List α} {s : Step R u v} {s' : Step R u' v'}
    (h₁ : s.pre = s'.pre) (h₂ : s.rule = s'.rule) (h₃ : s.suf = s'.suf) : v = v' := by
  rw [s.tgt_eq, s'.tgt_eq, h₁, h₂, h₃]

/-- A one-step path is positive. -/
theorem toPath_positive {u v : List α} (s : Step R u v) : s.toPath.Positive := trivial

theorem toPath_whisker {u v : List α} (s : Step R u v) (x y : List α) :
    s.toPath.whisker x y = (s.whisker x y).toPath := by
  rw [Step.toPath, Path.whisker.eq_2, Path.whisker.eq_1]; rfl

end Step

namespace Path

/-! ## Concatenation -/

@[simp] theorem comp_nil {u v : List α} (p : Path R u v) : p.comp (nil v) = p := rfl

@[simp] theorem comp_fwd {u v w x : List α} (p : Path R u v) (q : Path R v w)
    (s : Step R w x) : p.comp (q.fwd s) = (p.comp q).fwd s := rfl

@[simp] theorem comp_bwd {u v w x : List α} (p : Path R u v) (q : Path R v w)
    (s : Step R x w) : p.comp (q.bwd s) = (p.comp q).bwd s := rfl

theorem fwd_eq_comp {u v w : List α} (p : Path R u v) (s : Step R v w) :
    p.fwd s = p.comp s.toPath := rfl

theorem bwd_eq_comp {u v w : List α} (p : Path R u v) (s : Step R w v) :
    p.bwd s = p.comp ((nil v).bwd s) := rfl

@[simp] theorem nil_comp {u v : List α} (p : Path R u v) : (nil u).comp p = p := by
  induction p with
  | nil => rfl
  | fwd p s ih => rw [comp_fwd, ih]
  | bwd p s ih => rw [comp_bwd, ih]

theorem comp_assoc {u v w x : List α} (p : Path R u v) (q : Path R v w) (r : Path R w x) :
    (p.comp q).comp r = p.comp (q.comp r) := by
  induction r with
  | nil => rfl
  | fwd r s ih => rw [comp_fwd, comp_fwd, comp_fwd, ih]
  | bwd r s ih => rw [comp_bwd, comp_bwd, comp_bwd, ih]

/-! ## Inverse -/

theorem inv_comp_distrib {u v w : List α} (p : Path R u v) (q : Path R v w) :
    (p.comp q).inv = q.inv.comp p.inv := by
  induction q with
  | nil => exact (nil_comp _).symm
  | fwd q s ih =>
    change ((nil _).bwd s).comp (p.comp q).inv = (((nil _).bwd s).comp q.inv).comp p.inv
    rw [ih, comp_assoc]
  | bwd q s ih =>
    change ((nil _).fwd s).comp (p.comp q).inv = (((nil _).fwd s).comp q.inv).comp p.inv
    rw [ih, comp_assoc]

/-! ## Positivity -/

theorem Positive.comp {u v w : List α} {p : Path R u v} {q : Path R v w} (hp : p.Positive)
    (hq : q.Positive) : (p.comp q).Positive := by
  induction q with
  | nil => exact hp
  | fwd q s ih => exact ih hq
  | bwd q s ih => exact hq.elim

/-! ## Whiskering -/

theorem whisker_comp (x y : List α) {u v w : List α} (p : Path R u v) (q : Path R v w) :
    (p.comp q).whisker x y = (p.whisker x y).comp (q.whisker x y) := by
  induction q with
  | nil => rw [whisker.eq_1]; rfl
  | fwd q s ih => rw [comp_fwd, whisker.eq_2, whisker.eq_2, ih, comp_fwd]
  | bwd q s ih => rw [comp_bwd, whisker.eq_3, whisker.eq_3, ih, comp_bwd]

theorem Positive.whisker (x y : List α) {u v : List α} {p : Path R u v} (hp : p.Positive) :
    (p.whisker x y).Positive := by
  induction p with
  | nil => rw [whisker.eq_1]; trivial
  | fwd p s ih => rw [whisker.eq_2]; exact ih hp
  | bwd p s ih => exact hp.elim

/-! ## Transport along equalities of words -/

/-- Transport a path along equalities of its endpoints. -/
def cast {u v u' v' : List α} (hu : u = u') (hv : v = v') (p : Path R u v) : Path R u' v' :=
  hu ▸ hv ▸ p

@[simp] theorem cast_rfl {u v : List α} (p : Path R u v) : p.cast rfl rfl = p := rfl

theorem cast_comp {u v w u' v' w' : List α} (hu : u = u') (hv : v = v') (hw : w = w')
    (p : Path R u v) (q : Path R v w) :
    (p.cast hu hv).comp (q.cast hv hw) = (p.comp q).cast hu hw := by
  subst hu hv hw; rfl

theorem Positive.cast {u v u' v' : List α} (hu : u = u') (hv : v = v') {p : Path R u v}
    (hp : p.Positive) : (p.cast hu hv).Positive := by
  subst hu hv; exact hp

/-- Two steps with the same context and rule give the same one-step path, up to transport. -/
theorem _root_.Squier.Step.toPath_eq_cast {u v u' v' : List α} (s : Step R u v)
    (s' : Step R u' v') (h₁ : s.pre = s'.pre) (h₂ : s.rule = s'.rule) (h₃ : s.suf = s'.suf) :
    s.toPath = s'.toPath.cast (Step.src_eq_of_fields h₁ h₂ h₃).symm
      (Step.tgt_eq_of_fields h₁ h₂ h₃).symm := by
  have hu := Step.src_eq_of_fields h₁ h₂ h₃
  have hv := Step.tgt_eq_of_fields h₁ h₂ h₃
  subst hu hv
  obtain rfl := Step.eq_of_fields h₁ h₂ h₃
  rfl

/-! ## Positive paths and the rewriting relation -/

theorem exists_positive_of_reflTransGen {u v : List α}
    (h : Relation.ReflTransGen (Rewrites R) u v) : ∃ p : Path R u v, p.Positive := by
  induction h with
  | refl => exact ⟨nil _, trivial⟩
  | tail _ hbc ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨p.fwd hbc.some, hp⟩

theorem reflTransGen_of_positive {u v : List α} (p : Path R u v) (hp : p.Positive) :
    Relation.ReflTransGen (Rewrites R) u v := by
  induction p with
  | nil => exact .refl
  | fwd p s ih => exact (ih hp).tail ⟨s⟩
  | bwd p s ih => exact hp.elim

theorem reflTransGen_iff_exists_positive {u v : List α} :
    Relation.ReflTransGen (Rewrites R) u v ↔ ∃ p : Path R u v, p.Positive :=
  ⟨exists_positive_of_reflTransGen, fun ⟨p, hp⟩ => reflTransGen_of_positive p hp⟩

end Path

/-! ## Homotopy -/

namespace Homotopic

variable {B : Set (Cell R)}

theorem comp_left {u v w : List α} (p : Path R u v) {q q' : Path R v w}
    (h : Homotopic B q q') : Homotopic B (p.comp q) (p.comp q') :=
  .comp (.refl p) h

theorem comp_right {u v w : List α} {p p' : Path R u v} (h : Homotopic B p p')
    (q : Path R v w) : Homotopic B (p.comp q) (p'.comp q) :=
  .comp h (.refl q)

theorem cast {u v u' v' : List α} (hu : u = u') (hv : v = v') {p q : Path R u v}
    (h : Homotopic B p q) : Homotopic B (p.cast hu hv) (q.cast hu hv) := by
  subst hu hv; exact h

/-- A path followed by its inverse is homotopic to the empty path. -/
theorem comp_inv {u v : List α} (p : Path R u v) : Homotopic B (p.comp p.inv) (Path.nil u) := by
  induction p with
  | nil => exact .refl _
  | fwd p s ih =>
    have e : (p.fwd s).comp (((Path.nil _).bwd s).comp p.inv) =
        p.comp ((s.toPath.bwd s).comp p.inv) := by
      rw [← Path.comp_assoc, ← Path.comp_assoc]; rfl
    rw [show (p.fwd s).inv = ((Path.nil _).bwd s).comp p.inv from rfl, e]
    refine .trans (comp_left p (comp_right (.fwd_bwd s) p.inv)) ?_
    rw [Path.nil_comp]; exact ih
  | bwd p s ih =>
    have e : (p.bwd s).comp (((Path.nil _).fwd s).comp p.inv) =
        p.comp ((((Path.nil _).bwd s).fwd s).comp p.inv) := by
      rw [← Path.comp_assoc, ← Path.comp_assoc]; rfl
    rw [show (p.bwd s).inv = ((Path.nil _).fwd s).comp p.inv from rfl, e]
    refine .trans (comp_left p (comp_right (.bwd_fwd s) p.inv)) ?_
    rw [Path.nil_comp]; exact ih

end Homotopic

end Squier
