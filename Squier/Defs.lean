module

public import Mathlib

@[expose] public section

/-!
# Definitions for Squier's theorem (string rewriting, homotopy of derivations)

These definitions are copied verbatim into `Challenge.lean`. See that file for the account of
what is claimed.
-/

universe u

namespace Squier

variable {α : Type u}

/-! ## Rewriting steps and the rewriting relation -/

/-- A rewriting step from `u` to `v` for the string rewriting system `R`: a rule `rule ∈ R`
applied in the context `(pre, suf)`, so that `u = pre ++ l ++ suf` and `v = pre ++ r ++ suf`
where `rule = (l, r)`. A step is determined by its context and its rule. -/
structure Step (R : Finset (List α × List α)) (u v : List α) : Type u where
  /-- The left context. -/
  pre : List α
  /-- The rule applied, as a pair (left-hand side, right-hand side). -/
  rule : List α × List α
  /-- The rule belongs to the system. -/
  mem : rule ∈ R
  /-- The right context. -/
  suf : List α
  /-- The source is the left-hand side in context. -/
  src_eq : u = pre ++ rule.1 ++ suf
  /-- The target is the right-hand side in context. -/
  tgt_eq : v = pre ++ rule.2 ++ suf

/-- The one-step rewriting relation of `R`. -/
def Rewrites (R : Finset (List α × List α)) (u v : List α) : Prop :=
  Nonempty (Step R u v)

/-- `R` is terminating (noetherian): there is no infinite chain of rewriting steps. -/
def Terminating (R : Finset (List α × List α)) : Prop :=
  WellFounded fun v u : List α => Rewrites R u v

/-- Two words are joinable: both rewrite, in zero or more steps, to a common word. -/
def Joinable (R : Finset (List α × List α)) (v w : List α) : Prop :=
  Relation.Join (Relation.ReflTransGen (Rewrites R)) v w

/-- `R` is locally confluent: any two one-step rewrites of a word are joinable. -/
def LocallyConfluent (R : Finset (List α × List α)) : Prop :=
  ∀ ⦃u v w : List α⦄, Rewrites R u v → Rewrites R u w → Joinable R v w

/-- `R` is confluent: any two multi-step rewrites of a word are joinable. -/
def Confluent (R : Finset (List α × List α)) : Prop :=
  ∀ ⦃u v w : List α⦄, Relation.ReflTransGen (Rewrites R) u v →
    Relation.ReflTransGen (Rewrites R) u w → Joinable R v w

/-! ## Branchings and critical branchings -/

/-- Two steps from the same word are *independent* when they rewrite disjoint factors: the
word is `a ++ l₁ ++ b ++ l₂ ++ c` and one step rewrites the occurrence of `l₁` while the other
rewrites the occurrence of `l₂` (in either order). -/
def Step.Independent {R : Finset (List α × List α)} {w v₁ v₂ : List α}
    (s₁ : Step R w v₁) (s₂ : Step R w v₂) : Prop :=
  (∃ b : List α, s₂.pre = s₁.pre ++ s₁.rule.1 ++ b ∧ s₁.suf = b ++ s₂.rule.1 ++ s₂.suf) ∨
    (∃ b : List α, s₁.pre = s₂.pre ++ s₂.rule.1 ++ b ∧ s₂.suf = b ++ s₁.rule.1 ++ s₁.suf)

/-- A local branching: two rewriting steps from a common source. -/
structure Branching (R : Finset (List α × List α)) : Type u where
  /-- The common source. -/
  src : List α
  /-- The target of the first step. -/
  tgt₁ : List α
  /-- The target of the second step. -/
  tgt₂ : List α
  /-- The first step. -/
  left : Step R src tgt₁
  /-- The second step. -/
  right : Step R src tgt₂

/-- A branching is *critical* when its two steps are distinct (they differ in position or in
rule), are not independent (the rewritten factors overlap, or one contains the other), and the
branching is minimal (no common nonempty left context and no common nonempty right context:
some step has empty left context and some step has empty right context). These are the
overlap and inclusion branchings of two rule left-hand sides. -/
def Branching.IsCritical {R : Finset (List α × List α)} (b : Branching R) : Prop :=
  (b.left.pre ≠ b.right.pre ∨ b.left.rule ≠ b.right.rule) ∧
    ¬ b.left.Independent b.right ∧
    (b.left.pre = [] ∨ b.right.pre = []) ∧ (b.left.suf = [] ∨ b.right.suf = [])

/-- The set of critical branchings of `R` (both orders of each critical pair are included). -/
def criticalBranchings (R : Finset (List α × List α)) : Set (Branching R) :=
  {b | b.IsCritical}

/-! ## Zig-zag paths in the derivation graph -/

/-- A zig-zag path from `u` to `v` in the derivation graph of `R` (vertices are words, edges are
steps): a finite sequence of steps, each traversed forwards (`fwd`) or backwards (`bwd`). -/
inductive Path (R : Finset (List α × List α)) : List α → List α → Type u
  /-- The empty path at `u`. -/
  | nil (u : List α) : Path R u u
  /-- Extend a path by a step traversed forwards. -/
  | fwd {u v w : List α} (p : Path R u v) (s : Step R v w) : Path R u w
  /-- Extend a path by a step traversed backwards. -/
  | bwd {u v w : List α} (p : Path R u v) (s : Step R w v) : Path R u w

namespace Path

variable {R : Finset (List α × List α)}

/-- Concatenation of paths. -/
def comp {u v w : List α} : Path R u v → Path R v w → Path R u w
  | p, nil _ => p
  | p, fwd q s => fwd (p.comp q) s
  | p, bwd q s => bwd (p.comp q) s

/-- The inverse path: the same steps in reverse order and reverse direction. -/
def inv {u v : List α} : Path R u v → Path R v u
  | nil u => nil u
  | fwd p s => ((nil _).bwd s).comp p.inv
  | bwd p s => ((nil _).fwd s).comp p.inv

/-- A path is positive (a rewriting sequence) when every step is traversed forwards. -/
def Positive {u v : List α} : Path R u v → Prop
  | nil _ => True
  | fwd p _ => p.Positive
  | bwd _ _ => False

end Path

/-- A step as a one-step path. -/
def Step.toPath {R : Finset (List α × List α)} {u v : List α} (s : Step R u v) : Path R u v :=
  (Path.nil u).fwd s

/-- Whiskering a step by the context `(x, y)`: the same rule applied in `x ++ _ ++ y`. -/
def Step.whisker {R : Finset (List α × List α)} {u v : List α} (x y : List α)
    (s : Step R u v) : Step R (x ++ u ++ y) (x ++ v ++ y) where
  pre := x ++ s.pre
  rule := s.rule
  mem := s.mem
  suf := s.suf ++ y
  src_eq := (congrArg (fun t => x ++ t ++ y) s.src_eq).trans (by simp)
  tgt_eq := (congrArg (fun t => x ++ t ++ y) s.tgt_eq).trans (by simp)

/-- Whiskering a path by the context `(x, y)`, step by step. -/
def Path.whisker {R : Finset (List α × List α)} (x y : List α) :
    {u v : List α} → Path R u v → Path R (x ++ u ++ y) (x ++ v ++ y)
  | _, _, nil _ => nil _
  | _, _, fwd p s => fwd (p.whisker x y) (s.whisker x y)
  | _, _, bwd p s => bwd (p.whisker x y) (s.whisker x y)

/-! ## Cells, homotopy and finite derivation type -/

/-- A 2-cell: a pair of parallel zig-zag paths. -/
structure Cell (R : Finset (List α × List α)) : Type u where
  /-- The common source. -/
  src : List α
  /-- The common target. -/
  tgt : List α
  /-- The first path. -/
  left : Path R src tgt
  /-- The second path. -/
  right : Path R src tgt

/-- One side of the independence square of two rules `ρ₁, ρ₂` in the word
`a ++ l₁ ++ b ++ l₂ ++ c`: first rewrite `l₁`, then `l₂`. -/
def indepLeft {R : Finset (List α × List α)} (a b c : List α) {ρ₁ ρ₂ : List α × List α}
    (h₁ : ρ₁ ∈ R) (h₂ : ρ₂ ∈ R) :
    Path R (a ++ ρ₁.1 ++ b ++ ρ₂.1 ++ c) (a ++ ρ₁.2 ++ b ++ ρ₂.2 ++ c) :=
  ((Path.nil _).fwd (⟨a, ρ₁, h₁, b ++ ρ₂.1 ++ c, by simp, by simp⟩ :
      Step R (a ++ ρ₁.1 ++ b ++ ρ₂.1 ++ c) (a ++ ρ₁.2 ++ b ++ ρ₂.1 ++ c))).fwd
    (⟨a ++ ρ₁.2 ++ b, ρ₂, h₂, c, rfl, rfl⟩ :
      Step R (a ++ ρ₁.2 ++ b ++ ρ₂.1 ++ c) (a ++ ρ₁.2 ++ b ++ ρ₂.2 ++ c))

/-- The other side of the independence square: first rewrite `l₂`, then `l₁`. -/
def indepRight {R : Finset (List α × List α)} (a b c : List α) {ρ₁ ρ₂ : List α × List α}
    (h₁ : ρ₁ ∈ R) (h₂ : ρ₂ ∈ R) :
    Path R (a ++ ρ₁.1 ++ b ++ ρ₂.1 ++ c) (a ++ ρ₁.2 ++ b ++ ρ₂.2 ++ c) :=
  ((Path.nil _).fwd (⟨a ++ ρ₁.1 ++ b, ρ₂, h₂, c, rfl, rfl⟩ :
      Step R (a ++ ρ₁.1 ++ b ++ ρ₂.1 ++ c) (a ++ ρ₁.1 ++ b ++ ρ₂.2 ++ c))).fwd
    (⟨a, ρ₁, h₁, b ++ ρ₂.2 ++ c, by simp, by simp⟩ :
      Step R (a ++ ρ₁.1 ++ b ++ ρ₂.2 ++ c) (a ++ ρ₁.2 ++ b ++ ρ₂.2 ++ c))

/-- The homotopy relation generated by a set `B` of 2-cells: the smallest relation on parallel
zig-zag paths that contains `B`, contains the independence squares (two steps rewriting
disjoint factors commute), identifies a step followed by its inverse (in either order) with the
empty path, is an equivalence relation, and is compatible with concatenation, inversion and
whiskering by contexts `x ++ _ ++ y`. Equivalently, the congruence generated by `B` on the
free (2,1)-category of the rewriting system, the independence squares playing the role of the
exchange law. -/
inductive Homotopic {R : Finset (List α × List α)} (B : Set (Cell R)) :
    {u v : List α} → Path R u v → Path R u v → Prop
  /-- The cells of `B`. -/
  | basis {u v : List α} {p q : Path R u v} : Cell.mk u v p q ∈ B → Homotopic B p q
  /-- The independence squares. -/
  | indep (a b c : List α) {ρ₁ ρ₂ : List α × List α} (h₁ : ρ₁ ∈ R) (h₂ : ρ₂ ∈ R) :
      Homotopic B (indepLeft a b c h₁ h₂) (indepRight a b c h₁ h₂)
  /-- A step followed by its inverse is homotopic to the empty path. -/
  | fwd_bwd {u v : List α} (s : Step R u v) : Homotopic B (s.toPath.bwd s) (Path.nil u)
  /-- The inverse of a step followed by the step is homotopic to the empty path. -/
  | bwd_fwd {u v : List α} (s : Step R u v) :
      Homotopic B (((Path.nil v).bwd s).fwd s) (Path.nil v)
  /-- Reflexivity. -/
  | refl {u v : List α} (p : Path R u v) : Homotopic B p p
  /-- Symmetry. -/
  | symm {u v : List α} {p q : Path R u v} : Homotopic B p q → Homotopic B q p
  /-- Transitivity. -/
  | trans {u v : List α} {p q r : Path R u v} :
      Homotopic B p q → Homotopic B q r → Homotopic B p r
  /-- Compatibility with concatenation. -/
  | comp {u v w : List α} {p p' : Path R u v} {q q' : Path R v w} :
      Homotopic B p p' → Homotopic B q q' → Homotopic B (p.comp q) (p'.comp q')
  /-- Compatibility with inversion. -/
  | inv {u v : List α} {p q : Path R u v} : Homotopic B p q → Homotopic B p.inv q.inv
  /-- Compatibility with whiskering by a context. -/
  | whisker (x y : List α) {u v : List α} {p q : Path R u v} :
      Homotopic B p q → Homotopic B (p.whisker x y) (q.whisker x y)

/-- `B` is a homotopy basis: any two parallel zig-zag paths are homotopic modulo `B`. -/
def IsHomotopyBasis {R : Finset (List α × List α)} (B : Set (Cell R)) : Prop :=
  ∀ ⦃u v : List α⦄ (p q : Path R u v), Homotopic B p q

/-- `R` has finite derivation type (FDT): it admits a finite homotopy basis. -/
def FiniteDerivationType (R : Finset (List α × List α)) : Prop :=
  ∃ B : Set (Cell R), B.Finite ∧ IsHomotopyBasis B

/-- `B` contains a resolution of the branching `b`: positive paths `ρ₁, ρ₂` from the two
targets to a common word `t`, such that the cell `(s₁ ρ₁, s₂ ρ₂)` formed by the branching and
the resolution belongs to `B`, in one orientation or the other. -/
def Resolves {R : Finset (List α × List α)} (B : Set (Cell R)) (b : Branching R) : Prop :=
  ∃ (t : List α) (ρ₁ : Path R b.tgt₁ t) (ρ₂ : Path R b.tgt₂ t), ρ₁.Positive ∧ ρ₂.Positive ∧
    (Cell.mk b.src t (b.left.toPath.comp ρ₁) (b.right.toPath.comp ρ₂) ∈ B ∨
      Cell.mk b.src t (b.right.toPath.comp ρ₂) (b.left.toPath.comp ρ₁) ∈ B)

/-! ## Example: the symmetric group `S₃` -/

/-- The complete rewriting system of the Coxeter presentation
`S₃ = ⟨a, b | a² = b² = 1, bab = aba⟩`, with `a = 0` and `b = 1`:
the rules `aa → ε`, `bb → ε`, `bab → aba`. -/
def s3 : Finset (List (Fin 2) × List (Fin 2)) :=
  {([0, 0], []), ([1, 1], []), ([1, 0, 1], [0, 1, 0])}

/-- The step `aaa → a` rewriting the left occurrence of `aa`. -/
def s3StepAAALeft : Step s3 [0, 0, 0] [0] := ⟨[], ([0, 0], []), by simp [s3], [0], rfl, rfl⟩

/-- The step `aaa → a` rewriting the right occurrence of `aa`. -/
def s3StepAAARight : Step s3 [0, 0, 0] [0] := ⟨[0], ([0, 0], []), by simp [s3], [], rfl, rfl⟩

/-- The cell of the critical pair `a·a·a` (overlap of `aa` with `aa`). -/
def s3CellAAA : Cell s3 :=
  ⟨[0, 0, 0], [0], s3StepAAALeft.toPath, s3StepAAARight.toPath⟩

/-- The cell of the critical pair `b·b·b` (overlap of `bb` with `bb`). -/
def s3CellBBB : Cell s3 :=
  ⟨[1, 1, 1], [1],
    (⟨[], ([1, 1], []), by simp [s3], [1], rfl, rfl⟩ : Step s3 [1, 1, 1] [1]).toPath,
    (⟨[1], ([1, 1], []), by simp [s3], [], rfl, rfl⟩ : Step s3 [1, 1, 1] [1]).toPath⟩

/-- The cell of the critical pair `b·b·ab` (overlap of `bb` with `bab`):
`bbab → ab` against `bbab → baba → abaa → ab`. -/
def s3CellBBAB : Cell s3 :=
  ⟨[1, 1, 0, 1], [0, 1],
    (⟨[], ([1, 1], []), by simp [s3], [0, 1], rfl, rfl⟩ : Step s3 [1, 1, 0, 1] [0, 1]).toPath,
    (((⟨[1], ([1, 0, 1], [0, 1, 0]), by simp [s3], [], rfl, rfl⟩ :
        Step s3 [1, 1, 0, 1] [1, 0, 1, 0]).toPath.fwd
      (⟨[], ([1, 0, 1], [0, 1, 0]), by simp [s3], [0], rfl, rfl⟩ :
        Step s3 [1, 0, 1, 0] [0, 1, 0, 0])).fwd
      (⟨[0, 1], ([0, 0], []), by simp [s3], [], rfl, rfl⟩ : Step s3 [0, 1, 0, 0] [0, 1]))⟩

/-- The cell of the critical pair `ba·b·b` (overlap of `bab` with `bb`):
`babb → abab → aaba → ba` against `babb → ba`. -/
def s3CellBABB : Cell s3 :=
  ⟨[1, 0, 1, 1], [1, 0],
    (((⟨[], ([1, 0, 1], [0, 1, 0]), by simp [s3], [1], rfl, rfl⟩ :
        Step s3 [1, 0, 1, 1] [0, 1, 0, 1]).toPath.fwd
      (⟨[0], ([1, 0, 1], [0, 1, 0]), by simp [s3], [], rfl, rfl⟩ :
        Step s3 [0, 1, 0, 1] [0, 0, 1, 0])).fwd
      (⟨[], ([0, 0], []), by simp [s3], [1, 0], rfl, rfl⟩ : Step s3 [0, 0, 1, 0] [1, 0])),
    (⟨[1, 0], ([1, 1], []), by simp [s3], [], rfl, rfl⟩ : Step s3 [1, 0, 1, 1] [1, 0]).toPath⟩

/-- The cell of the critical pair `ba·b·ab` (overlap of `bab` with `bab`):
`babab → abaab → abb → a` against `babab → baaba → bba → a`. -/
def s3CellBABAB : Cell s3 :=
  ⟨[1, 0, 1, 0, 1], [0],
    (((⟨[], ([1, 0, 1], [0, 1, 0]), by simp [s3], [0, 1], rfl, rfl⟩ :
        Step s3 [1, 0, 1, 0, 1] [0, 1, 0, 0, 1]).toPath.fwd
      (⟨[0, 1], ([0, 0], []), by simp [s3], [1], rfl, rfl⟩ :
        Step s3 [0, 1, 0, 0, 1] [0, 1, 1])).fwd
      (⟨[0], ([1, 1], []), by simp [s3], [], rfl, rfl⟩ : Step s3 [0, 1, 1] [0])),
    (((⟨[1, 0], ([1, 0, 1], [0, 1, 0]), by simp [s3], [], rfl, rfl⟩ :
        Step s3 [1, 0, 1, 0, 1] [1, 0, 0, 1, 0]).toPath.fwd
      (⟨[1], ([0, 0], []), by simp [s3], [1, 0], rfl, rfl⟩ :
        Step s3 [1, 0, 0, 1, 0] [1, 1, 0])).fwd
      (⟨[], ([1, 1], []), by simp [s3], [0], rfl, rfl⟩ : Step s3 [1, 1, 0] [0]))⟩

/-- The five cells of `S₃`, one for each critical pair of `s3`. -/
def s3Basis : Set (Cell s3) :=
  {s3CellAAA, s3CellBBB, s3CellBBAB, s3CellBABB, s3CellBABAB}

end Squier
