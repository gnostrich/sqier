module

public import Mathlib

@[expose] public section

/-!
# ChallengeGrowth.lean — growth series of monoids with a finite complete rewriting system are
rational (Mathlib-only statements)

For a finite set `F` of words over a finite alphabet, the number `aₙ` of words of length `n`
avoiding every element of `F` as a factor has a rational generating function. For a finite
terminating and confluent string rewriting system `R`, every element of the presented monoid
(Mathlib's `PresentedMonoid`) has exactly one normal form, the normal forms are exactly the words
avoiding the left-hand sides of `R`, and so the growth series of the monoid with respect to
normal-form length is rational. This file states, with `sorry` as every proof:

* `avoidCount_rational`: words avoiding a finite set of factors have a rational generating
  function (transfer matrix and Cayley–Hamilton);
* `unique_normalForm`: for a terminating, confluent system, every element of the presented
  monoid has exactly one normal-form representative;
* `growth_eq_avoidCount`: the number of monoid elements with a normal form of length `n` equals
  the number of words of length `n` avoiding all left-hand sides;
* `growth_rational`: hence the growth series (normal-form length) is rational;
* `s3_growth`, `s3_card`: for the system `aa → ε`, `bb → ε`, `bab → aba` of the symmetric group
  `S₃`, the growth series is `1 + 2z + 2z² + z³` and the presented monoid has `6` elements;
* `comm2_growth`: for `ba → ab` (the free commutative monoid on two generators) there are
  `n + 1` elements of length `n`, i.e. the series `1/(1-z)²`.

The growth series is taken with respect to the length of normal forms. For length-reducing or
shortlex-compatible complete systems this is the usual growth series with respect to the
generators; in general the two may differ.

The file imports **only Mathlib**. Its definitions are copied verbatim from `Squier/Defs.lean`
and `Squier/GrowthDefs.lean` (namespace `Squier`); the statements are in the namespace
`SquierGrowthChallenge`. The sorry-free proofs are in `Squier/`.

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.
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

end Squier

namespace Squier

/-- The complete rewriting system of the Coxeter presentation
`S₃ = ⟨a, b | a² = b² = 1, bab = aba⟩`, with `a = 0` and `b = 1`:
the rules `aa → ε`, `bb → ε`, `bab → aba`. -/
def s3 : Finset (List (Fin 2) × List (Fin 2)) :=
  {([0, 0], []), ([1, 1], []), ([1, 0, 1], [0, 1, 0])}

end Squier

namespace Squier

/-- The number of words of length `n` over the finite alphabet `α` that contain no element of
`F` as a factor (contiguous subword). -/
def avoidCount {α : Type u} [Fintype α] [DecidableEq α] (F : Finset (List α)) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun w : List.Vector α n => ∀ f ∈ F, ¬ f <:+: w.toList).card

/-- An integer sequence has a rational generating function: `Q · (∑ aₙ Xⁿ) = P` in `ℤ⟦X⟧` for
polynomials `P, Q` with `Q(0) = 1`. Equivalently, `a` eventually satisfies a linear recurrence
with constant integer coefficients. -/
def HasRationalGF (a : ℕ → ℤ) : Prop :=
  ∃ P Q : Polynomial ℤ, Q.coeff 0 = 1 ∧
    (Q : PowerSeries ℤ) * PowerSeries.mk a = (P : PowerSeries ℤ)

/-- The defining relations of the monoid presented by `R`: `l = r` for each rule `(l, r) ∈ R`,
as relations on Mathlib's free monoid. -/
def presentedRels {α : Type u} (R : Finset (List α × List α)) :
    FreeMonoid α → FreeMonoid α → Prop :=
  fun x y => (FreeMonoid.toList x, FreeMonoid.toList y) ∈ R

/-- A word is a normal form (irreducible) for `R` when no rewriting step applies to it. -/
def IsNormalForm {α : Type u} (R : Finset (List α × List α)) (w : List α) : Prop :=
  ∀ v : List α, ¬ Rewrites R w v

/-- The growth function of the monoid presented by `R`, with respect to normal-form length: the
number of elements of Mathlib's `PresentedMonoid` that are represented by a normal form of
length `n`. -/
noncomputable def growth {α : Type u} (R : Finset (List α × List α)) (n : ℕ) : ℕ :=
  Nat.card {m : PresentedMonoid (presentedRels R) //
    ∃ w : List α, w.length = n ∧ IsNormalForm R w ∧
      PresentedMonoid.mk (presentedRels R) (FreeMonoid.ofList w) = m}

/-- The rewriting system `ba → ab` (with `a = false`, `b = true`) of the free commutative monoid on
two generators. -/
def comm2 : Finset (List Bool × List Bool) :=
  {([true, false], [false, true])}

end Squier

namespace SquierGrowthChallenge

open Squier

/-! ## Statements -/

/-- Words avoiding a finite set of factors have a rational generating function. -/
theorem avoidCount_rational {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (List α)) :
    HasRationalGF fun n => (avoidCount F n : ℤ) := by
  sorry

/-- For a terminating, confluent system, every element of the presented monoid has exactly one
normal-form representative. -/
theorem unique_normalForm {α : Type*} (R : Finset (List α × List α)) (hR : Terminating R)
    (hc : Confluent R) (m : PresentedMonoid (presentedRels R)) :
    ∃! w : List α, IsNormalForm R w ∧
      PresentedMonoid.mk (presentedRels R) (FreeMonoid.ofList w) = m := by
  sorry

/-- The number of elements with a normal form of length `n` is the number of words of length
`n` avoiding every left-hand side. -/
theorem growth_eq_avoidCount {α : Type*} [Fintype α] [DecidableEq α]
    (R : Finset (List α × List α)) (hR : Terminating R) (hc : Confluent R) (n : ℕ) :
    growth R n = avoidCount (R.image Prod.fst) n := by
  sorry

/-- The growth series of a monoid with a finite complete rewriting system over a finite
alphabet (with respect to normal-form length) is rational. -/
theorem growth_rational {α : Type*} [Fintype α] [DecidableEq α]
    (R : Finset (List α × List α)) (hR : Terminating R) (hc : Confluent R) :
    HasRationalGF fun n => (growth R n : ℤ) := by
  sorry

/-- The growth series of `S₃` with respect to `s3` is `1 + 2z + 2z² + z³`. -/
theorem s3_growth (n : ℕ) : growth s3 n = [1, 2, 2, 1].getD n 0 := by
  sorry

/-- The monoid presented by `s3` has six elements. -/
theorem s3_card : Nat.card (PresentedMonoid (presentedRels s3)) = 6 := by
  sorry

/-- The free commutative monoid on two generators, presented by `ba → ab`, has `n + 1`
elements of normal-form length `n`. -/
theorem comm2_growth (n : ℕ) : growth comm2 n = n + 1 := by
  sorry

end SquierGrowthChallenge
