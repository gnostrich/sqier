module

public import Mathlib
public import Squier.Defs

@[expose] public section

/-!
# Definitions for the growth series of complete rewriting systems

These definitions are copied verbatim into `ChallengeGrowth.lean`, together with the
definitions they use from `Squier/Defs.lean`. See that file for the account of what is claimed.
-/

universe u

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
