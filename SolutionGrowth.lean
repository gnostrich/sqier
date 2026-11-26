module

public import Mathlib
public import Squier

@[expose] public section

/-!
# SolutionGrowth.lean — comparator bridge for `ChallengeGrowth.lean`

The definitions come from `Squier/Defs.lean` and `Squier/GrowthDefs.lean` (identical to those in `ChallengeGrowth.lean`). The theorem
statements are identical to `ChallengeGrowth.lean`, with each `sorry` replaced by a term-level appeal to the
named theorem of the development. No new mathematics is introduced.
-/

namespace SquierGrowthChallenge

open Squier

/-! ## Statements -/

/-- Words avoiding a finite set of factors have a rational generating function. -/
theorem avoidCount_rational {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (List α)) :
    HasRationalGF fun n => (avoidCount F n : ℤ) :=
  Squier.avoidCount_rational F

/-- For a terminating, confluent system, every element of the presented monoid has exactly one
normal-form representative. -/
theorem unique_normalForm {α : Type*} (R : Finset (List α × List α)) (hR : Terminating R)
    (hc : Confluent R) (m : PresentedMonoid (presentedRels R)) :
    ∃! w : List α, IsNormalForm R w ∧
      PresentedMonoid.mk (presentedRels R) (FreeMonoid.ofList w) = m :=
  Squier.unique_normalForm R hR hc m

/-- The number of elements with a normal form of length `n` is the number of words of length
`n` avoiding every left-hand side. -/
theorem growth_eq_avoidCount {α : Type*} [Fintype α] [DecidableEq α]
    (R : Finset (List α × List α)) (hR : Terminating R) (hc : Confluent R) (n : ℕ) :
    growth R n = avoidCount (R.image Prod.fst) n :=
  Squier.growth_eq_avoidCount R hR hc n

/-- The growth series of a monoid with a finite complete rewriting system over a finite
alphabet (with respect to normal-form length) is rational. -/
theorem growth_rational {α : Type*} [Fintype α] [DecidableEq α]
    (R : Finset (List α × List α)) (hR : Terminating R) (hc : Confluent R) :
    HasRationalGF fun n => (growth R n : ℤ) :=
  Squier.growth_rational R hR hc

/-- The growth series of `S₃` with respect to `s3` is `1 + 2z + 2z² + z³`. -/
theorem s3_growth (n : ℕ) : growth s3 n = [1, 2, 2, 1].getD n 0 :=
  Squier.s3_growth n

/-- The monoid presented by `s3` has six elements. -/
theorem s3_card : Nat.card (PresentedMonoid (presentedRels s3)) = 6 :=
  Squier.s3_card

/-- The free commutative monoid on two generators, presented by `ba → ab`, has `n + 1`
elements of normal-form length `n`. -/
theorem comm2_growth (n : ℕ) : growth comm2 n = n + 1 :=
  Squier.comm2_growth n

end SquierGrowthChallenge
