module

public import Mathlib
public import Squier.Transfer
public import Squier.CriticalPair
public import Squier.S3Aux

@[expose] public section

namespace Squier

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

end Squier
