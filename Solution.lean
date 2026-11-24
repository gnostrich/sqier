module

public import Mathlib
public import Squier

@[expose] public section

/-!
# Solution.lean — comparator bridge for `Challenge.lean`

The definitions come from `Squier/Defs.lean` (identical to those in `Challenge.lean`). The
theorem statements are identical to `Challenge.lean`, with each `sorry` replaced by a term-level
appeal to the named theorem of the development in `Squier/`. No new mathematics is introduced.
-/

namespace SquierChallenge

open Squier

/-! ## Statements -/

/-- Newman's lemma: a terminating, locally confluent relation is confluent. -/
theorem newman {β : Type*} {r : β → β → Prop} (hwf : WellFounded fun b a => r a b)
    (hloc : ∀ ⦃a b c : β⦄, r a b → r a c → Relation.Join (Relation.ReflTransGen r) b c) :
    ∀ ⦃a b c : β⦄, Relation.ReflTransGen r a b → Relation.ReflTransGen r a c →
      Relation.Join (Relation.ReflTransGen r) b c :=
  Squier.newman hwf hloc

/-- The critical pair lemma for string rewriting: a system is locally confluent if and only if
all its critical branchings are joinable. -/
theorem critical_pair_lemma {α : Type*} (R : Finset (List α × List α)) :
    LocallyConfluent R ↔ ∀ b ∈ criticalBranchings R, Joinable R b.tgt₁ b.tgt₂ :=
  Squier.critical_pair_lemma R

/-- A terminating string rewriting system is confluent if and only if all its critical
branchings are joinable. -/
theorem confluent_iff_criticalPairs_joinable {α : Type*} (R : Finset (List α × List α))
    (hR : Terminating R) :
    Confluent R ↔ ∀ b ∈ criticalBranchings R, Joinable R b.tgt₁ b.tgt₂ :=
  Squier.confluent_iff_criticalPairs_joinable R hR

/-- Over a finite alphabet, a finite string rewriting system has finitely many critical
branchings. -/
theorem criticalBranchings_finite {α : Type*} [Finite α] (R : Finset (List α × List α)) :
    (criticalBranchings R).Finite :=
  Squier.criticalBranchings_finite R

/-- Squier's theorem, homotopy-basis form: for a terminating system, a set of cells containing
a resolution cell for every critical branching is a homotopy basis. -/
theorem squier_homotopy_basis {α : Type*} (R : Finset (List α × List α)) (hR : Terminating R)
    (B : Set (Cell R)) (hB : ∀ b ∈ criticalBranchings R, Resolves B b) :
    IsHomotopyBasis B :=
  Squier.squier_homotopy_basis R hR B hB

/-- Squier's theorem: a finite convergent string rewriting system over a finite alphabet has
finite derivation type. -/
theorem squier_finiteDerivationType {α : Type*} [Finite α] (R : Finset (List α × List α))
    (hR : Terminating R) (hc : Confluent R) : FiniteDerivationType R :=
  Squier.squier_finiteDerivationType R hR hc

/-- Non-degeneracy: with no cells, the two one-step rewrites `aaa → a` of `s3` (rewriting the
left or the right occurrence of `aa`) are not homotopic. -/
theorem homotopy_nondegenerate :
    ¬ Homotopic (∅ : Set (Cell s3)) s3StepAAALeft.toPath s3StepAAARight.toPath :=
  Squier.homotopy_nondegenerate

/-- The rewriting system of `S₃` is terminating and confluent. -/
theorem s3_convergent : Terminating s3 ∧ Confluent s3 :=
  Squier.s3_convergent

/-- The five critical-pair cells of `S₃` form a homotopy basis. -/
theorem s3_homotopy_basis : IsHomotopyBasis s3Basis :=
  Squier.s3_homotopy_basis

end SquierChallenge
