module

public import Mathlib

@[expose] public section

/-!
# Definitions for Fagin's zero-one law

These definitions are copied verbatim into `ChallengeFagin.lean`. See that file for the account
of what is claimed.
-/

namespace Fagin

open FirstOrder FirstOrder.Language

/-- The proportion of labelled simple graphs on the vertex set `Fin n` in which the first-order
sentence `φ` (in Mathlib's language of graphs) holds. A uniformly random labelled graph on `n`
vertices is the Erdős–Rényi random graph `G(n, 1/2)`, so this is the probability that
`G(n, 1/2)` satisfies `φ`. -/
noncomputable def graphProb (φ : Language.graph.Sentence) (n : ℕ) : ℝ :=
  (Nat.card {G : SimpleGraph (Fin n) // @Sentence.Realize Language.graph (Fin n) G.structure φ} :
    ℝ) / 2 ^ n.choose 2

/-- The `k`-extension property of a graph: for any two disjoint finite sets `A, B` of vertices
with `|A| + |B| ≤ k` there is a vertex outside `A ∪ B` adjacent to every vertex of `A` and to no
vertex of `B`. -/
def ExtensionProperty {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ A B : Finset V, Disjoint A B → A.card + B.card ≤ k →
    ∃ z : V, z ∉ A ∧ z ∉ B ∧ (∀ a ∈ A, G.Adj z a) ∧ ∀ b ∈ B, ¬ G.Adj z b

/-- The Rado graph (Ackermann's model): vertices are natural numbers, and distinct `i, j` are
adjacent iff the binary digit of `max i j` in position `min i j` is `1`. -/
def radoGraph : SimpleGraph ℕ where
  Adj i j := i ≠ j ∧ Nat.testBit (max i j) (min i j) = true
  symm := ⟨fun i j h => ⟨h.1.symm, by rw [max_comm, min_comm]; exact h.2⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

end Fagin
