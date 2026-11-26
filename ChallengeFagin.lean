module

public import Mathlib

@[expose] public section

/-!
# ChallengeFagin.lean — Fagin's zero-one law for first-order sentences on random graphs
(Mathlib-only statements)

For a first-order sentence `φ` in Mathlib's language of graphs, `graphProb φ n` is the
proportion of labelled simple graphs on `n` vertices satisfying `φ`, that is, the probability
that the random graph `G(n, 1/2)` satisfies `φ`. This file states, with `sorry` as every proof:

* `card_simpleGraph`: there are `2^(n choose 2)` simple graphs on `Fin n`, so `graphProb` is a
  probability;
* `extension_almost_sure`: for each `k`, almost every finite graph has the `k`-extension
  property;
* `radoGraph_extension`: the Rado graph has the `k`-extension property for every `k`;
* `nonempty_iso_of_extension`: any two countable graphs with all extension properties are
  isomorphic (back and forth);
* `tendsto_one_of_rado` and `tendsto_zero_of_not_rado`: `graphProb φ n → 1` if the Rado graph
  satisfies `φ`, and `→ 0` otherwise (the almost-sure theory is the theory of the Rado graph);
* `zero_one_law` (Glebskii–Kogan–Liogon'kii–Talanov 1969, Fagin 1976): `graphProb φ n` tends to
  `0` or to `1`.

The file imports **only Mathlib**. Its definitions are copied verbatim from `Fagin/Defs.lean`;
the statements are in the namespace `FaginChallenge`. The sorry-free proofs are in `Fagin/`.

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.
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

namespace FaginChallenge

open Fagin FirstOrder FirstOrder.Language Filter Topology

/-! ## Statements -/

/-- There are `2^(n choose 2)` simple graphs on `n` labelled vertices. -/
theorem card_simpleGraph (n : ℕ) : Nat.card (SimpleGraph (Fin n)) = 2 ^ n.choose 2 := by
  sorry

/-- For each `k`, the proportion of graphs on `n` vertices with the `k`-extension property
tends to `1`. -/
theorem extension_almost_sure (k : ℕ) :
    Tendsto (fun n : ℕ =>
      (Nat.card {G : SimpleGraph (Fin n) // ExtensionProperty G k} : ℝ) / 2 ^ n.choose 2)
      atTop (𝓝 1) := by
  sorry

/-- The Rado graph has every extension property. -/
theorem radoGraph_extension (k : ℕ) : ExtensionProperty radoGraph k := by
  sorry

/-- Any two countable graphs with every extension property are isomorphic. -/
theorem nonempty_iso_of_extension {V W : Type*} [Countable V] [Countable W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hG : ∀ k, ExtensionProperty G k)
    (hH : ∀ k, ExtensionProperty H k) : Nonempty (G ≃g H) := by
  sorry

/-- If the Rado graph satisfies `φ`, then almost every finite graph satisfies `φ`. -/
theorem tendsto_one_of_rado (φ : Language.graph.Sentence)
    (h : @Sentence.Realize Language.graph ℕ radoGraph.structure φ) :
    Tendsto (graphProb φ) atTop (𝓝 1) := by
  sorry

/-- If the Rado graph does not satisfy `φ`, then almost no finite graph satisfies `φ`. -/
theorem tendsto_zero_of_not_rado (φ : Language.graph.Sentence)
    (h : ¬ @Sentence.Realize Language.graph ℕ radoGraph.structure φ) :
    Tendsto (graphProb φ) atTop (𝓝 0) := by
  sorry

/-- Fagin's zero-one law: the probability that `G(n, 1/2)` satisfies a first-order sentence
tends to `0` or to `1`. -/
theorem zero_one_law (φ : Language.graph.Sentence) :
    Tendsto (graphProb φ) atTop (𝓝 0) ∨ Tendsto (graphProb φ) atTop (𝓝 1) := by
  sorry

end FaginChallenge
