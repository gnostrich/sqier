module

public import Mathlib
public import Fagin

@[expose] public section

/-!
# SolutionFagin.lean — comparator bridge for `ChallengeFagin.lean`

The definitions come from `Fagin/Defs.lean` (identical to those in `ChallengeFagin.lean`). The theorem
statements are identical to `ChallengeFagin.lean`, with each `sorry` replaced by a term-level appeal to the
named theorem of the development. No new mathematics is introduced.
-/

namespace FaginChallenge

open Fagin FirstOrder FirstOrder.Language Filter Topology

/-! ## Statements -/

/-- There are `2^(n choose 2)` simple graphs on `n` labelled vertices. -/
theorem card_simpleGraph (n : ℕ) : Nat.card (SimpleGraph (Fin n)) = 2 ^ n.choose 2 :=
  Fagin.card_simpleGraph n

/-- For each `k`, the proportion of graphs on `n` vertices with the `k`-extension property
tends to `1`. -/
theorem extension_almost_sure (k : ℕ) :
    Tendsto (fun n : ℕ =>
      (Nat.card {G : SimpleGraph (Fin n) // ExtensionProperty G k} : ℝ) / 2 ^ n.choose 2)
      atTop (𝓝 1) :=
  Fagin.extension_almost_sure k

/-- The Rado graph has every extension property. -/
theorem radoGraph_extension (k : ℕ) : ExtensionProperty radoGraph k :=
  Fagin.radoGraph_extension k

/-- Any two countable graphs with every extension property are isomorphic. -/
theorem nonempty_iso_of_extension {V W : Type*} [Countable V] [Countable W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hG : ∀ k, ExtensionProperty G k)
    (hH : ∀ k, ExtensionProperty H k) : Nonempty (G ≃g H) :=
  Fagin.nonempty_iso_of_extension G H hG hH

/-- If the Rado graph satisfies `φ`, then almost every finite graph satisfies `φ`. -/
theorem tendsto_one_of_rado (φ : Language.graph.Sentence)
    (h : @Sentence.Realize Language.graph ℕ radoGraph.structure φ) :
    Tendsto (graphProb φ) atTop (𝓝 1) :=
  Fagin.tendsto_one_of_rado φ h

/-- If the Rado graph does not satisfy `φ`, then almost no finite graph satisfies `φ`. -/
theorem tendsto_zero_of_not_rado (φ : Language.graph.Sentence)
    (h : ¬ @Sentence.Realize Language.graph ℕ radoGraph.structure φ) :
    Tendsto (graphProb φ) atTop (𝓝 0) :=
  Fagin.tendsto_zero_of_not_rado φ h

/-- Fagin's zero-one law: the probability that `G(n, 1/2)` satisfies a first-order sentence
tends to `0` or to `1`. -/
theorem zero_one_law (φ : Language.graph.Sentence) :
    Tendsto (graphProb φ) atTop (𝓝 0) ∨ Tendsto (graphProb φ) atTop (𝓝 1) :=
  Fagin.zero_one_law φ

end FaginChallenge
