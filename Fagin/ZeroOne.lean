module

public import Mathlib
public import Fagin.Count
public import Fagin.Rado

@[expose] public section

namespace Fagin

open FirstOrder FirstOrder.Language Filter Topology

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

end Fagin
