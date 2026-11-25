module

public import Mathlib
public import Fagin.Defs

@[expose] public section

namespace Fagin

open FirstOrder FirstOrder.Language Filter Topology

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

end Fagin
