module

public import Mathlib
public import Fagin.Defs

@[expose] public section

namespace Fagin

open FirstOrder FirstOrder.Language Filter Topology

/-- The Rado graph has every extension property. -/
theorem radoGraph_extension (k : ℕ) : ExtensionProperty radoGraph k := by
  sorry

/-- Any two countable graphs with every extension property are isomorphic. -/
theorem nonempty_iso_of_extension {V W : Type*} [Countable V] [Countable W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hG : ∀ k, ExtensionProperty G k)
    (hH : ∀ k, ExtensionProperty H k) : Nonempty (G ≃g H) := by
  sorry

end Fagin
