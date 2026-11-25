module

public import Mathlib
public import Kontsevich.Polys

@[expose] public section

namespace Kontsevich

open MvPolynomial

/-- The point count of the graph hypersurface of the banana graph with `m = n + 1` parallel
edges, multiplied by `q`. -/
theorem banana_count (n : ℕ) (F : Type) [Field F] [Fintype F] :
    (Fintype.card F : ℤ) * pointCount (banana n).toGraph.ends F =
      (Fintype.card F : ℤ) ^ (n + 2) -
        (Fintype.card F : ℤ) * ((Fintype.card F : ℤ) - 1) ^ (n + 1) -
        ((n : ℤ) + 1) * (Fintype.card F : ℤ) * ((Fintype.card F : ℤ) - 1) ^ n +
        ((Fintype.card F : ℤ) - 1) ^ (n + 1) +
        (-1) ^ (n + 1) * ((Fintype.card F : ℤ) - 1) := by
  sorry

end Kontsevich
