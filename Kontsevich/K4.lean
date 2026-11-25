module

public import Mathlib
public import Kontsevich.Defs

@[expose] public section

namespace Kontsevich

open MvPolynomial

/-- The graph hypersurface of `K₄` has `q²(q³ + q - 1)` points over a field with `q`
elements. -/
theorem k4_count (F : Type) [Field F] [Fintype F] :
    (pointCount k4Ends F : ℤ) =
      (Fintype.card F : ℤ) ^ 2 * ((Fintype.card F : ℤ) ^ 3 + (Fintype.card F : ℤ) - 1) := by
  sorry

end Kontsevich
