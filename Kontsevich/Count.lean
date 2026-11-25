module

public import Mathlib
public import Kontsevich.Polys

@[expose] public section

namespace Kontsevich

open MvPolynomial

/-- Kontsevich's conjecture holds for series–parallel graphs: the number of points of the
affine graph hypersurface over a finite field with `q` elements is a polynomial in `q` with
integer coefficients, independent of the field. -/
theorem kontsevich_seriesParallel (s : SP) :
    ∃ P : Polynomial ℤ, ∀ (F : Type) [Field F] [Fintype F],
      (pointCount s.toGraph.ends F : ℤ) = P.eval (Fintype.card F : ℤ) := by
  sorry

end Kontsevich
