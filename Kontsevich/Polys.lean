module

public import Mathlib
public import Kontsevich.Defs

@[expose] public section

namespace Kontsevich

open MvPolynomial

/-- Series composition multiplies graph polynomials. -/
theorem kirchhoff_series (G H : TTGraph) :
    kirchhoffPoly (G.series H).ends =
      rename Sum.inl (kirchhoffPoly G.ends) * rename Sum.inr (kirchhoffPoly H.ends) := by
  sorry

/-- The 2-forest polynomial of a series composition. -/
theorem forest_series (G H : TTGraph) (hG : G.src ≠ G.tgt) (hH : H.src ≠ H.tgt) :
    forestPoly (G.series H).ends (G.series H).src (G.series H).tgt =
      rename Sum.inl (forestPoly G.ends G.src G.tgt) * rename Sum.inr (kirchhoffPoly H.ends) +
        rename Sum.inl (kirchhoffPoly G.ends) * rename Sum.inr (forestPoly H.ends H.src H.tgt) := by
  sorry

/-- The graph polynomial of a parallel composition. -/
theorem kirchhoff_parallel (G H : TTGraph) (hG : G.src ≠ G.tgt) (hH : H.src ≠ H.tgt) :
    kirchhoffPoly (G.parallel H).ends =
      rename Sum.inl (kirchhoffPoly G.ends) * rename Sum.inr (forestPoly H.ends H.src H.tgt) +
        rename Sum.inl (forestPoly G.ends G.src G.tgt) * rename Sum.inr (kirchhoffPoly H.ends) := by
  sorry

/-- The 2-forest polynomial of a parallel composition. -/
theorem forest_parallel (G H : TTGraph) (hG : G.src ≠ G.tgt) (hH : H.src ≠ H.tgt) :
    forestPoly (G.parallel H).ends (G.parallel H).src (G.parallel H).tgt =
      rename Sum.inl (forestPoly G.ends G.src G.tgt) *
        rename Sum.inr (forestPoly H.ends H.src H.tgt) := by
  sorry

end Kontsevich
