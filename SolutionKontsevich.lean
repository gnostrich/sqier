module

public import Mathlib
public import Kontsevich

@[expose] public section

/-!
# SolutionKontsevich.lean — comparator bridge for `ChallengeKontsevich.lean`

The definitions come from `Kontsevich/Defs.lean` (identical to those in
`ChallengeKontsevich.lean`). The theorem statements are identical to `ChallengeKontsevich.lean`,
with each `sorry` replaced by a term-level appeal to the named theorem of the development in
`Kontsevich/`. No new mathematics is introduced.
-/

namespace KontsevichChallenge

open Kontsevich MvPolynomial

/-! ## Statements -/

/-- Series composition multiplies graph polynomials. -/
theorem kirchhoff_series (G H : TTGraph) :
    kirchhoffPoly (G.series H).ends =
      rename Sum.inl (kirchhoffPoly G.ends) * rename Sum.inr (kirchhoffPoly H.ends) :=
  Kontsevich.kirchhoff_series G H

/-- The 2-forest polynomial of a series composition. -/
theorem forest_series (G H : TTGraph) (hG : G.src ≠ G.tgt) (hH : H.src ≠ H.tgt) :
    forestPoly (G.series H).ends (G.series H).src (G.series H).tgt =
      rename Sum.inl (forestPoly G.ends G.src G.tgt) * rename Sum.inr (kirchhoffPoly H.ends) +
        rename Sum.inl (kirchhoffPoly G.ends) * rename Sum.inr (forestPoly H.ends H.src H.tgt) :=
  Kontsevich.forest_series G H hG hH

/-- The graph polynomial of a parallel composition. -/
theorem kirchhoff_parallel (G H : TTGraph) (hG : G.src ≠ G.tgt) (hH : H.src ≠ H.tgt) :
    kirchhoffPoly (G.parallel H).ends =
      rename Sum.inl (kirchhoffPoly G.ends) * rename Sum.inr (forestPoly H.ends H.src H.tgt) +
        rename Sum.inl (forestPoly G.ends G.src G.tgt) * rename Sum.inr (kirchhoffPoly H.ends) :=
  Kontsevich.kirchhoff_parallel G H hG hH

/-- The 2-forest polynomial of a parallel composition. -/
theorem forest_parallel (G H : TTGraph) (hG : G.src ≠ G.tgt) (hH : H.src ≠ H.tgt) :
    forestPoly (G.parallel H).ends (G.parallel H).src (G.parallel H).tgt =
      rename Sum.inl (forestPoly G.ends G.src G.tgt) *
        rename Sum.inr (forestPoly H.ends H.src H.tgt) :=
  Kontsevich.forest_parallel G H hG hH

/-- Kontsevich's conjecture holds for series–parallel graphs: the number of points of the
affine graph hypersurface over a finite field with `q` elements is a polynomial in `q` with
integer coefficients, independent of the field. -/
theorem kontsevich_seriesParallel (s : SP) :
    ∃ P : Polynomial ℤ, ∀ (F : Type) [Field F] [Fintype F],
      (pointCount s.toGraph.ends F : ℤ) = P.eval (Fintype.card F : ℤ) :=
  Kontsevich.kontsevich_seriesParallel s

/-- The point count of the graph hypersurface of the banana graph with `m = n + 1` parallel
edges, multiplied by `q`. -/
theorem banana_count (n : ℕ) (F : Type) [Field F] [Fintype F] :
    (Fintype.card F : ℤ) * pointCount (banana n).toGraph.ends F =
      (Fintype.card F : ℤ) ^ (n + 2) -
        (Fintype.card F : ℤ) * ((Fintype.card F : ℤ) - 1) ^ (n + 1) -
        ((n : ℤ) + 1) * (Fintype.card F : ℤ) * ((Fintype.card F : ℤ) - 1) ^ n +
        ((Fintype.card F : ℤ) - 1) ^ (n + 1) +
        (-1) ^ (n + 1) * ((Fintype.card F : ℤ) - 1) :=
  Kontsevich.banana_count n F

/-- The graph hypersurface of `K₄` has `q²(q³ + q - 1)` points over a field with `q`
elements. -/
theorem k4_count (F : Type) [Field F] [Fintype F] :
    (pointCount k4Ends F : ℤ) =
      (Fintype.card F : ℤ) ^ 2 * ((Fintype.card F : ℤ) ^ 3 + (Fintype.card F : ℤ) - 1) :=
  Kontsevich.k4_count F

end KontsevichChallenge
