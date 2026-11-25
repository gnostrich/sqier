module

public import Mathlib

@[expose] public section

/-!
# ChallengeKontsevich.lean — point counts of graph hypersurfaces of series–parallel graphs
(Kontsevich's conjecture for series–parallel graphs) (Mathlib-only statements)

For a finite multigraph with edge set `E`, the graph polynomial (Kirchhoff polynomial, first
Symanzik polynomial) is `Ψ = ∑_T ∏_{e ∉ T} α_e`, summed over spanning trees. Its zero set is
the graph hypersurface, whose periods are Feynman amplitudes. Kontsevich asked whether the
number of points of the graph hypersurface over `𝔽_q` is always a polynomial in `q`; this is
false in general (Belkale–Brosnan) but true for small graphs. This file states, with `sorry` as
every proof:

* `kirchhoff_series`, `forest_series`, `kirchhoff_parallel`, `forest_parallel`: the rules for
  `Ψ` and the 2-forest polynomial `Φ` (spanning 2-forests separating the two terminals) under
  series and parallel composition of two-terminal multigraphs;
* `kontsevich_seriesParallel`: for every series–parallel graph there is one integer polynomial
  `P` such that, for every finite field `F` with `q` elements, the affine graph hypersurface
  `{a ∈ F^E | Ψ(a) = 0}` has exactly `P(q)` points;
* `banana_count`: for the banana graph with `m` parallel edges (`Ψ = e_{m-1}(α)`), the number of
  points is `qᵐ - (q-1)ᵐ - m(q-1)^(m-1) + ((q-1)ᵐ + (-1)ᵐ(q-1))/q`, stated multiplied by `q`;
* `k4_count`: for `K₄`, the smallest graph that is not series–parallel, the graph hypersurface
  has `q²(q³ + q - 1)` points.

The file imports **only Mathlib**. Its definitions are copied verbatim from
`Kontsevich/Defs.lean`; the statements are in the namespace `KontsevichChallenge`. The
sorry-free proofs are in `Kontsevich/`.

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.
-/

namespace Kontsevich

open MvPolynomial

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Two vertices are joined by a path using only edges of `S` (edges are undirected; `ends e`
lists the two endpoints of the edge `e`, which may coincide). -/
def Joined (ends : E → V × V) (S : Finset E) (u v : V) : Prop :=
  Relation.ReflTransGen (fun x y => ∃ e ∈ S, ends e = (x, y) ∨ ends e = (y, x)) u v

/-- `T` is a spanning tree of the multigraph: `T` connects all vertices and has
`|V| - 1` edges. -/
def IsSpanningTree (ends : E → V × V) (T : Finset E) : Prop :=
  T.card + 1 = Fintype.card V ∧ ∀ u v : V, Joined ends T u v

/-- `F` is a spanning 2-forest separating `s` from `t`: it has `|V| - 2` edges, every vertex is
joined to `s` or to `t` within `F`, and `s` is not joined to `t` within `F`. -/
def IsSeparatingForest (ends : E → V × V) (s t : V) (F : Finset E) : Prop :=
  F.card + 2 = Fintype.card V ∧ (∀ v : V, Joined ends F s v ∨ Joined ends F t v) ∧
    ¬ Joined ends F s t

open Classical in
/-- The graph polynomial (Kirchhoff polynomial, first Symanzik polynomial) of a multigraph:
`Ψ = ∑_T ∏_{e ∉ T} α_e`, the sum over spanning trees `T`, in one variable `α_e` per edge. -/
noncomputable def kirchhoffPoly (ends : E → V × V) : MvPolynomial E ℤ :=
  ∑ T ∈ Finset.univ.filter (IsSpanningTree ends), ∏ e ∈ Tᶜ, X e

open Classical in
/-- The 2-forest polynomial of a two-terminal multigraph: `Φ = ∑_F ∏_{e ∉ F} α_e`, the sum over
spanning 2-forests `F` separating the terminals `s` and `t`. -/
noncomputable def forestPoly (ends : E → V × V) (s t : V) : MvPolynomial E ℤ :=
  ∑ F ∈ Finset.univ.filter (IsSeparatingForest ends s t), ∏ e ∈ Fᶜ, X e

/-- The number of points over the finite field `F` of the affine graph hypersurface
`Ψ = 0` in `F^E`. -/
noncomputable def pointCount (ends : E → V × V) (F : Type) [Field F] [Fintype F] : ℕ :=
  Nat.card {a : E → F // aeval a (kirchhoffPoly ends) = 0}

/-- A finite two-terminal multigraph. -/
structure TTGraph where
  /-- Vertices. -/
  V : Type
  /-- Edges. -/
  E : Type
  [instFintypeV : Fintype V]
  [instDecEqV : DecidableEq V]
  [instFintypeE : Fintype E]
  [instDecEqE : DecidableEq E]
  /-- The two endpoints of each edge. -/
  ends : E → V × V
  /-- The first terminal. -/
  src : V
  /-- The second terminal. -/
  tgt : V

attribute [instance] TTGraph.instFintypeV TTGraph.instDecEqV TTGraph.instFintypeE
  TTGraph.instDecEqE

namespace TTGraph

/-- A single edge between two distinct terminals. -/
def edge : TTGraph where
  V := Bool
  E := Unit
  ends := fun _ => (false, true)
  src := false
  tgt := true

/-- Series composition: identify the second terminal of `G` with the first terminal of `H`;
the new terminals are the first terminal of `G` and the second terminal of `H`. -/
def series (G H : TTGraph) : TTGraph where
  V := G.V ⊕ {v : H.V // v ≠ H.src}
  E := G.E ⊕ H.E
  ends := Sum.elim
    (fun e => (Sum.inl (G.ends e).1, Sum.inl (G.ends e).2))
    (fun e =>
      ((if h : (H.ends e).1 = H.src then Sum.inl G.tgt else Sum.inr ⟨(H.ends e).1, h⟩),
       (if h : (H.ends e).2 = H.src then Sum.inl G.tgt else Sum.inr ⟨(H.ends e).2, h⟩)))
  src := Sum.inl G.src
  tgt := if h : H.tgt = H.src then Sum.inl G.tgt else Sum.inr ⟨H.tgt, h⟩

/-- Parallel composition: identify the first terminals of `G` and `H`, and the second
terminals of `G` and `H`. -/
def parallel (G H : TTGraph) : TTGraph where
  V := G.V ⊕ {v : H.V // v ≠ H.src ∧ v ≠ H.tgt}
  E := G.E ⊕ H.E
  ends := Sum.elim
    (fun e => (Sum.inl (G.ends e).1, Sum.inl (G.ends e).2))
    (fun e =>
      ((if h₁ : (H.ends e).1 = H.src then Sum.inl G.src else
          if h₂ : (H.ends e).1 = H.tgt then Sum.inl G.tgt else Sum.inr ⟨(H.ends e).1, h₁, h₂⟩),
       (if h₁ : (H.ends e).2 = H.src then Sum.inl G.src else
          if h₂ : (H.ends e).2 = H.tgt then Sum.inl G.tgt else Sum.inr ⟨(H.ends e).2, h₁, h₂⟩)))
  src := Sum.inl G.src
  tgt := Sum.inl G.tgt

end TTGraph

/-- Series–parallel graphs, as terms: built from single edges by series and parallel
composition. -/
inductive SP where
  /-- A single edge. -/
  | edge : SP
  /-- Series composition. -/
  | series : SP → SP → SP
  /-- Parallel composition. -/
  | parallel : SP → SP → SP

/-- The two-terminal multigraph of a series–parallel term. -/
def SP.toGraph : SP → TTGraph
  | .edge => TTGraph.edge
  | .series s t => s.toGraph.series t.toGraph
  | .parallel s t => s.toGraph.parallel t.toGraph

/-- The banana graph with `n + 1` parallel edges between two vertices. -/
def banana : ℕ → SP
  | 0 => .edge
  | n + 1 => .parallel (banana n) .edge

/-- The complete graph `K₄` (the wheel with three spokes), the smallest graph that is not
series–parallel: vertices `0, 1, 2, 3` and the six edges `01, 02, 03, 12, 13, 23`. -/
def k4Ends : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

end Kontsevich

namespace KontsevichChallenge

open Kontsevich MvPolynomial

/-! ## Statements -/

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

/-- Kontsevich's conjecture holds for series–parallel graphs: the number of points of the
affine graph hypersurface over a finite field with `q` elements is a polynomial in `q` with
integer coefficients, independent of the field. -/
theorem kontsevich_seriesParallel (s : SP) :
    ∃ P : Polynomial ℤ, ∀ (F : Type) [Field F] [Fintype F],
      (pointCount s.toGraph.ends F : ℤ) = P.eval (Fintype.card F : ℤ) := by
  sorry

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

/-- The graph hypersurface of `K₄` has `q²(q³ + q - 1)` points over a field with `q`
elements. -/
theorem k4_count (F : Type) [Field F] [Fintype F] :
    (pointCount k4Ends F : ℤ) =
      (Fintype.card F : ℤ) ^ 2 * ((Fintype.card F : ℤ) ^ 3 + (Fintype.card F : ℤ) - 1) := by
  sorry

end KontsevichChallenge
