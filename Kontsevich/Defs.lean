module

public import Mathlib

@[expose] public section

/-!
# Definitions: graph polynomials, graph hypersurfaces and series–parallel graphs

These definitions are copied verbatim into `ChallengeKontsevich.lean`. See that file for the
account of what is claimed.
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
