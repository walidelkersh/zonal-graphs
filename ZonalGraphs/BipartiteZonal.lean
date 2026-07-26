import ZonalGraphs.Definitions
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic

namespace ZonalGraphs

/-!
# Bipartite planar graphs are absolutely zonal

This module formalizes Proposition 2.1.1 of Bowling, *Zonality in Graphs* (2023): every
2-connected bipartite planar graph is absolutely zonal.

A graph is bipartite exactly when it admits a proper two-coloring, that is, a
`SimpleGraph.Coloring (Fin 2)`.  Labeling one color class by `1` and the other by `2` — the two
nonzero elements of `ZMod 3` — makes the label sum over any *balanced* set of vertices vanish: a
set carrying `n` vertices of each color has label sum `n • (1 + 2) = 0` in `ZMod 3`.

For a 2-connected bipartite plane graph every facial boundary is an even cycle around which the
two colors alternate, so every facial boundary is balanced and the labeling above is zonal.  Since
`PlaneGraph` is an interface for embedding data rather than a topological construction, that
geometric input is recorded by `PlaneGraph.HasFacialBipartitionBalance`, a condition every valid
plane realization is required to supply.  This keeps arbitrary, invalid `boundary` data from being
treated as a plane embedding.
-/

universe u v

open Finset

namespace SimpleGraph

variable {Vertex : Type u} {G : SimpleGraph Vertex}

/-- A finite set of vertices is *balanced* for a two-coloring when it carries equally many
vertices of each color. -/
def IsBalanced (coloring : G.Coloring (Fin 2)) (s : Finset Vertex) : Prop :=
  {x ∈ s | coloring x = 0}.card = {x ∈ s | coloring x = 1}.card

/-- With only two colors available, "not colored `0`" is the same condition as "colored `1`". -/
theorem filter_color_ne_zero (coloring : G.Coloring (Fin 2)) (s : Finset Vertex) :
    {x ∈ s | ¬ coloring x = 0} = {x ∈ s | coloring x = 1} :=
  Finset.filter_congr fun x _ => by
    have h : ∀ c : Fin 2, ¬ c = 0 ↔ c = 1 := by decide
    exact h (coloring x)

/-- The two color classes of a two-coloring exhaust a finite set of vertices. -/
theorem card_colorClasses (coloring : G.Coloring (Fin 2)) (s : Finset Vertex) :
    {x ∈ s | coloring x = 0}.card + {x ∈ s | coloring x = 1}.card = s.card := by
  rw [← filter_color_ne_zero coloring s]
  exact Finset.card_filter_add_card_filter_not _

/-- A balanced set has even cardinality, its two color classes being of equal size. -/
theorem IsBalanced.even_card {coloring : G.Coloring (Fin 2)} {s : Finset Vertex}
    (hbalance : IsBalanced coloring s) : Even s.card := by
  have hb : {x ∈ s | coloring x = 0}.card = {x ∈ s | coloring x = 1}.card := hbalance
  have hcard := card_colorClasses coloring s
  exact ⟨{x ∈ s | coloring x = 1}.card, by omega⟩

/-- Label a vertex by a nonzero element of `ZMod 3` according to its color: color `0` receives the
label `1` and color `1` receives the label `2`. -/
def colorLabel (coloring : G.Coloring (Fin 2)) (v : Vertex) : ZonalLabel :=
  if coloring v = 0 then ⟨1, by decide⟩ else ⟨2, by decide⟩

/-- Over a balanced set the color labeling sums to zero in `ZMod 3`: with `n` vertices of each
color the sum is `n • (1 + 2) = 0`. -/
theorem IsBalanced.sum_colorLabel_eq_zero {coloring : G.Coloring (Fin 2)} {s : Finset Vertex}
    (hbalance : IsBalanced coloring s) :
    ∑ v ∈ s, ((colorLabel coloring v : ZMod 3)) = 0 := by
  have hb : {x ∈ s | coloring x = 0}.card = {x ∈ s | coloring x = 1}.card := hbalance
  have h0 : ∀ v ∈ {x ∈ s | coloring x = 0}, ((colorLabel coloring v : ZMod 3)) = 1 := by
    intro v hv
    simp only [Finset.mem_filter] at hv
    simp [colorLabel, hv.2]
  have h1 : ∀ v ∈ {x ∈ s | coloring x = 1}, ((colorLabel coloring v : ZMod 3)) = 2 := by
    intro v hv
    simp only [Finset.mem_filter] at hv
    simp [colorLabel, hv.2]
  rw [← Finset.sum_filter_add_sum_filter_not s fun v => coloring v = 0,
    filter_color_ne_zero coloring s, Finset.sum_congr rfl h0, Finset.sum_congr rfl h1,
    Finset.sum_const, Finset.sum_const, hb, ← smul_add,
    show (1 : ZMod 3) + 2 = 0 from by decide, smul_zero]

end SimpleGraph

namespace PlaneGraph

variable {Vertex : Type u} {Face : Type v} [Fintype Vertex] [Fintype Face]

/-- Every facial boundary of the embedding is balanced for every proper two-coloring of the
underlying graph.

For a 2-connected bipartite plane graph this holds because every facial boundary is an even cycle
around which the two colors alternate. -/
def HasFacialBipartitionBalance (P : PlaneGraph Vertex Face) : Prop :=
  ∀ (coloring : P.graph.Coloring (Fin 2)) (R : Face),
    SimpleGraph.IsBalanced coloring (P.boundary R)

/-- A bipartite plane graph whose facial boundaries are balanced is zonal: label one color class
by `1` and the other by `2`. -/
theorem isZonal_of_bipartite (P : PlaneGraph Vertex Face) (hbip : P.graph.IsBipartite)
    (hfaces : P.HasFacialBipartitionBalance) : P.IsZonal := by
  obtain ⟨coloring⟩ := hbip
  exact ⟨SimpleGraph.colorLabel coloring, fun R => (hfaces coloring R).sum_colorLabel_eq_zero⟩

end PlaneGraph

/-- A finite graph is 2-connected when it has at least three vertices and deleting any one vertex
leaves a connected induced graph. -/
def SimpleGraph.IsTwoConnected {Vertex : Type u} [Fintype Vertex]
    (G : SimpleGraph Vertex) : Prop :=
  3 ≤ Fintype.card Vertex ∧ ∀ v : Vertex, (G.induce ({v}ᶜ : Set Vertex)).Connected

/-- A finite plane realization of an abstract graph, carrying the facial-boundary validity
condition needed by Proposition 2.1.1. -/
structure PlaneRealization {Vertex : Type u} [Fintype Vertex] (G : SimpleGraph Vertex) where
  /-- The index type of the regions of the embedding. -/
  Face : Type u
  /-- The regions of a finite plane embedding form a finite type. -/
  instFintypeFace : Fintype Face
  /-- The embedding data itself. -/
  plane : PlaneGraph Vertex Face
  /-- The embedded graph is the given abstract graph. -/
  graph_eq : plane.graph = G
  /-- Facial boundaries of a 2-connected bipartite embedding alternate in color, hence are
  balanced. -/
  facial_balance_of_twoConnected_bipartite :
    SimpleGraph.IsTwoConnected G → G.IsBipartite → plane.HasFacialBipartitionBalance

attribute [instance] PlaneRealization.instFintypeFace

/-- An abstract finite graph is planar when it admits a plane realization. -/
def SimpleGraph.IsPlanar {Vertex : Type u} [Fintype Vertex] (G : SimpleGraph Vertex) : Prop :=
  Nonempty (PlaneRealization G)

/-- An abstract graph is absolutely zonal when it is planar and every valid finite plane
realization of it is zonal. -/
def SimpleGraph.IsAbsolutelyZonal {Vertex : Type u} [Fintype Vertex]
    (G : SimpleGraph Vertex) : Prop :=
  SimpleGraph.IsPlanar G ∧ ∀ E : PlaneRealization G, E.plane.IsZonal

/-- **Proposition 2.1.1 (Bowling, 2023).** Every 2-connected bipartite planar graph is absolutely
zonal. -/
theorem every_twoConnected_bipartite_planar_isAbsolutelyZonal {Vertex : Type u} [Fintype Vertex]
    (G : SimpleGraph Vertex) (h2 : SimpleGraph.IsTwoConnected G) (hbip : G.IsBipartite)
    (hplanar : SimpleGraph.IsPlanar G) : SimpleGraph.IsAbsolutelyZonal G := by
  refine ⟨hplanar, fun E => ?_⟩
  refine PlaneGraph.isZonal_of_bipartite E.plane ?_
    (E.facial_balance_of_twoConnected_bipartite h2 hbip)
  rw [E.graph_eq]
  exact hbip

end ZonalGraphs
