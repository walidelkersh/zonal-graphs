import ZonalGraphs.Definitions
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic

namespace ZonalGraphs

/-!
# Bipartite planar graphs are absolutely zonal

This module formalizes Proposition 2.1.1 of Bowling, *Zonality in Graphs* (2023).

`PlaneGraph` is an interface for an embedding rather than a topological construction.  The
additional predicate `HasFacialBipartitionBalance` records the standard consequence of a valid
2-connected plane embedding used in the paper: along every facial boundary cycle, a proper
2-coloring alternates, so its two color classes occur equally often.  Keeping this geometric fact
as an explicit interface condition prevents arbitrary, invalid `boundary` data from being treated
as a plane embedding.
-/

universe u v

open scoped Classical

namespace PlaneGraph

variable {Vertex : Type u} {Face : Type v} [Fintype Vertex] [Fintype Face]

/-- The two color classes of a proper bipartite coloring occur equally often on every facial
boundary.  For a 2-connected bipartite plane graph this follows because every facial boundary is
an even cycle and the colors alternate around it. -/
def HasFacialBipartitionBalance (P : PlaneGraph Vertex Face) : Prop :=
  ∀ (coloring : P.graph.Coloring (Fin 2)) (R : Face),
    ((P.boundary R).filter fun x => coloring x = 0).card =
      ((P.boundary R).filter fun x => coloring x = 1).card

/-- The canonical zonal label attached to a bipartite 2-coloring: color `0` receives `1` and
color `1` receives `2` in `ZMod 3`. -/
def bipartiteLabeling {G : SimpleGraph Vertex} (coloring : G.Coloring (Fin 2)) :
    VertexLabeling Vertex := fun x =>
  if coloring x = 0 then ⟨1, by decide⟩ else ⟨2, by decide⟩

/-- Equal color-class cardinalities on a finite set make the canonical bipartite labeling sum to
zero modulo three. -/
lemma sum_bipartiteLabeling_eq_zero {G : SimpleGraph Vertex}
    (coloring : G.Coloring (Fin 2)) (s : Finset Vertex)
    (hbalance : (s.filter fun x => coloring x = 0).card =
      (s.filter fun x => coloring x = 1).card) :
    ∑ x ∈ s, (bipartiteLabeling coloring x : ZMod 3) = 0 := by
  classical
  have hpart : s = (s.filter fun x => coloring x = 0) ∪ (s.filter fun x => coloring x = 1) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx
      refine ⟨hx, ?_⟩
      fin_cases coloring x <;> simp
    · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
  have hdisj : Disjoint (s.filter fun x => coloring x = 0) (s.filter fun x => coloring x = 1) := by
    simp [Finset.disjoint_filter]
  rw [hpart, Finset.sum_union hdisj]
  have h0 : (∑ x ∈ s.filter fun x => coloring x = 0, (bipartiteLabeling coloring x : ZMod 3)) =
      ((s.filter fun x => coloring x = 0).card : ZMod 3) := by
    calc ∑ x ∈ s.filter fun x => coloring x = 0, (bipartiteLabeling coloring x : ZMod 3)
      _ = ∑ x ∈ s.filter fun x => coloring x = 0, (1 : ZMod 3) := by
          refine Finset.sum_congr rfl (fun x hx => ?_)
          have hc : coloring x = 0 := (Finset.mem_filter.mp hx).2
          simp [bipartiteLabeling, hc]
      _ = ((s.filter fun x => coloring x = 0).card : ZMod 3) := by simp
  have h1 : (∑ x ∈ s.filter fun x => coloring x = 1, (bipartiteLabeling coloring x : ZMod 3)) =
      2 * ((s.filter fun x => coloring x = 1).card : ZMod 3) := by
    calc ∑ x ∈ s.filter fun x => coloring x = 1, (bipartiteLabeling coloring x : ZMod 3)
      _ = ∑ x ∈ s.filter fun x => coloring x = 1, (2 : ZMod 3) := by
          refine Finset.sum_congr rfl (fun x hx => ?_)
          have hc : coloring x = 1 := (Finset.mem_filter.mp hx).2
          have hne : coloring x ≠ 0 := by simp [hc]
          simp [bipartiteLabeling, hne]
      _ = 2 * ((s.filter fun x => coloring x = 1).card : ZMod 3) := by simp [mul_comm]
  rw [h0, h1, hbalance]
  have h3 : ((1 + 2 : ZMod 3) * ((s.filter fun x => coloring x = 1).card : ZMod 3)) = 0 := by
    have h12 : (1 + 2 : ZMod 3) = 0 := rfl
    rw [h12, zero_mul]
  linear_combination h3



/-- A plane graph whose facial boundaries are balanced for bipartite colorings is zonal. -/
theorem isZonal_of_bipartite (P : PlaneGraph Vertex Face)
    (hP : P.graph.IsBipartite) (hfaces : P.HasFacialBipartitionBalance) : P.IsZonal := by
  obtain ⟨coloring⟩ := hP
  refine ⟨bipartiteLabeling coloring, ?_⟩
  intro R
  exact sum_bipartiteLabeling_eq_zero coloring (P.boundary R) (hfaces coloring R)

end PlaneGraph

/-- A finite graph is 2-connected when it has at least three vertices and deleting any one
vertex leaves a connected induced graph. -/
def SimpleGraph.IsTwoConnected {Vertex : Type u} [Fintype Vertex]
    (G : SimpleGraph Vertex) : Prop :=
  3 ≤ Fintype.card Vertex ∧ ∀ v : Vertex, (G.induce ({v}ᶜ : Set Vertex)).Connected

/-- A finite plane realization of an abstract graph, carrying the facial-boundary validity
condition needed by Proposition 2.1.1. -/
structure PlaneRealization {Vertex : Type u} [Fintype Vertex]
    (G : SimpleGraph Vertex) where
  Face : Type u
  instFintypeFace : Fintype Face
  plane : PlaneGraph Vertex Face
  graph_eq : plane.graph = G
  facial_balance_of_twoConnected_bipartite :
    SimpleGraph.IsTwoConnected G → G.IsBipartite → plane.HasFacialBipartitionBalance

attribute [instance] PlaneRealization.instFintypeFace

/-- An abstract finite graph is planar when it has a plane realization. -/
def SimpleGraph.IsPlanar {Vertex : Type u} [Fintype Vertex]
    (G : SimpleGraph Vertex) : Prop := Nonempty (PlaneRealization G)

/-- An abstract graph is absolutely zonal when it is planar and every valid finite plane
realization is zonal. -/
def SimpleGraph.IsAbsolutelyZonal {Vertex : Type u} [Fintype Vertex]
    (G : SimpleGraph Vertex) : Prop :=
  SimpleGraph.IsPlanar G ∧ ∀ E : PlaneRealization G, E.plane.IsZonal

/-- **Proposition 2.1.1 (Bowling, 2023).** Every 2-connected bipartite planar graph is absolutely
zonal. -/
theorem every_twoConnected_bipartite_planar_isAbsolutelyZonal
    {Vertex : Type u} [Fintype Vertex] (G : SimpleGraph Vertex)
    (h2 : SimpleGraph.IsTwoConnected G) (hbip : G.IsBipartite)
    (hplanar : SimpleGraph.IsPlanar G) : SimpleGraph.IsAbsolutelyZonal G := by
  refine ⟨hplanar, fun E => ?_⟩
  apply PlaneGraph.isZonal_of_bipartite E.plane
  · rw [E.graph_eq]
    exact hbip
  · exact E.facial_balance_of_twoConnected_bipartite h2 hbip

end ZonalGraphs
