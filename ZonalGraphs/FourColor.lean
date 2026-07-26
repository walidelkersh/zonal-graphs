import ZonalGraphs.Definitions
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace ZonalGraphs

/-!
# Zonality and the Four Color Theorem

This file states the connection used in the cubic formulation of the Four Color Theorem: a
bridgeless cubic plane graph admits a proper coloring of its faces with four colors if and only if
it is zonal.

Since `PlaneGraph` records face-boundary edges rather than a separate dual graph, two distinct
faces are declared adjacent when their boundary-edge sets intersect.  For the intended (valid)
plane embeddings this is precisely adjacency across an edge.

The mathematical assertion is packaged as `PlaneGraph.FourColorZonalStatement`.  Packaging the
claim as a proposition records its statement without introducing an axiom or claiming a proof of
the Four Color Theorem.  The theorem `fourColorZonalStatement_iff` gives its fully expanded form.
-/

universe u v

namespace PlaneGraph

variable {Vertex : Type u} {Face : Type v} [Fintype Vertex] [Fintype Face]

/-- Two faces are adjacent when they are distinct and share a boundary edge. -/
def FacesAdjacent (P : PlaneGraph Vertex Face) (R S : Face) : Prop :=
  R ≠ S ∧ ∃ e, e ∈ P.boundaryEdges R ∧ e ∈ P.boundaryEdges S

/-- A proper face coloring of a plane graph with colors from `Color`. -/
def IsFaceColoring (P : PlaneGraph Vertex Face) {Color : Type*}
    (coloring : Face → Color) : Prop :=
  ∀ ⦃R S : Face⦄, P.FacesAdjacent R S → coloring R ≠ coloring S

/-- A plane graph is four-face-colorable if it has a proper face coloring using `Fin 4`.

The use of `Fin 4` allows any of the four available colors to be unused, as in the usual meaning
of four-colorability. -/
def IsFourFaceColorable (P : PlaneGraph Vertex Face) : Prop :=
  ∃ coloring : Face → Fin 4, P.IsFaceColoring coloring

/-- A graph is bridgeless when none of its edges satisfies Mathlib's
`SimpleGraph.IsBridge` predicate.  That predicate already includes the requirement that its
argument belongs to the graph's edge set. -/
def IsBridgeless (P : PlaneGraph Vertex Face) : Prop :=
  ∀ e, ¬ P.graph.IsBridge e

/-- A plane graph is cubic when its underlying graph is regular of degree three, using Mathlib's
native regularity predicate. -/
noncomputable def IsCubic (P : PlaneGraph Vertex Face) : Prop := by
  letI := Classical.decRel P.graph.Adj
  exact P.graph.IsRegularOfDegree 3

/-- The zonal-graph formulation of the Four Color Theorem for a particular plane graph:
if the graph is bridgeless and cubic, then it is four-face-colorable exactly when it is zonal. -/
def FourColorZonalStatement (P : PlaneGraph Vertex Face) : Prop :=
  P.IsBridgeless → P.IsCubic → (P.IsFourFaceColorable ↔ P.IsZonal)

/-- The explicit theorem statement connecting four-face-colorability and zonality for bridgeless
cubic plane graphs.  This theorem unfolds `FourColorZonalStatement`; proving that proposition for
all valid plane embeddings is the corresponding formulation of the Four Color Theorem. -/
theorem fourColorZonalStatement_iff (P : PlaneGraph Vertex Face) :
    P.FourColorZonalStatement ↔
      (P.IsBridgeless → P.IsCubic → (P.IsFourFaceColorable ↔ P.IsZonal)) :=
  Iff.rfl

/-- A *tricoloring* of a plane graph: a colouring of the edges with three colours in which every colour
appears on the boundary of every region.

This is the notion dual to a proper edge 3-colouring of a cubic map, and it is what Theorem 1.4 of
Bowling (2025) relates to cozonal labelings of plane triangulations.  That equivalence is *not* proved
here; its argument lives in a reference outside this project's sources, and guessing it would risk
building on a wrong reading. The definition is recorded so the statement is at least expressible. -/
def IsTricoloring (P : PlaneGraph Vertex Face) (colouring : Sym2 Vertex → Fin 3) : Prop :=
  ∀ (R : Face) (i : Fin 3), ∃ e ∈ P.boundaryEdges R, colouring e = i

/-- On a triangulation a tricoloring is injective on each region's boundary: three edges carrying three
colours forces the three to be distinct.

Counting does the work. Every colour appears, so the image of the boundary has all three elements, and a
three-element set whose image has three elements is mapped injectively. -/
theorem IsTricoloring.injOn_boundaryEdges [DecidableEq (Sym2 Vertex)]
    {P : PlaneGraph Vertex Face} {colouring : Sym2 Vertex → Fin 3} (h : P.IsTricoloring colouring)
    (R : Face) (htri : (P.boundaryEdges R).card = 3) :
    Set.InjOn colouring (P.boundaryEdges R) := by
  refine Finset.injOn_of_card_image_eq ?_
  have hsub : (Finset.univ : Finset (Fin 3)) ⊆ (P.boundaryEdges R).image colouring := by
    intro i _
    obtain ⟨e, he, hei⟩ := h R i
    exact Finset.mem_image.mpr ⟨e, he, hei⟩
  have hge : 3 ≤ ((P.boundaryEdges R).image colouring).card := by
    simpa using Finset.card_le_card hsub
  have hle := Finset.card_image_le (s := P.boundaryEdges R) (f := colouring)
  omega

end PlaneGraph

end ZonalGraphs
