import Mathlib.Combinatorics.SimpleGraph.Path

namespace ZonalGraphs

/-!
# Basic concepts for plane graphs

Mathlib does not currently provide a combinatorial type for a fixed plane embedding and its
faces.  The structure below records exactly the data about an embedding needed for zonal
labelings: its underlying connected graph, its finite collection of regions, the vertices on the
boundary of each region, and the distinguished exterior region.

`boundary R` is a `Finset` because the definition in Bowling's dissertation sums over the *set of
vertices* on a region boundary.  Thus a vertex is counted once even if a boundary walk encounters
it more than once.
-/

universe u v

/-- A finite connected graph together with the face-boundary data of a chosen plane embedding.

The type `Face` indexes the regions (zones) of the embedding.  The field `exterior` records which
region is unbounded in the chosen drawing.  Geometric validity of the supplied face data is part
of the intended meaning of a value of this structure; the structure is an interface for that data,
not a topological construction of an embedding. -/
structure PlaneGraph (Vertex : Type u) (Face : Type v)
    [Fintype Vertex] [Fintype Face] where
  graph : SimpleGraph Vertex
  connected : graph.Connected
  boundary : Face → Finset Vertex
  exterior : Face

namespace PlaneGraph

variable {Vertex : Type u} {Face : Type v} [Fintype Vertex] [Fintype Face]

/-- The interior regions of a plane graph are all regions other than its exterior region. -/
def IsInterior [DecidableEq Face] (P : PlaneGraph Vertex Face) (R : Face) : Prop :=
  R ≠ P.exterior

end PlaneGraph

end ZonalGraphs
