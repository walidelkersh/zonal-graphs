import ZonalGraphs.Realizability

namespace ZonalGraphs

/-!
# Facial boundaries as walks

`PlaneGraph.boundary` gives the *set* of vertices on a region's boundary. Every result checked in this development
needs only that set, which is why the interface has held. Two things it cannot express are a boundary walk that
revisits a vertex and, more sharply, one that traverses the same edge twice. The second is exactly what a bridge
does, and it is what Theorem 4.4.3 turns on.

This module adds walks without disturbing the existing field. `FacialWalks` carries a walk for each region together
with the requirement that its vertex set *is* the existing boundary, so the two views cannot drift apart. Nothing
here changes `PlaneGraph`, and no existing statement or proof is affected.

The compatibility is the field `boundary_eq`, and what it buys is recorded in `card_boundary_le_length` and
`card_boundary_eq_length`: the boundary's size is at most the walk's length, with equality exactly when the walk
repeats no vertex. The gap between the two is the information the `Finset` view discards.
-/

universe u v

variable {Vertex : Type u} {Face : Type v} [Fintype Vertex] [Fintype Face] [DecidableEq Vertex]

/-- Walks around the regions of a plane graph, agreeing with its boundary data.

Additive by design: the walk is extra structure on a `PlaneGraph`, not a replacement for `boundary`. -/
structure FacialWalks (P : PlaneGraph Vertex Face) where
  /-- The boundary walk of each region, as a list of vertices in order. -/
  walk : Face → List Vertex
  /-- The walk's vertices are exactly the region's boundary. This is the compatibility guarantee. -/
  boundary_eq : ∀ R : Face, (walk R).toFinset = P.boundary R
  /-- Consecutive vertices of a walk are adjacent. -/
  chain : ∀ R : Face, List.IsChain P.graph.Adj (walk R)

namespace FacialWalks

variable {P : PlaneGraph Vertex Face} (W : FacialWalks P)

/-- A region's boundary has at most as many vertices as its walk has steps. -/
theorem card_boundary_le_length (R : Face) : (P.boundary R).card ≤ (W.walk R).length := by
  rw [← W.boundary_eq R]
  exact List.toFinset_card_le (W.walk R)

/-- The two agree exactly when the walk repeats no vertex, so the shortfall in
`card_boundary_le_length` measures what the `Finset` view discards. -/
theorem card_boundary_eq_length (R : Face) (h : (W.walk R).Nodup) :
    (P.boundary R).card = (W.walk R).length := by
  rw [← W.boundary_eq R]
  exact List.toFinset_card_of_nodup h

/-- Every vertex of a walk lies on the region's boundary. -/
theorem mem_boundary_of_mem_walk {R : Face} {v : Vertex} (h : v ∈ W.walk R) :
    v ∈ P.boundary R := by
  rw [← W.boundary_eq R]
  exact List.mem_toFinset.mpr h

/-- Conversely every boundary vertex appears on the walk, so the walk misses nothing. -/
theorem mem_walk_of_mem_boundary {R : Face} {v : Vertex} (h : v ∈ P.boundary R) :
    v ∈ W.walk R := by
  rw [← W.boundary_eq R] at h
  exact List.mem_toFinset.mp h

/-- A zonal labeling's region value can be read off the walk when the walk repeats no vertex.

This is the bridge back to everything already proved: with `Nodup` the walk and the boundary carry the same sum, so
the walk-valued view refines the `Finset` view rather than replacing it. -/
theorem zoneValue_eq_sum_walk (labeling : VertexLabeling Vertex) (R : Face)
    (h : (W.walk R).Nodup) :
    P.zoneValue labeling R = ((W.walk R).map fun v => ((labeling v : ZonalLabel) : ZMod 3)).sum := by
  rw [PlaneGraph.zoneValue, ← W.boundary_eq R, List.sum_toFinset _ h]

end FacialWalks

end ZonalGraphs
