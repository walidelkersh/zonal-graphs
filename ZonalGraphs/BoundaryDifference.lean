import ZonalGraphs.Definitions
import Mathlib.Tactic

namespace ZonalGraphs

/-!
# Regions whose boundaries differ by one vertex

A single observation, used repeatedly in the literature under different disguises: if two regions of a
plane graph have boundaries differing by exactly one vertex, the graph is not zonal.  Both values would
have to be zero, yet they differ by that vertex's label, which is nonzero.

This is the obstruction behind several published non-zonality arguments:

* a cycle with one pendant edge, where the exterior boundary is the cycle plus the pendant vertex
  (Theorem 3.1.1);
* a graph of cycle rank two and type (2) with exactly one vertex on no cycle (Theorem 3.2.3);
* a minimal graph of cycle rank two and type (3) with `(n₁, n₂) = (2, 3)`, where two of the three
  regions differ by the lone interior vertex of the middle path (Theorem 3.3 of *Zonal Graphs of Small
  Cycle Rank*).

Isolating it keeps those proofs to a single application each.
-/

universe u v

namespace PlaneGraph

variable {Vertex : Type u} {Face : Type v} [Fintype Vertex] [Fintype Face] [DecidableEq Vertex]

/-- **Two regions whose boundaries differ by a single vertex forbid zonality.**

The larger boundary's value exceeds the smaller one's by the label of the extra vertex, so they cannot
both vanish. -/
theorem not_isZonal_of_boundary_insert (P : PlaneGraph Vertex Face) {R S : Face}
    {B : Finset Vertex} {w : Vertex} (hR : P.boundary R = B)
    (hS : P.boundary S = insert w B) (hw : w ∉ B) : ¬P.IsZonal := by
  rintro ⟨labeling, hlabeling⟩
  have hsmall : (∑ x ∈ B, (labeling x : ZMod 3)) = 0 := by
    have h := hlabeling R; rwa [zoneValue, hR] at h
  have hlarge : (∑ x ∈ insert w B, (labeling x : ZMod 3)) = 0 := by
    have h := hlabeling S; rwa [zoneValue, hS] at h
  rw [Finset.sum_insert hw, hsmall, add_zero] at hlarge
  exact (labeling w).2 hlarge

/-- The same obstruction stated for boundaries presented as unions: if one region is bounded by
`B ∪ {w}` and another by `B`, with `w` outside `B`, the graph is not zonal. -/
theorem not_isZonal_of_boundary_union_singleton (P : PlaneGraph Vertex Face) {R S : Face}
    {B : Finset Vertex} {w : Vertex} (hR : P.boundary R = B)
    (hS : P.boundary S = B ∪ {w}) (hw : w ∉ B) : ¬P.IsZonal :=
  P.not_isZonal_of_boundary_insert hR (by rw [hS, Finset.union_comm, Finset.insert_eq]) hw

end PlaneGraph

end ZonalGraphs
