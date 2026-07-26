import ZonalGraphs.Definitions
import Mathlib.Tactic

namespace ZonalGraphs

/-!
# Unicyclic plane graphs

Theorem 2.3 of Bowling–Zhang, *Zonal Graphs of Small Cycle Rank* (2023), which is Theorem 3.1.1 of
Bowling's dissertation: a unicyclic graph `G` is zonal if and only if `G ≠ C ⋆ K₂` for every cycle `C`,
where `C ⋆ K₂` is the cycle with a single pendant edge attached.

A unicyclic plane graph has exactly two regions: one bounded by the cycle `C`, the other by the whole
graph.  Writing `S = V(C)`, the value of the first region is the label sum over `S` and the value of the
second is the sum over all vertices, so the two values differ by the sum over `V(G) \ S` — the vertices
off the cycle.  Zonality therefore forces that sum to vanish, and it can vanish exactly when the number
of off-cycle vertices is not one: none at all gives an empty sum, two or more can be balanced by
Lemma 2.0.4, but a single vertex contributes its own label, which is nonzero.

The case of exactly one off-cycle vertex is `G = C ⋆ K₂`, and that direction is proved here as
`PlaneGraph.not_isZonal_of_card_sdiff_boundary_eq_one`.  It needs no construction, only the two region
values, and it is the direction that does the work in the characterization.
-/

universe u v

namespace PlaneGraph

variable {Vertex : Type u} {Face : Type v} [Fintype Vertex] [Fintype Face] [DecidableEq Vertex]

/-- **The non-zonal half of Theorem 3.1.1.** A plane graph carrying a region bounded by `S` and a region
bounded by every vertex is not zonal when exactly one vertex lies outside `S`.

For a unicyclic graph, `S` is the vertex set of the cycle and the hypothesis says `G = C ⋆ K₂`: the
cycle bounds a region of value zero, so the other region has value `ℓ(u)` for the pendant vertex `u`,
and zonal labels are nonzero. -/
theorem not_isZonal_of_card_sdiff_boundary_eq_one (P : PlaneGraph Vertex Face) {R₁ R₂ : Face}
    {S : Finset Vertex} (h₁ : P.boundary R₁ = S) (h₂ : P.boundary R₂ = Finset.univ)
    (hcard : (Finset.univ \ S).card = 1) : ¬P.IsZonal := by
  rintro ⟨labeling, hlabeling⟩
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcard
  have hcycle : (∑ v ∈ S, (labeling v : ZMod 3)) = 0 := h₁ ▸ hlabeling R₁
  have hall : (∑ v ∈ Finset.univ, (labeling v : ZMod 3)) = 0 := h₂ ▸ hlabeling R₂
  have hsplit : (∑ v ∈ Finset.univ \ S, (labeling v : ZMod 3)) + ∑ v ∈ S, (labeling v : ZMod 3)
      = ∑ v ∈ Finset.univ, (labeling v : ZMod 3) :=
    Finset.sum_sdiff (Finset.subset_univ S)
  rw [hu, Finset.sum_singleton, hcycle, hall, add_zero] at hsplit
  exact (labeling u).2 hsplit

/-- Restated for a plane graph with exactly two regions, which is the shape of a unicyclic embedding:
the region bounded by the cycle and the region bounded by the whole graph. -/
theorem not_isZonal_of_unicyclicLike (P : PlaneGraph Vertex Face) (R₁ R₂ : Face)
    (hpendant : (Finset.univ \ P.boundary R₁).card = 1)
    (hall : P.boundary R₂ = Finset.univ) : ¬P.IsZonal :=
  P.not_isZonal_of_card_sdiff_boundary_eq_one rfl hall hpendant

end PlaneGraph

end ZonalGraphs
