import ZonalGraphs.GroupZonal

namespace ZonalGraphs

/-!
# Inner zonality and zonality coincide on cubic maps

Theorem 4.4.5 says every inner zonal cubic map is zonal, and Corollary 4.4.6 turns that into an
equivalence. The proof is a count, and cubicity enters only through its consequence that each vertex
lies on exactly three region boundaries.

Summing the values of all regions counts each vertex once per region on whose boundary it lies, so the
total is `∑ v, |X_v| · ℓ v` where `X_v` is the set of regions at `v`. With `|X_v| = 3` every term dies
in `ZMod 3`, so the region values sum to zero whatever the labeling. An inner zonal labeling makes
every region but one vanish, and a sum of zeros plus one term being zero forces that term to vanish
too. The exceptional region therefore has value zero and the labeling was zonal all along.

Nothing here needs the graph to be cubic in the sense of `IsRegularOfDegree 3`, nor bridgeless, nor
planar. `three_regionsAt` is the hypothesis actually used, and for a cubic map it is the standard
incidence count.
-/

universe u v

namespace PlaneGraph

variable {Vertex : Type u} {Face : Type v} [Fintype Vertex] [Fintype Face] [DecidableEq Vertex]

/-- **Region values, summed, count each vertex once per region at it.**

Both sides count the incidences between vertices and the regions they bound, one grouping by region and
the other by vertex. -/
theorem sum_zoneValue_eq_sum_regionsAt (P : PlaneGraph Vertex Face)
    (labeling : VertexLabeling Vertex) :
    (∑ R : Face, P.zoneValue labeling R)
      = ∑ v : Vertex, ((P.regionsAt v).card : ZMod 3) * (labeling v : ZMod 3) := by
  classical
  have hindicator : ∀ R : Face, P.zoneValue labeling R
      = ∑ v : Vertex, if v ∈ P.boundary R then (labeling v : ZMod 3) else 0 := by
    intro R
    rw [zoneValue, ← Finset.sum_filter]
    exact Finset.sum_congr (by ext v; simp) fun _ _ => rfl
  rw [Finset.sum_congr rfl fun R _ => hindicator R, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rfl

/-- With every vertex on exactly three region boundaries, the region values sum to zero for every
labeling, because each vertex contributes three copies of its label and `3 = 0` in `ZMod 3`. -/
theorem sum_zoneValue_eq_zero_of_three_regionsAt (P : PlaneGraph Vertex Face)
    (hthree : ∀ v : Vertex, (P.regionsAt v).card = 3) (labeling : VertexLabeling Vertex) :
    (∑ R : Face, P.zoneValue labeling R) = 0 := by
  rw [P.sum_zoneValue_eq_sum_regionsAt labeling]
  refine Finset.sum_eq_zero fun v _ => ?_
  rw [hthree v, show ((3 : ℕ) : ZMod 3) = 0 from by decide, zero_mul]

/-- **Theorem 4.4.5 (Bowling, 2025).** An inner zonal cubic map is zonal.

The one region an inner zonal labeling is allowed to miss cannot in fact be missed: the region values
sum to zero, and every other region contributes zero, so the exceptional region does too. -/
theorem isZonal_of_isInnerZonal_of_three_regionsAt [DecidableEq Face] (P : PlaneGraph Vertex Face)
    (hthree : ∀ v : Vertex, (P.regionsAt v).card = 3) (h : P.IsInnerZonal) : P.IsZonal := by
  obtain ⟨labeling, exceptional, hexc⟩ := h
  refine ⟨labeling, fun R => ?_⟩
  by_cases hR : R = exceptional
  · subst hR
    have hsum := P.sum_zoneValue_eq_zero_of_three_regionsAt hthree labeling
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ R)] at hsum
    rwa [Finset.sum_eq_zero fun S hS => hexc S (Finset.ne_of_mem_erase hS), add_zero] at hsum
  · exact hexc R hR

/-- **Corollary 4.4.6 (Bowling, 2025).** A cubic map is zonal exactly when it is inner zonal.

One direction is Theorem 4.4.5. The other holds of any plane graph with a region to nominate as
exceptional, since a zonal labeling misses nothing. -/
theorem isZonal_iff_isInnerZonal_of_three_regionsAt [DecidableEq Face] [Nonempty Face]
    (P : PlaneGraph Vertex Face) (hthree : ∀ v : Vertex, (P.regionsAt v).card = 3) :
    P.IsZonal ↔ P.IsInnerZonal := by
  refine ⟨fun ⟨labeling, hlabeling⟩ =>
    ⟨labeling, Classical.arbitrary Face, fun R _ => hlabeling R⟩,
    P.isZonal_of_isInnerZonal_of_three_regionsAt hthree⟩

end PlaneGraph

end ZonalGraphs
