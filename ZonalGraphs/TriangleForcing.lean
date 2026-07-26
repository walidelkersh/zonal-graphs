import ZonalGraphs.Definitions
import Mathlib.Tactic

namespace ZonalGraphs

/-!
# A three-vertex region forces its labels equal

`DivisibleBoundary` supplies the existence direction: a region whose boundary has three vertices can
always be given value zero. The forcing direction is separate and is what the non-zonality arguments
run on. Three nonzero elements of `ZMod 3` summing to zero must all coincide, since `1 + 1 + 1` and
`2 + 2 + 2` are the only nonzero triples that vanish. So a zonal labeling is constant on the boundary of
every triangular region.

This is the engine of Theorem 2.5.11 in the dissertation, where a chain of triangles forces a whole
block of `Gn,k` to carry one label and a five-vertex region then fails to vanish. Recording it
separately keeps that argument free of element-wise arithmetic.
-/

universe u v

/-- Three nonzero elements of `ZMod 3` summing to zero are all equal: only `1 + 1 + 1` and `2 + 2 + 2`
vanish. -/
theorem eq_of_three_nonzero_sum_eq_zero {x y z : ZMod 3} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hsum : x + y + z = 0) : x = y ∧ y = z := by
  revert hx hy hz hsum
  revert x y z
  decide

namespace PlaneGraph

variable {Vertex : Type u} {Face : Type v} [Fintype Vertex] [Fintype Face] [DecidableEq Vertex]

/-- **A region with three boundary vertices forces a zonal labeling to be constant on it.**

The three labels are nonzero and sum to zero, and in `ZMod 3` that leaves only three equal labels. -/
theorem eq_of_zoneValue_eq_zero_of_card_boundary_eq_three (P : PlaneGraph Vertex Face)
    {labeling : VertexLabeling Vertex} {R : Face} (h : P.zoneValue labeling R = 0)
    (hcard : (P.boundary R).card = 3) {u v : Vertex} (hu : u ∈ P.boundary R)
    (hv : v ∈ P.boundary R) : labeling u = labeling v := by
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp hcard
  rw [zoneValue, hset, Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton, ← add_assoc] at h
  obtain ⟨h1, h2⟩ := eq_of_three_nonzero_sum_eq_zero (labeling a).2 (labeling b).2 (labeling c).2 h
  rw [hset] at hu hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  have key : ∀ w : Vertex, (w = a ∨ w = b ∨ w = c) → (labeling w : ZMod 3) = (labeling a : ZMod 3) := by
    rintro w (rfl | rfl | rfl)
    · rfl
    · exact h1.symm
    · exact (h1.trans h2).symm
  exact Subtype.ext ((key u hu).trans (key v hv).symm)

/-- A zonal labeling is constant on the boundary of every triangular region. -/
theorem IsZonalLabeling.eq_of_card_boundary_eq_three {P : PlaneGraph Vertex Face}
    {labeling : VertexLabeling Vertex} (h : P.IsZonalLabeling labeling) {R : Face}
    (hcard : (P.boundary R).card = 3) {u v : Vertex} (hu : u ∈ P.boundary R)
    (hv : v ∈ P.boundary R) : labeling u = labeling v :=
  P.eq_of_zoneValue_eq_zero_of_card_boundary_eq_three (h R) hcard hu hv

end PlaneGraph

end ZonalGraphs
