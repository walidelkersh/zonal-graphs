import ZonalGraphs.Definitions
import Mathlib.Tactic

namespace ZonalGraphs

/-!
# Plane graphs whose region boundaries have size divisible by three

Proposition 5.1 of Bowling–Zhang (2022), which is Proposition 2.4.1 of Bowling's dissertation, states
that the plane graph `F_k` is zonal.  Its published proof is one line: label every vertex `1`, and note
that the boundary of every region of `F_k` has order `3` or `9`, so every region value is `0` in
`ZMod 3`.

That argument uses nothing about `F_k` beyond the divisibility, so it is recorded here in the general
form `PlaneGraph.isZonal_of_three_dvd_card_boundary`: a plane graph all of whose region boundaries have
size divisible by three is zonal, witnessed by the constant labeling `1`.

The same lemma covers Proposition 2.3 of Barrientos–Minion (2024), that every triangulation is zonal,
since a triangulation has all boundaries of size three.
-/

universe u v

namespace PlaneGraph

variable {Vertex : Type u} {Face : Type v} [Fintype Vertex] [Fintype Face]

/-- **The constant labeling `1` is zonal whenever every region boundary has size divisible by
three.**

Every region then has value `card • 1 = card = 0` in `ZMod 3`. -/
theorem isZonal_of_three_dvd_card_boundary (P : PlaneGraph Vertex Face)
    (hdvd : ∀ R : Face, 3 ∣ (P.boundary R).card) : P.IsZonal := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  refine ⟨fun _ => ⟨1, by decide⟩, fun R => ?_⟩
  obtain ⟨c, hc⟩ := hdvd R
  show ∑ _v ∈ P.boundary R, (1 : ZMod 3) = 0
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, hc]
  push_cast
  linear_combination (c : ZMod 3) * h3

/-- A plane graph every one of whose regions is bounded by a triangle is zonal.  This is the
triangulation case. -/
theorem isZonal_of_card_boundary_eq_three (P : PlaneGraph Vertex Face)
    (htri : ∀ R : Face, (P.boundary R).card = 3) : P.IsZonal :=
  P.isZonal_of_three_dvd_card_boundary fun R => (htri R) ▸ dvd_rfl

end PlaneGraph

end ZonalGraphs
