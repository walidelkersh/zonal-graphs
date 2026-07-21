import ZonalGraphs.Definitions
import Mathlib.Tactic

namespace ZonalGraphs

/-!
# Region boundaries in zonal plane graphs

This file formalizes Lemma 2.0.3 from Bowling, *Zonality in Graphs* (2023): on the
boundary of any region in a zonally labeled plane graph, the numbers of vertices carrying
the two possible labels are congruent modulo three.
-/

universe u v

namespace PlaneGraph

variable {Vertex : Type u} {Face : Type v} [Fintype Vertex] [Fintype Face]

/-- The number of vertices on the boundary of `R` whose label, viewed in `ZMod 3`, is `i`.

The boundary is represented by a `Finset`, so every boundary vertex is counted once, in
accordance with the definition of `zoneValue`. -/
def boundaryLabelCount (P : PlaneGraph Vertex Face) (labeling : VertexLabeling Vertex)
    (R : Face) (i : ZMod 3) : ℕ :=
  ((P.boundary R).filter fun vertex => (labeling vertex : ZMod 3) = i).card

/-- **Lemma 2.0.3.** If `labeling` is zonal, then on the boundary of every region the
number of vertices labeled `1` is congruent modulo three to the number labeled `2`. -/
theorem zonal_boundary_label_counts_modEq (P : PlaneGraph Vertex Face)
    (labeling : VertexLabeling Vertex) (hlabeling : P.IsZonalLabeling labeling) (R : Face) :
    Nat.ModEq 3 (P.boundaryLabelCount labeling R 1)
      (P.boundaryLabelCount labeling R 2) := by
  classical
  have hone : (1 : ZMod 3) ≠ 2 := by decide
  have htwo : (2 : ZMod 3) ≠ 1 := by decide
  have label_cases (x : Vertex) :
      (labeling x : ZMod 3) = 1 ∨ (labeling x : ZMod 3) = 2 := by
    generalize hy : (labeling x : ZMod 3) = y
    have hn : y ≠ 0 := by simpa [← hy] using (labeling x).property
    fin_cases y <;> simp_all
  have hsum : P.zoneValue labeling R =
      (P.boundaryLabelCount labeling R 1 : ZMod 3) +
        2 * (P.boundaryLabelCount labeling R 2 : ZMod 3) := by
    simp only [zoneValue, boundaryLabelCount]
    induction P.boundary R using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rcases label_cases a with h1 | h2
      · have hne : (labeling a : ZMod 3) ≠ 2 := by simpa [h1] using hone
        simp [Finset.filter_insert, ha, h1, hne, ih, hone]
        ring
      · have hne : (labeling a : ZMod 3) ≠ 1 := by simpa [h2] using htwo
        simp [Finset.filter_insert, ha, h2, hne, ih, htwo]
        ring
  have hz := hlabeling R
  rw [hsum] at hz
  have heq : (P.boundaryLabelCount labeling R 1 : ZMod 3) =
      (P.boundaryLabelCount labeling R 2 : ZMod 3) := by
    calc
      _ = (P.boundaryLabelCount labeling R 1 : ZMod 3) +
          3 * (P.boundaryLabelCount labeling R 2 : ZMod 3) := by
            have hthree : (3 : ZMod 3) = 0 := rfl
            rw [hthree, zero_mul, add_zero]
      _ = ((P.boundaryLabelCount labeling R 1 : ZMod 3) +
          2 * (P.boundaryLabelCount labeling R 2 : ZMod 3)) +
          (P.boundaryLabelCount labeling R 2 : ZMod 3) := by ring
      _ = _ := by rw [hz]; simp
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp heq

end PlaneGraph

end ZonalGraphs
