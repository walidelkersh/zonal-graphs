import ZonalGraphs.Definitions
import Mathlib.Tactic

namespace ZonalGraphs

/-!
# Complementing a zonal labeling

Observation 2.1 of Bowling–Zhang, *Absolutely and Conditionally Zonal Graphs* (2022), which appears
as Observation 1.4.2 in Bowling's dissertation: exchanging the two labels of a zonal labeling gives
another zonal labeling.  The published proofs invoke it constantly, to normalize a chosen vertex —
usually the hub of a windmill — to carry the label `1`.

The reason is one line.  The two admissible labels are the nonzero elements of `ZMod 3`, and those
are negatives of one another, so complementing every label negates the value of every region.  As
`-0 = 0`, zonality survives.
-/

universe u v

/-- Exchange of the two admissible labels: `1` becomes `2` and `2` becomes `1`. -/
def ZonalLabel.compl (x : ZonalLabel) : ZonalLabel := ⟨-(x : ZMod 3), neg_ne_zero.mpr x.2⟩

@[simp] theorem ZonalLabel.coe_compl (x : ZonalLabel) :
    (x.compl : ZMod 3) = -(x : ZMod 3) := rfl

/-- Complementing every label of a labeling. -/
def VertexLabeling.compl {Vertex : Type u} (labeling : VertexLabeling Vertex) :
    VertexLabeling Vertex := fun v => (labeling v).compl

namespace PlaneGraph

variable {Vertex : Type u} {Face : Type v} [Fintype Vertex] [Fintype Face]

/-- Complementing a labeling negates the value of every region. -/
theorem zoneValue_compl (P : PlaneGraph Vertex Face) (labeling : VertexLabeling Vertex) (R : Face) :
    P.zoneValue labeling.compl R = -P.zoneValue labeling R := by
  simp only [zoneValue, VertexLabeling.compl, ZonalLabel.coe_compl, Finset.sum_neg_distrib]

/-- **Observation 2.1.** The complement of a zonal labeling is again zonal. -/
theorem IsZonalLabeling.compl {P : PlaneGraph Vertex Face} {labeling : VertexLabeling Vertex}
    (h : P.IsZonalLabeling labeling) : P.IsZonalLabeling labeling.compl := by
  intro R
  rw [P.zoneValue_compl labeling R, h R, neg_zero]

/-- **Normalization at a vertex.** A zonal plane graph has, for any chosen vertex, a zonal labeling
giving that vertex the label `1`.

This is the "we may assume `ℓ(u) = 1`" step that the published proofs of the windmill theorems open
with. -/
theorem exists_isZonalLabeling_apply_eq_one (P : PlaneGraph Vertex Face) (h : P.IsZonal)
    (u : Vertex) :
    ∃ labeling : VertexLabeling Vertex,
      P.IsZonalLabeling labeling ∧ (labeling u : ZMod 3) = 1 := by
  obtain ⟨labeling, hlabeling⟩ := h
  by_cases hu : (labeling u : ZMod 3) = 1
  · exact ⟨labeling, hlabeling, hu⟩
  · refine ⟨labeling.compl, hlabeling.compl, ?_⟩
    have hcases : ∀ c : ZMod 3, c ≠ 1 → c ≠ 0 → c = 2 := by decide
    have htwo := hcases _ hu (labeling u).2
    rw [VertexLabeling.compl, ZonalLabel.coe_compl, htwo]
    decide

end PlaneGraph

end ZonalGraphs
