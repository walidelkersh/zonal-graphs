import ZonalGraphs.LabelingSums
import Mathlib.Tactic

namespace ZonalGraphs

/-!
# Subdivisions preserve zonality

This file formalizes Proposition 2.0.5 of Bowling, *Zonality in Graphs* (2023).
A subdivision is presented by an equivalence between the new vertex type and the
old vertices together with a finite fibre of new vertices for each subdivided
edge.  Its boundary condition says that a face keeps its old boundary vertices
and acquires exactly the new vertices lying on each subdivided boundary edge.
This is the part of geometric edge subdivision relevant to zone values.
-/

universe u v w u'

open scoped Classical

section

variable {Vertex : Type u} {Face : Type v} {Vertex' : Type u'}
  [Fintype Vertex] [Fintype Face] [Fintype Vertex']

namespace PlaneGraph

/-- The canonical boundary in the vertex type consisting of old vertices and
new subdivision vertices. -/
noncomputable def subdivisionBoundary (P : PlaneGraph Vertex Face)
    (X : Finset (Sym2 Vertex)) (NewVertex : ↥X → Type w)
    [∀ e, Fintype (NewVertex e)] (R : Face) :
    Finset (Vertex ⊕ (Σ e : ↥X, NewVertex e)) := by
  classical
  exact (P.boundary R).map Function.Embedding.inl ∪
    ((Finset.univ.filter fun z : Σ e : ↥X, NewVertex e =>
      (z.1.1 : Sym2 Vertex) ∈ P.boundaryEdges R).map Function.Embedding.inr)

/-- Data witnessing that `H` is obtained from `P` by subdividing every edge in
`X`.  `NewVertex e` is the finite nonempty fibre of vertices inserted into the
edge `e`; Proposition 2.0.5 assumes that every such fibre has at least two
vertices.  The face type is unchanged, as it is under edge subdivision. -/
structure IsSubdivision (P : PlaneGraph Vertex Face) (X : Finset (Sym2 Vertex))
    (H : PlaneGraph Vertex' Face) where
  NewVertex : ↥X → Type w
  instFintypeNewVertex : ∀ e, Fintype (NewVertex e)
  two_le_card : ∀ e, 2 ≤ Fintype.card (NewVertex e)
  vertexEquiv : Vertex' ≃ Vertex ⊕ (Σ e : ↥X, NewVertex e)
  boundary_eq : ∀ R,
    H.boundary R = (P.subdivisionBoundary X NewVertex R).map vertexEquiv.symm.toEmbedding

attribute [instance] IsSubdivision.instFintypeNewVertex

/-- A canonical subdivision boundary sum separates into the old boundary sum
and one sum over the new vertices on each subdivided boundary edge. -/
lemma sum_subdivisionBoundary (P : PlaneGraph Vertex Face)
    (X : Finset (Sym2 Vertex)) (NewVertex : ↥X → Type w)
    [∀ e, Fintype (NewVertex e)] (R : Face)
    (oldValue : Vertex → ZMod 3)
    (newValue : (Σ e : ↥X, NewVertex e) → ZMod 3) :
    ∑ z ∈ P.subdivisionBoundary X NewVertex R,
        Sum.elim oldValue newValue z =
      ∑ x ∈ P.boundary R, oldValue x +
        ∑ z : Σ e : ↥X, NewVertex e,
          if (z.1.1 : Sym2 Vertex) ∈ P.boundaryEdges R then newValue z else 0 := by
  classical
  unfold subdivisionBoundary
  rw [Finset.sum_union]
  · rw [Finset.sum_map, Finset.sum_map, Finset.sum_filter]
    simp
  · simp [Finset.disjoint_left]

/-- If each fibre of new subdivision vertices has total label zero, inserting
those fibres does not change any face value. -/
lemma zoneValue_subdivision_eq (P : PlaneGraph Vertex Face)
    (X : Finset (Sym2 Vertex)) (H : PlaneGraph Vertex' Face)
    (S : P.IsSubdivision X H)
    (oldLabeling : VertexLabeling Vertex)
    (newLabeling : ∀ e, VertexLabeling (S.NewVertex e))
    (hnew : ∀ e, labelingSum (newLabeling e) = 0) (R : Face) :
    H.zoneValue
      (fun x =>
        match S.vertexEquiv x with
        | Sum.inl v => oldLabeling v
        | Sum.inr z => newLabeling z.1 z.2) R =
      P.zoneValue oldLabeling R := by
  classical
  unfold zoneValue
  rw [S.boundary_eq, Finset.sum_map]
  simp only [Equiv.coe_toEmbedding, Equiv.apply_symm_apply]
  have hcast : (∑ x ∈ P.subdivisionBoundary X S.NewVertex R,
      ((match x with
       | Sum.inl v => (oldLabeling v : ZonalLabel)
       | Sum.inr z => newLabeling z.1 z.2 : ZonalLabel) : ZMod 3)) =
      ∑ x ∈ P.subdivisionBoundary X S.NewVertex R,
        Sum.elim (fun v => (oldLabeling v : ZMod 3))
          (fun z => (newLabeling z.1 z.2 : ZMod 3)) x := by
    apply Finset.sum_congr rfl
    intro x hx
    cases x <;> rfl
  rw [hcast, sum_subdivisionBoundary]
  suffices (∑ z : Σ e : ↥X, S.NewVertex e,
      if (z.1.1 : Sym2 Vertex) ∈ P.boundaryEdges R then
        ((newLabeling z.1 z.2 : ZonalLabel) : ZMod 3) else 0) = 0 by
    rw [this, add_zero]
  rw [Fintype.sum_sigma]
  apply Finset.sum_eq_zero
  intro e he
  by_cases hedge : (e.1 : Sym2 Vertex) ∈ P.boundaryEdges R
  · simp only [hedge, ↓reduceIte]
    exact hnew e
  · simp [hedge]

/-- **Proposition 2.0.5.** If `G` is zonal and `H` is obtained by subdividing
all edges in `X` two or more times, then `H` is zonal. -/
theorem zonal_of_isSubdivision (P : PlaneGraph Vertex Face)
    (X : Finset (Sym2 Vertex)) (H : PlaneGraph Vertex' Face)
    (hP : P.IsZonal) (S : P.IsSubdivision X H) : H.IsZonal := by
  classical
  obtain ⟨oldLabeling, hold⟩ := hP
  have hexists : ∀ e, ∃ labeling : VertexLabeling (S.NewVertex e),
      labelingSum labeling = 0 := fun e =>
    exists_labelingSum_zero_of_two_le (S.NewVertex e) (S.two_le_card e)
  choose newLabeling hnew using hexists
  refine ⟨fun x =>
    match S.vertexEquiv x with
    | Sum.inl v => oldLabeling v
    | Sum.inr z => newLabeling z.1 z.2, ?_⟩
  intro R
  rw [zoneValue_subdivision_eq P X H S oldLabeling newLabeling hnew R]
  exact hold R

end PlaneGraph

end

end ZonalGraphs
