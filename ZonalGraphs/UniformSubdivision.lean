import ZonalGraphs.DutchWindmill
import ZonalGraphs.Subdivisions

namespace ZonalGraphs

/-!
# Subdividing every edge

Proposition 3.3.2 subdivides all edges of a 2-connected bipartite graph of cycle rank three a number
of times of the same parity and concludes that the result is zonal. Three of those four hypotheses do
no work.

What the parity argument in the source establishes is that the subdivided graph is again bipartite, so
that facial balance applies. Labeling the subdivided graph directly is shorter and asks for less. Give
every old vertex the label `1` and give the new vertices inserted into each edge labels summing to `2`.
A region whose boundary is a cycle has as many boundary vertices as boundary edges, say `n` of each, so
its value is `n + 2n = 3n = 0`. Cycle rank plays no part, bipartiteness plays no part, the parity of the
subdivision plays no part, and a single new vertex per edge already suffices.

What survives of the hypotheses is `hcycle`, that every region boundary has as many vertices as edges.
That is what 2-connectedness supplies in the source, since facial boundaries are then cycles. The
fibres need only be nonempty, which is where this parts company with `zonal_of_isSubdivision`: that
result asks for two new vertices per edge because it drives the fibre sums to `0`, and `0` is not the
sum of one nonzero label.
-/

universe u v w u'

open scoped Classical

section

variable {Vertex : Type u} {Face : Type v} {Vertex' : Type u'}
  [Fintype Vertex] [Fintype Face] [Fintype Vertex']

/-- A nonempty finite type carries a labeling by nonzero elements summing to `2`.

The block engine supplies it: one block, target `2`, and the fit condition holds because `ZMod.val` is
below `3`, so a type with two or more elements absorbs any target, while a one-element type gets the
single label `2`. -/
theorem exists_labelingSum_eq_two {X : Type*} [Fintype X] (hne : Nonempty X) :
    ∃ labeling : VertexLabeling X, labelingSum labeling = 2 := by
  classical
  have hfit : ∀ _ : Unit,
      ((2 : ZMod 3) - (((Finset.univ : Finset X).card : ℕ) : ZMod 3)).val
        ≤ (Finset.univ : Finset X).card := by
    intro _
    rw [Finset.card_univ]
    have hlt : (2 - ((Fintype.card X : ℕ) : ZMod 3)).val < 3 := ZMod.val_lt _
    have hpos : 0 < Fintype.card X := Fintype.card_pos_iff.mpr hne
    rcases Nat.lt_or_ge (Fintype.card X) 2 with h2 | h2
    · have h1 : Fintype.card X = 1 := by omega
      rw [h1]
      decide
    · omega
  obtain ⟨labeling, hlabeling⟩ :=
    PlaneGraph.exists_labeling_blockSum_eq (Vertex := X) (Block := Unit) (fun _ => Finset.univ)
      (fun b c hbc => absurd (Subsingleton.elim b c) hbc) (fun _ => 2) hfit
  exact ⟨labeling, hlabeling ()⟩

namespace PlaneGraph

/-- **Every edge subdivided, with no parity or bipartiteness hypothesis.**

If every boundary edge of every region is subdivided, and every region boundary has as many vertices as
edges, then the subdivided plane graph is zonal. Old vertices take the label `1` and the new vertices on
each edge take labels summing to `2`, so a region with `n` boundary vertices and `n` boundary edges has
value `n + 2n = 3n = 0`.

The subdivision data is taken apart rather than packaged as `IsSubdivision`, whose `two_le_card` field
is exactly the hypothesis this result does without. -/
theorem isZonal_of_uniform_subdivision (P : PlaneGraph Vertex Face) (X : Finset (Sym2 Vertex))
    (NewVertex : ↥X → Type w) [∀ e, Fintype (NewVertex e)] (hne : ∀ e, Nonempty (NewVertex e))
    (H : PlaneGraph Vertex' Face) (vertexEquiv : Vertex' ≃ Vertex ⊕ (Σ e : ↥X, NewVertex e))
    (hbd : ∀ R, H.boundary R
      = (P.subdivisionBoundary X NewVertex R).map vertexEquiv.symm.toEmbedding)
    (hsub : ∀ R : Face, P.boundaryEdges R ⊆ X)
    (hcycle : ∀ R : Face, (P.boundary R).card = (P.boundaryEdges R).card) : H.IsZonal := by
  classical
  choose newLabeling hnew using fun e => exists_labelingSum_eq_two (hne e)
  refine ⟨fun x =>
    match vertexEquiv x with
    | Sum.inl _ => ⟨1, by decide⟩
    | Sum.inr z => newLabeling z.1 z.2, fun R => ?_⟩
  rw [zoneValue, hbd R, Finset.sum_map]
  simp only [Equiv.coe_toEmbedding, Equiv.apply_symm_apply]
  have hcast : (∑ x ∈ P.subdivisionBoundary X NewVertex R,
      ((match x with
        | Sum.inl _ => (⟨1, by decide⟩ : ZonalLabel)
        | Sum.inr z => newLabeling z.1 z.2 : ZonalLabel) : ZMod 3)) =
      ∑ x ∈ P.subdivisionBoundary X NewVertex R,
        Sum.elim (fun _ => (1 : ZMod 3))
          (fun z => ((newLabeling z.1 z.2 : ZonalLabel) : ZMod 3)) x :=
    Finset.sum_congr rfl fun x _ => by cases x <;> rfl
  rw [hcast, sum_subdivisionBoundary]
  -- the new vertices on a boundary edge contribute `2`, and there is one such edge per boundary edge
  have hstep : ∀ e : ↥X,
      (∑ x : NewVertex e,
        if (e.1 : Sym2 Vertex) ∈ P.boundaryEdges R then ((newLabeling e x : ZonalLabel) : ZMod 3)
        else 0) = if (e.1 : Sym2 Vertex) ∈ P.boundaryEdges R then 2 else 0 := by
    intro e
    by_cases h : (e.1 : Sym2 Vertex) ∈ P.boundaryEdges R
    · simpa [h, labelingSum] using hnew e
    · simp [h]
  have hcard : (Finset.univ.filter fun e : ↥X => (e.1 : Sym2 Vertex) ∈ P.boundaryEdges R).card
      = (P.boundaryEdges R).card := by
    refine Finset.card_bij (fun e _ => (e.1 : Sym2 Vertex)) (fun e he => (Finset.mem_filter.mp he).2)
      (fun a _ b _ hab => Subtype.ext hab) fun a ha =>
      ⟨⟨a, hsub R ha⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩
  have hfib : (∑ z : Σ e : ↥X, NewVertex e,
      if (z.1.1 : Sym2 Vertex) ∈ P.boundaryEdges R then
        ((newLabeling z.1 z.2 : ZonalLabel) : ZMod 3) else 0)
      = ((P.boundaryEdges R).card : ZMod 3) * 2 := by
    rw [Fintype.sum_sigma, Finset.sum_congr rfl fun e _ => hstep e, ← Finset.sum_filter,
      Finset.sum_const, hcard, nsmul_eq_mul]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, hfib, hcycle R]
  have hthree : ((P.boundaryEdges R).card : ZMod 3) + ((P.boundaryEdges R).card : ZMod 3) * 2
      = ((P.boundaryEdges R).card : ZMod 3) * 3 := by ring
  rw [hthree, show (3 : ZMod 3) = 0 from by decide, mul_zero]

/-- **Proposition 3.3.2 (Bowling, 2025), with three hypotheses discharged.**

The source subdivides all edges of a 2-connected bipartite graph of cycle rank three a number of times
of the same parity. Bipartiteness, the cycle rank and the parity are all unused: what the labeling
needs is that each region boundary has as many vertices as edges, which is the 2-connected part, and
that each edge receives at least one new vertex.

This is stated as the specialization of `isZonal_of_uniform_subdivision` to `X` the full edge set, so
that "all edges are subdivided" becomes the hypothesis that every boundary edge lies in `X`. -/
theorem isZonal_of_subdivide_all_edges (P : PlaneGraph Vertex Face) (X : Finset (Sym2 Vertex))
    (hall : ∀ R : Face, P.boundaryEdges R ⊆ X) (NewVertex : ↥X → Type w)
    [∀ e, Fintype (NewVertex e)] (hne : ∀ e, Nonempty (NewVertex e)) (H : PlaneGraph Vertex' Face)
    (vertexEquiv : Vertex' ≃ Vertex ⊕ (Σ e : ↥X, NewVertex e))
    (hbd : ∀ R, H.boundary R
      = (P.subdivisionBoundary X NewVertex R).map vertexEquiv.symm.toEmbedding)
    (hcycle : ∀ R : Face, (P.boundary R).card = (P.boundaryEdges R).card) : H.IsZonal :=
  isZonal_of_uniform_subdivision P X NewVertex hne H vertexEquiv hbd hall hcycle

end PlaneGraph

end

end ZonalGraphs
