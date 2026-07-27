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

/-- The edges a walk traverses, as an ordered list of consecutive pairs. -/
def edgeSteps (l : List Vertex) : List (Sym2 Vertex) :=
  l.zipWith (fun a b => s(a, b)) l.tail

/-- A region **traverses an edge twice** when that edge occurs at least twice among its walk's steps.

This is the configuration a `Finset` boundary cannot see and the one a bridge creates: the region on either side of
a bridge is the same region, so its boundary walk runs along that edge once in each direction. -/
def TraversesTwice (W : FacialWalks P) (R : Face) (e : Sym2 Vertex) : Prop :=
  2 ≤ (edgeSteps (W.walk R)).count e

/-- A plane graph **has a bridge witnessed by its walks** when some region traverses some edge twice. -/
def HasRepeatedEdge (W : FacialWalks P) : Prop :=
  ∃ (R : Face) (e : Sym2 Vertex), W.TraversesTwice R e

end FacialWalks


/-!
## The matching bound behind overfull graphs

Theorem 4.4.3 is Theorem 6.13 of Chartrand, Egan and Zhang, and its contradiction comes from a counting theorem about
*overfull* graphs: one of odd order `n` and size `m` with `m > Δ(n-1)/2` admits no proper `Δ`-edge-colouring. Mathlib
has no edge-colouring theory to draw on, so the counting core is proved here.

That core is about disjoint pairs rather than about graphs, which is why it is stated that way: a matching is a family
of pairwise disjoint two-element vertex sets, and all the bound needs is that such a family cannot be larger than half
the vertex set. Stated abstractly it is reusable, and it specializes to the matching bound `|M| ≤ (n-1)/2` for odd `n`.
-/

/-- **Pairwise disjoint pairs cannot exceed half the ambient type.** The counting core of the matching bound. -/
theorem two_mul_card_le_of_pairwise_disjoint_pairs {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (ends : ι → Finset V) (hcard : ∀ i, (ends i).card = 2)
    (hdisj : ∀ i j, i ≠ j → Disjoint (ends i) (ends j)) : 2 * Fintype.card ι ≤ Fintype.card V := by
  classical
  have hcardb : (Finset.univ.biUnion ends).card = ∑ _i : ι, 2 :=
    (Finset.card_biUnion fun i _ j _ hij => hdisj i j hij).trans
      (Finset.sum_congr rfl fun i _ => hcard i)
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm] at hcardb
  have hle := Finset.card_le_card (Finset.subset_univ (Finset.univ.biUnion ends))
  rw [hcardb, Finset.card_univ] at hle
  exact hle

/-- The matching bound in the form the overfull argument uses: on an odd number of vertices a family of pairwise
disjoint pairs has at most `(n-1)/2` members. -/
theorem card_le_of_pairwise_disjoint_pairs_odd {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (ends : ι → Finset V) (hcard : ∀ i, (ends i).card = 2)
    (hdisj : ∀ i j, i ≠ j → Disjoint (ends i) (ends j)) (hodd : Odd (Fintype.card V)) :
    Fintype.card ι ≤ (Fintype.card V - 1) / 2 := by
  have h := two_mul_card_le_of_pairwise_disjoint_pairs ends hcard hdisj
  obtain ⟨t, ht⟩ := hodd
  omega

omit [DecidableEq Vertex] in
/-- **Observation 6.9 of Chartrand, Egan and Zhang.** A zonal labeling, restricted to the vertices bounding one
region, is a zonal labeling of the cycle that region bounds.

Near-trivial in this development, and that is the point: `zoneValue` already computes the sum over a region's
boundary, so "the restriction is zonal for the cycle" is the same arithmetic statement as "that region has value
zero". The cycle is presented as any plane graph all of whose regions are bounded by exactly those vertices, which is
what a cycle's two regions do. -/
theorem isZonalLabeling_of_boundary_eq {Face' : Type v} [Fintype Face'] {P : PlaneGraph Vertex Face}
    {Q : PlaneGraph Vertex Face'} {R : Face} (hQ : ∀ S : Face', Q.boundary S = P.boundary R)
    (labeling : VertexLabeling Vertex) (h : P.zoneValue labeling R = 0) :
    Q.IsZonalLabeling labeling := by
  intro S
  rw [PlaneGraph.zoneValue, hQ S]
  exact h

omit [DecidableEq Vertex] in
/-- The same for a labeling zonal on the whole plane graph: its restriction is zonal on every region's cycle. -/
theorem isZonalLabeling_restrict {Face' : Type v} [Fintype Face'] {P : PlaneGraph Vertex Face}
    {Q : PlaneGraph Vertex Face'} {R : Face} (hQ : ∀ S : Face', Q.boundary S = P.boundary R)
    {labeling : VertexLabeling Vertex} (h : P.IsZonalLabeling labeling) :
    Q.IsZonalLabeling labeling :=
  isZonalLabeling_of_boundary_eq hQ labeling (h R)

end ZonalGraphs
