import ZonalGraphs.Definitions
import Mathlib.Tactic

namespace ZonalGraphs

/-!
# Dutch windmill graphs with two blades

This module formalizes Proposition 2.2.1 of Bowling, *Zonality in Graphs* (2023): for every
multiset `S` of two cycles, the Dutch windmill graph `D(S)` is not zonal.

For a two-element `S`, the graph `D(S)` consists of two cycles meeting in a single vertex, the
*hub*.  Its plane embedding has three regions: each cycle bounds one interior region, and the two
cycles together bound the exterior region.

The obstruction depends only on the region boundaries, so it is isolated in
`PlaneGraph.not_isZonal_of_isTwoBladedWindmill`.  The exterior boundary is the union of the two
blade boundaries, and those meet exactly in the hub.  Summing labels over a union together with a
sum over the intersection counts every vertex exactly twice, so the three region values satisfy
`0 + ℓ(hub) = 0 + 0`.  That forces `ℓ(hub) = 0`, which is impossible because zonal labels are the
*nonzero* elements of `ZMod 3`.  Note that no property of cycles is used: only the shape of the
face data.

Mathlib provides no windmill construction, so the canonical three-region realization is built here
as `PlaneGraph.ofTwoBladedWindmill`.
-/

universe u v

namespace PlaneGraph

variable {Vertex : Type u} [Fintype Vertex] [DecidableEq Vertex]

section FaceStructure

variable {Face : Type v} [Fintype Face]

/-- The face structure of a two-bladed windmill: two regions whose boundaries meet in exactly one
vertex, the hub, together bounding a third region. -/
structure IsTwoBladedWindmill (P : PlaneGraph Vertex Face) (blade₁ blade₂ exterior : Face)
    (hub : Vertex) : Prop where
  /-- The two blades together bound the third region. -/
  boundary_union : P.boundary exterior = P.boundary blade₁ ∪ P.boundary blade₂
  /-- The two blades meet exactly in the hub. -/
  boundary_inter : P.boundary blade₁ ∩ P.boundary blade₂ = {hub}

/-- A plane graph carrying the face structure of a two-bladed windmill is not zonal.

If the two blade regions both had value zero, the value of the third region would be the negative
of the hub's label, and hence nonzero. -/
theorem not_isZonal_of_isTwoBladedWindmill {P : PlaneGraph Vertex Face}
    {blade₁ blade₂ exterior : Face} {hub : Vertex}
    (hwindmill : P.IsTwoBladedWindmill blade₁ blade₂ exterior hub) : ¬ P.IsZonal := by
  rintro ⟨labeling, hlabeling⟩
  have hval : ∀ R : Face, (∑ v ∈ P.boundary R, (labeling v : ZMod 3)) = 0 := hlabeling
  have hsum : (∑ v ∈ P.boundary exterior, (labeling v : ZMod 3)) +
      ∑ v ∈ P.boundary blade₁ ∩ P.boundary blade₂, (labeling v : ZMod 3) =
      (∑ v ∈ P.boundary blade₁, (labeling v : ZMod 3)) +
        ∑ v ∈ P.boundary blade₂, (labeling v : ZMod 3) := by
    rw [hwindmill.boundary_union]
    exact Finset.sum_union_inter
  rw [hwindmill.boundary_inter, Finset.sum_singleton] at hsum
  simp only [hval, zero_add, add_zero] at hsum
  exact (labeling hub).property hsum

end FaceStructure

/-- The canonical three-region realization of a two-bladed windmill: a connected graph whose vertex
set is covered by two blades meeting exactly in the hub.

Region `0` is bounded by the first blade, region `1` by the second, and the exterior region `2` by
both blades together.  That this face data really describes a windmill is expressed separately, by
`isTwoBladedWindmill_ofTwoBladedWindmill`. -/
def ofTwoBladedWindmill (G : SimpleGraph Vertex) (hG : G.Connected)
    (blade₁ blade₂ : Finset Vertex)
    (bladeEdges₁ bladeEdges₂ : Finset (Sym2 Vertex)) : PlaneGraph Vertex (Fin 3) where
  graph := G
  connected := hG
  boundary := fun R => if R = 0 then blade₁ else if R = 1 then blade₂ else Finset.univ
  boundaryEdges := fun R =>
    if R = 0 then bladeEdges₁ else if R = 1 then bladeEdges₂ else bladeEdges₁ ∪ bladeEdges₂
  exterior := 2

variable (G : SimpleGraph Vertex) (hG : G.Connected) (blade₁ blade₂ : Finset Vertex)
  (bladeEdges₁ bladeEdges₂ : Finset (Sym2 Vertex))

/-- Two blades covering the vertex set and meeting exactly in the hub do give the canonical
realization the face structure of a two-bladed windmill. -/
theorem isTwoBladedWindmill_ofTwoBladedWindmill {hub : Vertex}
    (hcover : blade₁ ∪ blade₂ = Finset.univ) (hmeet : blade₁ ∩ blade₂ = {hub}) :
    (ofTwoBladedWindmill G hG blade₁ blade₂ bladeEdges₁ bladeEdges₂).IsTwoBladedWindmill
      0 1 2 hub where
  boundary_union := by simpa [ofTwoBladedWindmill] using hcover.symm
  boundary_inter := by simpa [ofTwoBladedWindmill] using hmeet

/-- **Proposition 2.2.1 (Bowling, 2023).** For every multiset `S` of two cycles the Dutch windmill
graph `D(S)` is not zonal: two cycles meeting in a single hub admit no zonal labeling. -/
theorem not_isZonal_ofTwoBladedWindmill {hub : Vertex}
    (hcover : blade₁ ∪ blade₂ = Finset.univ) (hmeet : blade₁ ∩ blade₂ = {hub}) :
    ¬ (ofTwoBladedWindmill G hG blade₁ blade₂ bladeEdges₁ bladeEdges₂).IsZonal :=
  not_isZonal_of_isTwoBladedWindmill
    (isTwoBladedWindmill_ofTwoBladedWindmill G hG blade₁ blade₂ bladeEdges₁ bladeEdges₂
      hcover hmeet)

end PlaneGraph

end ZonalGraphs
